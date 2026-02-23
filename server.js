const express = require('express');
const { execFile } = require('child_process');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');

const app = express();
const PORT = process.env.PORT || 3000;

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

const LEAN_TIMEOUT_MS = 15000;
const THEOREM_NAME = '_lean_vis_tmp';

function rewriteCodeForExtraction(userCode) {
  let code = userCode;

  const exampleRe = /\bexample\s*:/;
  const theoremRe = /\btheorem\s+(\w+)\s*:/;

  let printName = THEOREM_NAME;
  const theoremMatch = code.match(theoremRe);

  if (theoremMatch) {
    printName = theoremMatch[1];
  } else if (exampleRe.test(code)) {
    code = code.replace(exampleRe, `theorem ${THEOREM_NAME} :`);
    printName = THEOREM_NAME;
  } else {
    return { code: null, printName: null, error: 'No theorem or example found in code.' };
  }

  const byIndex = code.lastIndexOf(':= by');
  if (byIndex === -1) {
    return { code: null, printName: null, error: 'No ":= by" tactic block found.' };
  }

  const afterBy = code.substring(byIndex + 5);
  const lines = afterBy.split('\n');

  let indentLevel = 2;
  for (const line of lines) {
    const stripped = line.trimStart();
    if (stripped.length > 0 && stripped !== 'by') {
      indentLevel = line.length - stripped.length;
      break;
    }
  }

  const indent = ' '.repeat(indentLevel);
  code = code.trimEnd() + `\n${indent}try all_goals sorry\n`;
  code += `\nset_option pp.funBinderTypes true in\n#print ${printName}\n`;

  return { code, printName, error: null };
}

function parsePrintOutput(output, printName) {
  const lines = output.split('\n');
  let capturing = false;
  let termLines = [];
  let typeLine = '';

  for (const line of lines) {
    if (!capturing) {
      const prefix = `theorem ${printName}`;
      if (line.startsWith(prefix)) {
        capturing = true;
        typeLine = line;
        const assignIdx = line.indexOf(':=');
        if (assignIdx !== -1) {
          const after = line.substring(assignIdx + 2).trim();
          if (after) {
            termLines.push(after);
          }
        }
      }
    } else {
      if (
        line.startsWith('theorem ') ||
        line.startsWith('#') ||
        line.startsWith('def ') ||
        line.startsWith('warning:') ||
        line.startsWith('/') && line.includes(': warning:')
      ) {
        break;
      }
      termLines.push(line);
    }
  }

  let rawTerm = termLines.join('\n').trim();

  const typeMatch = typeLine.match(/theorem\s+\S+\s*:\s*(.*?)\s*:=\s*$/);
  const fullType = typeMatch ? typeMatch[1] : '';

  return { rawTerm, fullType };
}

function parseErrors(stdout, stderr) {
  const errors = [];
  const combined = stdout + '\n' + stderr;
  const lines = combined.split('\n');
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.includes(': error:')) {
      const msgStart = line.indexOf(': error:') + 8;
      let msg = line.substring(msgStart).trim();
      // Collect continuation lines (indented or "Note:" lines)
      for (let j = i + 1; j < lines.length; j++) {
        const next = lines[j];
        if (next.startsWith('  ') || next.startsWith('Note:')) {
          msg += '\n' + next;
          i = j;
        } else {
          break;
        }
      }
      errors.push(msg);
    }
  }
  return errors;
}

function formatTermForDisplay(rawTerm) {
  let term = rawTerm.replace(/\bsorry\b/g, '?');
  return term;
}

function parseVariableNames(userCode) {
  const names = [];
  const lines = userCode.split('\n');
  for (const line of lines) {
    const trimmed = line.trim();
    if (!trimmed.startsWith('variable')) continue;
    const rest = trimmed.substring('variable'.length);
    const groupRe = /[({[\[]([^)}\]]*)[)}\]]/g;
    let match;
    while ((match = groupRe.exec(rest)) !== null) {
      const inside = match[1].trim();
      const colonIdx = inside.indexOf(':');
      if (colonIdx !== -1) {
        const namesPart = inside.substring(0, colonIdx).trim();
        for (const n of namesPart.split(/\s+/)) {
          if (n) names.push(n);
        }
      }
    }
  }
  return names;
}

function parseFunParams(paramsStr) {
  const params = [];
  let i = 0;
  const s = paramsStr.trim();

  while (i < s.length) {
    while (i < s.length && /\s/.test(s[i])) i++;
    if (i >= s.length) break;

    if (s[i] === '(' || s[i] === '{' || s[i] === '[') {
      const open = s[i];
      const close = open === '(' ? ')' : open === '{' ? '}' : ']';
      const start = i;
      let depth = 1;
      i++;
      while (i < s.length && depth > 0) {
        if (s[i] === open) depth++;
        else if (s[i] === close) depth--;
        i++;
      }
      const raw = s.substring(start, i);
      const inner = s.substring(start + 1, i - 1).trim();
      const colonIdx = inner.indexOf(':');
      if (colonIdx !== -1) {
        const namesPart = inner.substring(0, colonIdx).trim();
        const typePart = inner.substring(colonIdx + 1).trim();
        const individualNames = namesPart.split(/\s+/).filter(n => n);
        for (const name of individualNames) {
          params.push({ name, type: typePart, raw: `(${name} : ${typePart})` });
        }
      } else {
        params.push({ name: inner, type: null, raw });
      }
    } else {
      const start = i;
      while (i < s.length && !/\s/.test(s[i])) i++;
      const name = s.substring(start, i);
      params.push({ name, type: null, raw: name });
    }
  }

  return params;
}

function stripVariableParams(rawTerm, varNames) {
  if (!rawTerm || varNames.length === 0) return rawTerm;

  const varSet = new Set(varNames);
  const funMatch = rawTerm.match(/^fun\s+([\s\S]*?)\s*=>([\s\S]*)$/);
  if (!funMatch) return rawTerm;

  const params = parseFunParams(funMatch[1]);
  const body = funMatch[2];

  let stripCount = 0;
  for (const param of params) {
    if (varSet.has(param.name)) {
      stripCount++;
    } else {
      break;
    }
  }

  if (stripCount === 0) return rawTerm;

  const remaining = params.slice(stripCount);
  if (remaining.length > 0) {
    const paramStr = remaining.map(p => p.raw).join(' ');
    return 'fun ' + paramStr + ' =>' + body;
  }
  return body.trim();
}

function stripForallPrefix(fullType, varNames) {
  if (!fullType || varNames.length === 0) return fullType;

  let type = fullType.trim();
  const varSet = new Set(varNames);

  while (type.startsWith('∀') || type.startsWith('forall')) {
    const prefix = type.startsWith('∀') ? '∀' : 'forall';
    const afterPrefix = type.substring(prefix.length).trimStart();

    let depth = 0;
    let commaIdx = -1;
    for (let i = 0; i < afterPrefix.length; i++) {
      const ch = afterPrefix[i];
      if (ch === '(' || ch === '{' || ch === '[') depth++;
      else if (ch === ')' || ch === '}' || ch === ']') depth--;
      else if (ch === ',' && depth === 0) {
        commaIdx = i;
        break;
      }
    }

    if (commaIdx === -1) break;

    const binderSection = afterPrefix.substring(0, commaIdx);
    const binderGroupRe = /[({[\[]([^)}\]]*)[)}\]]/g;
    let match;
    const binderNames = [];
    while ((match = binderGroupRe.exec(binderSection)) !== null) {
      const inside = match[1].trim();
      const colonIdx = inside.indexOf(':');
      if (colonIdx !== -1) {
        const namesPart = inside.substring(0, colonIdx).trim();
        for (const n of namesPart.split(/\s+/)) {
          if (n) binderNames.push(n);
        }
      }
    }

    if (binderNames.length === 0) break;
    if (!binderNames.every(n => varSet.has(n))) break;

    type = afterPrefix.substring(commaIdx + 1).trim();
  }

  return type;
}

app.post('/api/elaborate', (req, res) => {
  const { code: userCode } = req.body;

  if (!userCode || typeof userCode !== 'string') {
    return res.status(400).json({ error: 'Missing "code" field.' });
  }

  const { code, printName, error } = rewriteCodeForExtraction(userCode);
  if (error) {
    return res.json({ term: null, displayTerm: null, errors: [error], complete: false });
  }

  const tmpDir = os.tmpdir();
  const tmpFile = path.join(tmpDir, `lean_vis_${crypto.randomBytes(6).toString('hex')}.lean`);

  fs.writeFileSync(tmpFile, code, 'utf-8');

  const env = { ...process.env, ELAN_OFFLINE: '1' };
  execFile('lean', [tmpFile], { timeout: LEAN_TIMEOUT_MS, env }, (err, stdout, stderr) => {
    try { fs.unlinkSync(tmpFile); } catch (_) {}

    // #print goes to stdout in Lean 4; if not found there, check stderr too
    let parseSource = stdout;
    if (!parseSource.includes(`theorem ${printName}`)) {
      parseSource = stderr;
    }
    if (!parseSource.includes(`theorem ${printName}`)) {
      parseSource = stdout + '\n' + stderr;
    }

    const { rawTerm, fullType } = parsePrintOutput(parseSource, printName);
    const errors = parseErrors(stdout, stderr);

    const varNames = parseVariableNames(userCode);
    const strippedTerm = rawTerm ? stripVariableParams(rawTerm, varNames) : rawTerm;
    const strippedType = fullType ? stripForallPrefix(fullType, varNames) : fullType;

    const displayTerm = strippedTerm ? formatTermForDisplay(strippedTerm) : null;
    const complete = rawTerm ? !rawTerm.includes('sorry') : false;

    res.json({
      term: strippedTerm || null,
      displayTerm: displayTerm || null,
      type: strippedType || null,
      errors,
      complete,
    });
  });
});

app.listen(PORT, () => {
  console.log(`Lean Term Visualizer running at http://localhost:${PORT}`);
});
