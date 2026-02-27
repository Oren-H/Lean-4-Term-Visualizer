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

const MAX_CACHE = 20;
const elaborateCache = new Map();
const goalsCache = new Map();

function getCacheKey(code) {
  return crypto.createHash('sha256').update(code).digest('hex');
}

function cacheSet(cache, key, value) {
  if (cache.size >= MAX_CACHE) {
    const oldest = cache.keys().next().value;
    cache.delete(oldest);
  }
  cache.set(key, value);
}

function rewriteCodeForExtraction(userCode) {
  let code = userCode;

  const exampleRe = /\bexample\s*(?=[\(\{\[:])/;
  const theoremRe = /\btheorem\s+(\w+)/;

  let printName = THEOREM_NAME;
  const theoremMatch = code.match(theoremRe);

  if (theoremMatch) {
    printName = theoremMatch[1];
  } else if (exampleRe.test(code)) {
    code = code.replace(/\bexample\b/, `theorem ${THEOREM_NAME}`);
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
        /:\d+:\d+: (error|warning):/.test(line)
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

function parseErrors(stdout, stderr, maxLine) {
  const errors = [];
  const combined = stdout + '\n' + stderr;
  const lines = combined.split('\n');
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    if (line.includes(': error:')) {
      if (maxLine !== undefined) {
        const lineMatch = line.match(/:(\d+):\d+:/);
        if (lineMatch && parseInt(lineMatch[1]) > maxLine) continue;
      }
      const msgStart = line.indexOf(': error:') + 8;
      let msg = line.substring(msgStart).trim();
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

function parseTheoremHypotheses(userCode) {
  const lines = userCode.split('\n');
  let sigText = '';
  let found = false;

  for (const line of lines) {
    const trimmed = line.trim();
    if (!found) {
      if (/\b(theorem|example)\b/.test(trimmed)) {
        found = true;
        sigText += trimmed;
      }
    } else {
      sigText += ' ' + trimmed;
    }
    if (found && sigText.includes(':= by')) break;
  }

  if (!found) return [];

  const byIdx = sigText.indexOf(':= by');
  if (byIdx === -1) return [];

  let afterKeyword = sigText;
  const theoremMatch = afterKeyword.match(/\btheorem\s+\S+\s*/);
  const exampleMatch = afterKeyword.match(/\bexample\s*/);
  if (theoremMatch) {
    afterKeyword = afterKeyword.substring(theoremMatch.index + theoremMatch[0].length);
  } else if (exampleMatch) {
    afterKeyword = afterKeyword.substring(exampleMatch.index + exampleMatch[0].length);
  } else {
    return [];
  }

  const sigBody = afterKeyword.substring(0, afterKeyword.indexOf(':= by')).trim();

  let lastColonAtDepth0 = -1;
  let depth = 0;
  for (let i = 0; i < sigBody.length; i++) {
    const ch = sigBody[i];
    if (ch === '(' || ch === '{' || ch === '[') depth++;
    else if (ch === ')' || ch === '}' || ch === ']') depth--;
    else if (ch === ':' && depth === 0) lastColonAtDepth0 = i;
  }

  if (lastColonAtDepth0 === -1) return [];

  const paramsSection = sigBody.substring(0, lastColonAtDepth0).trim();
  if (!paramsSection) return [];

  const params = parseFunParams(paramsSection);
  return params.map(p => p.name);
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

function stripLeadingArrows(type, count) {
  if (!type || count <= 0) return type;
  let result = type.trim();
  const arrow = '→';
  for (let i = 0; i < count; i++) {
    let depth = 0;
    let arrowIdx = -1;
    for (let j = 0; j < result.length; j++) {
      const ch = result[j];
      if (ch === '(' || ch === '{' || ch === '[') depth++;
      else if (ch === ')' || ch === '}' || ch === ']') depth--;
      else if (depth === 0 && result.startsWith(arrow, j)) {
        arrowIdx = j;
        break;
      }
    }
    if (arrowIdx === -1) break;
    result = result.substring(arrowIdx + arrow.length).trim();
  }
  return result;
}

function rewriteCodeForGoalState(userCode, cursorLine) {
  let code = userCode;

  const exampleRe = /\bexample\s*(?=[\(\{\[:])/;
  const theoremRe = /\btheorem\s+(\w+)/;

  if (!theoremRe.test(code) && exampleRe.test(code)) {
    code = code.replace(/\bexample\b/, `theorem ${THEOREM_NAME}`);
  }

  let byLineIdx = -1;
  const codeLines = code.split('\n');
  for (let i = 0; i < codeLines.length; i++) {
    if (codeLines[i].includes(':= by')) {
      byLineIdx = i;
      break;
    }
  }

  if (byLineIdx === -1) {
    return { code: null, error: 'No ":= by" tactic block found.' };
  }

  const keepUntilLine = Math.max(byLineIdx, Math.min(cursorLine, codeLines.length - 1));
  const keptLines = codeLines.slice(0, keepUntilLine + 1);
  const truncated = keptLines.join('\n');

  return { code: truncated, error: null };
}

function parseGoalState(stdout, stderr) {
  const combined = stdout + '\n' + stderr;
  const lines = combined.split('\n');
  const goals = [];
  let i = 0;

  while (i < lines.length) {
    if (lines[i].includes('unsolved goals')) {
      i++;
      while (i < lines.length) {
        while (i < lines.length && lines[i].trim() === '') i++;
        if (i >= lines.length) break;

        if (lines[i].match(/^\S.*:\d+:\d+:/) || lines[i].includes(': error:') || lines[i].includes(': warning:')) {
          break;
        }

        let caseName = null;
        const caseMatch = lines[i].match(/^case\s+(.+)/);
        if (caseMatch) {
          caseName = caseMatch[1].trim();
          i++;
        }

        const hypotheses = [];
        let target = '';

        while (i < lines.length) {
          const line = lines[i];
          if (line.startsWith('⊢') || line.startsWith('|-')) {
            target = line.replace(/^⊢\s*/, '').replace(/^\|-\s*/, '').trim();
            i++;
            while (i < lines.length && lines[i].startsWith('  ')) {
              target += ' ' + lines[i].trim();
              i++;
            }
            break;
          }
          if (line.trim() === '' || line.match(/^\S.*:\d+:\d+:/)) break;
          hypotheses.push(line.trim());
          i++;
        }

        if (target) {
          goals.push({ caseName, hypotheses, target });
        } else {
          break;
        }
      }
      break;
    }
    i++;
  }

  return goals;
}

let activeGoalsProc = null;
let activeGoalsTmpFile = null;

app.post('/api/goals', (req, res) => {
  const { code: userCode, cursorLine } = req.body;

  if (!userCode || typeof userCode !== 'string') {
    return res.status(400).json({ error: 'Missing "code" field.' });
  }
  if (typeof cursorLine !== 'number') {
    return res.status(400).json({ error: 'Missing "cursorLine" field.' });
  }

  if (activeGoalsProc) {
    activeGoalsProc.kill();
    activeGoalsProc = null;
    if (activeGoalsTmpFile) {
      try { fs.unlinkSync(activeGoalsTmpFile); } catch (_) {}
      activeGoalsTmpFile = null;
    }
  }

  const { code, error } = rewriteCodeForGoalState(userCode, cursorLine);
  if (error) {
    return res.json({ goals: [], error });
  }

  const goalsCacheKey = getCacheKey(code);
  const cachedOutput = goalsCache.get(goalsCacheKey);
  if (cachedOutput) {
    const goals = parseGoalState(cachedOutput.stdout, cachedOutput.stderr);
    return res.json({ goals });
  }

  const tmpDir = os.tmpdir();
  const tmpFile = path.join(tmpDir, `lean_goals_${crypto.randomBytes(6).toString('hex')}.lean`);

  fs.writeFileSync(tmpFile, code, 'utf-8');
  activeGoalsTmpFile = tmpFile;

  const env = { ...process.env, ELAN_OFFLINE: '1' };
  const proc = execFile('lean', [tmpFile], { timeout: LEAN_TIMEOUT_MS, env }, (err, stdout, stderr) => {
    if (activeGoalsProc === proc) {
      activeGoalsProc = null;
      activeGoalsTmpFile = null;
    }
    try { fs.unlinkSync(tmpFile); } catch (_) {}

    if (err && err.killed) return;

    cacheSet(goalsCache, goalsCacheKey, { stdout, stderr });
    const goals = parseGoalState(stdout, stderr);
    res.json({ goals });
  });
  activeGoalsProc = proc;
});

let activeElaborateProc = null;
let activeElaborateTmpFile = null;

app.post('/api/elaborate', (req, res) => {
  const { code: userCode } = req.body;

  if (!userCode || typeof userCode !== 'string') {
    return res.status(400).json({ error: 'Missing "code" field.' });
  }

  if (activeElaborateProc) {
    activeElaborateProc.kill();
    activeElaborateProc = null;
    if (activeElaborateTmpFile) {
      try { fs.unlinkSync(activeElaborateTmpFile); } catch (_) {}
      activeElaborateTmpFile = null;
    }
  }

  const { code, printName, error } = rewriteCodeForExtraction(userCode);
  if (error) {
    return res.json({ term: null, displayTerm: null, errors: [error], complete: false });
  }

  const cacheKey = getCacheKey(userCode);
  const cached = elaborateCache.get(cacheKey);
  if (cached) {
    return res.json(cached);
  }

  const tmpDir = os.tmpdir();
  const tmpFile = path.join(tmpDir, `lean_vis_${crypto.randomBytes(6).toString('hex')}.lean`);

  fs.writeFileSync(tmpFile, code, 'utf-8');
  activeElaborateTmpFile = tmpFile;

  const env = { ...process.env, ELAN_OFFLINE: '1' };
  const proc = execFile('lean', [tmpFile], { timeout: LEAN_TIMEOUT_MS, env }, (err, stdout, stderr) => {
    if (activeElaborateProc === proc) {
      activeElaborateProc = null;
      activeElaborateTmpFile = null;
    }
    try { fs.unlinkSync(tmpFile); } catch (_) {}

    if (err && err.killed) return;

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
    const hypNames = parseTheoremHypotheses(userCode);
    const allStripNames = [...varNames, ...hypNames];

    const strippedTerm = rawTerm ? stripVariableParams(rawTerm, allStripNames) : rawTerm;
    const strippedType = fullType ? stripForallPrefix(fullType, varNames) : fullType;
    const displayType = strippedType ? stripLeadingArrows(strippedType, hypNames.length) : strippedType;

    const displayTerm = strippedTerm ? formatTermForDisplay(strippedTerm) : null;
    const complete = rawTerm ? !rawTerm.includes('sorry') : false;

    const result = {
      term: strippedTerm || null,
      displayTerm: displayTerm || null,
      type: displayType || null,
      errors,
      complete,
    };

    cacheSet(elaborateCache, cacheKey, result);
    res.json(result);
  });
  activeElaborateProc = proc;
});

const GOALS_THEOREM_NAME = '_lean_vis_goals';

function rewriteCodeForCombined(userCode, cursorLine) {
  const elaborate = rewriteCodeForExtraction(userCode);
  if (elaborate.error) {
    return { code: null, printName: null, elaborateLineCount: 0, error: elaborate.error };
  }

  const elaborateLineCount = elaborate.code.split('\n').length;

  let goalsCode = userCode;
  const exampleRe = /\bexample\s*(?=[\(\{\[:])/;
  const theoremRe = /\btheorem\s+(\w+)/;

  if (!theoremRe.test(goalsCode) && exampleRe.test(goalsCode)) {
    goalsCode = goalsCode.replace(/\bexample\b/, `theorem ${THEOREM_NAME}`);
  }

  const codeLines = goalsCode.split('\n');
  let byLineIdx = -1;
  for (let i = 0; i < codeLines.length; i++) {
    if (codeLines[i].includes(':= by')) {
      byLineIdx = i;
      break;
    }
  }

  if (byLineIdx === -1) {
    return { code: elaborate.code, printName: elaborate.printName, elaborateLineCount, error: null };
  }

  let theoremLineIdx = -1;
  for (let i = 0; i < codeLines.length; i++) {
    if (/\btheorem\s+/.test(codeLines[i])) {
      theoremLineIdx = i;
      break;
    }
  }

  if (theoremLineIdx === -1) {
    return { code: elaborate.code, printName: elaborate.printName, elaborateLineCount, error: null };
  }

  const keepUntilLine = Math.max(byLineIdx, Math.min(cursorLine, codeLines.length - 1));
  const goalsTheoremLines = codeLines.slice(theoremLineIdx, keepUntilLine + 1);
  let goalsSection = goalsTheoremLines.join('\n');
  goalsSection = goalsSection.replace(/\btheorem\s+\S+/, `theorem ${GOALS_THEOREM_NAME}`);

  const combined = elaborate.code + '\n' + goalsSection + '\n';
  return { code: combined, printName: elaborate.printName, elaborateLineCount, error: null };
}

const checkCache = new Map();
let activeCheckProc = null;
let activeCheckTmpFile = null;

app.post('/api/check', (req, res) => {
  const { code: userCode, cursorLine } = req.body;

  if (!userCode || typeof userCode !== 'string') {
    return res.status(400).json({ error: 'Missing "code" field.' });
  }
  if (typeof cursorLine !== 'number') {
    return res.status(400).json({ error: 'Missing "cursorLine" field.' });
  }

  if (activeCheckProc) {
    activeCheckProc.kill();
    activeCheckProc = null;
    if (activeCheckTmpFile) {
      try { fs.unlinkSync(activeCheckTmpFile); } catch (_) {}
      activeCheckTmpFile = null;
    }
  }

  const checkCacheKey = getCacheKey(userCode + ':' + cursorLine);
  const cachedCheck = checkCache.get(checkCacheKey);
  if (cachedCheck) {
    return res.json(cachedCheck);
  }

  const elaborateCacheKey = getCacheKey(userCode);
  const cachedElaborate = elaborateCache.get(elaborateCacheKey);
  const { code: goalsOnlyCode } = rewriteCodeForGoalState(userCode, cursorLine);
  const goalsCacheKey = goalsOnlyCode ? getCacheKey(goalsOnlyCode) : null;
  const cachedGoalsOutput = goalsCacheKey ? goalsCache.get(goalsCacheKey) : null;

  if (cachedElaborate && cachedGoalsOutput) {
    const goals = parseGoalState(cachedGoalsOutput.stdout, cachedGoalsOutput.stderr);
    const result = { ...cachedElaborate, goals };
    cacheSet(checkCache, checkCacheKey, result);
    return res.json(result);
  }

  const { code, printName, elaborateLineCount, error } = rewriteCodeForCombined(userCode, cursorLine);
  if (error) {
    return res.json({ term: null, displayTerm: null, errors: [error], complete: false, goals: [] });
  }

  const tmpDir = os.tmpdir();
  const tmpFile = path.join(tmpDir, `lean_check_${crypto.randomBytes(6).toString('hex')}.lean`);

  fs.writeFileSync(tmpFile, code, 'utf-8');
  activeCheckTmpFile = tmpFile;

  const env = { ...process.env, ELAN_OFFLINE: '1' };
  const proc = execFile('lean', [tmpFile], { timeout: LEAN_TIMEOUT_MS, env }, (err, stdout, stderr) => {
    if (activeCheckProc === proc) {
      activeCheckProc = null;
      activeCheckTmpFile = null;
    }
    try { fs.unlinkSync(tmpFile); } catch (_) {}

    if (err && err.killed) return;

    let parseSource = stdout;
    if (!parseSource.includes(`theorem ${printName}`)) {
      parseSource = stderr;
    }
    if (!parseSource.includes(`theorem ${printName}`)) {
      parseSource = stdout + '\n' + stderr;
    }

    const { rawTerm, fullType } = parsePrintOutput(parseSource, printName);
    const errors = parseErrors(stdout, stderr, elaborateLineCount);

    const varNames = parseVariableNames(userCode);
    const hypNames = parseTheoremHypotheses(userCode);
    const allStripNames = [...varNames, ...hypNames];

    const strippedTerm = rawTerm ? stripVariableParams(rawTerm, allStripNames) : rawTerm;
    const strippedType = fullType ? stripForallPrefix(fullType, varNames) : fullType;
    const displayType = strippedType ? stripLeadingArrows(strippedType, hypNames.length) : strippedType;

    const displayTerm = strippedTerm ? formatTermForDisplay(strippedTerm) : null;
    const complete = rawTerm ? !rawTerm.includes('sorry') : false;

    const elaborateResult = {
      term: strippedTerm || null,
      displayTerm: displayTerm || null,
      type: displayType || null,
      errors,
      complete,
    };
    cacheSet(elaborateCache, elaborateCacheKey, elaborateResult);

    const goals = parseGoalState(stdout, stderr);

    if (goalsOnlyCode) {
      cacheSet(goalsCache, getCacheKey(goalsOnlyCode), { stdout, stderr });
    }

    const result = { ...elaborateResult, goals };
    cacheSet(checkCache, checkCacheKey, result);
    res.json(result);
  });
  activeCheckProc = proc;
});

app.listen(PORT, '0.0.0.0', () => {
  console.log(`Lean Term Visualizer running on port ${PORT}`);
});
