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
  code += `\n#print ${printName}\n`;

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
    const displayTerm = rawTerm ? formatTermForDisplay(rawTerm) : null;
    const complete = rawTerm ? !rawTerm.includes('sorry') : false;

    res.json({
      term: rawTerm || null,
      displayTerm: displayTerm || null,
      type: fullType || null,
      errors,
      complete,
    });
  });
});

app.listen(PORT, () => {
  console.log(`Lean Term Visualizer running at http://localhost:${PORT}`);
});
