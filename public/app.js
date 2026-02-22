// --- Unicode shortcut table ---
const UNICODE_SHORTCUTS = {
  '\\and':     '∧',
  '\\or':      '∨',
  '\\to':      '→',
  '\\->':      '→',
  '\\not':     '¬',
  '\\neg':     '¬',
  '\\iff':     '↔',
  '\\<->':     '↔',
  '\\forall':  '∀',
  '\\exists':  '∃',
  '\\lam':     'λ',
  '\\fun':     'λ',
  '\\langle':  '⟨',
  '\\rangle':  '⟩',
  '\\la':      '⟨',
  '\\ra':      '⟩',
  '\\sub':     '⊂',
  '\\sup':     '⊃',
  '\\x':       '×',
  '\\times':   '×',
  '\\ne':      '≠',
  '\\le':      '≤',
  '\\ge':      '≥',
  '\\inf':     '∞',
  '\\nat':     'ℕ',
  '\\int':     'ℤ',
  '\\rat':     'ℚ',
  '\\real':    'ℝ',
  '\\comp':    '∘',
  '\\circ':    '∘',
  '\\empty':   '∅',
  '\\in':      '∈',
  '\\notin':   '∉',
  '\\union':   '∪',
  '\\inter':   '∩',
  '\\alpha':   'α',
  '\\beta':    'β',
  '\\gamma':   'γ',
  '\\delta':   'δ',
  '\\epsilon': 'ε',
  '\\sigma':   'σ',
  '\\tau':     'τ',
  '\\phi':     'φ',
  '\\psi':     'ψ',
  '\\omega':   'ω',
  '\\Pi':      'Π',
  '\\Sigma':   'Σ',
};

const SHORTCUT_PREFIXES = new Set();
for (const key of Object.keys(UNICODE_SHORTCUTS)) {
  for (let i = 1; i <= key.length; i++) {
    SHORTCUT_PREFIXES.add(key.substring(0, i));
  }
}

// Shortcuts that are also strict prefixes of longer shortcuts
const HAS_LONGER_MATCH = new Set();
for (const key of Object.keys(UNICODE_SHORTCUTS)) {
  for (const other of Object.keys(UNICODE_SHORTCUTS)) {
    if (other !== key && other.startsWith(key)) {
      HAS_LONGER_MATCH.add(key);
      break;
    }
  }
}

// --- CodeMirror Lean mode ---
CodeMirror.defineMode('lean4', function () {
  const keywords = new Set([
    'theorem', 'def', 'lemma', 'example', 'variable', 'section', 'end',
    'namespace', 'open', 'import', 'set_option', 'universe', 'axiom',
    'class', 'instance', 'structure', 'inductive', 'where', 'with',
    'let', 'in', 'have', 'show', 'fun', 'match', 'do', 'return', 'if',
    'then', 'else', 'for', 'by', 'at', 'deriving',
  ]);

  const tactics = new Set([
    'intro', 'intros', 'apply', 'exact', 'assumption', 'constructor',
    'cases', 'left', 'right', 'have', 'obtain', 'sorry', 'rfl',
    'simp', 'ring', 'omega', 'trivial', 'contradiction', 'exfalso',
    'rcases', 'rintro', 'refine', 'use', 'specialize', 'revert',
    'clear', 'rename_i', 'subst', 'induction', 'all_goals', 'any_goals',
    'try', 'repeat', 'first', 'rw', 'rewrite', 'calc',
  ]);

  const builtinTypes = new Set([
    'Prop', 'Type', 'Sort', 'Nat', 'Int', 'Bool', 'True', 'False',
    'And', 'Or', 'Not', 'Iff', 'Exists', 'Eq',
  ]);

  return {
    startState: function () {
      return { inComment: false, commentDepth: 0 };
    },
    token: function (stream, state) {
      if (state.inComment) {
        while (!stream.eol()) {
          if (stream.match('/-')) {
            state.commentDepth++;
          } else if (stream.match('-/')) {
            state.commentDepth--;
            if (state.commentDepth === 0) {
              state.inComment = false;
              return 'comment';
            }
          } else {
            stream.next();
          }
        }
        return 'comment';
      }

      if (stream.match('/-')) {
        state.inComment = true;
        state.commentDepth = 1;
        while (!stream.eol()) {
          if (stream.match('/-')) {
            state.commentDepth++;
          } else if (stream.match('-/')) {
            state.commentDepth--;
            if (state.commentDepth === 0) {
              state.inComment = false;
              return 'comment';
            }
          } else {
            stream.next();
          }
        }
        return 'comment';
      }

      if (stream.match('--')) {
        stream.skipToEnd();
        return 'comment';
      }

      if (stream.match(/^"(?:[^"\\]|\\.)*"/)) return 'string';

      if (stream.match(/^\d+/)) return 'number';

      if (stream.match(/^[(){}⟨⟩\[\]]/)) return 'bracket';

      if (stream.match(/^[:=|→←↔∧∨¬∀∃λ⊂⊃∈∉∪∩×∘≤≥≠]+/)) return 'operator';
      if (stream.match(/^[<>\-\+\*\/\\\.,:;@#$&!]+/)) return 'operator';

      if (stream.match(/^[a-zA-Z_]\w*'*/)) {
        const word = stream.current();
        if (keywords.has(word)) return 'keyword';
        if (tactics.has(word)) return 'builtin';
        if (builtinTypes.has(word)) return 'type';
        if (word === 'sorry') return 'error';
        if (word[0] === word[0].toUpperCase() && word[0] !== '_') return 'variable-2';
        return 'variable';
      }

      stream.next();
      return null;
    },
  };
});

// --- Editor setup ---
const INITIAL_CODE = `variable (A B : Prop)

example : A ∧ (A → B) → B := by
  intro h
`;

const editor = CodeMirror(document.getElementById('editor-container'), {
  value: INITIAL_CODE,
  mode: 'lean4',
  theme: 'material-darker',
  lineNumbers: true,
  matchBrackets: true,
  autoCloseBrackets: true,
  indentUnit: 2,
  tabSize: 2,
  indentWithTabs: false,
  lineWrapping: true,
  extraKeys: {
    Tab: function (cm) {
      cm.replaceSelection('  ', 'end');
    },
  },
});

// --- Unicode shortcut handling ---
let shortcutBuffer = '';
let shortcutStart = null;

editor.on('inputRead', function (cm, change) {
  if (change.origin !== '+input') return;
  const inserted = change.text.join('\n');

  if (inserted === ' ' && shortcutBuffer) {
    const replacement = UNICODE_SHORTCUTS[shortcutBuffer];
    if (replacement) {
      const cursor = cm.getCursor();
      cm.replaceRange(replacement, shortcutStart, cursor);
      shortcutBuffer = '';
      shortcutStart = null;
      return;
    }
    shortcutBuffer = '';
    shortcutStart = null;
    return;
  }

  if (inserted === '\\' && !shortcutBuffer) {
    shortcutBuffer = '\\';
    shortcutStart = { line: change.from.line, ch: change.from.ch };
    return;
  }

  if (shortcutBuffer) {
    shortcutBuffer += inserted;

    if (UNICODE_SHORTCUTS[shortcutBuffer] && !HAS_LONGER_MATCH.has(shortcutBuffer)) {
      const cursor = cm.getCursor();
      cm.replaceRange(UNICODE_SHORTCUTS[shortcutBuffer], shortcutStart, cursor);
      shortcutBuffer = '';
      shortcutStart = null;
      return;
    }

    if (!SHORTCUT_PREFIXES.has(shortcutBuffer)) {
      // No shortcut starts with this sequence; check if dropping the last
      // character gives a valid shortcut (user finished typing the shortcut
      // and moved on to the next character).
      const withoutLast = shortcutBuffer.slice(0, -1);
      if (UNICODE_SHORTCUTS[withoutLast]) {
        const cursor = cm.getCursor();
        const endOfShortcut = { line: cursor.line, ch: cursor.ch - inserted.length };
        cm.replaceRange(UNICODE_SHORTCUTS[withoutLast], shortcutStart, endOfShortcut);
      }
      shortcutBuffer = '';
      shortcutStart = null;
    }
  }
});

// --- API interaction ---
const statusEl = document.getElementById('status-indicator');
const termTypeEl = document.getElementById('term-type');
const termBodyEl = document.getElementById('term-body');
const termErrorsEl = document.getElementById('term-errors');

let debounceTimer = null;
let requestId = 0;

function setStatus(type, text) {
  statusEl.className = 'status ' + type;
  statusEl.textContent = text;
}

function highlightTerm(displayTerm) {
  if (!displayTerm) return '';

  const escaped = displayTerm
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');

  let html = escaped.replace(/\?/g, '<span class="sorry-hole">?</span>');

  const termKeywords = ['fun', 'let', 'match', 'have', 'show', 'if', 'then', 'else', 'in'];
  for (const kw of termKeywords) {
    const re = new RegExp('\\b(' + kw + ')\\b', 'g');
    html = html.replace(re, '<span class="keyword">$1</span>');
  }

  const constructors = [
    'And\\.casesOn', 'And\\.intro', 'Or\\.casesOn', 'Or\\.inl', 'Or\\.inr',
    'Eq\\.refl', 'Iff\\.intro', 'Exists\\.intro',
  ];
  for (const c of constructors) {
    const re = new RegExp('\\b(' + c + ')\\b', 'g');
    html = html.replace(re, '<span class="constructor-name">$1</span>');
  }

  return html;
}

async function elaborate() {
  const code = editor.getValue();
  const currentRequest = ++requestId;

  setStatus('loading', 'Elaborating...');

  try {
    const resp = await fetch('/api/elaborate', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ code }),
    });

    if (currentRequest !== requestId) return;

    const data = await resp.json();

    if (data.type) {
      termTypeEl.textContent = data.type;
    } else {
      termTypeEl.textContent = '';
    }

    if (data.displayTerm) {
      termBodyEl.innerHTML = highlightTerm(data.displayTerm);
    } else if (data.errors && data.errors.length > 0) {
      termBodyEl.innerHTML = '<span class="placeholder">Could not extract term.</span>';
    } else {
      termBodyEl.innerHTML = '<span class="placeholder">No term generated yet.</span>';
    }

    termErrorsEl.innerHTML = '';
    if (data.errors && data.errors.length > 0) {
      for (const err of data.errors) {
        const div = document.createElement('div');
        div.className = 'error-item';
        div.textContent = err;
        termErrorsEl.appendChild(div);
      }
    }

    if (data.complete) {
      setStatus('complete', 'Proof complete');
    } else if (data.displayTerm) {
      setStatus('incomplete', 'Proof incomplete');
    } else if (data.errors && data.errors.length > 0) {
      setStatus('error', 'Error');
    } else {
      setStatus('', '');
    }
  } catch (err) {
    if (currentRequest !== requestId) return;
    setStatus('error', 'Connection error');
    termBodyEl.innerHTML = '<span class="placeholder">Failed to connect to server.</span>';
  }
}

editor.on('change', function () {
  clearTimeout(debounceTimer);
  debounceTimer = setTimeout(elaborate, 1500);
});

elaborate();
