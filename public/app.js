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
    'Cmd-Z': 'undo',
    'Ctrl-Z': 'undo',
    'Shift-Cmd-Z': 'redo',
    'Shift-Ctrl-Z': 'redo',
    'Cmd-Y': 'redo',
    'Ctrl-Y': 'redo',
  },
});

// --- Unicode shortcut handling ---
let shortcutBuffer = '';
let shortcutStart = null;
let shortcutHistoryLen = 0;

function applyShortcutReplacement(cm, replacement, from, to) {
  const savedLen = shortcutHistoryLen;
  setTimeout(function () {
    cm.operation(function () {
      cm.replaceRange(replacement, from, to, '+input');
    });
    const hist = cm.getHistory();
    const numNew = hist.done.length - savedLen;
    if (numNew > 1) {
      const merged = hist.done.splice(savedLen);
      const allChanges = [];
      for (const event of merged) {
        if (event.changes) {
          allChanges.push(...event.changes);
        }
      }
      if (allChanges.length > 0) {
        hist.done.push({ changes: allChanges });
        cm.setHistory(hist);
      }
    }
  }, 0);
}

editor.on('inputRead', function (cm, change) {
  if (change.origin !== '+input') return;
  const inserted = change.text.join('\n');

  if (inserted === ' ' && shortcutBuffer) {
    const replacement = UNICODE_SHORTCUTS[shortcutBuffer];
    if (replacement) {
      applyShortcutReplacement(cm, replacement, shortcutStart, cm.getCursor());
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
    shortcutHistoryLen = cm.getHistory().done.length;
    return;
  }

  if (shortcutBuffer) {
    shortcutBuffer += inserted;

    if (UNICODE_SHORTCUTS[shortcutBuffer] && !HAS_LONGER_MATCH.has(shortcutBuffer)) {
      applyShortcutReplacement(cm, UNICODE_SHORTCUTS[shortcutBuffer], shortcutStart, cm.getCursor());
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
        applyShortcutReplacement(cm, UNICODE_SHORTCUTS[withoutLast], shortcutStart, endOfShortcut);
      }
      shortcutBuffer = '';
      shortcutStart = null;
    }
  }
});

// --- Tactic info modal ---
const TACTIC_INFO = {
  intro: {
    tactic: 'Introduces one hypothesis or variable from the goal into the local context. If the goal is <code>A → B</code>, then <code>intro h</code> moves <code>A</code> into the context as <code>h</code> and changes the goal to <code>B</code>.',
    term: 'Corresponds to a lambda abstraction <code>fun h =&gt; ...</code>. The introduced hypothesis becomes a bound variable in the proof term.',
    example: 'example (A B : Prop) : A → B → A := by\n  intro ha\n  intro hb\n  exact ha',
  },
  intros: {
    tactic: 'Introduces multiple hypotheses or variables at once. <code>intros h1 h2</code> is equivalent to calling <code>intro</code> repeatedly. Without names, Lean auto-generates them.',
    term: 'Corresponds to nested lambda abstractions <code>fun h1 h2 =&gt; ...</code>. Each introduced name adds another layer of binding.',
    example: 'example (A B : Prop) : A → B → A := by\n  intros ha hb\n  exact ha',
  },
  apply: {
    tactic: 'Given a lemma or hypothesis <code>f : A → B</code> and a goal <code>B</code>, <code>apply f</code> reduces the goal to <code>A</code>. Works with any number of arguments.',
    term: 'Corresponds to function application. The proof term becomes <code>f ?_</code> where each <code>?_</code> placeholder is a remaining subgoal to fill in.',
    example: 'example (A B : Prop) (ha : A) (f : A → B) : B := by\n  apply f\n  exact ha',
  },
  exact: {
    tactic: 'Closes the current goal by providing a term whose type exactly matches the goal. <code>exact h</code> finishes the goal if <code>h</code> has the right type.',
    term: 'Directly supplies the proof term. <code>exact h</code> simply inserts <code>h</code> as-is into the proof term at that position.',
    example: 'example (A : Prop) (ha : A) : A := by\n  exact ha',
  },
  assumption: {
    tactic: 'Searches the local context for a hypothesis whose type exactly matches the current goal and uses it automatically.',
    term: 'Resolves to whichever local variable (bound by <code>fun</code> or <code>have</code>) has a type matching the goal. Equivalent to <code>exact</code> with the matching hypothesis.',
    example: 'example (A : Prop) (ha : A) : A := by\n  assumption',
  },
  constructor: {
    tactic: 'When the goal is an inductive type, applies its default constructor. For <code>A ∧ B</code> it splits into two subgoals: prove <code>A</code> and prove <code>B</code>.',
    term: 'Applies the type\'s constructor directly. For conjunctions this becomes <code>And.intro _ _</code>; for existentials, <code>Exists.intro _ _</code>.',
    example: 'example (A B : Prop) (ha : A) (hb : B) : A ∧ B := by\n  constructor\n  · exact ha\n  · exact hb',
  },
  cases: {
    tactic: 'Performs case analysis on a hypothesis. For <code>h : A ∨ B</code>, creates two subgoals — one assuming <code>A</code>, one assuming <code>B</code>. Works on any inductive type.',
    term: 'Translates to a <code>.casesOn</code> eliminator or pattern match. For <code>h : A ∨ B</code>, becomes <code>Or.casesOn h (fun h1 =&gt; ...) (fun h2 =&gt; ...)</code>.',
    example: 'example (A B : Prop) (h : A ∨ B) : B ∨ A := by\n  cases h with\n  | inl ha => right; exact ha\n  | inr hb => left; exact hb',
  },
  left: {
    tactic: 'When the goal is <code>A ∨ B</code>, selects the left disjunct and changes the goal to <code>A</code>.',
    term: 'Corresponds to <code>Or.inl</code>, the left injection into a sum type. The proof term becomes <code>Or.inl _</code>.',
    example: 'example (A B : Prop) (ha : A) : A ∨ B := by\n  left\n  exact ha',
  },
  right: {
    tactic: 'When the goal is <code>A ∨ B</code>, selects the right disjunct and changes the goal to <code>B</code>.',
    term: 'Corresponds to <code>Or.inr</code>, the right injection into a sum type. The proof term becomes <code>Or.inr _</code>.',
    example: 'example (A B : Prop) (hb : B) : A ∨ B := by\n  right\n  exact hb',
  },
  have: {
    tactic: 'Introduces an intermediate lemma. <code>have h : P := proof</code> adds <code>h : P</code> to the context, then you continue proving the original goal with <code>h</code> available.',
    term: 'Corresponds to a <code>have</code> or <code>let</code> binding in the proof term: <code>have h : P := proof; body</code>. The intermediate result is bound and used in the rest of the term.',
    example: 'example (A B : Prop) (ha : A) (f : A → B) : B := by\n  have hb : B := f ha\n  exact hb',
  },
  obtain: {
    tactic: 'Destructures an existential or structure hypothesis. <code>obtain ⟨x, hx⟩ := h</code> extracts the witness and proof from <code>h : ∃ x, P x</code>, adding both to the context.',
    term: 'Corresponds to pattern matching on the existential: the term uses the eliminator or <code>let ⟨x, hx⟩ := h; ...</code> to bind the components.',
    example: 'example (h : ∃ n : Nat, n = 0) : ∃ n : Nat, n = 0 := by\n  obtain ⟨n, hn⟩ := h\n  exact ⟨n, hn⟩',
  },
};

(function initTacticModal() {
  const overlay = document.getElementById('tactic-modal-overlay');
  const titleEl = document.getElementById('modal-title');
  const tacticDescEl = document.getElementById('modal-tactic-desc');
  const termDescEl = document.getElementById('modal-term-desc');
  const exampleEl = document.getElementById('modal-example');
  const closeBtn = document.getElementById('modal-close-btn');

  function openModal(tactic) {
    const info = TACTIC_INFO[tactic];
    if (!info) return;
    titleEl.textContent = tactic;
    tacticDescEl.innerHTML = info.tactic;
    termDescEl.innerHTML = info.term;
    exampleEl.textContent = info.example;
    overlay.classList.remove('hidden');
  }

  function closeModal() {
    overlay.classList.add('hidden');
  }

  document.querySelectorAll('.tactic-btn').forEach(function (btn) {
    btn.addEventListener('click', function () {
      openModal(btn.dataset.tactic);
    });
  });

  closeBtn.addEventListener('click', closeModal);

  overlay.addEventListener('click', function (e) {
    if (e.target === overlay) closeModal();
  });

  document.addEventListener('keydown', function (e) {
    if (e.key === 'Escape' && !overlay.classList.contains('hidden')) {
      closeModal();
    }
  });
})();

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
  clearTimeout(goalsDebounceTimer);
  goalsDebounceTimer = setTimeout(fetchGoals, 1500);
});

elaborate();

// --- InfoView / Goal state ---
const infoviewEl = document.getElementById('infoview-display');

let goalsDebounceTimer = null;
let goalsRequestId = 0;

function escapeHtml(str) {
  return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function renderGoals(goals) {
  infoviewEl.innerHTML = '';

  if (goals.length === 0) {
    infoviewEl.innerHTML = '<span class="goals-complete">No goals</span>';
    return;
  }

  for (const goal of goals) {
    const block = document.createElement('div');
    block.className = 'goal-block';

    if (goal.caseName) {
      const caseEl = document.createElement('div');
      caseEl.className = 'goal-case';
      caseEl.textContent = 'case ' + goal.caseName;
      block.appendChild(caseEl);
    }

    if (goal.hypotheses.length > 0) {
      const hypEl = document.createElement('div');
      hypEl.className = 'goal-hypotheses';
      hypEl.innerHTML = goal.hypotheses.map(h => escapeHtml(h)).join('\n');
      block.appendChild(hypEl);
    }

    const targetEl = document.createElement('div');
    targetEl.className = 'goal-target';
    targetEl.innerHTML = '<span class="turnstile">⊢</span>' + escapeHtml(goal.target);
    block.appendChild(targetEl);

    infoviewEl.appendChild(block);
  }
}

async function fetchGoals() {
  const code = editor.getValue();
  const cursorLine = editor.getCursor().line;
  const currentRequest = ++goalsRequestId;

  try {
    const resp = await fetch('/api/goals', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ code, cursorLine }),
    });

    if (currentRequest !== goalsRequestId) return;

    const data = await resp.json();
    renderGoals(data.goals || []);
  } catch (err) {
    if (currentRequest !== goalsRequestId) return;
    infoviewEl.innerHTML = '<span class="placeholder">Failed to fetch goals.</span>';
  }
}

editor.on('cursorActivity', function () {
  clearTimeout(goalsDebounceTimer);
  goalsDebounceTimer = setTimeout(fetchGoals, 500);
});

fetchGoals();
