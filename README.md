# Lean 4 Term Visualizer

A web app that visualizes how Lean 4 tactics build proof terms in real time.

Write tactic proofs on the left; see the generated term on the right, with `?` marking subgoals that still need to be filled in.

## Prerequisites

- **Lean 4** installed via [elan](https://github.com/leanprover/elan) (available as `lean` in PATH)
- **Node.js** (v18+)

## Quick Start

```bash
npm install
npm start
```

Open http://localhost:3000 in your browser.

## How It Works

As you write tactics in the editor, the app:

1. Appends `try all_goals sorry` to fill any remaining subgoals
2. Runs `lean` on the code and uses `#print` to extract the elaborated term
3. Replaces `sorry` with `?` to clearly mark incomplete parts of the term

## Unicode Shortcuts

Type `\` followed by a shortcut name in the editor. The replacement triggers automatically or on space:

| Shortcut | Symbol | Shortcut | Symbol |
|----------|--------|----------|--------|
| `\and`   | ∧      | `\or`    | ∨      |
| `\to`    | →      | `\iff`   | ↔      |
| `\not`   | ¬      | `\forall`| ∀      |
| `\exists`| ∃      | `\lam`   | λ      |
| `\la`    | ⟨      | `\ra`    | ⟩      |
| `\sub`   | ⊂      | `\times` | ×      |
| `\in`    | ∈      | `\ne`    | ≠      |
| `\le`    | ≤      | `\ge`    | ≥      |
| `\alpha` | α      | `\beta`  | β      |

## Supported Tactics

The app works with any Lean 4 tactic, but is optimized for these basics:

`intro`, `intros`, `apply`, `exact`, `assumption`, `constructor`, `cases`, `left`, `right`, `have`, `obtain`
