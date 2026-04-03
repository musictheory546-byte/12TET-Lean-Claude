---
name: build-tex
description: Sync proof.tex listing line numbers with current .lean source files, then compile with latexmk
---

You are performing two tasks in sequence.

## Task 1 — sync listing line numbers

Read `doc/proof.tex` and every `.lean` file it references under `Music/`.

For each `\lstinputlisting` and each `linerange=` entry in `proof.tex`, verify that:

1. The `firstline`/`lastline` values still point to the same Lean declaration they are intended to show (match by declaration name / surrounding context, not by line number alone).
2. Any `linerange={a-b,c-d,...}` entries still exclude exactly the doc-comment lines (`/-- ... -/` and `/-! ... -/` block openers) that the listing is supposed to skip, while retaining inline and trailing `--` comments.

If any line numbers are stale, update them in `doc/proof.tex` with the Edit tool. Report every change made (old range → new range, which file, which listing).

If all line numbers are current, say so briefly and do not touch the file.

## Task 2 — compile

Run the following command and report the outcome (success or the first error LaTeX reports):

```
cd /Users/lean/Documents/Working/music/doc && latexmk -pdf -interaction=nonstopmode proof.tex 2>&1 | tail -40
```
