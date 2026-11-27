# Contributing

Questions, corrections, mistakes in the documents, proofs that do not go
through, build trouble: please open an issue. Pull requests are welcome.
This file is short, and the two things it asks are the two that are hard to
undo once they are posted in public.

## Before you open an issue or a pull request

**1. Nothing hazardous goes in this repository, in either direction.**

The subject of this project is the machinery: readers for molecular formats,
the `Mol` object, the proof that a checker implements the rule it claims to
implement, and the audit that keeps those claims honest. Its subject is not
the assembly of hazard lists. So an issue, a comment, a commit message or a
patch here must not carry structures of compounds chosen because they are
dangerous, routes for making anything, or a list of structures of that kind, nor a neighbourhood, family or transformation set defined around such a
list (see [`RISKS.md`](RISKS.md)).

**2. A way past a filter is a security report, not a bug report.**

If you find a class of molecule that a filter here hands on although its
rule should refuse it, or an input that makes a filter answer where it
should refuse, use the private channel in [`SECURITY.md`](SECURITY.md)
rather than an issue.

Editing something out of an issue afterwards does not remove it: GitHub
keeps the earlier text in the edit history. [`RISKS.md`](RISKS.md), under
"If something that crosses the line is posted", says what happens then.

## Pull requests

- `lake test` must pass. It builds everything, runs the audit, checks every
  proof and runs the tests. The CI workflow runs the same thing on a clean
  machine, and checks the kernel and the axioms with tools the project did
  not write.
- Do not change `TestData.lean` by hand. It is written by
  `reference/check_tests.py --write` from the model in `reference/model.py`.
- Some files are the thing that checks everything else: [`Audit.lean`](Audit.lean),
  [`Audit/Ledger.lean`](Audit/Ledger.lean), `approvedMain`, the rule and
  "sound" in [`VeriMol/Proofs/Predicates/`](VeriMol/Proofs/Predicates/), the
  definitions of Core they rest on, `lakefile.toml`, `lean-toolchain`,
  `Tests.lean` and `reference/check_tests.py`. A pull request that touches
  any of them gets read line by line, and should say in its description why
  it touches them. [`RISKS.md`](RISKS.md), under "What is asked of
  contributors", says what the fingerprints of the ledger do and do not
  catch.
- A new rule needs its own short, readable definition under
  `VeriMol/Proofs/Predicates/`, a proof that its checker agrees with it for
  every `Mol`, and the known compounds that fix its meaning.

## What the documents are for

| Document | What it says |
|---|---|
| [`README.md`](README.md) | what the project is, and what it does not claim |
| [`SPEC.md`](SPEC.md) | what the program does and does not do, exactly |
| [`CLAIMS.md`](CLAIMS.md) | what is proven, what is tested and what is trusted, in full |
| [`RISKS.md`](RISKS.md) | the risks, the line of scope, and what is asked of contributors and users |
| [`SECURITY.md`](SECURITY.md) | how to report a way past a filter, or a hole in the audit, privately |

By contributing you agree that your contribution is licensed under the terms
in [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
