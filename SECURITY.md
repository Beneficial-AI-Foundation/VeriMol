# Reporting a problem privately

Most things belong in a public issue: questions, corrections, mistakes in the
documents, proofs that do not go through, build trouble. Please open one.
This file is for the few kinds of report where going public first is the
wrong order.

## What belongs here instead of in an issue

- **A way past a filter.** A class of molecule that the filter in this
  repository hands on although the rule it is built on should refuse it, or
  an input that makes the filter answer when it should refuse.
- **A hole in the audit.** A way to get a `sorry`, an axiom, a `partial` or
  `unsafe` declaration, input or output in `VeriMol.Core`, or a changed
  theorem statement, past [`Audit.lean`](Audit.lean) and its ledger. The
  audit is what stands behind every claim in [`CLAIMS.md`](CLAIMS.md), so a
  way around it undermines all of them at once.
- **A reading of a SMILES that is wrong in a direction that matters.** The
  reader disagreeing with RDKit is usually an ordinary bug and an ordinary
  issue; the case for this channel is a disagreement that would make a filter
  pass something it should not.
- **Anything you would rather not post**, including a concern about the
  project's scope or about something in the repository that you think should
  not be public. [`RISKS.md`](RISKS.md) sets out how the project thinks about
  this; tell the author privately if you think it has it wrong.

The ordinary software kinds — a crash, a non-terminating input, a way to make
the program write something it should not — are welcome here too.

## How to report

Use GitHub's private reporting:
[**Report a vulnerability**](https://github.com/Beneficial-AI-Foundation/VeriMol/security/advisories/new),
which is also the **Security** tab of the repository. The report is visible
to the maintainer and to you, and to nobody else.

Please include the SMILES or the input, the command you ran, what you
expected and what happened. A failing test or a Lean snippet is ideal but not
required.

**If that page does not offer the form**, private reporting has been turned
off by mistake, or you are signed out. Do not fall back to a public issue
with the finding in it: an issue cannot be taken back, because GitHub keeps
the edit history. Open an issue that says only that you have a report to make
privately and nothing else about it, and wait to be asked.

## What to expect

This is a research project maintained by one person, not a product with an
on-call rota. There is no paid bounty and no guaranteed response time. What
the author undertakes:

- an acknowledgement within about a week;
- an assessment of whether the finding is a known limit, a bug, or something
  that changes what the project claims;
- credit in the fix, under whatever name you give, unless you ask otherwise;
- where the finding changes what is claimed, a correction to
  [`CLAIMS.md`](CLAIMS.md) or [`SPEC.md`](SPEC.md), because an uncorrected
  claim is the real failure for a project like this one.

For most findings the answer will be "publish it" — the limits of the one
rule that exists are documented and not secret. Asking first is about who
makes that call, not about keeping things quiet.

## Scope

This file covers this repository. It does not cover Lean, RDKit, Open Babel,
the datasets the checks download, or anything else the project depends on:
those go to their own maintainers.

## No warranty

Nothing here is a guarantee. The project is version 0.1.0 and the warning at
the top of [`README.md`](README.md) applies: it must not be relied on to
check safety-relevant features of chemical compounds. See [`LICENSE`](LICENSE).
