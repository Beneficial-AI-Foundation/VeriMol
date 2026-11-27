<!-- Thank you. CONTRIBUTING.md is short and worth the two minutes.
     Delete whatever does not apply. -->

## What this changes, and why

<!-- One paragraph. If it changes what the project claims, say so here. -->

## Checks

- [ ] `lake test` passes (it builds everything, runs the audit, checks every
      proof and runs the tests).
- [ ] Nothing in this pull request — patch, commit message or description —
      carries structures of compounds chosen because they are dangerous,
      routes for making anything, or a list of that kind
      ([`RISKS.md`](../RISKS.md), "The line of scope").
- [ ] This is not a way past a filter or a hole in the audit. Those go to the
      private channel in [`SECURITY.md`](../SECURITY.md) first, not here.
- [ ] `TestData.lean` is unchanged, or was written by
      `reference/check_tests.py --write` and not by hand.

## Does it touch what checks everything else?

<!-- Audit.lean, Audit/Ledger.lean, approvedMain, VeriMol/Proofs/Predicates/,
     the definitions of Core they rest on, lakefile.toml, lean-toolchain,
     Tests.lean, reference/check_tests.py.

     If yes: say which, and why it has to change. These get read line by line.
     The fingerprints of the ledger catch an accidental change to a statement;
     they are not built to catch a deliberate one, so the reading is the
     defence. If no: write "no". -->

## What is now claimed that was not claimed before

<!-- A new theorem, a changed statement, a new number in CLAIMS.md — or "none". -->
