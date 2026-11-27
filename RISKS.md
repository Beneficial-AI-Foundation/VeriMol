# Risks, scope and dual use

A filter that decides which molecules are handed on is a safety tool, and a
safety tool is worth asking hard questions about. This document says what the
author believes the risks of this project are, where the line of its scope
runs, and what is asked of anyone who contributes to it or uses it. It is
part of the project in the same way as [`CLAIMS.md`](CLAIMS.md): a statement
that can be held against the repository and corrected where it is wrong.

Version 0.1.0. Like the rest of the project, this document is early and will
change.

## What is in this repository today

A reader and a writer for SMILES, proofs about them, and one filter with one
rule: no perfluorinated group of `n` or more carbon atoms. The compounds that
the documents speak of are PFAS, ibuprofen, acetic acid and a few other small
molecules. The tests hold more: `reference/test_cases.py` and `TestData.lean`
carry well over a thousand SMILES texts. Most of them were written to try the
reader, and 100 are compounds of the public NCI Open Database, from a file
that RDKit ships ([`NOTICE`](NOTICE) names it). Those 100 were taken by their
place in that file, the first one and then every 49th, and not by what they
are. The larger public collections that the checks run on are fetched, and
they are not stored here. PFAS are an environmental and health
concern, not a weapon, and the structural pattern that the rule looks for is
public knowledge: it is in regulations and in review articles, and a short
search with a widely used cheminformatics toolkit finds it; this repository
contains such a search, written for RDKit, because the checks hold the Lean
filter against it (`reference/check_filter.py`).

The risks below are about what this project could become, and about
how it could be read, rather than about what it now contains.

## Why a safety filter is a dual-use object

Four properties of filters in general, all of which apply here:

- **A filter states what it lets through.** The rule is the boundary, so
  reading the rule tells you both what is caught and what is not. This
  repository makes that explicit on purpose: the section "What the filter
  does not say" in [`README.md`](README.md) lists the ways a compound passes
  the perfluoro rule, and [`SPEC.md`](SPEC.md), section 16, gives the
  examples. For the rule that exists, publishing this is right: a user who
  does not know the limits of the filter will misuse it, and the limits are
  not secret. For a rule aimed at genuinely dangerous chemistry, the same
  list would be an instruction for getting past it, and must thus be held back together with the rule it describes, which is what "The line of scope" below asks for.

- **The rule and the map of what evades it are the same object.** This is
  sharpest for rules that work from a list. A rule of the form "no compound
  on a list can be reached in at most *k* steps of a fixed list of
  transformations" is, read in one direction, a filter; read in the other, a
  machine-readable description of the neighbourhood around the listed
  compounds. Those two readings cannot be separated, because they are the
  same definition.

- **A published filter is a target.** A generative model that is trained or
  steered against a known filter is rewarded for whatever the filter lets
  through. [`README.md`](README.md) gives this as a reason to prove the
  checker correct, which it is; it is also a reason not to assume that
  publishing every rule in full is safe.

- **Every answer is information, in both directions.** A filter can be run
  backwards: a model rewarded for what the filter *refuses* is steered towards
  the class the rule describes as easily as one rewarded for what it lets
  through is steered away from it. And a filter that anyone may ask as often
  as they like tells them, one question at a time, where its boundary runs; a
  refusal that names what was matched tells them more. For the perfluoro rule
  none of this matters, because the boundary is public anyway. For a rule
  whose list is kept private, the refusal should not say which entry was
  matched, and a deployment should not answer unlimited questions from
  strangers.

## The line of scope

The project's subject is the **machinery**: readers for molecular formats,
the `Mol` object, the proof that a checker implements the rule it claims to
implement, and the audit that keeps those claims honest. Its subject is not
the assembly of hazard lists.

Concretely, and as a rule for this repository:

> **A hazard list does not go in this repository.** No rule is committed here
> whose statement is, or contains, an enumeration of structures chosen
> because they are dangerous — nor a neighbourhood, family or transformation
> set defined around such an enumeration.

This does not block the rule kinds that [`README.md`](README.md) sketches. It
changes where the list lives. The intended shape is:

- the **checker** is public, in this repository, and proven: the theorem says
  that it answers yes exactly when the molecule matches nothing in the list
  it was given. That theorem is about the checker and holds for every list,
  so it carries no hazard content at all;
- the **list** is an input, not part of the program, and is distributed by
  whoever is responsible for it, under whatever terms that responsibility
  calls for;
- where a deployment has to be auditable without the list being readable, the
  deployment can publish a hash of the list it ran. That is a commitment
  anyone can check later against the list, without the list being public now.
  The hash is taken together with a random value that is kept with the list
  and not published (a salt), so that the hash cannot be used to confirm a
  guess. This matters most if the entries are ever committed to one by one.

This is also the better engineering. The size `n` of the perfluoro rule is
already a runtime argument rather than a compiled-in constant, and a
list-agnostic checker with a list-agnostic theorem is more useful than one
proven for a single list. It also means that the AI which writes a checker
and its proof never needs to see the list, so the list does not pass through
the logs of whoever runs that AI. The dual-use argument and the design
argument point the same way, which is a good sign for both.

Rules built on chemistry that is public and regulatory in character (the
perfluoro rule is the example) cam stay in the repository in full.

**The same line applies to the checks, and that is easy to miss.** A test
harness naturally enumerates the class a rule is about, because that is how
you test a rule. `reference/check_filter.py` already does it: it builds every
perfluoroalkyl group of 1 to 10 carbon atoms without a ring, as a carboxylic
acid and as a sulfonic acid, and demands that the filter and RDKit agree on
each. For PFAS that is an unremarkable correctness test, and these structures
are in any textbook. But a generator of every member of a class is the same
object whatever the class, and for a rule that aims at dangerous chemistry
the test harness would be the analogue generator, sitting in `reference/`
where nobody thinks to look for one. A rule whose list stays outside the
repository takes its enumerating test with it; what stays here is the test
that the checker handles *an arbitrary list* correctly.

The same goes for every other place where known answers live: the theorems
about known compounds in
[`VeriMol/Proofs/Compounds.lean`](VeriMol/Proofs/Compounds.lean), the expected
results in `TestData.lean`, and the entries of `reference/sources.py`, where a
URL and a checksum of a curated collection are a pointer to that collection.
Step 3 of the method in [`README.md`](README.md) asks that known compounds get
their known answers. For a rule about dangerous chemistry, those known
compounds *are* the list. They are checked where the list is kept, and what is
published is that they were checked, together with the hash of the list.

## What is asked of contributors

- Do not open a pull request or an issue that contains structures of
  compounds chosen for their hazard, routes for making anything, or a dangerous list of
  the kind described above. If you think the project needs one of these to
  make progress, write to the author privately first:
  [`SECURITY.md`](SECURITY.md) says how.
- If you find a way past a filter in this repository, treat it as a security
  report, not as a bug report, and use the private channel.
- Changes to [`Audit.lean`](Audit.lean), [`Audit/Ledger.lean`](Audit/Ledger.lean)
  and to `approvedMain` are changes to the thing that checks everything else.
  So are changes to the rule and to "sound"
  ([`VeriMol/Proofs/Predicates/`](VeriMol/Proofs/Predicates/)), to the
  definitions of Core that they rest on (the report of the audit lists them
  for each theorem), and to `lakefile.toml`, `lean-toolchain`, `Tests.lean`
  and `reference/check_tests.py`. They get read line by line, and a pull
  request that touches them should say in its description why. The
  fingerprints of the ledger catch an *accidental* change to a statement or to
  the definitions behind it. They are not built to catch a deliberate one:
  they are made from Lean's own 32-bit hashes of expressions, and a change
  that keeps them can be searched for. Against a deliberate change, the
  reading is the defence.

## What is asked of users

- **Do not cite this project as assurance.** Not to a regulator, not to a
  funder, not in a safety case, not as evidence that a pipeline is screened.
  It is version 0.1.0, written in a two-week research sprint, with one rule, and the
  warning at the top of [`README.md`](README.md) means what it says.
- **"Formally verified" is a claim about one link in a chain.** It says that
  the checker implements the written rule for the graph the program built. It
  says nothing about whether the rule is the right rule, whether the graph is
  the molecule a chemist would read, whether a compound that passes is
  harmless, or whether anyone ran the filter at all.
  [`CLAIMS.md`](CLAIMS.md) gives the full account of what is proven, what is
  tested and what is trusted; the "Trusted" section is the one to read before
  relying on anything here.
- A filter is only ever as good as its rule, and no proof reaches the rule.
- **Bound the length of what you feed it.** The filter's cost grows with the
  square of the number of atoms: a chain of 800 fluorinated carbon atoms is
  answered in about a third of a second, one of 3,000 in about six seconds,
  with memory flat. The answer stays correct, the program gets slow, not
  wrong, and it refuses rather than passes, but a caller that accepts a
  SMILES of unbounded length from a stranger has given that stranger a way to
  spend its processor time. Cap the length of the input. And a caller that
  stops the program after a time limit should count that as a refusal, never
  as a pass.

## If you wire the filter into something

Everything in this section is in [`SPEC.md`](SPEC.md) already, and none of it
is a defect: the program does what it is specified to do. They are collected
here because they are the places where a caller that reads the program
casually will build a pipeline that says "screened" while letting things
through, and because `SPEC.md` is long and a person wiring this up will not
read all of it.

- **The exit code is the whole answer.** Exit code 0 means handed on;
  anything else means refused, whether the reason is the rule, soundness, a
  text that is not read, or a command that is not understood. What the
  program prints is the `Mol`, and *a printed `Mol` that passed looks like
  any other printed `Mol`* ([`SPEC.md`](SPEC.md), section 16.1). So a caller
  that keys on there being output, or on the output parsing, has not asked
  the filter anything. Key on the exit code, and treat everything that is not
  a clean 0 (an error, a crash, a time limit, a process the system killed)
  as a refusal.

- **Exit code 0 means handed on only if the command was `filter`.** The
  program has four other commands, and none of them asks the rule. The
  plainest is a text and nothing else. It ends with exit code 0 for every
  text that is read, and it prints the `Mol` of that text, in the very layout
  of a pass, whatever the rule would say of it: `app '<SMILES>'` ends with 0
  for PFOA, and `app filter perfluoro 6 '<SMILES>'` ends with 1. So a caller
  that puts the arguments together from parts and loses the three words in
  front of the text (a variable that is empty, a setting that is switched
  off, a list that is built wrongly) has a pipeline in which everything that
  can be read passes, and neither the exit code nor the output shows it.
  Write the four arguments out in one place. And try the wiring itself, not
  only the program, with a compound that the rule must refuse: if PFOA does
  not come back with exit code 1, the filter is not being asked.

- **The empty text passes.** It is read as the `Mol` with no atoms, which is
  sound and has no group, so the filter hands it on with exit code 0
  ([`SPEC.md`](SPEC.md), section 16.1). That is the right answer to the
  question asked. It also means that a field which can arrive empty, missing
  or truncated to nothing arrives as a pass. Check for that before the
  filter, not after it.

- **A large `n` turns the rule off, and says nothing.** The size is an
  argument of the command, not a constant of the program, which is
  deliberate. The other side of it: with an `n` larger than any group that
  will ever be seen, every sound `Mol` is handed on with exit code 0, and
  nothing in the output says the rule did no work. Pin the number where it is
  read rather than passing it through from configuration that something else
  can set, and record it beside each answer, so that a run can be told apart
  later from a run with the rule effectively switched off.

- **Act on the `Mol` the filter returned, not on the text a second time.**
  No theorem says the `Mol` is the molecule a chemist reads in the SMILES;
  that is tested against RDKit and Open Babel, and the agreement is good but
  not total (5 of 62,075 differ, in the hydrogen count of one to four atoms —
  [`CLAIMS.md`](CLAIMS.md)). The rule asks whether a carbon atom carries
  hydrogen, so a disagreement about hydrogens is a disagreement about the
  answer. A pipeline that passes the *text* on to whatever comes next, and
  lets that re-read it with a different toolkit, has made every such
  disagreement into a way through. Hand on the `Mol`.

- **Nothing here makes anyone run the filter.** A verified filter is an
  auditable commitment by whoever deploys it, and nothing more. Whether it
  ran, on what, and what was done with the refusals, is a property of the
  system around it, not of this repository.

## A green audit does not travel

The audit ([`Audit.lean`](Audit.lean)) checks what a machine can check about
the code in the same commit as itself: that no proof is missing, that no
axiom was added, that Core neither reads nor prints, that each of the 97
statements of the ledger is the statement the ledger records. It is a strong
check, and it is meant to be one. What it is not is a judgement about the
rule: the rule is an input to the question the audit asks, never the subject
of it, so a narrow, badly drawn or deliberately easy rule passes just as
green. Hence:

- a fork can keep all of this ("formally verified", the audit, the green
  badge) while shipping a rule weaker than this one, or vacuous. Nothing in
  the apparatus would complain, and nothing would look wrong from outside;
- a green audit here is a statement about this commit and these 97
  statements. It does not transfer to anything built on top;
- a fingerprint fixes a statement, not the function the statement is about,
  and the audit prints that gap for every entry. Change `VeriMol.read` or
  `VeriMol.run` and the wording of the theorem is untouched, so the ledger
  says nothing; all that must still hold is that the proof goes through. A
  theorem can also stay true while saying very little: "the program either
  succeeds or reports an error in one fixed form" is true of a program that
  errors on everything. Proving a cheap statement does not make it expensive.

So anyone deciding whether to trust a filter built with this framework has to
read the rule (the short definition under
[`VeriMol/Proofs/Predicates/`](VeriMol/Proofs/Predicates/), written to be read
for exactly this reason) and the list of known compounds that fixes its
meaning. The proof frees you from reading the checker. Nothing frees you from
reading the rule.

## If something that crosses the line is posted

Editing it out of an issue or a comment is not enough: GitHub keeps the
earlier text in the edit history, which anyone can open, until that revision
is deleted from the history or the comment or issue is deleted. Commits that
were pushed to a pull request stay reachable through the pull request even
after a force push; removing them takes a request to GitHub Support.

## What is not claimed by this document

That the author has thought of everything. This is a first pass by one
person, and the judgement that the current contents are safe to publish is
that person's judgement. Disagreement is welcome, and
[`SECURITY.md`](SECURITY.md) says how to raise it privately if the
disagreement is itself something you would rather not post in public.
