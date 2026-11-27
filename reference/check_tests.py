"""Make the expected results of the Lean tests from the model, and check that they are up to date.

    .venv/bin/python -I reference/check_tests.py            check; ends with exit code 1 if anything is off
    .venv/bin/python -I reference/check_tests.py --write    write TestData.lean anew, then check

`lake test` must work without Python. So the expected results that come from the model are stored in a
Lean file, TestData.lean, and this script is what writes it: from the model (model.py) and from the test
cases (test_cases.py). Nobody changes TestData.lean by hand. The expected results are what the model reads,
prints and writes for the test cases.

reference/README.md, "Reading the output of `check_tests.py`", says what each check asks.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model
import sources
import test_cases

ROOT = HERE.parent
TARGET = ROOT / "TestData.lean"
SPEC = (ROOT / "SPEC.md").read_text()
check = sources.check           # one line for each check: PASS or FAIL, and what was asked


def reads(text):
    return model.problem_of(text) is None


# ------------------------------------------------------------------------------- writing Lean
def lean_string(text):
    """The text as a string of Lean source code."""
    plain = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t", "\r": "\\r"}
    out = []
    for ch in text:
        if ch in plain:
            out.append(plain[ch])
        elif 32 <= ord(ch) < 127:
            out.append(ch)
        elif ord(ch) <= 0xFFFF:
            out.append(f"\\u{ord(ch):04x}")
        else:
            raise ValueError(f"cannot write the character {ch!r} into a Lean file")
    return '"' + "".join(out) + '"'


def wrapped(items, indent="  ", width=100):
    """The items with commas between them, on as many lines as are needed."""
    lines, line = [], indent
    for k, item in enumerate(items):
        piece = item + ("," if k + 1 < len(items) else "")
        if line.strip() and len(line) + 1 + len(piece) > width:
            lines.append(line.rstrip())
            line = indent
        line += piece + " "
    return "\n".join(lines + [line.rstrip()])


def long_list(name, lean_type, entries, comment, size=200, large=500):
    """A Lean list that may have many entries. Lean stops with "maximum recursion depth has been reached"
    when one definition holds too much: a list of about 500 large entries in one piece, or a list of
    200 entries one of which holds a list of 600. So a long list is written in parts, which are then
    joined, and an entry of more than `large` lines gets a part of its own."""
    parts = [[]]
    alone = lambda e: e.count("\n") >= large                 # so many line breaks are more than `large` lines
    for entry in entries:
        if parts[-1] and (len(parts[-1]) == size or alone(entry) or alone(parts[-1][-1])):
            parts.append([])
        parts[-1].append(entry)
    listed = lambda part: "[\n" + ",\n".join(part) + "\n]"
    if len(parts) == 1:
        return f"{comment}\ndef {name} : {lean_type} := {listed(parts[0])}"
    names = [f"{name}Part{k}" for k in range(1, len(parts) + 1)]
    out = [f"/-- Part {k} of {len(parts)} of `{name}`. -/\ndef {part_name} : {lean_type} := {listed(part)}"
           for k, (part_name, part) in enumerate(zip(names, parts), 1)]
    out.append(f"{comment}\ndef {name} : {lean_type} :=\n  " + " ++ ".join(names))
    return "\n\n".join(out)


def printed_lines(mol):
    """The lines that the model prints for a Mol (SPEC.md, section 7)."""
    printed = model.show(mol)
    assert printed.endswith("\n") and "\n\n" not in printed
    return printed[:-1].split("\n")


def as_lean(mol):
    """The Mol as Lean source code: the text that the model prints for it, moved four places to the
    right. The printed layout is valid Lean (SPEC.md, section 7)."""
    return "\n".join("    " + line for line in printed_lines(mol))


def mol_entry(name, mol, of_a_text):
    """One entry of `mols`."""
    as_text = ",\n".join("      " + lean_string(line) for line in printed_lines(mol))
    return (f"  ({lean_string(name)}, {'true' if of_a_text else 'false'},\n{as_lean(mol)},\n    [\n{as_text} ],\n"
            f"    {'true' if model.is_well_formed(mol) else 'false'})")


def filter_entry(name, mol):
    """One entry of `filters`: the name of the Mol; the first reason why it is not sound, as the model gives
    it, or `none`; and, for a well formed Mol, its perfluorinated groups, each as the list of its atoms in
    increasing order (SPEC.md, sections 16.2 and 16.3)."""
    problem = model.sound_problem(mol)
    reason = "none" if problem is None else f"some {lean_string(problem)}"
    if not model.is_well_formed(mol):
        return f"  ({lean_string(name)}, {reason}, none)"
    groups = ", ".join("[" + ", ".join(str(atom) for atom in group) + "]" for group in model.perfluorinated_groups(mol))
    return f"  ({lean_string(name)}, {reason}, some [{groups}])"


def written(function, *arguments):
    """What a function of the model's writer gives, as Lean source code: `(true, the text)`, or
    `(false, the reason)` if the model gives no text for the Mol (SPEC.md, sections 9.4, 12.3 and 3.2)."""
    try:
        return f"(true, {lean_string(function(*arguments))})"
    except model.WriteError as refusal:
        return f"(false, {lean_string(str(refusal))})"


def three_writings(mol):
    """How the model writes a Mol, three times over: what the program writes for `plain` and for
    `rewrite` (SPEC.md, sections 9.3 and 12.3), which are the plain spelling and the spelling with round
    brackets, with the stereo marks of the Mol; and what it writes for `canonical`, which is the chosen
    form of the Mol in the spelling of `rewrite` (section 3.2)."""
    return ",\n".join("    " + answer for answer in (
        written(model.write_plain, mol), written(model.write, mol), written(model.write_chosen, mol)))


TEXTS = test_cases.SPEC_TEXTS + test_cases.MORE_TEXTS + test_cases.NCI_TEXTS


def lexed(text):
    """The tokens that the model cuts from the text before it meets a character or a pair of square
    brackets that it cannot read, and that problem as (position, message), or None."""
    tokens = []
    try:
        for token in model.tokens_of(text):
            tokens.append(token)
    except model.SmilesError as e:
        return tokens, (e.position, e.message)
    return tokens, None


def placed(token):
    """A token of the model as a `VeriMol.Placed` of Lean."""
    position = token.pos
    if token.kind == "atom":
        a = token.value
        option = lambda value: "none" if value is None else f"some {value}"
        mark = {None: "none", "@": "some .anticlockwise", "@@": "some .clockwise"}[a.chiral]
        what = (f".atom {{ element := .{a.element}, aromatic := {'true' if a.aromatic else 'false'}, "
                f"isotope := {option(a.isotope)}, charge := {a.charge}, hydrogens := {option(a.hydrogens)}, mark := {mark} }}")
        if a.chiral:                        # SPEC.md reports an atom with a stereo mark at its "@"
            position = a.chiral_pos
    elif token.kind == "bond":
        what = {"/": ".bond .up", "\\": ".bond .down"}.get(token.value) or f".bond (.order .{model.ORDER_OF[token.value]})"
    elif token.kind == "ring":
        what = f".ring {token.value}"
    else:
        what = {"(": ".branchOpen", ")": ".branchClose", ".": ".dot"}[token.kind]
    return f"{{ token := {what}, position := {position} }}"


def cut_entry(text):
    """One entry of `cuts`: the text; its tokens, as the model cuts them; whether that is to the end of
    the text; and, if it is not, the problem in the characters that stopped the cutting."""
    tokens, problem = lexed(text)
    listed = "[]" if not tokens else "[\n" + ",\n".join("      " + placed(token) for token in tokens) + " ]"
    found = "none" if problem is None else f"some ({problem[0]}, {lean_string(problem[1])})"
    return f"  ({lean_string(text)},\n    {listed},\n    {'true' if problem is None else 'false'}, {found})"


def program_entry(args):
    """One entry of `programs`: the arguments, and what the model prints for them."""
    stdout, stderr, code = model.run(args)
    assert stdout == "" or stdout.endswith("\n")
    lines = stdout[:-1].split("\n") if stdout else []
    listed = "[]" if not lines else "[\n" + ",\n".join("      " + lean_string(line) for line in lines) + " ]"
    arguments = "[" + ", ".join(lean_string(a) for a in args) + "]"
    return f"  ({arguments},\n    {listed},\n    {lean_string(stderr)}, {code})"


def first_of_each_message(texts, how_many):
    """Of the texts that are not read: the first one of each of the first `how_many` different
    messages, in the order of the texts."""
    kept, seen = [], set()
    for text in texts:
        try:
            model.read(text)
        except model.SmilesError as e:
            if e.message not in seen and len(kept) < how_many:
                kept.append(text)
            seen.add(e.message)
    return kept


def first_unread_with(texts, test):
    """Of the texts that are not read: the first one for which `test` holds."""
    for text in texts:
        if not reads(text) and test(text):
            return text
    raise SystemExit("check_tests.py: no test text of this kind is left")


# A text that is not read gets the reader's error behind each of the three command words. That is
# theorem 5 of CLAIMS.md, for every text. So behind the words the tests have every test text that is
# read, and of the others only a handful: five with different messages.
# The five have plain characters only. So that the built program still gets an odd text behind a command
# word, four more are kept: one with a character from outside ASCII, one with a control character, one
# with a line break, and one that begins with a minus sign.
ODD_BEHIND_A_WORD = [first_unread_with(TEXTS, lambda t: any(ord(c) > 126 for c in t)),
                     first_unread_with(TEXTS, lambda t: any(ord(c) < 32 and c not in "\n\r" for c in t)),
                     first_unread_with(TEXTS, lambda t: "\n" in t),
                     first_unread_with(TEXTS, lambda t: t.startswith("-"))]
UNREAD_BEHIND_A_WORD = first_of_each_message(TEXTS, 5)
UNREAD_BEHIND_A_WORD += [text for text in ODD_BEHIND_A_WORD if text not in UNREAD_BEHIND_A_WORD]
BEHIND_A_WORD = [text for text in TEXTS if reads(text) or text in UNREAD_BEHIND_A_WORD]

# Other lists of arguments. The first 18 are no SMILES text, alone or behind a word (SPEC.md, section 8),
# and get the same error. In the last seven the text behind the word is one of the words itself: they
# get the reader's answer for that text.
OTHER_ARGUMENTS = [[], ["rewrite"], ["plain"], ["C", "C"], ["print", "C"], ["C", "rewrite"], ["", ""], ["a", "b", "c"],
                   ["rewrite", "C", "C"], ["plain", "rewrite", "C"], ["Rewrite", "C"], ["rewrite ", "C"], ["PLAIN", "C"],
                   ["write", "C"], ["canonical"], ["canonical", "C", "C"], ["Canonical", "C"], ["canonical ", "C"],
                   ["rewrite", "rewrite"], ["rewrite", "plain"], ["plain", "plain"], ["plain", "rewrite"],
                   ["canonical", "canonical"], ["canonical", "rewrite"], ["rewrite", "canonical"]]
# The command `filter` (SPEC.md, sections 8 and 16.1). The word `filter` alone is taken for a text, which is
# not read. The 21 after it are not the two words, a number from 1 on and a text, and get the error about
# the arguments: too few arguments or too many, a number that is 0, or that is not written with the
# digits 0 to 9 alone (the last two of these are a digit six of another script and a digit six of full
# width), and other words. The last three are the command: with a text without a character, which is
# read as the Mol without atoms, and with a word of the program as the text.
OTHER_ARGUMENTS += [["filter"], ["filter", "perfluoro"], ["filter", "perfluoro", "6"], ["filter", "perfluoro", "6", "C", "C"],
                    ["a", "b", "c", "d"], ["a", "b", "c", "d", "e"],
                    ["filter", "perfluoro", "0", "C"], ["filter", "perfluoro", "00", "C"], ["filter", "perfluoro", "", "C"],
                    ["filter", "perfluoro", "six", "C"], ["filter", "perfluoro", "+6", "C"], ["filter", "perfluoro", "-6", "C"],
                    ["filter", "perfluoro", "6.0", "C"], ["filter", "perfluoro", " 6", "C"], ["filter", "perfluoro", "6 ", "C"],
                    ["filter", "perfluoro", "\u0666", "C"], ["filter", "perfluoro", "\uff16", "C"],
                    ["Filter", "perfluoro", "6", "C"], ["filter", "Perfluoro", "6", "C"], ["filter", "pfas", "6", "C"],
                    ["perfluoro", "filter", "6", "C"], ["rewrite", "perfluoro", "6", "C"],
                    ["filter", "perfluoro", "6", ""], ["filter", "perfluoro", "6", "filter"], ["filter", "perfluoro", "6", "rewrite"]]

# Behind the words `filter perfluoro` and a number (SPEC.md, section 16). With the number 6: every text of
# SPEC.md, every real text and every text written for the filter that is read, and the handful of texts
# that are not read. Then the texts whose Mol is sound and has a fluorinated carbon atom, each three
# times more: with the number 1, with the size of its largest perfluorinated group, which the filter still
# refuses, and with the number after it, which it lets through. And one such text with numbers that are
# written in other ways: with zeros in front, and with 31 digits.
PFOA = "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F"
BEHIND_THE_FILTER = ([text for text in test_cases.SPEC_TEXTS + test_cases.NCI_TEXTS + test_cases.FILTER_TEXTS
                      if reads(text)] + UNREAD_BEHIND_A_WORD)


def largest_group(text):
    """The size of the largest perfluorinated group of a text that is read as a sound Mol, or None."""
    mol = model.read(text)
    if model.sound_problem(mol) is not None:
        return None
    return max((len(group) for group in model.perfluorinated_groups(mol)), default=0)


WITH_A_GROUP = [(text, largest_group(text)) for text in test_cases.SPEC_TEXTS + test_cases.FILTER_TEXTS
                if reads(text) and largest_group(text)]
FILTER_ARGUMENTS = ([["filter", "perfluoro", "6", text] for text in BEHIND_THE_FILTER]
                    + [["filter", "perfluoro", number, text] for text, size in WITH_A_GROUP
                       for number in dict.fromkeys(("1", str(size), str(size + 1))) if number != "6"]
                    + [["filter", "perfluoro", number, PFOA] for number in ("006", "0007", "08", "1" + "0" * 30)])


def written_texts():
    """Every text that the model writes for a test text that it reads, in the plain spelling and in the
    spelling with round brackets, with the stereo marks of the Mol."""
    out = []
    for text in TEXTS:
        try:
            mol = model.read(text)
        except model.SmilesError:
            continue
        for writer in (model.write_plain, model.write):
            try:
                out.append(writer(mol))
            except model.WriteError:
                pass
    return list(dict.fromkeys(out))


def test_data():
    """The whole text of TestData.lean."""
    read_texts = [t for t in test_cases.SPEC_TEXTS if reads(t)]
    mols = ([(t, model.read(t), True) for t in read_texts]
            + [(name, mol, False) for name, mol, _ in test_cases.HAND_MADE_MOLS])
    probes = [f"({lean_string(t)}, {'some ' + lean_string(t) if t in model.ELEMENTS else 'none'})"
              for t in test_cases.SYMBOL_PROBES]
    the_mols = long_list("mols", "List (String × Bool × VeriMol.Mol × List String × Bool)",
                         [mol_entry(name, mol, of_a_text) for name, mol, of_a_text in mols],
                         f"""/-- `Mol`s. Each entry holds a name, whether the name is a SMILES text and the
`Mol` is what the model reads from it, the `Mol` as a Lean object, the lines
that the model prints for it (SPEC.md, section 7), and whether the model calls
it well formed (section 3).

The first {len(read_texts)} entries are the `Mol`s of the texts of SPEC.md that are read.
The other {len(test_cases.HAND_MADE_MOLS)} are written out by hand in `reference/test_cases.py`. -/""", size=100)
    the_writings = long_list("writings",
                             "List (String × (Bool × String) × (Bool × String) × (Bool × String))",
                             [f"  ({lean_string(name)},\n{three_writings(mol)})" for name, mol, _ in mols],
                             """/-- How the model writes each `Mol` of `mols`, in the same order. Each entry
holds the name of the `Mol` and three answers:

* what the program writes for `plain`: the plain spelling, with the stereo
  marks of the `Mol` (SPEC.md, sections 9.1, 9.3 and 12.3);
* what the program writes for `rewrite`: the spelling with round brackets,
  with the stereo marks of the `Mol` (sections 9.2, 9.3 and 12.3);
* what the program writes for `canonical` (section 3.2): the chosen form of
  the `Mol`, as `rewrite` writes it.

An answer is `(true, the text)`, or `(false, the reason)` where the model
refuses the `Mol` (sections 9.4 and 12.3) or gives no chosen form (section
3.2). -/""")
    the_filters = long_list("filters", "List (String × Option String × Option (List (List Nat)))",
                            [filter_entry(name, mol) for name, mol, _ in mols],
                            """/-- What the filter asks of a `Mol`, for each `Mol` of `mols`, in the same order
(SPEC.md, section 16). Each entry holds the name of the `Mol` and two answers
of the model:

* the first reason why the `Mol` is not sound, or `none` if it is sound
  (section 16.2);
* its perfluorinated groups, each as the list of its atoms in increasing
  order, in the order of the lowest atom of each group (section 16.3). `none`
  for a `Mol` that is not well formed: the groups are defined for a well
  formed `Mol`. -/""")
    the_renumbered = long_list("renumbered",
                               "List (String × VeriMol.Mol × (Bool × String) × (Bool × String) × (Bool × String))",
                               [f"  ({lean_string(name)},\n{as_lean(mol)},\n{three_writings(mol)})"
                                for name, mol in test_cases.RENUMBERED_MOLS],
                               f"""/-- The `Mol`s of {len(test_cases.RENUMBERED_MOLS)} texts, real ones and ones with stereo marks, with their
atoms numbered in another order (`reference/test_cases.py` says how). For
nearly all of them that is another `Mol` than the reader returns for the
text. Each entry holds a name, the `Mol`, and how the model writes it: the
same three answers as in `writings`. -/""")
    the_cuts = long_list("cuts", "List (String × List VeriMol.Placed × Bool × Option (Nat × String))",
                         [cut_entry(text) for text in TEXTS],
                         f"""/-- How the model cuts each of the {len(TEXTS)} test texts into tokens. Each entry holds:

* the text;
* its tokens, cut as far as the text can be cut;
* whether that is to the end of the text;
* if it is not: the problem in the characters that stopped the cutting, as a
  position and a message. -/""")
    the_programs = long_list("programs", "List (List String × List String × String × Nat)",
                             [program_entry(args) for args in [[text] for text in TEXTS]
                              + [[word, text] for word in model.WORDS for text in BEHIND_A_WORD] + OTHER_ARGUMENTS
                              + FILTER_ARGUMENTS],
                             f"""/-- What the program prints, as the model says. Each entry holds the
command-line arguments, the lines on standard output, the text on standard
error, and the exit code.

The first {len(TEXTS)} entries have one of the test texts as their only argument. The
next {len(BEHIND_A_WORD)} have the word `rewrite` in front of a test text, the {len(BEHIND_A_WORD)} after them
the word `plain`, and the {len(BEHIND_A_WORD)} after those the word `canonical`. Behind a word
stand the test texts that are read, and {len(UNREAD_BEHIND_A_WORD)} of those that are not: a text that
is not read gets the reader's error behind each word, which is theorem 5 of
CLAIMS.md. The next {len(OTHER_ARGUMENTS)} are other lists of arguments (SPEC.md, section 8). The
last {len(FILTER_ARGUMENTS)} are the command `filter` (section 16): the words `filter` and
`perfluoro`, a number and a text. {len(BEHIND_THE_FILTER)} of them have the number 6: the texts of
SPEC.md, the real texts and the texts written for the filter that are read,
and the {len(UNREAD_BEHIND_A_WORD)} texts that are not read. The others have a text with a
perfluorinated group and another number, or the number 6 written with zeros
in front. -/""")
    the_spellings = written_texts()
    return f'''import VeriMol.Core

/-!
# The expected results of the tests

This file is written by `reference/check_tests.py --write`. Do not change it by
hand. It is made from the model (`reference/model.py`, which is SPEC.md as a
Python program) and from the test cases in `reference/test_cases.py`. Without
`--write`, the script says whether this file is still what the model gives.

`Tests.lean` turns every entry into tests.
-/

namespace TestData

/-- The 118 element symbols, in the order of SPEC.md, section 15. -/
def elementSymbols : List String := [
{wrapped([lean_string(s) for s in model.ELEMENTS])}
]

/-- Texts, each with the answer to the question: which element has exactly this
text as its symbol? `none` if no element has. -/
def symbolProbes : List (String × Option String) := [
{wrapped(probes)}
]

{the_mols}

{the_writings}

{the_filters}

{the_renumbered}

{the_cuts}

{the_programs}

/-- The {len(the_spellings)} different texts that the model writes for the test texts, in its two
spellings (SPEC.md, section 9). Spelling the tokens of such a text must give
the text back, character for character. -/
def spellings : List String := [
{wrapped([lean_string(s) for s in the_spellings])}
]

end TestData
'''


# ------------------------------------------------------------------------------- the checks
expected = test_data()
if "--write" in sys.argv[1:]:
    before = TARGET.read_text() if TARGET.exists() else None
    TARGET.write_text(expected)
    print("TestData.lean was up to date; nothing changed." if before == expected else
          "TestData.lean is written anew. Run `lake test` now.")
    print()

# SPEC_TEXTS against SPEC.md. Text inside ``` blocks is not counted as quoted.
outside_blocks = re.sub(r"```.*?```", "", SPEC, flags=re.S)
quoted = list(dict.fromkeys(re.findall(r"`([^`\n]+)`", outside_blocks)))
with_position = list(dict.fromkeys(text for text, _ in re.findall(r"`([^`\n]+)` \((\d+)\)", outside_blocks)))
spec_texts = test_cases.SPEC_TEXTS
check(f"SPEC_TEXTS: each of its {len(spec_texts)} texts stands in SPEC.md between backticks",
      all(t in quoted for t in spec_texts), f"not quoted any more: {[t for t in spec_texts if t not in quoted]}")
missing = [t for t in quoted if reads(t) and t not in spec_texts]
check("SPEC_TEXTS: it holds everything between backticks in SPEC.md that the model reads as a SMILES text",
      not missing, f"missing: {missing}")
missing = [t for t in with_position if t not in spec_texts]
# 51: the 50 examples of the error tables, which check_spec.py counts, and `C/1CC=1` (6), which stands in
# a sentence of section 12.2.
check(f"SPEC_TEXTS: it holds all {len(with_position)} examples that SPEC.md gives with a position",
      len(with_position) == 51 and not missing, f"missing: {missing}")

# Theorems 4 and 5 together, on the model's side. The tests have a text that is not read behind a
# command word for a handful of texts only, so the model is asked here, for every test text that
# is not read.
unread = [text for text in TEXTS if not reads(text) and text not in model.WORDS]
differs = [(word, text) for text in unread for word in model.WORDS if model.run([word, text]) != model.run([text])]
check(f"the model gives each of the {len(unread)} test texts that it does not read the same answer behind a command word as alone",
      len(unread) >= 200 and not differs, f"differs for: {differs[:5]}")

# NCI_TEXTS against the file that RDKit ships (sources.corpus() has held that file against its recorded
# checksum and its 4,900 different texts).
nci = [text for name, text in sources.corpus() if name == "nci5k"]
check(f"NCI_TEXTS: its {len(test_cases.NCI_TEXTS)} texts are the first and then every {test_cases.EVERY}th text of that file",
      test_cases.NCI_TEXTS == nci[::test_cases.EVERY] and len(test_cases.NCI_TEXTS) == 100)

check(f"FILTER_TEXTS: each of its {len(test_cases.FILTER_TEXTS)} texts is read, and stands in MORE_TEXTS",
      all(reads(t) and t in test_cases.MORE_TEXTS for t in test_cases.FILTER_TEXTS),
      f"not so: {[t for t in test_cases.FILTER_TEXTS if not (reads(t) and t in test_cases.MORE_TEXTS)]}")
check(f"no text stands in two of the lists SPEC_TEXTS, MORE_TEXTS and NCI_TEXTS, or twice in one ({len(TEXTS)} texts)",
      len(set(TEXTS)) == len(TEXTS), f"twice: {sorted(t for t in set(TEXTS) if TEXTS.count(t) > 1)}")

# The table "What may come next" of SPEC.md, section 6. Each row is written out here as it stands in
# SPEC.md, with what it says, and so is the rule for the message of a refused token, from the paragraph
# behind the table of messages. Only the cutting into tokens is the model's (`model.tokens_of`).
BOND_AFTER_A_BRACKET = "| a bond symbol after `(` or `)` | an atom |"
MAY_COME_NEXT = {
    "nothing yet": ("| nothing yet | an atom, or the end of the text |", {"atom", "end"}),
    "a dot": ("| a dot | an atom |", {"atom"}),
    "(": ("| `(` | an atom, a bond symbol, a dot |", {"atom", "bond", "."}),
    "a bond symbol after (": (BOND_AFTER_A_BRACKET, {"atom"}),
    "a bond symbol after )": (BOND_AFTER_A_BRACKET, {"atom"}),
    "a bond symbol after an atom or a ring number":
        ("| a bond symbol after an atom or a ring number | an atom, a ring number |", {"atom", "ring"}),
    "an atom or a ring number":
        ("| an atom or a ring number | an atom, a bond symbol, a ring number, `(`, `)`, a dot, the end of the text |",
         {"atom", "bond", "ring", "(", ")", ".", "end"}),
    ")": ("| `)` | an atom, a bond symbol, `(`, `)`, a dot, the end of the text |",
          {"atom", "bond", "(", ")", ".", "end"}),
}
KINDS = ["atom", "bond", "ring", "(", ")", ".", "end"]
# The three messages for something that the table does not let come.
NOT_ALLOWED_HERE = ("an atom is expected here", "an atom or a ring number is expected here",
                    "a ring number must come before the branches of its atom")
# Messages of section 6 with which the reader stops at a token that the table lets come.
STOPS_AT_ITS_TOKEN = ("an atom cannot be bonded to itself", "these two atoms are already bonded", "')' has no matching '('")


def read_last(before, kind):
    """What was read last, once a token of this kind has been read."""
    if kind in ("atom", "ring"):
        return "an atom or a ring number"
    if kind == "bond":
        return {"(": "a bond symbol after (", ")": "a bond symbol after )"}.get(before, "a bond symbol after an atom or a ring number")
    return {"(": "(", ")": ")", ".": "a dot"}[kind]


def message_for(before, kind):
    """The message for an atom, a symbol or a number that the table does not let come next."""
    if kind == "ring" and before in (")", "a bond symbol after )"):
        return "a ring number must come before the branches of its atom"
    if before == "a bond symbol after an atom or a ring number":
        return "an atom or a ring number is expected here"
    return "an atom is expected here"


def places_of(text):
    """The places of the table that the reader passes in a text, each as (what was read last, what comes
    next); and, where the table refuses the text at the last of them, the answer worked out by hand, as
    (position, message)."""
    problem = model.problem_of(text)
    passed, before, position = [], "nothing yet", None
    try:
        for token in model.tokens_of(text):
            passed.append((before, token.kind))
            if token.kind not in MAY_COME_NEXT[before][1]:
                return passed, (token.pos, message_for(before, token.kind))
            if problem is not None and problem[0] == token.pos and (
                    problem[1] in STOPS_AT_ITS_TOKEN or problem[1].startswith("the two ends of ring")):
                return passed, None            # the table lets the token come, and another rule stops the reader here
            if problem is not None and problem[0] == token.pos and problem[1] in NOT_ALLOWED_HERE:
                return passed, (token.pos, "the table lets this come")      # the model refuses what the table allows
            before, position = read_last(before, token.kind), token.pos
    except model.SmilesError:
        return passed, None                    # a character that is not read: the reader stops here
    passed.append((before, "end"))
    if "end" in MAY_COME_NEXT[before][1]:
        return passed, None
    if before.startswith("a bond symbol"):
        return passed, (position, "the text ends after a bond symbol")
    return passed, (position, {"a dot": "the text ends after a dot", "(": "'(' is never closed"}[before])


reached, refused, not_by_the_rule = set(), 0, []
for text in TEXTS:
    passed, by_hand = places_of(text)
    reached.update(passed)
    if by_hand is not None:
        refused += 1
        if model.problem_of(text) != by_hand:
            not_by_the_rule.append((text, by_hand, model.problem_of(text)))
without = [(before, kind) for before in MAY_COME_NEXT for kind in KINDS if (before, kind) not in reached]
# The rows that are written out above must be the rows of the table in SPEC.md, all of them and no other.
table = re.search(r"\| Read last \| May come next \|\n\|---\|---\|\n((?:\|.*\n)+)", SPEC)
rows_of_the_table = table.group(1).splitlines() if table else []
check(f"every one of the {len(MAY_COME_NEXT) * len(KINDS)} places of the table \"What may come next\" (SPEC.md, section 6: its "
      f"{len(rows_of_the_table)} rows, of which the one for a bond symbol after `(` or `)` is taken as two, times {len(KINDS)} "
      "things that can come) is reached by a test text",
      sorted(rows_of_the_table) == sorted({row for row, _ in MAY_COME_NEXT.values()}) and not without,
      f"the table of SPEC.md has the rows {rows_of_the_table}, which are not the rows written out here, or no test text "
      f"reaches: {without}")
check(f"each of the {refused} test texts that this table refuses has the position and the message that section 6 gives in words",
      refused >= 60 and not not_by_the_rule, f"(the text, by hand, the model): {not_by_the_rule[:5]}")

# The hand-made Mols: "well formed" was answered by hand in test_cases.py. The model must agree.
disagree = [name for name, mol, by_hand in test_cases.HAND_MADE_MOLS if model.is_well_formed(mol) != by_hand]
check(f"HAND_MADE_MOLS: for each of the {len(test_cases.HAND_MADE_MOLS)} Mols the model says \"well formed\" or \"not well formed\" as was worked out by hand",
      not disagree, f"the model says otherwise for: {disagree}")
names = [t for t in spec_texts if reads(t)] + [name for name, _, _ in test_cases.HAND_MADE_MOLS]
check("no two entries of `mols` have the same name", len(set(names)) == len(names))

# The renumbered Mols: each is another numbering of a Mol that the model reads.
renumbered = test_cases.RENUMBERED_MOLS
of_the_text = [model.read(text) for text in test_cases.NCI_TEXTS + test_cases.RENUMBERED_STEREO_TEXTS if reads(text)]
with_stereo = sum(model.has_stereo(mol) for _, mol in renumbered)
check(f"RENUMBERED_MOLS: one Mol for each of the {len(of_the_text)} texts of NCI_TEXTS and RENUMBERED_STEREO_TEXTS "
      f"that are read, with the same atoms and as many bonds, orientations and geometries, well formed, under a "
      f"name of its own; {with_stereo} of them have stereo facts",
      len(renumbered) == len(of_the_text) == len({name for name, _ in renumbered})
      and with_stereo == len(test_cases.RENUMBERED_STEREO_TEXTS)
      and all(text in TEXTS for text in test_cases.RENUMBERED_STEREO_TEXTS)
      and all(sorted(map(repr, mol.atoms)) == sorted(map(repr, original.atoms)) and len(mol.bonds) == len(original.bonds)
              and len(mol.orientations) == len(original.orientations)
              and len(mol.geometries) == len(original.geometries)
              and model.is_well_formed(mol) for (_, mol), original in zip(renumbered, of_the_text)))


# The renumbering of the stereo facts is written out in test_cases.py by the rule for a stored mark. The
# model restates them through its two statements. The two must give the same Mol.
def order_of(original, mol_name):
    """The order in which `model.arrange` must put the atoms to get the renumbered Mol: read off the name."""
    n = len(original.atoms)
    if mol_name.endswith("numbered backwards"):
        new = [n - 1 - i for i in range(n)]
    elif mol_name.endswith("numbered last"):
        new = [(i - 1) % n for i in range(n)]
    else:
        m = int(re.search(r"\(i \* (\d+)\) mod", mol_name).group(1))
        new = [(i * m) % n for i in range(n)]
    order = [None] * n
    for i, j in enumerate(new):
        order[j] = i
    return order


differ = [name for (name, mol), original in zip(renumbered, of_the_text)
          if model.arrange(original, order_of(original, name)) != mol]
check("RENUMBERED_MOLS: each is what the model gives when it puts the atoms of the Mol in that order, stereo facts included",
      not differ, f"differs for: {differ[:3]}")
other = sum(mol != original for (_, mol), original in zip(renumbered, of_the_text))
check(f"RENUMBERED_MOLS: {other} of them are another Mol than the reader returns for the text (the rest are "
      "molecules that read the same backwards)", other >= 0.9 * len(renumbered))

# TestData.lean against the model.
on_disk = TARGET.read_text() if TARGET.exists() else None
check("TestData.lean is exactly what the model gives", on_disk == expected,
      "TestData.lean is missing." if on_disk is None else
      "It differs. If the model, SPEC.md or test_cases.py was changed on purpose, run this script with --write,\n"
      "        look at `git diff TestData.lean`, and run `lake test`.")

sys.exit(sources.end_of_checks())
