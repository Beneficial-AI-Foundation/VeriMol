"""Check the examples and claims of SPEC.md against the model, RDKit, Open Babel and the OpenSMILES text.

    .venv/bin/python -I reference/check_spec.py

Three kinds of checks:
  * read out of SPEC.md itself: every row of the error tables (sections 6 and 12.2), the two printed
    examples of section 7, the table of spellings in section 9.2, the table of chosen texts and the two
    keys of section 3.2, the element symbols of section 15, and of the filter (section 16) the three
    commands at its head, the table of messages and the examples with the sizes of their largest
    groups. If SPEC.md changes, these follow.
  * written out below: claims that SPEC.md makes in sentences. Where such a claim is about texts that
    SPEC.md quotes, the check names them, and it fails if SPEC.md does not quote one of them: so the two
    cannot drift apart unnoticed.
    Every text in the tables of differences from RDKit (sections 11.2 and 12.4) must have a check here.
  * read out of VeriMol/Proofs/Read.lean: the Mols that its theorems about single texts write out by
    hand. RDKit and Open Babel must read the atoms and the bonds of these Mols from the same texts, and
    Open Babel's own record must hold their stereo facts.

Prints one line per check and ends with exit code 1 if any check fails.
"""
import itertools
import re
import shlex
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_canonical
import check_filter
import check_stereo
import model
import others
import sources
import test_cases
from rdkit import Chem

SPEC = (Path(__file__).resolve().parent.parent / "SPEC.md").read_text()
# SPEC.md with every line break and run of spaces as one space: a sentence of it may be broken over two lines.
words = " ".join(SPEC.split())


def check(section, what, passed, detail=""):
    """One line for each check: PASS or FAIL, the section of SPEC.md that it belongs to, and what was asked."""
    sources.check(f"{section:5s} {what}", passed, f"    {detail}")


def quoted(*texts):
    """Every one of these texts must stand in SPEC.md between backticks."""
    missing = [t for t in texts if f"`{t}`" not in SPEC]
    if missing:
        check("-", f"SPEC.md still quotes {', '.join(texts)}", False, "not found any more: " + ", ".join(missing))
    return not missing


reads = model.read_or_none          # the Mol of a text, or None
error_of = model.problem_of         # the problem in a text as (position, message), or None


def atoms_of(text):
    return reads(text).atoms


def hydrogens(text):
    return [a.hydrogens for a in atoms_of(text)]


def part(start, end):
    """The text of SPEC.md from one heading to the next."""
    return SPEC[SPEC.index(start):SPEC.index(end)]


# ---------------------------------------------------------------------------- read out of SPEC.md itself
lines = SPEC.splitlines()
section, rows = 0, 0
for line in lines:
    m = re.match(r"## (\d+)\.", line)
    if m:
        section = int(m.group(1))
    if section not in (6, 12) or not line.startswith("| `"):
        continue
    cells = [c.strip() for c in line.strip().strip("|").split("|")]
    examples = re.findall(r"`([^`]*)` \((\d+)\)", cells[-1])
    if len(cells) != 2 or not examples:
        continue
    message = re.match(r"`([^`]*)`", cells[0]).group(1)
    for text, position in examples:
        rows += 1
        expected = (int(position), f"'{text[int(position)]}' cannot be read here" if message.startswith("'X'") else message)
        got = error_of(text)
        check(str(section), f"{text!r} gives \"{expected[1]}\" at position {expected[0]}", got == expected, f"the model gives {got}")
# The number is written out, so that a row which is lost from SPEC.md is noticed. When a row is added or
# taken out on purpose, change the number here.
check("6, 12", f"the error tables of SPEC.md have their {rows} examples", rows == 50)

blocks = re.findall(r"```\n\$ app '([^']*)'\n(.*?)```", SPEC, re.S)
check("7", f"the two printed examples of SPEC.md were found, one of them with stereo facts ({len(blocks)} found)",
      len(blocks) == 2 and [bool(reads(text).orientations or reads(text).geometries) for text, _ in blocks] == [False, True])
for text, printed in blocks:
    check("7", f"the printed example for {text!r} is what the model prints", model.run([text])[0] == printed, repr(model.run([text])[0]))

table = re.findall(r"^\| `([^`]*)` \| `([^`]*)` \| `([^`]*)` \|$", part("### 9.2", "### 9.3"), re.M)
check("9.2", f"the table of spellings of SPEC.md has its {len(table)} rows", len(table) == 6)
for text, plain, brackets in table:
    mol = reads(text)
    got = None if mol is None else (model.write_plain(mol), model.write(mol))
    check("9.2", f"{text!r} is written {plain!r} and {brackets!r}", got == (plain, brackets), f"the model writes {got}")

listed = re.search(r"## 15\..*?```\n(.*?)```", SPEC, re.S)
symbols = listed.group(1).split() if listed else []
check("15", "the 118 element symbols of SPEC.md, of the model and of RDKit are the same, in the same order",
      symbols == model.ELEMENTS == others.RDKIT_ELEMENTS)
standard = sources.checked_bytes("opensmiles").decode("utf-8")
theirs = re.findall(r"`'([A-Za-z]+)'`", standard[standard.index("_element_symbols_ ::="):standard.index("_aromatic_symbols_ ::=")])
check("4.1", "OpenSMILES lists 114 element symbols; SPEC.md has those and Nh, Mc, Ts, Og",
      len(theirs) == 114 and sorted(theirs + ["Nh", "Mc", "Ts", "Og"]) == sorted(model.ELEMENTS))
if quoted("[C+H]", "[C-H3]", "C[CH@](Br)Cl"):
    check("4.1", "the order inside square brackets: OpenSMILES has [C-H3] and C[CH@](Br)Cl among its examples, and the "
                 "model reads neither of them, nor [C+H]",
          "`[C-H3]`" in standard and "`C[CH@](Br)Cl`" in standard
          and all(reads(t) is None for t in ("[C+H]", "[C-H3]", "C[CH@](Br)Cl")))


# ------------------------------------------------------------------- claims that SPEC.md makes in sentences
if quoted("[Na+].[Cl-]"):
    m = reads("[Na+].[Cl-]")
    check("3", "[Na+].[Cl-] is one Mol with two pieces", len(m.atoms) == 2 and not m.bonds)
if quoted("[Co]", "[HH]"):
    check("4", "[Co] is cobalt", atoms_of("[Co]")[0].element == "Co")
    check("4", "[HH] is not read", reads("[HH]") is None)
check("4", "an empty text gives a Mol without atoms", reads("") == model.Mol((), ()))
if quoted("[13C]", "[013C]", "++", "--", "%05", "C1.C1", "c1ccccc1-c1ccccc1"):
    check("5", "[13C] and [013C] are the same", reads("[13C]") == reads("[013C]") and atoms_of("[13C]")[0].isotope == 13)
    check("5", "+ and - alone mean +1 and -1; ++ and -- mean +2 and -2",
          [atoms_of(t)[0].charge for t in ("[Na+]", "[Cl-]", "[Fe++]", "[O--]")] == [1, -1, 2, -2]
          and reads("[Fe++]") == reads("[Fe+2]") and reads("[O--]") == reads("[O-2]"))
    check("5", "H alone means 1 hydrogen", atoms_of("[CH]")[0].hydrogens == 1)
    check("5", "%05 and 5 are the same value", reads("C%05CC5") == reads("C1CC1") is not None)
    check("5", "C1.C1 is ethane", reads("C1.C1") == reads("CC"))
    with_dash, without = reads("c1ccccc1-c1ccccc1"), reads("c1ccccc1c1ccccc1")
    between = lambda m: next(b.order for b in m.bonds if (b.a, b.b) == (5, 6))
    check("5", "biphenyl needs its -", between(with_dash) == "single" and between(without) == "aromatic")
if quoted("CC(=O)O", "c1ccccc1", "c1ccncc1"):
    check("5", "hydrogens: C has 4; CC(=O)O has 3, 0, 0, 1; benzene 1 each; the nitrogen of pyridine 0",
          hydrogens("C") == [4] and hydrogens("CC(=O)O") == [3, 0, 0, 1] and hydrogens("c1ccccc1") == [1] * 6
          and hydrogens("c1ccncc1")[3] == 0)

# Section 6: the first problem is reported, and which message a character gets.
if quoted("CC(C))C(=O)[O-"):
    check("6", "CC(C))C(=O)[O- has two problems; the first one is reported",
          error_of("CC(C))C(=O)[O-") == (5, "')' has no matching '('"))
for text, expected in [("[C 1]", (2, "white space is not allowed")), ("[C/]", (2, "'/' cannot be read here")),
                       ("[C*]", (2, "the wildcard atom is not read")), ("[C:1]", (2, "atom classes are not read")),
                       ("[C!]", (2, "'!' cannot be read here")), ("[ C]", (1, "white space is not allowed")),
                       ("[*]", (1, "the wildcard atom is not read")), ("[/C]", (1, "an element symbol is expected here")),
                       ("[:1]", (1, "an element symbol is expected here")), ("[@C]", (1, "an element symbol is expected here")),
                       ("C@", (1, "'@' cannot be read here")), ("[C@@@]", (4, "'@' cannot be read here")),
                       ("C!", (1, "'!' cannot be read here")),
                       ("C%12", (1, "ring 12 is opened but never closed")), ("C(%12", (2, "an atom is expected here"))]:
    check("6", f"{text!r} gives \"{expected[1]}\" at position {expected[0]}", error_of(text) == expected, f"the model gives {error_of(text)}")

check("7", "a Mol without atoms, and one without bonds and without stereo facts, are printed as said",
      model.run([""])[0] == "{ atoms := [],\n  bonds := [],\n  orientations := [],\n  geometries := [] }\n"
      and model.run(["C"])[0].endswith("  bonds := [],\n  orientations := [],\n  geometries := [] }\n"))
usage = ("error: expected a SMILES text, or one of the words rewrite, plain and canonical followed by a SMILES text, "
         "or the words filter perfluoro followed by a number from 1 on and a SMILES text")
check("8", "anything else gives the usage message and exit code 1", usage in SPEC
      and all(model.run(a) == ("", usage + "\n", 1)
              for a in ([], ["a", "b", "c"], ["print", "C"], ["rewrite"], ["plain"], ["canonical"],
                        ["filter", "perfluoro"], ["filter", "perfluoro", "6"], ["filter", "perfluoro", "0", "C"],
                        ["filter", "other", "6", "C"], ["a", "b", "c", "d", "e"])))
check("8", "rewrite and plain print one line", model.run(["rewrite", "CC(C)C"]) == ("CC(C)C\n", "", 0)
      and model.run(["plain", "CC(C)C"]) == ("[CH3]-[CH]-1-[CH3].[CH3]1\n", "", 0))
if quoted("[13CH4]", "[nH]", "[NH4+]", "[Fe+2]", "[O-]", "c1cc[nH]c1", "[NH]"):
    check("9", "the examples of atoms in square brackets are written as they stand, [nH] inside pyrrole",
          all(model.run(["rewrite", t])[0] == t + "\n" for t in ("[13CH4]", "c1cc[nH]c1", "[NH4+]", "[Fe+2]", "[O-]"))
          and model.run(["rewrite", "[Fe++]"])[0] == "[Fe+2]\n")
    check("9", "the case of a symbol comes from the bonds: [nH] alone comes back as [NH], C:C as [cH3][cH3], c-c as [CH2][CH2]",
          [model.run(["rewrite", t])[0] for t in ("[nH]", "C:C", "c-c")] == ["[NH]\n", "[cH3][cH3]\n", "[CH2][CH2]\n"]
          and all(reads(model.run(["rewrite", t])[0].strip()) == reads(t) for t in ("[nH]", "C:C", "c-c")))
no_real_text_has_a_colon = not any(":" in t for _, t in sources.corpus())
if quoted("C:C", "[cH3][cH3]", "[CH2][CH2]", "[NH]", "F:C", "[F]:[cH3]"):
    back = {t: model.run(["rewrite", t])[0].strip() for t in ("[nH]", "C:C", "c-c", "F:C")}
    check("9", "RDKit reads the rewritten text of [nH], of C:C, of c-c and of F:C as the Mol that was written, with lowercase symbols where section 9 asks for them",
          all(others.rdkit_mol(written) == reads(t) and others.rdkit_lowercase(written) == others.lowercase_by_rule(reads(t))
              for t, written in back.items()), str(back))
    ob_orders = [[b.order for b in others.openbabel_mol(t).bonds] for t in ("C:C", "[cH3][cH3]")]
    check("9", "Open Babel reads C:C with a single bond and [cH3][cH3] with a double bond, and no real text has the symbol ':'",
          ob_orders == [["single"], ["double"]] and no_real_text_has_a_colon, str(ob_orders))
    check("9.2", "condition 5: F:C comes back as [F]:[cH3], in both spellings",
          [model.run([word, "F:C"])[0] for word in ("rewrite", "plain")] == ["[F]:[cH3]\n"] * 2, back["F:C"])
if quoted("CC(C)C", "[CH3]-[CH]-1-[CH3].[CH3]1", "C1.CC1"):
    check("9.1", "isobutane is written [CH3]-[CH]-1-[CH3].[CH3]1 in the plain spelling, and both texts give the same Mol",
          model.write_plain(reads("CC(C)C")) == "[CH3]-[CH]-1-[CH3].[CH3]1" and reads("[CH3]-[CH]-1-[CH3].[CH3]1") == reads("CC(C)C"))
    c3, c2 = model.Atom("C", None, 0, 3), model.Atom("C", None, 0, 2)
    propane = model.Mol((c3, c3, c2), (model.Bond(0, 2, "single"), model.Bond(1, 2, "single")))
    check("9.2", "propane numbered end, end, middle is C1.CC1 with round brackets",
          model.write(propane) == "C1.CC1" and reads("C1.CC1") == propane)
if quoted("Cl[I]Cl", "ClICl"):
    check("9.2", "an atom whose bonds add up to no normal valence keeps its square brackets: Cl[I]Cl",
          model.run(["rewrite", "Cl[I]Cl"])[0] == "Cl[I]Cl\n" and model.run(["rewrite", "CS(C)(=O)=O"])[0] == "CS(C)(=O)=O\n")
    check("9.2", "RDKit reads ClICl with one hydrogen more than Cl[I]Cl", others.rdkit_mol("ClICl").atoms[1].hydrogens == 1
          and others.rdkit_mol("Cl[I]Cl").atoms[1].hydrogens == 0)
check("9.3", "rewrite writes aspirin, CC(=O)Oc1ccccc1C(=O)O, back as it stands",
      model.run(["rewrite", "CC(=O)Oc1ccccc1C(=O)O"]) == ("CC(=O)Oc1ccccc1C(=O)O\n", "", 0))
for text in ("CC(C)C", "OC(=O)C", "C1CC1C", "c1ccccc1-c1ccccc1", "[O-]C(=O)C.[Na+]", "CN(C)(C)C"):
    for word in ("rewrite", "plain"):
        once = model.run([word, text])[0].strip()
        check("10", f"theorems 13 and 14 on one example: {word} {text!r} gives {once!r}, which reads as the same Mol and is written the same again",
              reads(once) == reads(text) and model.run([word, once])[0].strip() == once)

# Section 11.2: the three kinds of difference from RDKit, clean-up off. Each entry: the texts, this program, RDKit.
rd = others.rdkit_mol
known = [
    (("[0C]",), lambda: atoms_of("[0C]")[0].isotope == 0, lambda: rd("[0C]").atoms[0].isotope is None),
    (("CN(C)(C)C",), lambda: hydrogens("CN(C)(C)C")[1] == 1, lambda: rd("CN(C)(C)C").atoms[1].hydrogens == 0),
    (("FP(F)(F)(F)(F)F",), lambda: hydrogens("FP(F)(F)(F)(F)F")[1] == 0, lambda: rd("FP(F)(F)(F)(F)F").atoms[1].hydrogens == 1),
    (("CIC",), lambda: hydrogens("CIC")[1] == 0, lambda: rd("CIC").atoms[1].hydrogens == 1),
    (("C:C",), lambda: hydrogens("C:C") == [3, 3], lambda: [a.hydrogens for a in rd("C:C").atoms] == [2, 2]),
    (("c",), lambda: hydrogens("c") == [3], lambda: rd("c").atoms[0].hydrogens == 4),
    (("[013C]",), lambda: atoms_of("[013C]")[0].isotope == 13, lambda: rd("[013C]") is None),
    (("C%01CC1",), lambda: reads("C%01CC1") == reads("C1CC1"), lambda: rd("C%01CC1") is None),
    (("C(.C)C",), lambda: reads("C(.C)C") is not None, lambda: rd("C(.C)C") is None),
    (("C C",), lambda: reads("C C") is None, lambda: len(rd("C C").atoms) == 1),
    (("[HH]", "[CH10]"), lambda: reads("[CH10]") is None and reads("[HH]") is None, lambda: rd("[CH10]") is not None and rd("[HH]") is not None),
    (("C=1CC-1", "C-1CC=1"), lambda: reads("C=1CC-1") is None and reads("C-1CC=1") is None,
     lambda: [b.order for b in rd("C=1CC-1").bonds].count("double") == 1 and {b.order for b in rd("C-1CC=1").bonds} == {"single"}),
    (("[C+100]",), lambda: reads("[C+100]") is None,
     lambda: rd("[C+100]").atoms[0].charge == 100 and others.openbabel_mol("[C+100]").atoms[0].charge == 100),
    (("C~C",), lambda: reads("C~C") is None, lambda: len(rd("C~C").atoms) == 2),
    (("C\N{LATIN SMALL LETTER E WITH ACUTE}", "C\N{SUPERSCRIPT TWO}"),
     lambda: reads("C\N{LATIN SMALL LETTER E WITH ACUTE}") is None and reads("C\N{SUPERSCRIPT TWO}") is None,
     lambda: len(rd("C\N{LATIN SMALL LETTER E WITH ACUTE}").atoms) == 1 and len(rd("C\N{SUPERSCRIPT TWO}").atoms) == 1),
    (("C(C)1CC1",), lambda: reads("C(C)1CC1") is None, lambda: rd("C(C)1CC1") is not None),
    (("[te]", "[si]"), lambda: reads("[te]") is None and reads("[si]") is None, lambda: rd("[te]") is not None and rd("[si]") is not None),
    (("*", "[CH3:1]"), lambda: reads("*") is None and reads("[CH3:1]") is None, lambda: rd("*") is not None and rd("[CH3:1]") is not None),
    (("N->[Fe]",), lambda: reads("N->[Fe]") is None, lambda: rd("N->[Fe]") is not None and rd("N<-[Fe]") is not None),
]
for texts, ours, rdkit in known:
    if quoted(*texts):
        check("11.2", f"difference {', '.join(texts)}: this program as the table says", ours())
        check("11.2", f"difference {', '.join(texts)}: RDKit as the table says", rdkit())
in_tables = set()
for line in part("### 11.2", "## 12.").splitlines():
    if line.startswith("| `"):
        in_tables |= set(re.findall(r"`([^`]*)`", line.strip("|").split("|")[0]))
covered = {t for texts, _, _ in known for t in texts}
long_number = "[12345678901234567890C]"
check("11.2", "a mass number of 20 digits: this program keeps it, RDKit and Open Babel refuse the text",
      "a mass number of 20 digits" in SPEC and atoms_of(long_number)[0].isotope == 12345678901234567890
      and rd(long_number) is None and others.openbabel_mol(long_number) is None)
most = others.MOST_THAT_RDKIT_TAKES
check("11.2", f"the kinds that no test text shows: RDKit keeps a mass number from 65,536 to {most:,} modulo 65,536 and refuses "
      "a larger one, refuses a charge with a zero in front, and reads an atomic number behind #, a ring number in round "
      "brackets, and the nine old names of the elements 110 to 118",
      "Known as well" in SPEC and f"from 65,536 to {most:,}" in SPEC and "from Uun to Uuo" in SPEC
      and atoms_of("[65549C]")[0].isotope == 65549 and rd("[65549C]").atoms[0].isotope == 13
      and atoms_of(f"[{most}C]")[0].isotope == most and rd(f"[{most}C]").atoms[0].isotope == most % 65536
      and atoms_of(f"[{most + 1}C]")[0].isotope == most + 1 and rd(f"[{most + 1}C]") is None
      and atoms_of("[C+07]")[0].charge == 7 and rd("[C+07]") is None
      and reads("[#6]") is None and rd("[#6]") is not None
      and reads("C%(100)CC%(100)") is None and rd("C%(100)CC%(100)") is not None
      and [(reads(f"[{old}]"), rd(f"[{old}]").atoms[0].element) for old in others.OLD_NAMES]
      == [(None, new) for new in ("Ds", "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og")])
check("11.2", "every text in the three tables of differences has a check here", in_tables and in_tables <= covered,
      f"without a check: {sorted(in_tables - covered)}")

# Sections 5 and 11.2: the hydrogens of every bare symbol with every combination of up to four bonds.
cases, differs_from_ob, outside_the_five, misread = 0, [], [], []
for sym in ["B", "C", "N", "O", "P", "S", "F", "Cl", "Br", "I", "b", "c", "n", "o", "p", "s"]:
    for k in range(5):
        for bonds in itertools.combinations_with_replacement("-=#:$", k):
            cases += 1
            text = sym + "".join(f"({b}[C])" for b in bonds)        # a star: bracket carbons around the atom
            mol = reads(text)
            ours, total = mol.atoms[0].hydrogens, sum({"-": 1, "=": 2, "#": 3, ":": 1, "$": 4}[b] for b in bonds)
            if others.openbabel_mol(text).atoms[0].hydrogens != ours:
                differs_from_ob.append(text)
            element = model.LOWERCASE.get(sym, sym)
            if rd(text).atoms[0].hydrogens != ours and not others.one_of_the_five(element, sym.islower(), total, ":" in bonds):
                outside_the_five.append(text)
            if rd(model.write(mol)) != mol:
                misread.append(text)
check("5", f"rule 7 gives the hydrogens that Open Babel counts, in all {cases} cases", cases == 2016 and not differs_from_ob, str(differs_from_ob[:5]))
check("11.2", "RDKit counts other hydrogens only in the five situations of the table", not outside_the_five, str(outside_the_five[:5]))
check("9.2", f"RDKit reads the spelling with round brackets of all {cases} cases as exactly the Mol", not misread, str(misread[:5]))
ob = others.openbabel_mol
check("11.2", "Open Babel counts the hydrogens of the five rows as this program does",
      ob("CN(C)(C)C").atoms[1].hydrogens == 1 and ob("FP(F)(F)(F)(F)F").atoms[1].hydrogens == 0 and ob("CIC").atoms[1].hydrogens == 0
      and ob("c").atoms[0].hydrogens == 3 and [a.hydrogens for a in ob("C:C").atoms] == [3, 3])

# Section 3.2: the chosen form. The table of the section is read out of SPEC.md: every text of a row must
# get the chosen text of the row. The key that the section defines is worked out by check_canonical.py,
# without the model's search.
section_3_2 = part("### 3.2 The chosen form", "## 4. Which texts are read")
chosen_rows = [(re.findall(r"`([^`]+)`", cells[0]), cells[1].strip("` "))
               for cells in (line.strip("|").split("|") for line in section_3_2.splitlines()
                             if line.startswith("| `"))
               if len(cells) == 2]
check("3.2", f"the table of chosen texts was found in SPEC.md ({len(chosen_rows)} rows, four of them with stereo marks)",
      len(chosen_rows) == 11 and sum(bool(re.search(r"[@/\\]", chosen)) for _, chosen in chosen_rows) == 4)
for texts, chosen in chosen_rows:
    answers = [model.run(["canonical", t]) for t in texts]
    check("3.2", f"canonical writes {chosen} for {', '.join(texts)}", all(a == (chosen + "\n", "", 0) for a in answers), str(answers))
if quoted("OCC", "CCO"):
    as_read, as_chosen = reads("OCC"), reads("CCO")
    least = min(check_canonical.key_of(as_read, list(order)) for order in itertools.permutations(range(3)))
    # The two keys as the section writes them out: the rows of its table "| Atom | `OCC` | `CCO` |".
    key_rows = [line.strip("|").split("|")[1:] for line in section_3_2.splitlines()
                if re.fullmatch(r"\| \d+ \|[\d, then]+\|[\d, then]+\|", line)]
    written_out = [[tuple(int(number) for number in re.findall(r"\d+", row[column])) for row in key_rows] for column in (0, 1)]
    check("3.2", "the keys of OCC and of CCO that the section writes out are the keys by its rules, and the key of CCO is the least of the six numberings",
          len(key_rows) == 3 and check_canonical.key_of(as_read, [0, 1, 2]) == written_out[0]
          and check_canonical.key_of(as_chosen, [0, 1, 2]) == written_out[1] and written_out[1] == least,
          f"written out: {written_out}; by the rules: {check_canonical.key_of(as_read, [0, 1, 2])} {check_canonical.key_of(as_chosen, [0, 1, 2])}")
search_gives_up = "error: the chosen form is not worked out: too many numberings of this molecule look alike\n"
if quoted("N[Co+3](N)(N)(N)(N)N", "OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO", "c1ccccc1", "C1=CC=CC=C1"):
    check("3.2", "atoms and groups that can be exchanged: N[Co+3](N)(N)(N)(N)N and OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO get a chosen text, "
                 "and SPEC.md quotes the message of the search that gives up",
          model.run(["canonical", "N[Co+3](N)(N)(N)(N)N"])[2] == 0
          and model.run(["canonical", "OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO"])[1:] == ("", 0) and search_gives_up.strip() in SPEC)
    lowercase, alternating = model.run(["canonical", "c1ccccc1"]), model.run(["canonical", "C1=CC=CC=C1"])
    check("3.2", "c1ccccc1 and C1=CC=CC=C1 keep two chosen texts",
          lowercase[2] == 0 and alternating[2] == 0 and lowercase[0] != alternating[0], f"{lowercase} {alternating}")
    check("3.2", "the ladder of section 9.4, which rewrite refuses, gets a chosen text, and canonical writes that text again",
          model.run(["canonical", test_cases.LADDER])[2] == 0
          and model.run(["canonical", model.run(["canonical", test_cases.LADDER])[0].strip()]) == model.run(["canonical", test_cases.LADDER]))


def with_another_limit(limit, text):
    """What the model's `canonical` answers for a text when its search may hold `limit` beginnings."""
    usual = model.SEARCH_LIMIT
    model.SEARCH_LIMIT = limit
    try:
        return model.run(["canonical", text])
    finally:
        model.SEARCH_LIMIT = usual


with_alanine = ("C1CCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O", "C1CCCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O")
if quoted("C1CCCCC1.N1NNNN1.O1OOOO1", *with_alanine, "CC"):
    def with_the_least_key(text):
        """How many numberings of a small Mol have the least key, counted one by one from the definition."""
        mol = reads(text)
        keys = [check_canonical.key_of(mol, list(order)) for order in itertools.permutations(range(len(mol.atoms)))]
        return keys.count(min(keys))
    check("3.2", "the limit for a Mol with stereo facts: a ring of five atoms has 10 numberings with the least key and the ring of six has 12; "
                 "beside alanine, with 10 times 10 times 10 the search gives a chosen text, also when it may hold 1,000 and no more, "
                 "and not when it may hold 999; with 12 times 10 times 10 it gives up, and not when it may hold 1,200",
          [with_the_least_key(t) for t in ("C1CCCC1", "N1NNNN1", "O1OOOO1", "C1CCCCC1")] == [10, 10, 10, 12]
          and "exactly 1,000" in words and "which is 1,200" in words
          and model.run(["canonical", with_alanine[0]])[1:] == ("", 0)
          and with_another_limit(999, with_alanine[0]) == ("", search_gives_up, 1)
          and model.run(["canonical", with_alanine[1]]) == ("", search_gives_up, 1)
          and with_another_limit(1200, with_alanine[1])[1:] == ("", 0)
          and with_another_limit(1199, with_alanine[1]) == ("", search_gives_up, 1))
    check("3.2", "without stereo facts the ways round a ring are alike once it is closed: C1CCCCC1.N1NNNN1.O1OOOO1 gets a chosen text, "
                 "also when the search may hold 12 beginnings and no more, and not when it may hold 11",
          "never holds more than 12 beginnings" in words
          and model.run(["canonical", "C1CCCCC1.N1NNNN1.O1OOOO1"])[1:] == ("", 0)
          and with_another_limit(12, "C1CCCCC1.N1NNNN1.O1OOOO1")[1:] == ("", 0)
          and with_another_limit(11, "C1CCCCC1.N1NNNN1.O1OOOO1") == ("", search_gives_up, 1))
    check("3.2", "CC: both numberings have the least key, by the definition, and the search keeps the atoms as they are numbered",
          with_the_least_key("CC") == 2 and model.chosen_order(reads("CC")) == [0, 1])
    check("3.2", "the rule for twins at work: the test text S(C)(C)(C)(C)(C)(C)C has 5,040 numberings with the least key, by the "
                 "definition, and the search holds one beginning for it: it gives a chosen text also when it may hold one and no more",
          "S(C)(C)(C)(C)(C)(C)C" in test_cases.MORE_TEXTS and with_the_least_key("S(C)(C)(C)(C)(C)(C)C") == 5040
          and with_another_limit(1, "S(C)(C)(C)(C)(C)(C)C")[1:] == ("", 0))

# Section 3.1, and theorems 41 and 42 of CLAIMS.md: the two examples of "the same molecule, numbered
# differently". Lean proves them. Here RDKit is asked, which knows nothing of the definition.
if quoted("CCO", "OCC", "C1CCCCC1", "C1CC1.C1CC1"):
    as_read = others.rdkit_canonical_as_read
    from_carbon, from_oxygen = as_read("CCO"), as_read("OCC")
    check("3.1", "CCO and OCC are read as two different Mols, each is rewritten as it stands, and RDKit takes them for one molecule",
          reads("CCO") != reads("OCC") and [model.run(["rewrite", t])[0] for t in ("CCO", "OCC")] == ["CCO\n", "OCC\n"]
          and from_carbon is not None and from_carbon == from_oxygen, f"{from_carbon} {from_oxygen}")
    ring, rings = reads("C1CCCCC1"), reads("C1CC1.C1CC1")
    one_ring, two_rings = as_read("C1CCCCC1"), as_read("C1CC1.C1CC1")
    check("3.1", "C1CCCCC1 and C1CC1.C1CC1 are read with the same atoms and as many bonds, and RDKit takes them for two molecules",
          ring.atoms == rings.atoms and len(ring.bonds) == len(rings.bonds) == 6
          and one_ring is not None and two_rings is not None and one_ring != two_rings, f"{one_ring} {two_rings}")

# Section 3: spelling that a Mol does not store.
if quoted("C", "[CH4]", "[CH4+0]", "C1CC1", "C2CC2", "[Fe+2]", "[Fe++]", "CC", "C-C", "c-c", "[CH2][CH2]"):
    one_mol = [("C", "[CH4]", "[CH4+0]"), ("C1CC1", "C2CC2"), ("[Fe+2]", "[Fe++]"), ("CC", "C-C"), ("c-c", "[CH2][CH2]")]
    check("3", "texts that differ in spelling only give one Mol: " + "; ".join(" and ".join(group) for group in one_mol),
          all(reads(group[0]) is not None and all(reads(t) == reads(group[0]) for t in group) for group in one_mol))

# Section 3.2: the search gives up in the round, also where fewer would be left at the end. The rounds
# are counted here from the words of the section, without the model's search: the key of the definition
# (check_canonical.key_of), the twins and the beginnings that are alike are written out a second time.
def rounds_of_the_search(mol, kinds_of_bonds=True):
    """The search of section 3.2 for a Mol: in every round the beginnings with the least entry, twins in
    the order of their numbers, and, for a Mol without stereo facts, of the beginnings that are alike only
    the first. Returns, round by round, how many beginnings have the least entry and how many of these
    are held, and the first numbering that is held at the end. With `kinds_of_bonds` off, two beginnings
    count as alike without a look at the kinds of their bonds: a wrong rule, to show that an example of
    the section decides."""
    n = len(mol.atoms)
    order_of = {}
    for bond in mol.bonds:
        order_of[(bond.a, bond.b)] = order_of[(bond.b, bond.a)] = bond.order
    near = [[x for x in range(n) if (a, x) in order_of] for a in range(n)]
    in_a_stereo_fact = set()
    for x in mol.orientations:
        in_a_stereo_fact.update([x.atom] + near[x.atom])
    for x in mol.geometries:
        in_a_stereo_fact.update([x.a, x.b] + near[x.a] + near[x.b])

    def twins(a, b):
        return (mol.atoms[a] == mol.atoms[b] and a not in in_a_stereo_fact and b not in in_a_stereo_fact
                and all(order_of.get((a, x)) == order_of.get((b, x)) for x in range(n) if x not in (a, b)))

    def alike(p, q):
        if set(p) != set(q):
            return False
        for u in range(n):
            if u not in p:
                for i in range(len(p)):
                    one, other = order_of.get((u, p[i])), order_of.get((u, q[i]))
                    if (one != other) if kinds_of_bonds else ((one is None) != (other is None)):
                        return False
        return True

    held, with_the_least_entry, kept = [[]], [], []
    for _ in mol.atoms:
        entries = [((check_canonical.key_of(mol, beginning + [a])[-1],
                     1 if any(twins(a, b) and b not in beginning for b in range(a)) else 0), beginning + [a])
                   for beginning in held for a in range(n) if a not in beginning]
        least = min(entry for entry, _ in entries)
        least_ones = [beginning for entry, beginning in entries if entry == least]
        if mol.orientations or mol.geometries:
            held = least_ones
        else:
            held = []
            for beginning in least_ones:
                if not any(alike(beginning, other) for other in held):
                    held.append(beginning)
        with_the_least_entry.append(len(least_ones))
        kept.append(len(held))
    return with_the_least_entry, kept, held[0]


nine_ethanes, ten_ethanes = ".".join(["CC"] * 9), ".".join(["CC"] * 10)
if quoted(nine_ethanes, ten_ethanes, "C1CCCCC1"):
    counts = [rounds_of_the_search(reads(text))[1] for text in (nine_ethanes, ten_ethanes, "C1CCCCC1")]
    check("3.2", "nine molecules of ethane: by the words of the section the search holds 126 beginnings after four molecules and 630 with "
                 "the first atom of a fifth, which is the most; it gives a chosen text, also when it may hold 630 and no more, and not with 629",
          "which are 126" in words and "which is 630" in words and counts[0][7] == 126 and counts[0][8] == 630 and max(counts[0]) == 630
          and model.run(["canonical", nine_ethanes]) == (nine_ethanes + "\n", "", 0) and with_another_limit(630, nine_ethanes)[1:] == ("", 0)
          and with_another_limit(629, nine_ethanes) == ("", search_gives_up, 1), f"{counts[0]}")
    check("3.2", "ten molecules of ethane: 210 beginnings after four molecules, 1,260 with the first atom of a fifth, and one at the end; "
                 "the search gives up, and not when it may hold 1,260",
          "210 choices of four" in words and "that makes 1,260" in words and counts[1][7] == 210 and counts[1][8] == 1260
          and max(counts[1]) == 1260 and counts[1][-1] == 1 and model.run(["canonical", ten_ethanes]) == ("", search_gives_up, 1)
          and with_another_limit(1260, ten_ethanes) == (ten_ethanes + "\n", "", 0) and with_another_limit(1259, ten_ethanes) == ("", search_gives_up, 1),
          f"{counts[1]}")
    check("3.2", "going round the ring of C1CCCCC1 the search holds up to 12 beginnings, and one when the ring is closed",
          "up to 12 beginnings" in words and counts[2] == [6, 12, 12, 12, 6, 1], f"{counts[2]}")

# Section 3.2: three examples that decide what the words leave open.
kinds, tail = "C=1=[C](=[C])[C]1", "[N][N][N]1[N][N][N][N]1"
six, five = "CC.CC.CC.CC.CC.CC.C[C@H](N)O", "CC.CC.CC.CC.CC.C[C@H](N)O"
if quoted(kinds, "[C]1=C=[C]1=[C]", tail, six):
    mol = reads(kinds)
    keys = {order: check_canonical.key_of(mol, list(order)) for order in itertools.permutations(range(len(mol.atoms)))}
    least_mols = {test_cases.renumbered(mol, list(order)) for order, key in keys.items() if key == min(keys.values())}
    right = test_cases.renumbered(mol, rounds_of_the_search(mol)[2])
    wrong = test_cases.renumbered(mol, rounds_of_the_search(mol, kinds_of_bonds=False)[2])
    check("3.2", f"the kind of bond counts for beginnings that are alike: for {kinds} the search of the section ends with the least key of "
                 "all numberings, and a search that does not look at the kinds of the bonds ends with another Mol; canonical writes "
                 "[C]1=C=[C]1=[C], which is read as the Mol with the least key",
          len(least_mols) == 1 and right in least_mols and wrong not in least_mols
          and model.run(["canonical", kinds]) == ("[C]1=C=[C]1=[C]\n", "", 0) and reads("[C]1=C=[C]1=[C]") in least_mols)
    least_ones, held, _ = rounds_of_the_search(reads(tail))
    check("3.2", f"the beginnings are counted after those that are alike are taken out: for {tail}, by the words of the section, 18 "
                 "beginnings have the least key after four rounds and 17 are held, and no round holds more; the search gives a chosen "
                 "text when it may hold 17, and gives up when it may hold 16",
          "18 beginnings" in words and "search holds 17" in words and least_ones == [7, 14, 16, 18, 9, 1, 1]
          and held == [7, 14, 16, 17, 5, 1, 1] and with_another_limit(17, tail)[1:] == ("", 0)
          and with_another_limit(16, tail) == ("", search_gives_up, 1), f"{least_ones} {held}")
    held_six, held_five = rounds_of_the_search(reads(six))[1], rounds_of_the_search(reads(five))[1]
    check("3.2", "six molecules of ethane beside a molecule with a stereo fact: by the words of the section 360 beginnings after four of "
                 "them and 1,080 in the next round, so the search gives up; with five molecules of ethane it holds 240 at most and "
                 "gives a chosen text, also when it may hold 240 and no more",
          "which is 360" in words and "makes 1,080" in words and "240 beginnings at most" in words
          and held_six[7] == 360 and held_six[8] == 1080 and max(held_six[:8]) <= 1000
          and model.run(["canonical", six]) == ("", search_gives_up, 1) and with_another_limit(1079, six) == ("", search_gives_up, 1)
          and max(held_five) == 240 and model.run(["canonical", five])[1:] == ("", 0)
          and with_another_limit(240, five)[1:] == ("", 0) and with_another_limit(239, five) == ("", search_gives_up, 1),
          f"{held_six} {held_five}")

# Section 3.2: the chosen form can need more ring numbers than the text that was read.
two_rails = test_cases.LADDER_OF_TWO_RAILS
two_rails_recipe = "`C1NN2C1`, then `C1N2N2C1` written 49 times, then `C1N2NC1`"
too_many = "error: more than 99 ring numbers are needed at the same time\n"
check("3.2", "the ladder of two rails is the text that section 3.2 describes: rewrite and plain write it, and canonical answers with the writer's error",
      two_rails_recipe in words and two_rails == "C1NN2C1" + "C1N2N2C1" * 49 + "C1N2NC1" and len(two_rails) == 406
      and len(reads(two_rails).atoms) == 204 and model.run(["rewrite", two_rails])[2] == 0 and model.run(["plain", two_rails])[2] == 0
      and model.run(["canonical", two_rails]) == ("", too_many, 1))

# Section 2: white space is a space, a tab or a line break. Only the space can be shown in SPEC.md.
check("2, 6", "a space, a tab, a line feed and a carriage return each give \"white space is not allowed\"",
      all(error_of("C" + character + "C") == (1, "white space is not allowed") for character in " \t\n\r"),
      str([error_of("C" + character + "C") for character in " \t\n\r"]))

# Section 9.4: 99 ring numbers are written, with the smallest free number each time.
star_99 = "C" + "(C)" * 99 + "C"
by_hand = ("[C]" + "".join("-" + test_cases.ring_number(n) for n in range(1, 100)) + "-[CH3]"
           + "".join(".[CH3]" + test_cases.ring_number(n) for n in range(1, 100)) + "\n")
check("9.4", "with (C) written 99 times, plain writes the text and uses every ring number from 1 to 99, the smallest free one each time",
      "written 99 times `plain` writes the text as well" in SPEC and model.run(["plain", star_99]) == (by_hand, "", 0),
      repr(model.run(["plain", star_99]))[:200])

# Section 9.4: "needed" means needed by the two spellings. A ladder of 100 rings is read and then refused.
# The text is the test text `test_cases.LADDER`, and SPEC.md must give the recipe for exactly that text.
ladder = test_cases.LADDER
recipe = "`C(` written 100 times, then `CC1`, then `)C11` written 99 times, then `)C1`"
as_the_recipe_says = "C(" * 100 + "CC1" + ")C11" * 99 + ")C1"
open_now, most_open = set(), 0          # the ring numbers that are open, and the most that were open at once
for character in ladder:
    if character in open_now:
        open_now.remove(character)      # a ring number that is written a second time closes
    elif character.isdigit():
        open_now.add(character)
        most_open = max(most_open, len(open_now))


def refusal(writer, mol):
    try:
        writer(mol)
    except model.WriteError as e:
        return str(e)
    return None


ladder_mol = reads(ladder)
refusals = None if ladder_mol is None else (refusal(model.write, ladder_mol), refusal(model.write_plain, ladder_mol))
check("9.4", "a ladder of 100 rings, round brackets 100 deep, one ring number open at a time: SPEC.md gives its recipe, it is read, and both spellings refuse its Mol",
      recipe in words and ladder == as_the_recipe_says and len(ladder) == 602 and most_open == 1
      and ladder_mol is not None and len(ladder_mol.atoms) == 202 and len(ladder_mol.bonds) == 301
      and refusals == ("more than 99 ring numbers are needed at the same time",) * 2,
      f"{len(ladder)} characters; {most_open} open at once; read: {ladder_mol is not None}; rewrite and plain: {refusals}")

# Section 9.4: the order in which the writer asks, on Mols with two faults (test_cases.HAND_MADE_MOLS).
two_faults = {name: mol for name, mol, _ in test_cases.HAND_MADE_MOLS}
not_formed = two_faults["not well formed, and an atom with 10 hydrogens: that it is not well formed is said"]
ten = two_faults["atom 0 is bonded to the atoms 2 to 101, and atom 101 has 10 hydrogens: the message about the atom comes, "
                 "although the ring numbers run out at atom 0"]
ethanes = two_faults["ten molecules of ethane, as in CC.CC.CC.CC.CC.CC.CC.CC.CC.CC, with the bonds in the reverse order: not "
                     "well formed, which `canonical` says before it searches"]
in_order = two_faults["ten molecules of ethane with the bonds in order: well formed, and the search gives up"]
answers = [refusal(writer, mol) for mol in (not_formed, ten) for writer in (model.write, model.write_plain)]
answers += [refusal(model.write_chosen, ethanes), refusal(model.write_chosen, in_order)]
check("9.4, 3.2", "the writer asks first whether the Mol is well formed, then its atoms, then the ring numbers; canonical asks 'well formed' "
                  "before it searches: ten molecules of ethane with their bonds in the reverse order get that answer, and in order the search gives up",
      answers == ["the Mol is not well formed"] * 2 + ["an atom has more than 9 hydrogens, or a charge beyond +99 or -99"] * 2
      + ["the Mol is not well formed", "the chosen form is not worked out: too many numberings of this molecule look alike"], str(answers))
answers = [refusal(writer, two_faults[name]) for name in ("a hydrogen atom with 10 hydrogens",
                                                          "an atom with 10 hydrogens behind a hydrogen atom with hydrogens",
                                                          "a hydrogen atom with hydrogens behind an atom with 10 hydrogens")
           for writer in (model.write, model.write_plain)]
check("9.4", "of the two reasons about one atom the one about hydrogens and charge is given, and of two atoms that cannot be written the first",
      answers == ["an atom has more than 9 hydrogens, or a charge beyond +99 or -99"] * 2 + ["a hydrogen atom has hydrogens of its own"] * 2
      + ["an atom has more than 9 hydrogens, or a charge beyond +99 or -99"] * 2, str(answers))
thousand_and_one = model.Mol(tuple([model.Atom("C", None, 0, 0)] * 1001), (model.Bond(1, 0, "single"),))
check("3.2", "canonical asks whether the Mol is well formed before it counts the atoms: a Mol of 1,001 atoms with a bond the wrong way round",
      refusal(model.write_chosen, thousand_and_one) == "the Mol is not well formed", str(refusal(model.write_chosen, thousand_and_one)))

# Section 12: stereo marks.
def facts(mol):
    """The stereo facts of a Mol as two dictionaries: the orientation of every atom that has one, and the
    geometry of every double bond that has one."""
    return ({x.atom: x.orientation for x in mol.orientations}, {(g.a, g.b): g.geometry for g in mol.geometries})


def stored(text):
    """The stereo facts that the model stores for a text, in that form."""
    return facts(reads(text))


def record(text):
    """Open Babel's own record of the stereo facts of a text, in the same form (check_stereo.py)."""
    return check_stereo.openbabel_record(text, len(reads(text).atoms))


def rdkit_inchi(text):
    return Chem.MolToInchi(Chem.MolFromSmiles(text))


def openbabel_inchi(text):
    from openbabel import openbabel
    conversion, m = openbabel.OBConversion(), openbabel.OBMol()
    conversion.SetInAndOutFormats("smi", "inchi")
    conversion.ReadString(m, text)
    return conversion.WriteString(m).strip()


canon = others.rdkit_canonical
alanine = "N[C@@H](C)C(=O)O"
if quoted(alanine, "F/C=C/F"):
    m = reads(alanine)
    said = [model.orientation_of(m, model.neighbours_of(m), 1, places) for places in ([None, 0, 2, 3], [0, None, 2, 3], [0, 2, 3])]
    check("12.1", "alanine: atom 1 is stored as anticlockwise; for the order in which the text writes its places the first "
                  "statement says clockwise, and for three places it says nothing",
          m.orientations == (model.AtomOrientation(1, "anticlockwise"),) and said == ["anticlockwise", "clockwise", None],
          f"{m.orientations} {said}")
    m = reads("F/C=C/F")
    nb = model.neighbours_of(m)
    said = [model.geometry_of(m, nb, 1, 2, 0, 3), model.geometry_of(m, nb, 2, 1, 3, 0), model.geometry_of(m, nb, 1, 2, 3, 0)]
    check("12.1", "F/C=C/F: the second statement says oppositeSides for the two fluorine atoms, with the two atoms of the double "
                  "bond in either order, and nothing for an atom that is no such neighbour",
          said == ["oppositeSides", "oppositeSides", None], str(said))
if quoted("F/C=C/F", "F/C=C/1.F1", "F/C=C1.F\\1", "C/1=C/C=C\\C=C/C=C\\1", "C/1CC=1", "C/", "F\\\\C=C/F"):
    check("12.2", "F/C=C/F, F/C=C/1.F1 and F/C=C1.F\\1 say the same",
          reads("F/C=C/F") == reads("F/C=C/1.F1") == reads("F/C=C1.F\\1") is not None)
    cot = reads("C/1=C/C=C\\C=C/C=C\\1")
    check("12.2", "cyclooctatetraene as OpenSMILES spells it is read, with four double bonds of the same geometry",
          cot is not None and [g.geometry for g in cot.geometries] == ["sameSide"] * 4
          and "C/1=C/C=C\\C=C/C=C\\1" in standard)
    for text, expected in [("C/1CC=1", (6, "the two ends of ring 1 name different bonds")),
                           ("C/", (1, "the text ends after a bond symbol")),
                           ("F\\\\C=C/F", (2, "an atom or a ring number is expected here"))]:
        check("12.2", f"{text!r} gives \"{expected[1]}\" at position {expected[0]}", error_of(text) == expected,
              f"the model gives {error_of(text)}")
# Rule 8: a ring bond with a mark at both ends. SPEC.md says it in a sentence and quotes no text for it.
two_marks = {"C/1CC\\1": (1, "this mark has no partner on the other side of a double bond"),
             "F/C=C/1/F.C\\1": (7, "these marks contradict each other")}
check("12.2", "a ring bond with a mark at both ends: a message names the position of the mark at the number that opens "
              "the ring (C/1CC\\1 at 1; F/C=C/1/F.C\\1 at 7, the later of the marks at 5 and 7, not at 11)",
      "the mark at the number that opens the ring is the one whose position a message names" in words
      and all(error_of(text) == expected for text, expected in two_marks.items()),
      f"the model gives {[error_of(text) for text in two_marks]}")

# Section 12.2, rule 9: an atom with a free place. Where the program reads it, Open Babel's own record and
# RDKit agree with it.
free_place = ["C[S@](=O)CC", "C[S@+](CC)CCC", "CC1CCC2CC[S@+]12", "O=[S@]1CC[C@H](C)C1"]
if quoted(*free_place, "[S@](C)(=O)CC"):
    check("12.2", "an atom with a free place is read where no ring number stands at it, or two, or where it has a double bond: at "
                  "every atom of the four texts the model stores the orientation of Open Babel's own record",
          all(reads(t) is not None and stored(t)[0] and record(t) == stored(t) for t in free_place),
          str([(t, stored(t), record(t)) for t in free_place if reads(t) is None or record(t) != stored(t)][:2]))
    inchis = [(t, rdkit_inchi(t), openbabel_inchi(t)) for t in free_place]
    check("12.2", "RDKit and Open Babel read the same molecule from each of these four texts",
          all(theirs.startswith("InChI=") and theirs == other for _, theirs, other in inchis),
          str([entry for entry in inchis if entry[1] != entry[2]]))
    from openbabel import pybel
    ob_canon = lambda t: pybel.readstring("smi", t).write("can").split()[0]
    check("12.2", "[S@](C)(=O)CC: RDKit reads it as C[S@](=O)CC, Open Babel as the mirror image of that",
          canon("[S@](C)(=O)CC") == canon("C[S@](=O)CC") and ob_canon("[S@](C)(=O)CC") == ob_canon("C[S@@](=O)CC")
          and ob_canon("C[S@](=O)CC") != ob_canon("C[S@@](=O)CC"))

# Sections 12.2 (rule 9) and 12.4: an atom with a free place at which exactly one ring number is written
# and whose bonds are all single. RDKit and Open Babel read mirror images there, and the program refuses
# the text.
mirror = {"C[N@]1C[C@H]1C": "C[N@@]1C[C@H]1C", "C[S@+]1CC[C@H](C)C1": "C[S@@+]1CC[C@H](C)C1"}
if quoted(*mirror, *mirror.values(), "C[N@]1CC1C", "C[S@+]1CCCC1"):
    four = list(mirror) + list(mirror.values())
    by_rdkit = {t: rdkit_inchi(t) for t in four}
    by_openbabel = {t: openbabel_inchi(t) for t in four}
    check("12.4", "RDKit and Open Babel both give an InChI for each of the two texts and for the two with the other mark, so that "
                  "no comparison below is one of two empty answers",
          all(answer.startswith("InChI=") for answer in list(by_rdkit.values()) + list(by_openbabel.values())),
          str([t for t in four if not (by_rdkit[t].startswith("InChI=") and by_openbabel[t].startswith("InChI="))]))
    check("12.4", "one ring number at an atom with a free place and single bonds: RDKit and Open Babel read mirror images of each other at that atom "
                  "(each reads what the other reads from the text with the other mark there)",
          all(by_rdkit[t] != by_openbabel[t] and by_rdkit[t] == by_openbabel[other] and by_openbabel[t] == by_rdkit[other]
              for t, other in mirror.items()),
          str([(t, by_rdkit[t], by_openbabel[t], by_openbabel[other]) for t, other in mirror.items()]))
    refused = four + ["C[N@]1CC1C", "C[S@+]1CCCC1"]
    check("12.2", "the program reads none of these six texts: each gets the second message of rule 9, at its atom with the free place",
          f"`{model.FREE_PLACE_AND_ONE_RING_NUMBER}`" in SPEC
          and all(error_of(t) == (3, model.FREE_PLACE_AND_ONE_RING_NUMBER) for t in refused),
          str([(t, error_of(t)) for t in refused]))

# Section 12.3: writing.
if quoted("C[C@H](F)/C=C/Cl", "[CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl]", "F\\C=C\\F", "F/C=C/F", "F/C(/F)=C/F", "F/C(F)=C/F",
          "C[S@+](CC)CCC"):
    m = reads("C[C@H](F)/C=C/Cl")
    check("12.3", "C[C@H](F)/C=C/Cl is written the same with round brackets, and [CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl] in the plain "
                  "spelling, which is read as the same Mol",
          model.write(m) == "C[C@H](F)/C=C/Cl" and model.write_plain(m) == "[CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl]"
          and reads("[CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl]") == m)
    check("12.3", "a text need not come back with the marks it had: F\\C=C\\F comes back as F/C=C/F, and F/C(/F)=C/F as F/C(F)=C/F, "
                  "each as the same Mol",
          model.run(["rewrite", "F\\C=C\\F"]) == ("F/C=C/F\n", "", 0) and model.run(["rewrite", "F/C(/F)=C/F"]) == ("F/C(F)=C/F\n", "", 0)
          and reads("F\\C=C\\F") == reads("F/C=C/F") and reads("F/C(/F)=C/F") == reads("F/C(F)=C/F"),
          f"{model.run(['rewrite', 'F' + chr(92) + 'C=C' + chr(92) + 'F'])} {model.run(['rewrite', 'F/C(/F)=C/F'])}")
    five_messages = ["a stereo centre with a free place would be written without an atom before it",
                     "a stereo centre with a free place would be written with one ring number and only single bonds",
                     "at one atom of a double bond with a geometry, no bond can carry a mark",
                     "the marks would give a geometry to a double bond that has none",
                     "no choice of marks gives every geometry"]
    check("12.3", "C[S@+](CC)CCC is read, rewrite writes it back, and plain answers with the second message of the list",
          model.run(["rewrite", "C[S@+](CC)CCC"]) == ("C[S@+](CC)CCC\n", "", 0)
          and model.run(["plain", "C[S@+](CC)CCC"]) == ("", f"error: {five_messages[1]}\n", 1), str(model.run(["plain", "C[S@+](CC)CCC"])))
    given = {refusal(writer, mol) for _, mol, _ in test_cases.HAND_MADE_MOLS for writer in (model.write, model.write_plain)}
    ring = reads("C/1=C/C=C\\C=C/C=C\\1")
    turned = model.Mol(ring.atoms, ring.bonds, (), (model.BondGeometry(0, 1, "oppositeSides"),) + ring.geometries[1:])
    check("12.3", "the ring of C/1=C/C=C\\C=C/C=C\\1 with the geometry of its first double bond turned round is well formed, is "
                  "one of the Mols that test_cases.py writes out by hand, and both spellings refuse it with the fifth message",
          model.is_well_formed(turned) and any(mol == turned for _, mol, _ in test_cases.HAND_MADE_MOLS)
          and [refusal(model.write, turned), refusal(model.write_plain, turned)] == [five_messages[4]] * 2,
          str([refusal(model.write, turned), refusal(model.write_plain, turned)]))
    check("12.3", "each of the five messages for a Mol with stereo facts stands in SPEC.md, and the model gives it for one of the "
                  "Mols that test_cases.py writes out by hand",
          all(f"`{message}`" in SPEC for message in five_messages) and all(message in given for message in five_messages),
          f"not in SPEC.md: {[m for m in five_messages if f'`{m}`' not in SPEC]}; given for no hand-made Mol: {[m for m in five_messages if m not in given]}")

# Sections 6 and 12.2: which problems with stereo marks are looked for last, and the order of the ring messages.
if quoted("F[C@H2]Cl)", "C1.[S@]1(C)=O", "C/1C/1"):
    for text, expected in [("F[C@H2]Cl)", (9, "')' has no matching '('")),
                           ("C1.[S@]1(C)=O", (5, "a stereo centre with a free place needs an atom before it")),
                           ("C/1C/1", (5, "the two ends of ring 1 name different directions"))]:
        check("6, 12.2", f"{text!r} gives \"{expected[1]}\" at position {expected[0]}", error_of(text) == expected,
              f"the model gives {error_of(text)}")

# Section 12.3: the third and the fourth refusal can come for a Mol that the reader returned.
if quoted("c1ccccc1/C(:F)=C/F", "F/C=C(/c1ccccc1):C=C/C=C/F"):
    answers = [refusal(writer, reads(text)) for text in ("c1ccccc1/C(:F)=C/F", "F/C=C(/c1ccccc1):C=C/C=C/F")
               for writer in (model.write, model.write_plain)]
    check("12.3", "c1ccccc1/C(:F)=C/F is read and both spellings refuse it with the third message; "
                  "F/C=C(/c1ccccc1):C=C/C=C/F is read and both refuse it with the fourth; no real text has the symbol ':'",
          answers == ["at one atom of a double bond with a geometry, no bond can carry a mark"] * 2
          + ["the marks would give a geometry to a double bond that has none"] * 2
          and no_real_text_has_a_colon, str(answers))

# Section 12.3: the fifth refusal can come for a Mol that the reader returned as well, where the text marks
# other bonds than the writer chooses. The same ring with marks that say the same side at both double bonds
# is written: it is the two geometries together that the bonds which the writer marks cannot say.
if quoted("F/C1=C(/F)C(/F)=C1/F"):
    ring = reads("F/C1=C(/F)C(/F)=C1/F")
    answers = [refusal(writer, ring) for writer in (model.write, model.write_plain, model.write_chosen)]
    check("12.3", "F/C1=C(/F)C(/F)=C1/F is read with a geometry at each of its two double bonds, and both spellings and "
                  "canonical refuse its Mol with the fifth message; with marks that say the same side twice, the ring is written",
          ring is not None and [(g.a, g.b, g.geometry) for g in ring.geometries] == [(1, 2, "oppositeSides"), (4, 6, "sameSide")]
          and answers == ["no choice of marks gives every geometry"] * 3
          and model.run(["rewrite", "F/C1=C(\\F)C(/F)=C1/F"]) == ("F/C/1=C(\\F)/C(F)=C1F\n", "", 0), str(answers))

# Sections 4.1 and 12.4: the short form of OpenSMILES at an atom with five or six neighbours.
if quoted("C[Co@](F)(Cl)(Br)(I)S"):
    check("12.4", "C[Co@](F)(Cl)(Br)(I)S is an example of the OpenSMILES text, and the program answers that this atom cannot be a stereo centre",
          "C[Co@](F)(Cl)(Br)(I)S" in standard and error_of("C[Co@](F)(Cl)(Br)(I)S") == (4, "this atom cannot be a stereo centre"),
          str(error_of("C[Co@](F)(Cl)(Br)(I)S")))

# Section 12.4: what is not covered, and the known differences from RDKit.
if quoted("Br[C@H](Br)C", "Br[C@@H](Br)C", "F/C(/F)=C/F", "CC(Br)Br", "C[C@@H](Br)Br"):
    two = [model.run(["canonical", t]) for t in ("Br[C@H](Br)C", "Br[C@@H](Br)C")]
    exchanged = model.arrange(reads("Br[C@H](Br)C"), [2, 1, 0, 3])
    check("12.4", "Br[C@H](Br)C and F/C(/F)=C/F are stored as written; Br[C@H](Br)C and Br[C@@H](Br)C are two Mols, exchanging the "
                  "two bromine atoms turns the one into the other, and canonical gives both the text C[C@@H](Br)Br",
          bool(reads("Br[C@H](Br)C").orientations) and bool(reads("F/C(/F)=C/F").geometries)
          and reads("Br[C@H](Br)C") != reads("Br[C@@H](Br)C") and exchanged == reads("Br[C@@H](Br)C")
          and two == [("C[C@@H](Br)Br\n", "", 0)] * 2, f"{two}; exchanged: {exchanged}")
    check("12.4", "RDKit's writer leaves out a mark that tells nothing apart, which is the usual convention: it writes Br[C@H](Br)C as CC(Br)Br",
          canon("Br[C@H](Br)C") == "CC(Br)Br", str(canon("Br[C@H](Br)C")))
# Each entry: the texts of a row, those of them that the program must refuse, and what RDKit does.
differences = [
    (("C/C", "C/C=CC", "F/C=C=C=C/F"), ("C/C", "C/C=CC", "F/C=C=C=C/F"),
     lambda: all(not re.search(r"[/\\]", canon(t)) for t in ("C/C", "C/C=CC", "F/C=C=C=C/F"))),
    (("C/C(\\F)=C/F",), ("C/C(\\F)=C/F",), lambda: not re.search(r"[/\\]", canon("C/C(\\F)=C/F"))),
    (("F/C=C/1.F/1", "F/C=C\\F"), ("F/C=C/1.F/1",), lambda: canon("F/C=C/1.F/1") == canon("F/C=C\\F")),
    (("C/1CC=1", "C1=CC1"), ("C/1CC=1",), lambda: canon("C/1CC=1") == canon("C1=CC1")),
    (("F[C@H2]Cl",), ("F[C@H2]Cl",), lambda: "@" not in canon("F[C@H2]Cl")),
    (("C[C@TH1](F)(Cl)Br", "C[C@](F)(Cl)Br"), ("C[C@TH1](F)(Cl)Br",), lambda: canon("C[C@TH1](F)(Cl)Br") == canon("C[C@](F)(Cl)Br")),
    (("F\\\\C=C/F",), ("F\\\\C=C/F",), lambda: canon("F\\\\C=C/F") is not None),
    (("[S@](C)(=O)CC", "C[S@](=O)CC"), ("[S@](C)(=O)CC",), lambda: canon("[S@](C)(=O)CC") == canon("C[S@](=O)CC")),
    (("C[N@]1CC1C", "C[S@+]1CCCC1"), ("C[N@]1CC1C", "C[S@+]1CCCC1"),
     lambda: canon("C[N@]1CC1C") is not None and canon("C[S@+]1CCCC1") is not None),
]
for texts, refused, rdkit in differences:
    if quoted(*texts):
        check("12.4", f"known difference {', '.join(refused)}: this program answers with an error", all(reads(t) is None for t in refused))
        check("12.4", f"known difference {', '.join(refused)}: RDKit as the table says", rdkit())
in_table = set()
for line in part("### 12.4", "## 13.").splitlines():
    if line.startswith("| `"):
        in_table |= set(re.findall(r"`([^`]*)`", line.strip("|").split("|")[0]))
check("12.4", "every text in the table of known differences has a check here",
      in_table and in_table <= {t for _, refused, _ in differences for t in refused},
      f"without a check: {sorted(in_table - {t for _, refused, _ in differences for t in refused})}")

# Theorems 36 to 38 of CLAIMS.md and the first statement of theorem 39: single examples that are theorems
# of VeriMol/Proofs/Read.lean. Each of them but theorem 37 writes out the Mol that the reader must give,
# by hand; theorem 37 says of two pairs of texts that they are read alike. Here RDKit and Open Babel are
# asked for the same texts: for the atoms and the bonds both of them, and for the stereo facts of theorem
# 38 Open Babel's own record. Nothing of the model's reader is used.
PROOFS = (Path(__file__).resolve().parent.parent / "VeriMol" / "Proofs" / "Read.lean").read_text()


def written_by_hand(lean):
    """A Mol as a Lean file writes it out, as a Mol of the model."""
    atoms = tuple(model.Atom(element, None if isotope == "none" else int(number), int(charge), int(hydrogens))
                  for element, isotope, number, charge, hydrogens in others.PRINTED_ATOM.findall(lean))
    bonds = tuple(model.Bond(int(a), int(b), order) for a, b, order in others.PRINTED_BOND.findall(lean))
    orientations = tuple(model.AtomOrientation(int(atom), orientation)
                         for atom, orientation in re.findall(r"\{ atom := (\d+), orientation := \.(\w+) \}", lean))
    geometries = tuple(model.BondGeometry(int(a), int(b), geometry)
                       for a, b, geometry in re.findall(r"\{ a := (\d+), b := (\d+), geometry := \.(\w+) \}", lean))
    return model.Mol(atoms, bonds, orientations, geometries)


mols_by_hand = {text.replace("\\\\", "\\"): written_by_hand(lean) for text, lean in
                re.findall(r'theorem read_\w+ :\s+read "([^"]+)"\.toList = \.ok\s+(\{ atoms := \[.*?\] \}) := by', PROOFS, flags=re.S)}
written_out = ["CC(=O)O", "CC", "C=CC#N", "c1ccccc1", "[Na+].[Cl-]", "[2H]O[2H]", "[NH4+]", "[Mo]$[Mo]"]
with_marks = ["N[C@@H](C)C(=O)O", "F/C=C/F", "F/C=C\\F"]
if quoted(*written_out, *with_marks, "C-C", "CC", "c:1:c:c:c:c:c:1"):
    def read_as_written(t):
        """Whether RDKit and Open Babel both read the text with the atoms and the bonds that the Lean file writes
        out for it."""
        return (t in mols_by_hand and others.without_stereo(mols_by_hand[t]) == others.rdkit_mol(t)
                and others.without_stereo(mols_by_hand[t]) == others.without_stereo(others.openbabel_mol(t)))
    differs = [t for t in written_out + with_marks if not read_as_written(t)]
    check("10", f"theorems 36, 38 and 39: the atoms and the bonds that VeriMol/Proofs/Read.lean writes out by hand for each of "
                f"{len(written_out) + len(with_marks)} texts are what RDKit and Open Babel read",
          set(mols_by_hand) == set(written_out + with_marks) and not differs,
          f"written out in VeriMol/Proofs/Read.lean: {sorted(mols_by_hand)}; differs for: {differs}")
    check("10", "theorems 36 and 39: the Mols of the eight texts without stereo marks are written out without stereo facts",
          all(t in mols_by_hand and not mols_by_hand[t].orientations and not mols_by_hand[t].geometries for t in written_out))
    differs = [t for t in with_marks if t not in mols_by_hand or facts(mols_by_hand[t]) != check_stereo.openbabel_record(t, len(mols_by_hand[t].atoms))]
    check("10", "theorem 38: the stereo facts that VeriMol/Proofs/Read.lean writes out by hand for its three texts are those of Open Babel's "
                "own record: anticlockwise at atom 1 of alanine, oppositeSides and sameSide for the two difluoroethenes",
          not differs and [facts(mols_by_hand[t]) for t in with_marks if t in mols_by_hand]
          == [({1: "anticlockwise"}, {}), ({}, {(1, 2): "oppositeSides"}), ({}, {(1, 2): "sameSide"})],
          f"differs for: {differs}")
    same = [("C-C", "CC"), ("c:1:c:c:c:c:c:1", "c1ccccc1")]
    check("10", "theorem 37: RDKit and Open Babel read C-C as the Mol of CC, and c:1:c:c:c:c:c:1 as the Mol of c1ccccc1",
          all(reader(a) is not None and reader(a) == reader(b)
              for a, b in same for reader in (others.rdkit_mol, others.openbabel_mol)))

# Section 3.1 and theorem 43: two texts for L-alanine are the same molecule, and the text of its mirror image
# is not. Lean proves it. Here RDKit is asked, with its clean-up on, which knows nothing of the definition.
if quoted("N[C@@H](C)C(=O)O", "C[C@H](N)C(=O)O", "N[C@H](C)C(=O)O"):
    from_nitrogen, from_carbon, mirrored = (canon(t) for t in ("N[C@@H](C)C(=O)O", "C[C@H](N)C(=O)O", "N[C@H](C)C(=O)O"))
    check("3.1", "N[C@@H](C)C(=O)O and C[C@H](N)C(=O)O are read as two different Mols, and RDKit takes them for one molecule; "
                 "N[C@H](C)C(=O)O it takes for another",
          reads("N[C@@H](C)C(=O)O") != reads("C[C@H](N)C(=O)O") and from_nitrogen is not None and from_nitrogen == from_carbon
          and mirrored is not None and mirrored != from_nitrogen, f"{from_nitrogen} {from_carbon} {mirrored}")

# ------------------------------------------------------------------------------------------ the filter (16)
filter_part = part("## 16. The filter", "### 16.4 What the filter does not say")


def filter_of(text, number="1"):
    """What the model's filter answers for a text behind a number: None if the Mol is handed on, or the
    message."""
    stdout, stderr, code = model.run(["filter", "perfluoro", number, text])
    return None if code == 0 else stderr[len("error: "):-1]


# The commands of the block at the head of section 16, read out of SPEC.md: each line that begins with `$`
# and the lines that follow it must be what the model prints for those arguments.
block = re.search(r"```\n(\$ app filter.*?)```", filter_part, re.S).group(1)
commands = [(lines.split("\n")[0], "\n".join(lines.split("\n")[1:])) for lines in block.split("$ app ")[1:]]
for command, shown in commands:
    stdout, stderr, code = model.run(shlex.split(command))
    check("16", f"the model prints what SPEC.md shows for: app {command[:60]}", (stdout if code == 0 else stderr) == shown,
          f"the model: {(stdout if code == 0 else stderr)!r}; SPEC.md: {shown!r}")
check("16", "the block at the head of section 16 has three commands: one Mol that passes, one refused by the rule, one not sound",
      len(commands) == 3 and [model.run(shlex.split(c))[2] for c, _ in commands] == [0, 1, 1])

# Section 16.1: which arguments are a number.
if quoted("6", "12", "006", "0", "00", "+6", "6.0"):
    check("16.1", "6, 12 and 006 are numbers of the filter, and 0, 00, +6, 6.0 and an argument without a character are not",
          [model.group_size(t) for t in ("6", "12", "006", "0", "00", "+6", "6.0", "")] == [6, 12, 6, None, None, None, None, None])
check("16.1", "the filter prints for a text exactly what the program prints for the text alone, or an error",
      all(model.run(["filter", "perfluoro", "6", t]) == model.run([t]) or model.run(["filter", "perfluoro", "6", t])[2] == 1
          for t in test_cases.SPEC_TEXTS + test_cases.FILTER_TEXTS))
check("16.1", "a text that is not read gets the reader's error behind the filter",
      all(model.run(["filter", "perfluoro", "6", t]) == model.run([t]) for t in ("C1CC", "C C", "[Xx]", "C(")))

# Section 16.2: the table of messages, read out of SPEC.md. Each message stands there for atom 3; the
# model must give it, with the number of its atom, for a text that fails that test and no earlier one.
table = dict(re.findall(r"^\| (the `Mol` is not well formed|test \d) \| `([^`]+)` \|$", filter_part, re.M))
failing = {"test 1": "CCC[Si]", "test 2": "CCC[13CH3]", "test 3": "CCC[O-]", "test 4": "CCCC:C", "test 5": "CCC[CH3]C"}
check("16.2", "the table of messages has a row for a Mol that is not well formed and a row for each of the five tests",
      sorted(table) == ["test 1", "test 2", "test 3", "test 4", "test 5", "the `Mol` is not well formed"])
for row, text in failing.items():
    check("16.2", f"{row}: the message of the table is what the model gives for {text}, whose atom 3 fails that test first",
          row in table and filter_of(text) == table[row], f"the model: {filter_of(text)!r}; the table: {table.get(row)!r}")
not_well_formed = model.Mol((model.Atom("C", None, 0, 4), model.Atom("C", None, 0, 4)), (model.Bond(1, 0, "single"),))
check("16.2", "a Mol that is not well formed gets the first message of the table, whatever its atoms are",
      model.sound_problem(not_well_formed) == table.get("the `Mol` is not well formed") == "the Mol is not well formed")
# The examples of section 16.2, written out here.
sound = ["c1ccccc1", "C1=CC=CC=C1", "c1ccncc1", "c1cc[nH]c1", "c1ccoc1", "N[C@@H](C)C(=O)O", "[CH4]", "CN(=O)=O", "C1CC1.C1CC1",
         "c1cccc1", "CN(C)(C)(C)C"]
not_sound = [("C[N+](=O)[O-]", "atom 1 has a charge"),
             ("[Na+].[Cl-]", "atom 0 is no atom of B, C, N, O, P, S, F, Cl, Br or I"),
             ("[13CH4]", "atom 0 has a mass number"),
             ("[H]C([H])([H])[H]", "atom 0 is no atom of B, C, N, O, P, S, F, Cl, Br or I"),
             ("C:C", "atom 0 has exactly one aromatic bond"), ("FC(F)(F):c1ccccc1", "atom 1 has exactly one aromatic bond"),
             ("CC(F)(F)(F)F", "the bonds and hydrogens of atom 1 add up to no usual valence of its element"),
             ("[CH3]", "the bonds and hydrogens of atom 0 add up to no usual valence of its element")]
if quoted(*sound, *[text for text, _ in not_sound]):
    wrong = [t for t in sound if model.sound_problem(reads(t)) is not None]
    check("16.2", f"the {len(sound)} examples that SPEC.md calls sound are sound", not wrong, f"not sound: {wrong}")
    wrong = [(t, model.sound_problem(reads(t))) for t, why in not_sound if model.sound_problem(reads(t)) != "the Mol is not sound: " + why]
    check("16.2", f"the {len(not_sound)} examples that SPEC.md calls not sound fail the test that it names, at the atom that it names",
          not wrong, f"otherwise: {wrong}")
    check("16.2", "[CH4] is the Mol of C", reads("[CH4]") == reads("C"))
    refused = [t for t in sound if Chem.MolFromSmiles(t) is None]
    check("16.2", "RDKit, with its clean-up on, reads every example that SPEC.md calls sound, apart from the two of which "
                  "SPEC.md says that the five tests do not notice them: c1cccc1, a ring that no single and double bonds "
                  "in turn give, and CN(C)(C)(C)C, a nitrogen atom with five single bonds",
          refused == ["c1cccc1", "CN(C)(C)(C)C"], f"RDKit refuses: {refused}")
    check("16.2", "RDKit, with its clean-up on, refuses CC(F)(F)(F)F, whose carbon atom has five bonds",
          Chem.MolFromSmiles("CC(F)(F)(F)F") is None)

# Section 16.3: the examples with the sizes of their largest groups, read out of SPEC.md. Each stands as
# `text`, some words, a colon and the size.
examples = re.findall(r"^- `([^`]+)`[^:`]*: (\d+)", filter_part[filter_part.index("Examples, each with the size"):], re.M)
check("16.3", "section 16.3 gives 21 examples with the size of the largest group", len(examples) == 21, f"found: {len(examples)}")
size_of = lambda t: (0 if filter_of(t) is None else
                     int(re.fullmatch(r"the Mol has a perfluorinated group of size (\d+), and size 1 or more is refused", filter_of(t)).group(1)))
wrong = [(t, size_of(t), int(size)) for t, size in examples if model.sound_problem(reads(t)) is not None or size_of(t) != int(size)]
check("16.3", "each of these examples is sound, and the model gives its largest group the size that SPEC.md gives",
      not wrong, f"otherwise (text, the model, SPEC.md): {wrong}")
theirs = [(t, check_filter.rdkit_size(t), int(size)) for t, size in examples]
check("16.3", "a search written for RDKit finds a largest group of the same size in each of them, also in the one with "
              "lowercase symbols at carbon atoms with four bonds",
      all(found == size for _, found, size in theirs), f"(text, RDKit, SPEC.md): {theirs}")
pfoa, ibuprofen = "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F", "CC(C)Cc1ccc(cc1)C(C)C(=O)O"
if quoted(pfoa, ibuprofen):
    check("16.3", "PFOA is refused with the numbers 1 to 7 and handed on with 8, and the message names the two sizes",
          [filter_of(pfoa, str(n)) is None for n in range(1, 10)] == [False] * 7 + [True] * 2
          and filter_of(pfoa, "6") == "the Mol has a perfluorinated group of size 7, and size 6 or more is refused"
          and f"error: {filter_of(pfoa, '6')}" in filter_part
          and filter_of(pfoa, "007") == "the Mol has a perfluorinated group of size 7, and size 7 or more is refused")
    check("16.3", "ibuprofen has no fluorinated carbon atom, and the filter hands it on for every number",
          all(filter_of(ibuprofen, number) is None for number in ("1", "2", "6", "100")))
CUBE = "FC(F)(F)C12C3(C(F)(F)F)C4(C(F)(F)F)C1(C(F)(F)F)C1(C(F)(F)F)C2(C(F)(F)F)C3(C(F)(F)F)C41C(F)(F)F"
if quoted("FC(F)(F)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)F", "FC(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
          "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
          "OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
          "Oc1ccc(cc1)C(c1ccc(O)cc1)(C(F)(F)F)C(F)(F)F", CUBE):
    groups = lambda t: [len(g) for g in model.perfluorinated_groups(reads(t))]
    check("16.3", "the ether has a group of three and a group of two",
          groups("FC(F)(F)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)F") == [3, 2])
    check("16.3", "a branch carbon atom joins the atoms that hold it: the compound with a carbon atom without fluorine "
                  "in the middle is one group of five; the isomer of PFOA with such an atom at its branch is one group "
                  "of seven, and so is the isomer with two of them side by side",
          groups("FC(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F") == [5]
          and groups("OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F") == [7]
          and groups("OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F") == [7])
    check("16.3", "what is no branch carbon atom: the atom between the two -CF3 of bisphenol AF, which leaves two groups "
                  "of one; and the eight atoms of the cube, which would hold each other only, and leave eight groups of one",
          groups("Oc1ccc(cc1)C(c1ccc(O)cc1)(C(F)(F)F)C(F)(F)F") == [1, 1] and groups(CUBE) == [1] * 8)
    if quoted("FC(F)(Cl)C(F)(F)F", "FC(F)(F)C(F)(F)C(F)(F)C(F)(I)C(F)(F)C(F)(F)C(F)(F)F",
              "ClC(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)F", "FC(F)C(F)(F)F"):
        check("16.3", "the fifth condition names hydrogen alone: a carbon atom with a chlorine atom belongs to its group, "
                      "an iodine atom inside a chain does not part it, and a chain with four chlorine atoms is one "
                      "group of six; a carbon atom with a hydrogen belongs to none",
              groups("FC(F)(Cl)C(F)(F)F") == [2]
              and groups("FC(F)(F)C(F)(F)C(F)(F)C(F)(I)C(F)(F)C(F)(F)C(F)(F)F") == [7]
              and groups("ClC(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)F") == [6]
              and groups("FC(F)C(F)(F)F") == [1])
        conditions = lambda t: model.meets_the_five_conditions(reads(t))
        check("16.3", "what meets the five conditions: both carbon atoms of FC(F)(Cl)C(F)(F)F, and of FC(F)C(F)(F)F "
                      "the second only; carbon tetrachloride's atom meets them and is no carbon atom of a group",
              [i for i, yes in enumerate(conditions("FC(F)(Cl)C(F)(F)F")) if yes] == [1, 4]
              and [i for i, yes in enumerate(conditions("FC(F)C(F)(F)F")) if yes] == [3]
              and conditions("ClC(Cl)(Cl)Cl") == [False, True, False, False, False]
              and not any(model.group_carbons(reads("ClC(Cl)(Cl)Cl"))))
    members = lambda t: model.group_carbons(reads(t))
    check("16.3", "the carbon atoms of the groups are the fluorinated carbon atoms and the branch carbon atoms: in the "
                  "isomer of PFOA with two branch carbon atoms, seven atoms, of which five carry fluorine",
          sum(members("OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F")) == 7
          and sum(model.fluorinated_carbons(reads("OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F"))) == 5)

sys.exit(sources.end_of_checks())
