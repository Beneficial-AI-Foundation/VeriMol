"""What the tests of the Lean program are run on.

With one exception, this file does not say what the right answer is: the right answers come from the
model (model.py). check_tests.py works them out and writes them into TestData.lean, where `lake test`
finds them. The exception stands under HAND_MADE_MOLS.

  SPEC_TEXTS       the SMILES texts that SPEC.md quotes: every one that is read, every one that is given
                   with the position of its problem, and some of the others
  MORE_TEXTS       texts written for the tests, for what SPEC.md states in words
  FILTER_TEXTS     the texts among them that are written for the filter (SPEC.md, section 16)
  NCI_TEXTS        100 real SMILES texts
  HAND_MADE_MOLS   Mols that are written out here without a text (several of them no text can give),
                   each with the one answer that this file does give: is it well formed? check_tests.py
                   holds it against the model.
  RENUMBERED_MOLS  the Mols of the real texts, and of texts with stereo marks, with their atoms numbered
                   differently, for the writer
  SYMBOL_PROBES    texts that are tried as element symbols

check_tests.py also checks SPEC_TEXTS, FILTER_TEXTS and NCI_TEXTS against their rules, which are given
below.
"""
import math

from model import ELEMENTS, Atom, AtomOrientation, Bond, BondGeometry, Mol, SmilesError, read

# -------------------------------------------------------------------------------- the texts of SPEC.md
# In five groups, which the comments inside the list name. The rules, which check_tests.py checks:
#   1. Every text in this list stands in SPEC.md between backticks.
#   2. Everything that stands in SPEC.md between backticks and that the model reads as a SMILES text is
#      in this list, whatever SPEC.md quotes it for. (So `b` is here, which SPEC.md quotes as the name
#      of a field, and `SP`, which it quotes as a stereo class: both happen to be SMILES texts.)
#   3. Every example that SPEC.md gives with a position, as in "`C C` (1)", is in this list.
SPEC_TEXTS = [
    # read, without stereo marks
    "C", "Cl", "c", "[NH4+]", "[13CH4]", "[nH]", "b", "[CH4]", "[CH4+0]", "[H]", "[Na+].[Cl-]", "[Co]", "[13C]",
    "[013C]", "C1.C1", "c1ccccc1-c1ccccc1", "CC(=O)O", "c1ccccc1", "c1ccncc1", "[Fe+2]", "[O-]", "CC(C)C",
    "[CH3]-[CH]-1-[CH3].[CH3]1", "[CH3]", "Cl[I]Cl", "ClICl", "[CH3]-[C]-1=[O].[OH]1", "c1ccccc1O",
    "[cH]:1:[cH]:[cH]:[cH]:[cH]:[c]1-[OH]", "C1.CC1", "[0C]", "CN(C)(C)C", "FP(F)(F)(F)(F)F", "CIC", "C:C",
    "C%01CC1", "C(.C)C", "SP", "C=C=C", "C1=CC1",
    "C1=CC=CC=C1", "[H]C([H])([H])[H]", "[1C]", "[cH3][cH3]", "c-c", "[CH2][CH2]", "[NH]", "c1cc[nH]c1",
    "[cH3]:[cH3]", "[CH2]-[CH2]", "F:C", "[F]:[cH3]", "C1CC1", "C2CC2", "[Fe++]",
    "CCO", "OCC", "C1CCCCC1", "C1CC1.C1CC1", "C=CC#N", "[2H]O[2H]", "[Mo]$[Mo]", "C-C", "CC",
    "c:1:c:c:c:c:c:1",
    "C(O)C", "OC(=O)C", "O=C(O)C", "Oc1ccccc1", "c1cc(O)ccc1", "[Cl-].[Na+]", "CC(C)(C)C", "C(C)(C)(C)C",
    "O=C=O", "C(=O)=O", "FC(F)(F)C(F)(F)F", "C(C(F)(F)F)(F)(F)F", "N[Co+3](N)(N)(N)(N)N",
    "OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO", "CC.CC.CC.CC.CC.CC.CC.CC.CC", "CC.CC.CC.CC.CC.CC.CC.CC.CC.CC",
    "C1CCCCC1.N1NNNN1.O1OOOO1", "C=1=[C](=[C])[C]1", "[C]1=C=[C]1=[C]", "[N][N][N]1[N][N][N][N]1",
    "CC(Br)Br",
    # with stereo marks
    "N[C@@H](C)C(=O)O", "C[C@H](N)C(=O)O", "N[C@H](C)C(=O)O", "F/C=C/F", "F/C=C\\F",
    "C[C@@H](C(=O)O)N", "C[C@H](C(=O)O)N", "F\\C=C\\F", "C(\\F)=C/F", "C(=C\\F)/F", "C(=C/F)/F",
    "Br[C@@H](Br)C", "F/C=C/1.F1", "F/C=C1.F\\1", "C/1=C/C=C\\C=C/C=C\\1", "C[S@](=O)CC",
    "C[S@+](CC)CCC", "O=[S@]1CC[C@H](C)C1", "C[C@H](F)/C=C/Cl", "[CH3]-[C@@H]/1-[F].[CH]1=[CH]/[Cl]",
    "Br[C@H](Br)C", "F/C(/F)=C/F", "F/C(F)=C/F", "C[C@@H](Br)Br", "C[C@](F)(Cl)Br", "CC1CCC2CC[S@+]12",
    "c1ccccc1/C(:F)=C/F", "F/C=C(/c1ccccc1):C=C/C=C/F", "F/C1=C(/F)C(/F)=C1/F",
    "C1CCCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O", "C1CCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O",
    "CC.CC.CC.CC.CC.CC.C[C@H](N)O",
    # read: the examples of the filter (section 16) that stand in no group above
    "C[N+](=O)[O-]", "CN(=O)=O", "c1ccoc1", "FC(F)(F):c1ccccc1", "CC(F)(F)(F)F", "c1cccc1",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(C(F)(F)F)C(F)(F)F",
    "OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F", "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "FC1(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C1(F)F", "Fc1(F)c(F)(F)c(F)(F)c(F)(F)c(F)(F)c1(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)F", "FC(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F", "FC(F)C(F)(F)F",
    "FC(F)(Cl)C(F)(F)F", "FC(F)=C(F)C(F)(F)F", "CNCCC(Oc1ccc(cc1)C(F)(F)F)c1ccccc1",
    "CC(C)Cc1ccc(cc1)C(C)C(=O)O",
    "CN(C)(C)(C)C", "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F", "CC(C)(C)F",
    "OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F", "Oc1ccc(cc1)C(c1ccc(O)cc1)(C(F)(F)F)C(F)(F)F",
    "FC(F)(F)C12C3(C(F)(F)F)C4(C(F)(F)F)C1(C(F)(F)F)C1(C(F)(F)F)C2(C(F)(F)F)C3(C(F)(F)F)C41C(F)(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(I)C(F)(F)C(F)(F)C(F)(F)F", "ClC(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)C(F)(F)C(F)(Cl)F",
    # not read: the examples that SPEC.md gives with the position of the problem
    "C C", "*C", "[CH3:1]", "[]", "[13]", "[Xx]", "[te]", "[HH]", "C[NH3", "C%1CC%1", "CX", "H", "CL", "[CH10]",
    "[Fe+++]", "=C", "(C)C", "C..C", "C()C", "C(=)C", "C==C", "C=(C)C", "C=.C", "C=)", "C(C)1CC1", "C(C)=1CC1", "C)C",
    "C11", "C=1-1", "C=1CC-1", "C1C1", "C12CC12", "C=", "C.", "C(C", "C(C(C", "C1(C", "C1CC", "C1C0",
    "C[C@TH1](F)(Cl)Br", "F/C=C/1.F/1",
    "F[C@H2]Cl", "C[C@](F)(Cl)(Br)I", "[S@](C)(=O)CC", "C/C(\\F)=C/F", "C/C", "C/C=CC", "F/C=C=C=C/F",
    "C/1CC=1", "C[N@]1CC1C", "C[S@+]1CCCC1",
    # not read: quoted in SPEC.md without a position
    "[*]", "*", "CC>>CO", "N->[Fe]", "CC(C))C(=O)[O-", "[si]", "F\\\\C=C/F",
    "F[C@H2]Cl)", "C1.[S@]1(C)=O", "C/1C/1", "C[Co@](F)(Cl)(Br)(I)S",
]


def ring_number(number):
    """A ring number as it is written: one digit, or % and two digits."""
    return str(number) if number < 10 else f"%{number}"


# A ladder of 100 rings, as SPEC.md, section 9.4, describes it: round brackets nested 100 deep, and one
# ring number open at a time. It has 602 characters, 202 atoms and 301 bonds.
LADDER = "C(" * 100 + "CC1" + ")C11" * 99 + ")C1"

# A ladder of 102 rungs with one rail of carbon and one of nitrogen, as SPEC.md, section 3.2, describes
# it: the text goes down the ladder rung by rung, with two ring numbers open at a time. It has 406
# characters, 204 atoms and 304 bonds. `rewrite` and `plain` write it; its chosen form needs more than
# 99 ring numbers, so `canonical` answers with the writer's error.
LADDER_OF_TWO_RAILS = "C1NN2C1" + "C1N2N2C1" * 49 + "C1N2NC1"


# ------------------------------------------------------------------- texts for the filter (section 16)
# Written by hand for this project, and a part of MORE_TEXTS below. SPEC.md, section 16, quotes a text
# for most of what it says about a sound Mol and about the rule `perfluoro`; those stand in SPEC_TEXTS.
# These go through the same two sections once more, with other compounds. The rule, which
# check_tests.py checks: each of them is read. What the filter answers for each, the model says.
FILTER_TEXTS = [
    # sound (section 16.2). An element that is none of the ten, a mass number, a charge:
    "C[Si](C)(C)C(F)(F)F", "C[18F]", "CC(=O)[O-]", "C[N+](C)(C)C.[Cl-]",
    # aromatic bonds: three at one atom, rings with nitrogen and sulfur in them, a double bond at an
    # atom of the ring, and an atom whose bonds and hydrogens add up to too much
    "Cc1ccccc1:c1ccccc1", "O=c1cc[nH]cc1", "Cc1ccc2ccccc2c1", "c1ccsc1", "Cn1cccc1", "n1cccc1", "[cH3]1ccccc1",
    # usual valences and others, without aromatic bonds. A bare atom gets the hydrogens that bring it
    # to its next normal valence (section 5, rule 7), so it fails only beyond the largest one.
    "CCS(C)(=O)=O", "CS(C)(C)C", "CS(C)(C)(C)C", "CS(C)(C)(C)(C)(C)C", "CB(C)C", "ClC(Cl)(Cl)Cl", "C[CH2]",
    "C[OH]", "C[SH](C)C",
    # the rule (section 16.3): chains of six, five and eight, with and without something else attached
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F", "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OCC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    # two groups of three in one molecule, and groups in two molecules
    "FC(F)(F)C(F)(F)C(F)(F)CC(F)(F)C(F)(F)C(F)(F)F", "FC(F)(F)C(F)(F)C(F)(F)F.FC(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    # branches, and two rings that share a bond
    "FC(F)(F)C(F)(C(F)(F)F)C(F)(C(F)(F)F)C(F)(F)F",
    "FC1(F)C(F)(F)C(F)(F)C2(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C2(F)C1(F)F",
    # a bromine and an iodine atom on a carbon atom, which do not end a group; and what does: a nitrogen
    # atom between two groups, and a hydrogen written as an atom of its own
    "FC(F)(F)C(F)(Br)C(F)(F)F", "FC(F)(F)C(F)(I)C(F)(F)F", "FC(F)(F)C(F)(F)N(C(F)(F)F)C(F)(F)F",
    "[H]C(F)(F)C(F)(F)F",
    # fluorine on an aromatic ring; a stereo mark at a fluorinated carbon atom that also carries a
    # chlorine and a bromine atom; and a stereo mark next to a group
    "Fc1c(F)c(F)c(F)c(F)c1F", "F[C@](Cl)(Br)C(F)(F)F", "C[C@H](N)C(F)(F)C(F)(F)F",
    # a branch carbon atom: two -CF3 on one atom inside a chain, a ring with two -CF3 on one atom, two
    # rings that share one atom, an isomer of perfluorooctanesulfonic acid, an alcohol
    "OC(=O)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)C(F)(F)F",
    "FC(F)(F)C1(C(F)(F)F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C1(F)F",
    "FC1(F)C(F)(F)C(F)(F)C(F)(F)C12C(F)(F)C(F)(F)C(F)(F)C2(F)F",
    "OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F", "OC(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
    # and what is none: an atom with two -CF3 only, with a hydrogen, and a carbon atom without hydrogen
    # that has one -CF3 and three methyl groups; between them one that is: three -CF3 and a chlorine atom
    "CC(C)(C(F)(F)F)C(F)(F)F", "FC(F)(F)C(C(F)(F)F)C(F)(F)F", "ClC(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
    "CC(C)(C)C(F)(F)F",
    # chlorine, bromine and iodine are not looked at: an iodine atom at the end of a group; a chlorine atom
    # at the end of one, with an ether beside it; two chlorine atoms on each of two carbon atoms; and a
    # carbon atom with two chlorine atoms between two -CF3, which has no fluorine and is no branch carbon atom
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)I",
    "OS(=O)(=O)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)Cl",
    "FC(Cl)(Cl)C(F)(Cl)Cl", "FC(F)(F)C(Cl)(Cl)C(F)(F)F",
]

# ------------------------------------------------------------------- more texts, written for the tests
# Written by hand for this project. SPEC.md quotes one or two texts for each rule. These go, one by one,
# through the ways in which a text is cut into tokens and the tokens become a Mol (SPEC.md, sections 4
# to 6), and through the ways in which that fails; then through the stereo marks (section 12), the
# writer (section 9) and the chosen form (section 3.2). What the right answer for each is, the model
# says.
MORE_TEXTS = [
    # the empty text
    "",
    # atoms without square brackets, alone and next to each other
    "B", "N", "O", "P", "S", "F", "Br", "I", "n", "o", "p", "s", "BrCCl", "ClCBr", "CI", "Sc", "Co", "Cn", "Bn",
    # letters that are not an atom without square brackets
    "Si", "Na", "Fe", "se", "as", "A", "R", "a", "e", "h", "l", "r", "Cr", "Bl",
    # bond symbols and direction marks
    "C=C", "C#N", "C$C", "c:c", "C\\C", "C/C\\C", "C-=C", "-", "/",
    # ring numbers
    "C0CC0", "C9CC9", "C12CC1C2", "C%10CC%10", "C%99CC%99", "C%00CC%00", "C%05CC5", "C=1CCCCC=1",
    "C%12", "1", "%12", "C%", "C%1", "C%1C", "C%a1", "C%1a", "C%%12", "C%-1", "C%(12)",
    # round brackets and dots: any order is cut into tokens, the reader decides whether it is allowed
    "C(C)C", "C(C)(C)C", "C(C(C)C)C", "C.C", "()", ")(", "..", "C(.C)(=O)O",
    # square brackets: the isotope
    "[2H]", "[14C]", "[238U]", "[0000C]", "[007C]", "[12345678901234567890C]",
    # square brackets: the symbol
    "[C]", "[Cl]", "[Br]", "[Se]", "[As]", "[Sc]", "[Cs]", "[Hg]", "[Hf]", "[Og]", "[Nh]", "[U]", "[W]",
    "[b]", "[c]", "[n]", "[o]", "[p]", "[s]", "[se]", "[as]", "[seH]", "[sH]", "[cH]", "[asH2+]",
    "[CO]", "[cl]", "[nh]", "[sn]", "[A]", "[a]", "[Te]", "[1]", "[+]", "[H2]", "[Cc]", "[cC]", "[SE]",
    # square brackets: the hydrogen count
    "[CH]", "[CH0]", "[CH1]", "[CH2]", "[CH9]", "[H+]", "[H-]", "[HH2]", "[2HH]", "[OH-]", "[OH2]", "[CHH]", "[CH2H]",
    "[CHh]", "[Ch]",
    # square brackets: the charge
    "[C+]", "[C-]", "[C++]", "[C--]", "[C+0]", "[C-0]", "[C+1]", "[C-1]", "[C+9]", "[C+10]", "[C+99]", "[C-99]",
    "[C+100]", "[C-100]", "[C+-]", "[C-+]", "[C+2+]", "[C++2]", "[C+H]", "[13CH3-]", "[Fe+3]", "[O-2]", "[O--2]",
    # stereo marks in square brackets
    "[C@]", "[C@@]", "[C@H]", "[C@@H]", "[C@@@]", "[C@X]", "[C@H+]", "[C@TH1]", "[CH@]", "[C+@]", "[H@H]",
    "[13C@@H2-]", "[@C]", "[/C]", "[C/]", "[C\\]", "[C@H](N)(C)[C@X]",
    # stereo marks outside square brackets
    "@", "C@", "C@@", "\\", "C/", "F/C=C/[C@X]", "C[C@X]/C", "C(/F)=C/F",
    # white space
    " ", "C\tC", "C\nC", "C\rC", " C", "C ", "[ C]", "[C ]", "[C 1]", "[13 C]", "[C\t]",
    # the wildcard atom, atom classes and other characters
    "C*", "[C*]", "[C:1]", "[:1]", "[C:]", "C!", "[C!]", "C?", "C'C", "C\"C", "C\u00e9", "[C\u00e9]", "C,C", "C>C", "C~C",
    "C&C", "C{C}", "C_C", "C;C",
    # control characters, and characters from outside ASCII: whatever one of them looks like, it is
    # not white space, not a digit and not a letter of SMILES
    "C\x0bC", "C\x0cC", "C\x7fC", "C\N{NO-BREAK SPACE}C", "\N{CYRILLIC CAPITAL LETTER ES}",
    "[\N{FULLWIDTH LATIN CAPITAL LETTER C}]", "C\N{COMBINING ACUTE ACCENT}", "C\N{SUPERSCRIPT TWO}",
    "C\N{ARABIC-INDIC DIGIT THREE}", "C%1\N{ARABIC-INDIC DIGIT THREE}", "[\N{ARABIC-INDIC DIGIT THREE}C]",
    "[1\N{FULLWIDTH DIGIT THREE}C]", "[CH\N{ARABIC-INDIC DIGIT THREE}]", "[C+\N{FULLWIDTH DIGIT THREE}]",
    # square brackets that are not closed, or closed once too often
    "[", "[C", "C[", "C[C", "C[C C", "[C[C]", "]", "C]", "[C]]", "[[C]]", "[]C", "[C@", "C[13",

    # ---- how the tokens become a Mol (SPEC.md, section 5), and what may come next (section 6) ----
    # chains, branches and dots
    "CCC", "C(C)(C)(C)(C)C", "C(=O)O", "C(-C)C", "C(C)C(C)C", "C(C(C(C)))C", "C.C.C",
    "C(C.C)C", "C(.C.C)C", "[O-]C(=O)C.[Na+]", "CC(=O)Oc1ccccc1C(=O)O",
    # ring bonds
    "C1CC1C", "C1CC1C1CC1", "C1CC%01", "C1.C2.C12", "C=1CCCCC1", "C1CCCCC=1", "C1CC2CC1C2",
    "C%05CC%05", "c1ccc2ccccc2c1", "C1CCC1C2CCC2", "C#1CCCCCCC#1",
    # the order of a bond without a symbol
    "cc", "cC", "Cc", "c=c", "cc(c)c", "Cc1ccccc1", "c1ccccc1c1ccccc1", "C:1:C:C:C:C:C:1",
    "c:1:c:c:c:c:c1",
    # the hydrogens of atoms without square brackets
    "NC", "N=C", "N#C", "N(C)(C)C", "N(C)(C)(C)(C)C", "[N+](C)(C)(C)C", "S(C)C", "CS(C)(=O)=O", "S(=O)(=O)(O)O",
    "S(C)(C)(C)(C)(C)(C)C", "P(C)(C)C", "P(=O)(O)(O)O", "PC", "P(C)(C)(C)(C)C", "FC", "F(C)C", "ClC", "BrC",
    "IC", "I(C)(C)C", "B(C)(C)C", "BC", "B(C)(C)(C)C", "OC", "O=C", "O=O", "O(C)(C)C", "C#C", "C(=C)=C",
    "n1ccccc1", "[nH]1cccc1", "o1cccc1", "s1cccc1", "nc", "n(c)c", "n(c)(c)c", "oc", "o(c)c", "s(c)c", "pc",
    "b(c)c", "c(c)c", "c(c)(c)c", "c(c)(c)(c)c", "C:C:C", "cO", "c=O", "C(:C):C",
    # a token that may not come at its place
    "C(", "C((", "(", ")", "C)", "C))", "C(C))", "C(C)(", "C(C)1", "C(=1)", "C(=1", "C.1", "C.(C)", "C(.)",
    "C=(", "C=.", "C(=.C)", "C..", ".C", ".", "C((C)C)C", "C()", "C(C)()", "C(C)(=)", "(C", "((", "C=#C",
    "C==", "=", "#C", "C(C)=1", "C-(C)C", "C1=(C)C1",
    # The nine places of the table "What may come next" (SPEC.md, section 6) that no text above reaches.
    # Eight are refused: a bond symbol after a dot; a ring number after `(`; a bond symbol and a `(` after
    # a bond symbol that follows `(`; a bond symbol, a `(`, a `)` and a dot after a bond symbol that
    # follows `)`. One is allowed: a dot after `)`. check_tests.py makes sure that every place of the
    # table is reached by a test text.
    "C.=C", "C(1)C", "C(==C)", "C(=(C))", "C(C)==C", "C(C)=(C)C", "C(C(C)=)", "C(C)=.C", "C(C).C",
    # ring numbers that are wrong, and one that is right: in `C:1CC:1` both ends name the same bond
    "C12", "C1C2", "CC11", "C1=C1", "C=1C-1", "C=1=1", "C-1CC=1", "C:1CC:1", "C1CC1C1", "C%10C%11", "C2CC1",
    "C1CC2", "C1.C", "C1CC1C=1", "C12CC21", "C1C=1",
    # the end of the text, and which problem comes first
    "C(-", "C(C)-", "C1(C=", "C1(C.", "C1(", "C(C(C)", "C=1(", "C.C(", "C1C2C(=",
    # stereo marks and other problems in one text: a problem of the characters or of the structure is
    # reported, wherever it stands, because most problems of the marks are looked for last (SPEC.md,
    # section 6). So `[C@H](C` is reported for its `(`, at position 5
    "C=/C", "=/C", "C(/C", "C/=C", "[C@H](C", "C)[C@H]", "C[C@H])", "C(C[Xx]", "C)C[X", "C1/C", "C/1CC1",
    "C(C[C@X]", "C1CC[C@@H]", "C..[C@H]", "C=[C@H](",

    # ---- stereo marks (SPEC.md, section 12) ----
    # an atom with `@` or `@@`: with four neighbours and with a hydrogen, as the first atom of the text,
    # with ring numbers before and behind its branches, and where a ring closes
    "[C@H](N)(C)O", "[C@@H](N)(C)O", "N[C@](C)(F)Cl", "C[C@@](N)(O)F", "[C@@](C)(N)(O)F", "[C@](C)(N)(O)F",
    "C[C@H]1CCCO1", "C[C@@H]1CCCO1", "[C@]12(F)CCC1C2", "C1CC[C@H](F)C1", "C1CC[C@]1(F)Cl", "F[C@]1(Cl)CCC1",
    "[C@H]1(F)CCCO1", "N1[C@H](C)C1", "C[C@H]1CC1", "C[C@@H]1C[C@H]1C",
    # neighbours that are alike: the text still says an orientation, and it is stored; and beside it
    # the same atom with three neighbours that differ
    "C[C@H](C)C", "C[C@H](N)O",
    # several atoms with an orientation in one ring: an inositol and a sugar
    "O[C@H]1[C@H](O)[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O", "OC[C@H]1O[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O",
    # an atom with a free place (rule 9): read, and refused where it is written with exactly one ring
    # number and only single bonds
    "C[S@@](=O)CC", "C[P@](CC)c1ccccc1", "C[N@](CC)CCC",
    "C[N@@]1CC1C", "C[P@]1CCCC1",
    "C[N@]1C[C@H]1C", "C[S@+]1CC[C@H](C)C1", "C[C@H]1[N@](C)C1", "C[S@]1(=O)CCCC1",
    "C[C@H]1CC[S@+](C)C1",
    # atoms that cannot be a stereo centre, and a stereo class that is written with letters
    "[N@H](C)CC", "N[C@H2]C", "C[C@]F", "C[C@SP1](F)(Cl)Br",
    # direction marks: both marks, both ways round, at a branch, at a ring number, in a chain of double
    # bonds, at an aromatic ring, at nitrogen
    "F\\C=C/F",
    "C/C=C/C=C/C", "C/C=C\\C=C/C", "C/C(F)=C/F", "F/C=C(/F)F",
    "F/C=C/1.F\\1",
    "c1ccccc1/C=C/c1ccccc1", "C/C=C/c1ccccc1", "N/C(=N/O)C", "F/C=N/O", "F/N=N/F", "F/C=C/C=C",
    "F/C=C/C=C\\F",
    # direction marks that say nothing about a double bond
    "CC(F)=C/F", "CC=C/C", "F/C=C=C/F", "C1CC/1", "F/C#C/F",
    # both kinds of marks in one text
    "C/C=C/[C@H](F)Cl", "F[C@H](Cl)/C=C/C",

    # ---- for the writer (SPEC.md, section 9) ----
    # atoms in square brackets that are written back without them, and atoms that keep them
    "[CH3][CH3]", "[CH2]=[CH2]", "[OH2].[OH2]", "[CH3][OH]", "[CH3][CH2][OH]", "[cH]1[cH][cH][cH][cH][cH]1",
    "[c]1[c][c][c][c][c]1",
    "[CH3][NH2]", "[NH4]", "[CH3][SH]", "[SH2]", "[BH3]", "[CH3]F", "[FH]", "[PH3]", "[pH]1cccc1", "[CH3-]",
    "[12CH4]", "[CH3]C", "N(=O)=O", "[N+](=O)[O-]", "C[S](C)(C)C", "Cs1cccc1", "C[n]1cccc1",
    # bond symbols that are written back, and bond symbols that are left out
    "C-C=C-C", "c:c:c", "c1ccccc1:c1ccccc1", "C:c", "c-C", "[Na]-Cl", "C=1C=CC=CC=1",
    # ring numbers: the smallest free number is taken, also right after it was closed
    "C1CC12CC2", "C5CC5", "C%42CC%42", "C1CC1C2CC2", "C12C3C1C23", "C1CCC2CC2C1", "C3CC3.C2CC2",
    # round brackets: branches inside branches, and branches that are written in another order
    "CC(C)(C)C(C)(C)C", "CC(C(C)C)C", "C(C(C(C)C)C)C", "OC(=O)C(N)CS", "C(Cl)(Br)I",
    "C1CC1(C)C", "C(C1CC1)C", "C.C(C)C.C", "C(C)C.C(C)C", "C(.C)(.C)C",
    # The writer has the ring numbers 1 to 99, so it has at most 99 open at the same time. The plain
    # spelling needs one for each neighbour of an atom, apart from the atom just before it and the atom
    # just behind it.
    "C" + "(C)" * 99 + "C", "C" + "(C)" * 100 + "C",
    # A text can have 100 ring numbers open at the same time, because 0 is a ring number too. The writer
    # uses 1 to 99 only. So for the first of these two texts, `rewrite` and `plain` both refuse.
    "C" + "".join(ring_number(n) for n in range(100)) + "C" + "".join("C" + ring_number(n) for n in range(100)),
    "C" + "".join(ring_number(n) for n in range(1, 100)) + "C" + "".join("C" + ring_number(n) for n in range(1, 100)),
    # How many ring numbers a text has open says nothing about how many its Mol needs when it is written.
    # The ladder has one open at a time. Both spellings of its Mol need 100, so `rewrite` and `plain`
    # both refuse it.
    LADDER,
    LADDER_OF_TWO_RAILS,
    # `canonical` refuses a Mol of more than 1,000 atoms before the search begins (SPEC.md, section
    # 3.2). This text has 1,001 atoms: the ten molecules of ethane, on which the search gives up, and a
    # chain of 981. So its answer also shows that the atoms are counted first.
    "CC.CC.CC.CC.CC.CC.CC.CC.CC.CC." + "C" * 981,
    # Texts with many numberings that look alike (SPEC.md, section 3.2). The first two get a chosen
    # text. The third has 1,001 atoms and gets the answer about the atoms.
    "C1CCCC1.N1NNNN1.O1OOOO1", "C1CCCCC1.N1NNNNNN1.O1OOOS1", "C1CCCCC1.N1NNNN1.O1OOOO1." + "C" * 985,
    # Beside alanine, which has a stereo fact, the second of them makes the search give up: with a
    # stereo fact no beginning is taken out, the search would hold 1,008 beginnings while it places the
    # last ring, and 336 would be left at the end. With the texts of SPEC.md that hold exactly 1,000 and
    # 1,200 this ties the limit down to between 1,000 and 1,007. The text behind it has five molecules
    # of ethane beside a molecule with a stereo fact and gets a chosen text; six make the search give up
    # (SPEC.md, section 3.2).
    "C1CCCCC1.N1NNNNNN1.O1OOOS1.N[C@@H](C)C(=O)O", "CC.CC.CC.CC.CC.C[C@H](N)O",
    # Whole groups that can be exchanged, inside one molecule and between molecules: two rings at one
    # atom, the arms of a star, four rings of three atoms, and nine and ten molecules of ethanol. Nine
    # get a chosen text; on ten the search gives up, as on ten of ethane.
    "c1ccccc1Cc1ccccc1", "CCN(CC)CC", "C1CC1.C1CC1.C1CC1.C1CC1", "CCO.CCO.CCO.CCO.CCO.CCO.CCO.CCO.CCO",
    "CCO.CCO.CCO.CCO.CCO.CCO.CCO.CCO.CCO.CCO",
] + FILTER_TEXTS

# ------------------------------------------------------------------------------------------ real texts
# 100 texts from the file first_5K.smi that RDKit ships: compounds of the NCI Open Database, the first
# of the seven collections of reference/README.md. The rule, which check_tests.py checks: of the 4,900
# different texts of that file, in the order of the file, the first one and then every 49th. The texts
# are stored exactly as they stand in the file. They are not this project's to license: NOTICE, in the
# root of the repository, names their source and its licence.
NCI_TEXTS = [
    "CC1=CC(=O)C=CC1=O", "CCC1=C(N)C=C(C)N=C1", "CCC(CC)([CH](O)C1=CC=CC=C1)C2=CC=CC=C2",
    "OS(=O)(=O)C1=CC(=C(Cl)C(=C1)[N+]([O-])=O)[N+]([O-])=O", "O=C(C=CC1=NC=CC=C1)C2=CC=CC=C2", "CC(C)CSC(C)=S",
    "OC(=O)CCCC1=CC=CC=C1", "CN(C)CCC1=C(C)C=C(C)C=C1C", "CO.[O-][N+](=O)N1C(=O)CCC1=O", "NCCNCCNCCN",
    "ClC1=CC=C(C=C1)C=C(C#N)C#N", "NC1=C(SC#N)C=C(C=C1)S(N)(=O)=O", "ClC1=CC2=NC=CC(=C2C=C1)Cl",
    "NNC(=O)C1=C(N)C=CC=C1", "NNC(=S)NN=CC1=CC=CC(=C1)[N+]([O-])=O", "ClC1=C2N=CNC2=NC=N1",
    "O=C(CC(CC(=O)C1=CC=CC=C1)C2=CC=CC=N2)C3=CC=CC=C3", "CCCCC(CCCC)C(O)=O", "CC(C)C(=O)C(C)(C)C",
    "CC(C)[C](C)(O)CC(C)(C)C", "CCCCN(CCCC)C1=CC=C(SC#N)C=C1", "CCN(CC)CCN(CC(O)=O)CC(O)=O", "CCOC(OCC)C=O",
    "ClC1=CC=C(C=C1)C2=CC=C(Cl)C=C2", "CCNC(=O)CCl", "COC1=C(OC(C)=O)C=CC(=C1)CC=C",
    "CC1=[N+](C=CC=C1)[Zn++]([N+]2=C(C)C=CC=C2)([N+]3=C(C)C=CC=C3)[N+]4=C(C)C=CC=C4.SC#N",
    "COC1=C(OC)C=C(C=C1)C=C(C#N)C#N", "CSC1=NC(=C2C=NNC2=N1)O", "ClC1=CC=C(C=C1)N2N=CC3=C(NCC4=CC=CO4)N=CN=C23",
    "NC1=C(Cl)C=CC(=C1)Cl", "OC1=CC=C(N=O)C(=C1N=O)O", "NC(=O)NN=CC1=CC=CC=C1", "CN1N=C(C)C2=C(N)N=CN=C12",
    "OCC(=O)[CH](O)[CH](O)[CH](O)C(O)=O", "OS(=O)(=O)C1=C2C(=CC=CC2=CC=C1)NC3=CC=CC=C3",
    "[O-][N+](=NC1=CC=CC=C1)C2=CC=CC=C2", "CCCCN(CCCC)CCC[CH](O)C1=CC=CC=C1", "N=C1NNC(=N)N1",
    "OC[CH](O)[CH](O)[CH](O)[CH](O)CO",
    "CCCCCC1=CC=[N+](C=C1)[Mn+3]([SH+]C#N)([SH+]C#N)([N+]2=CC=C(CCCCC)C=C2)([N+]3=CC=C(CCCCC)C=C3)[N+]4=CC=C(CCCCC)C=C4.SC#N",
    "NC(=O)CNC1=CC=C(C=C1)[As](O)(O)=O", "[O-][N+](=O)C1=CC=CC(=C1)N=CC2=CC=CC=C2",
    "CC(=O)OC1=CC(=C(OC(C)=O)C=C1)OC(C)=O", "CCCCCC[CH](CC=CCCCCCCCC(=O)OCCOC)OC(C)=O", "CCCCC(C(C)=O)C(C)=O",
    "OCCOC(=O)OCC=C", "CCCC(=O)C1=CC=CS1", "CCCCCCCC[CH](CO)CCCCCC",
    "O[CH]([CH]1CCCCN1)C2=C3C=CC=CC3=NC(=C2)C4=CC(=C(Cl)C=C4)Cl", "[O-][N+](=O)CC1=CCCCC1", "CC(C)=CC(O)=O",
    "CC(C)[CH]1CC[CH](C)C[CH]1O",
    "CC(C)(C)C1=CC=C(OP(=O)(OC2=CC=C(C=C2)C(C)(C)C)OC3=C(C=C(C=C3)C(C)(C)C)C4=CC=CC=C4)C=C1",
    "OS(=O)(=O)CC(=O)C1=CC=C(C=C1)C(=O)CS(O)(=O)=O", "OC(=O)C=CC(O)=O", "OC(=O)C1=C2C=CC=CC2=CC=C1O",
    "O=S(=O)(OCCOCCOS(=O)(=O)C1=CC=CC=C1)C2=CC=CC=C2", "[O-][N+]([O-])=O.F[Co+]12(F)(NCCN1)NCCN2",
    "CC(C)[CH]1CC[C]2(C)[CH](CC[CH]3[C](C)(CO)CCC[C]23O)C1",
    "COC(=O)C(CCC1=CC=C(C=C1)[N+]([O-])=O)(CCC2=CC=C(C=C2)[N+]([O-])=O)C(C)=O", "N1N=NC2=CC=CC=C12",
    "O=C(NC1=CC=CC=C1)OCC2OC(OC(=O)NC3=CC=CC=C3)C(OC(=O)NC4=CC=CC=C4)C(OC(=O)NC5=CC=CC=C5)C2OC(=O)NC6=CC=CC=C6.O=C(NC7=CC=CC=C7)OCC8OC(OC(=O)NC9=CC=CC=C9)C(OC(=O)NC%10=CC=CC=C%10)C(OC(=O)NC%11=CC=CC=C%11)C8OC(=O)NC%12=CC=CC=C%12",
    "OC[CH](O)[CH](O)[CH](O)[CH](O)C1=NC2=CC=CC=C2N1", "NC(=N)SCC1=CC=CC=C1",
    "CN(C)CC1=CC(=C(O)C(=C1)CN(C)C)CN(C)C", "CCOC(=O)C(=CNC(=O)NC)C#N",
    "C[C]1(O)CC[CH]2[CH]3CCC4=CC(=O)CC[C]4(C)[C]35O[CH]5C[C]12C", "CCCN=C1SSC(=O)N1CCC",
    "[O-][N+](=O)C1=C(CCNCC2=CC=CC=C2)C=CC=C1", "CNC(S)=S", "CCOC(=O)N(C1=CC=CC=C1)C2=CC=CC=C2",
    "COC1=CC=C(NC2=C3C=CC(=CC3=NC=C2)Cl)C=C1CNCC(C)C", "O=C1OC(=C2OC(=O)C3=C2C=CC=C3)C4=C1C=CC=C4",
    "OCCCC1=CC=NC=C1", "N#CCC#N", "CC(=CC1=C(Cl)C=CC=C1)C2=CC=CC=N2",
    "O=C1C2=C(C=CC=C2)C(=O)C3=C1C=C4CCCCC4=C3", "CCCCCC[CH](C)OC(=O)C1=C(C=CC=C1)C(=O)O[CH](C)CCCCCC",
    "OC(=O)C1=CC(=O)C=C(O1)C(O)=O", "CCCCCCCCCC(C)=O", "CCCC=NNC1=CC=CC=C1", "COC1=CC=C(Cl)C=C1",
    "O=C(NC1=CC=CC=C1)C(=O)NC2=CC=CC=C2",
    "CCC(=O)OC[CH]1O[CH](OC2=CC=C(C=C2)N=NC3=CC=CC=C3)[CH](OC(=O)CC)[CH](OC(=O)CC)[CH]1OC(=O)CC",
    "CC(=O)NC1=CC=C(C=C1)C(O)C2=CC=C(NC(C)=O)C=C2", "CC(=O)OCCOC(=O)NC1=CC=CC=C1", "CC(=O)CC(=O)OCC1=CC=CC=C1",
    "C[C]1(NC(=O)NC1=O)C2=CC=C(Cl)C=C2", "CCCCCCCCCCCC[N+](C)(C)C.[O-]S(=O)(=O)C1=CC=C(Cl)C=C1",
    "[O-][N+](=O)C[CH](N=O)C1=CC=CC=C1", "OC(=O)C1=CC=C(O1)S(O)(=O)=O", "ClC1=CC=CC=N1",
    "CC(C)C1=CC(=C(C)C=C1O)SC#N", "ON(N=O)C1=C2C=CC=CC2=CC=C1", "CCCCCCCC[CH](O)C(O)=O",
    "NC1=C(O)C(=CC(=C1)[N+]([O-])=O)[N+]([O-])=O", "OC[CH]1O[CH]([CH](O)[CH]1O)N2C=NC3=C(Cl)N=CN=C23",
    "C[CH](O)CNC[CH](C)O",
    "CC1=CC(=CC=C1N=NC2=C(N)C3=C(C=CC=C3)C(=C2)S(O)(=O)=O)C4=CC(=C(C=C4)N=NC5=CC(=C6C=CC=CC6=C5N)S(O)(=O)=O)C",
]
EVERY = 49      # the step of the rule above

# ------------------------------------------------------------------------------------- hand-made Mols
# A Mol is an ordinary object, so it can be written out without any text. First come Mols that show
# every part of the printed layout (SPEC.md, section 7), then Mols on both sides of the border of
# "well formed" (section 3). Several of them no SMILES text can give.
#
# Each entry: a name, the Mol, and whether it is well formed. That last answer is worked out by hand
# from SPEC.md, section 3. check_tests.py makes sure that the model gives the same answer.
def _atom(element="C", isotope=None, charge=0, hydrogens=0):
    return Atom(element, isotope, charge, hydrogens)


def _mol(atoms, bonds=(), orientations=(), geometries=()):
    return Mol(tuple(atoms), tuple(Bond(a, b, order) for a, b, order in bonds),
               tuple(AtomOrientation(atom, orientation) for atom, orientation in orientations),
               tuple(BondGeometry(a, b, geometry) for a, b, geometry in geometries))


def _star(first, how_many):
    """Atom 0 with a single bond to each of `how_many` atoms, from atom number `first` on."""
    return _mol([_atom()] * (first + how_many), [(0, j, "single") for j in range(first, first + how_many)])


_C = _atom()
HAND_MADE_MOLS = [
    ("no atoms and no bonds", _mol([]), True),
    ("all 118 elements, in the order of their atomic numbers", _mol([_atom(e) for e in ELEMENTS]), True),
    ("every kind of bond",
     _mol([_C] * 6, [(0, 1, "single"), (1, 2, "double"), (2, 3, "triple"), (3, 4, "quadruple"), (4, 5, "aromatic")]), True),
    ("isotopes 0, 1, 13 and 1000",
     _mol([_atom(isotope=0), _atom(isotope=1), _atom(isotope=13), _atom("U", isotope=1000)]), True),
    ("charges from -100 to 100",
     _mol([_atom("Fe", charge=q) for q in (-100, -99, -10, -1, 0, 1, 9, 10, 99, 100)]), True),
    ("hydrogens from 0 to 25", _mol([_atom(hydrogens=h) for h in (0, 1, 4, 9, 10, 25)]), True),
    ("aromatic bonds from a carbon atom to a selenium atom and to an iron atom, whose element has no lowercase symbol",
     _mol([_atom("C"), _atom("Se"), _atom("Fe")], [(0, 1, "aromatic"), (0, 2, "aromatic")]), True),

    ("several bonds at one atom, in increasing order",
     _mol([_C] * 4, [(0, 1, "single"), (0, 2, "single"), (0, 3, "single"), (1, 2, "double"), (2, 3, "single")]), True),
    ("a bond that ends at the last atom", _mol([_C] * 3, [(0, 2, "single")]), True),
    ("a bond that ends behind the last atom", _mol([_C] * 3, [(0, 3, "single")]), False),
    ("a bond, but no atoms", _mol([], [(0, 1, "single")]), False),
    ("an atom bonded to itself", _mol([_C] * 3, [(1, 1, "single")]), False),
    ("a bond with the larger atom number first", _mol([_C] * 3, [(2, 1, "single")]), False),
    ("bonds that are not in increasing order of a", _mol([_C] * 3, [(1, 2, "single"), (0, 1, "single")]), False),
    ("bonds of one atom that are not in increasing order of b",
     _mol([_C] * 3, [(0, 2, "single"), (0, 1, "single")]), False),
    ("the same two atoms bonded twice", _mol([_C] * 2, [(0, 1, "single"), (0, 1, "double")]), False),

    # for the writer (SPEC.md, section 9.4): what it refuses, and the limit of 99 ring numbers
    ("a hydrogen atom with a hydrogen of its own", _mol([_atom("H", hydrogens=1)]), True),
    ("an atom with 10 hydrogens behind an atom with a charge of 100",
     _mol([_atom("Fe", charge=100), _atom(hydrogens=10)], [(0, 1, "single")]), True),
    ("an atom with 10 hydrogens behind a hydrogen atom with hydrogens",
     _mol([_atom("H", hydrogens=2), _atom(hydrogens=10)]), True),
    ("a hydrogen atom with hydrogens behind an atom with 10 hydrogens",
     _mol([_atom(hydrogens=10), _atom("H", hydrogens=2)]), True),
    ("a hydrogen atom with 10 hydrogens", _mol([_atom("H", hydrogens=10)]), True),
    ("two iron atoms joined by an aromatic bond: no lowercase symbol, and nothing is refused",
     _mol([_atom("Fe"), _atom("Fe")], [(0, 1, "aromatic")]), True),
    ("propane with its atoms numbered end, end, middle", _mol([_atom(hydrogens=3), _atom(hydrogens=3), _atom(hydrogens=2)],
                                                              [(0, 2, "single"), (1, 2, "single")]), True),
    ("atom 0 bonded to the atoms 2 to 100: 99 ring numbers", _star(2, 99), True),
    ("atom 0 bonded to the atoms 2 to 101: 100 ring numbers", _star(2, 100), True),
    ("atom 0 bonded to the atoms 1 to 101: 100 ring numbers in the plain spelling, none with round brackets",
     _star(1, 100 + 1), True),
    # the limit once more, in three shapes that the Mol of no test text has
    ("atom 0 bonded to the atoms 2 to 100, and atom 2 to atom 101: 99 ring numbers, because the number that "
     "atom 2 closes is free again for the one that it opens",
     _mol([_C] * 102, [(0, j, "single") for j in range(2, 101)] + [(2, 101, "single")]), True),
    ("the atoms 0 to 99 bonded to atom 100: 99 ring numbers, opened at 99 atoms and closed at one",
     _mol([_C] * 101, [(j, 100, "single") for j in range(100)]), True),
    ("the atoms 0 to 100 bonded to atom 101: 100 ring numbers",
     _mol([_C] * 102, [(j, 101, "single") for j in range(101)]), True),

    # two reasons at once (SPEC.md, section 9.4): the order in which the writer asks decides the message
    ("not well formed, and an atom with 10 hydrogens: that it is not well formed is said",
     _mol([_atom(hydrogens=10), _C], [(1, 0, "single")]), False),
    ("atom 0 is bonded to the atoms 2 to 101, and atom 101 has 10 hydrogens: the message about the atom comes, "
     "although the ring numbers run out at atom 0",
     _mol([_C] * 101 + [_atom(hydrogens=10)], [(0, j, "single") for j in range(2, 102)]), True),
    ("ten molecules of ethane, as in CC.CC.CC.CC.CC.CC.CC.CC.CC.CC, with the bonds in the reverse order: not "
     "well formed, which `canonical` says before it searches",
     _mol([_atom(hydrogens=3)] * 20, list(reversed([(2 * j, 2 * j + 1, "single") for j in range(10)]))), False),
    ("three rings, as in C1CCCCC1.N1NNNN1.O1OOOO1, with the bonds in the reverse order: not well formed",
     _mol([_atom(hydrogens=2)] * 6 + [_atom("N", hydrogens=1)] * 5 + [_atom("O")] * 5,
          list(reversed([(0, 1, "single"), (0, 5, "single"), (1, 2, "single"), (2, 3, "single"), (3, 4, "single"),
                         (4, 5, "single"), (6, 7, "single"), (6, 10, "single"), (7, 8, "single"), (8, 9, "single"),
                         (9, 10, "single"), (11, 12, "single"), (11, 15, "single"), (12, 13, "single"),
                         (13, 14, "single"), (14, 15, "single")]))), False),
    ("ten molecules of ethane with the bonds in order: well formed, and the search gives up",
     _mol([_atom(hydrogens=3)] * 20, [(2 * j, 2 * j + 1, "single") for j in range(10)]), True),
    ("nine molecules of ethane, numbered so that the two atoms of a molecule stand far apart: the search holds "
     "630 beginnings at most and gives a chosen form",
     _mol([_atom(hydrogens=3)] * 18, [(j, j + 9, "single") for j in range(9)]), True),

    # stereo facts (SPEC.md, sections 3 and 12.1): on both sides of the border of "well formed".
    # An atom with an orientation must have four places: four neighbours and no hydrogen of its own, or
    # three neighbours and at most one hydrogen.
    ("an atom with four neighbours that has an orientation",
     _mol([_C, _atom("F"), _atom("Cl"), _atom("Br"), _atom("I")], [(0, j, "single") for j in range(1, 5)],
          [(0, "clockwise")]), True),
    ("an atom with three neighbours and one hydrogen that has an orientation",
     _mol([_atom(hydrogens=1), _atom("F"), _atom("Cl"), _atom("Br")], [(0, j, "single") for j in range(1, 4)],
          [(0, "anticlockwise")]), True),
    ("an atom with three neighbours and no hydrogen that has an orientation: its fourth place is free",
     _mol([_atom(hydrogens=3), _atom("S"), _atom("O"), _atom(hydrogens=3)],
          [(0, 1, "single"), (1, 2, "double"), (1, 3, "single")], [(1, "clockwise")]), True),
    ("an orientation at an atom with two neighbours",
     _mol([_atom(hydrogens=3), _atom(hydrogens=2), _atom(hydrogens=3)], [(0, 1, "single"), (1, 2, "single")],
          [(1, "clockwise")]), False),
    ("an orientation at an atom with three neighbours and two hydrogens",
     _mol([_atom(hydrogens=2), _atom("F"), _atom("Cl"), _atom("Br")], [(0, j, "single") for j in range(1, 4)],
          [(0, "clockwise")]), False),
    ("an orientation at an atom with four neighbours and a hydrogen",
     _mol([_atom(hydrogens=1), _atom("F"), _atom("Cl"), _atom("Br"), _atom("I")],
          [(0, j, "single") for j in range(1, 5)], [(0, "clockwise")]), False),
    ("an orientation at an atom with five neighbours",
     _mol([_atom("P")] + [_atom("F")] * 5, [(0, j, "single") for j in range(1, 6)], [(0, "clockwise")]), False),
    ("an orientation at an atom that does not exist", _mol([_C, _C], [(0, 1, "single")], [(5, "clockwise")]), False),
    ("two atoms with an orientation, in increasing order",
     _mol([_C] * 8, [(0, 1, "single"), (0, 2, "single"), (0, 3, "single"), (0, 4, "single"), (4, 5, "single"),
                     (4, 6, "single"), (4, 7, "single")], [(0, "clockwise"), (4, "anticlockwise")]), True),
    ("two atoms with an orientation, not in increasing order",
     _mol([_C] * 8, [(0, 1, "single"), (0, 2, "single"), (0, 3, "single"), (0, 4, "single"), (4, 5, "single"),
                     (4, 6, "single"), (4, 7, "single")], [(4, "anticlockwise"), (0, "clockwise")]), False),
    ("one atom with two orientations",
     _mol([_C, _atom("F"), _atom("Cl"), _atom("Br"), _atom("I")], [(0, j, "single") for j in range(1, 5)],
          [(0, "clockwise"), (0, "anticlockwise")]), False),
    # A double bond with a geometry must be a double bond of the Mol, and each of its two atoms must have
    # one or two other neighbours.
    ("a double bond with a geometry, with one other neighbour at each of its atoms",
     _mol([_atom("F"), _atom(hydrogens=1), _atom(hydrogens=1), _atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single")], [], [(1, 2, "oppositeSides")]), True),
    ("a double bond with a geometry, with two other neighbours at each of its atoms",
     _mol([_atom("F"), _atom("Cl"), _C, _C, _atom("Br"), _atom("I")],
          [(0, 2, "single"), (1, 2, "single"), (2, 3, "double"), (3, 4, "single"), (3, 5, "single")],
          [], [(2, 3, "sameSide")]), True),
    ("a geometry at a single bond",
     _mol([_atom("F"), _atom(hydrogens=2), _atom(hydrogens=2), _atom("F")],
          [(0, 1, "single"), (1, 2, "single"), (2, 3, "single")], [], [(1, 2, "oppositeSides")]), False),
    ("a geometry at a double bond one of whose atoms has no other neighbour",
     _mol([_atom(hydrogens=2), _atom(hydrogens=1), _atom("F")], [(0, 1, "double"), (1, 2, "single")],
          [], [(0, 1, "sameSide")]), False),
    ("a geometry at a double bond one of whose atoms has three other neighbours",
     _mol([_atom("F"), _atom(hydrogens=1), _atom("P"), _atom("F"), _atom("F"), _atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single"), (2, 4, "single"), (2, 5, "single")],
          [], [(1, 2, "sameSide")]), False),
    ("a geometry whose two atoms are given with the larger number first",
     _mol([_atom("F"), _atom(hydrogens=1), _atom(hydrogens=1), _atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single")], [], [(2, 1, "oppositeSides")]), False),
    ("a geometry at two atoms that are not bonded",
     _mol([_atom("F"), _atom(hydrogens=1), _atom(hydrogens=1), _atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single")], [], [(0, 3, "oppositeSides")]), False),
    ("two double bonds with a geometry, in the order of the bonds",
     _mol([_atom(hydrogens=3), _atom(hydrogens=1), _atom(hydrogens=1), _atom(hydrogens=1), _atom(hydrogens=1),
           _atom(hydrogens=3)], [(0, 1, "single"), (1, 2, "double"), (2, 3, "single"), (3, 4, "double"), (4, 5, "single")],
          [], [(1, 2, "oppositeSides"), (3, 4, "sameSide")]), True),
    ("two double bonds with a geometry, not in the order of the bonds",
     _mol([_atom(hydrogens=3), _atom(hydrogens=1), _atom(hydrogens=1), _atom(hydrogens=1), _atom(hydrogens=1),
           _atom(hydrogens=3)], [(0, 1, "single"), (1, 2, "double"), (2, 3, "single"), (3, 4, "double"), (4, 5, "single")],
          [], [(3, 4, "sameSide"), (1, 2, "oppositeSides")]), False),
    ("one double bond with two geometries",
     _mol([_atom("F"), _atom(hydrogens=1), _atom(hydrogens=1), _atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single")], [],
          [(1, 2, "oppositeSides"), (1, 2, "sameSide")]), False),
    ("an atom with an orientation at a double bond with a geometry",
     _mol([_atom(hydrogens=3), _atom(hydrogens=1), _atom(hydrogens=1), _atom(hydrogens=1), _atom("F"), _atom("Cl")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single"), (3, 4, "single"), (3, 5, "single")],
          [(3, "clockwise")], [(1, 2, "oppositeSides")]), True),

    # for the writer (SPEC.md, section 12.3): well formed Mols with stereo facts that it refuses
    ("a stereo centre with a free place as atom 0: every spelling would write it without an atom before it",
     _mol([_atom("S"), _atom(hydrogens=3), _atom("O"), _atom(hydrogens=3)],
          [(0, 1, "single"), (0, 2, "double"), (0, 3, "single")], [(0, "clockwise")]), True),
    ("a stereo centre with a free place and three single bonds, between its neighbours in the numbering: the "
     "plain spelling would write it with one ring number, the spelling with round brackets writes it",
     _mol([_atom(hydrogens=3), _atom("N"), _atom(hydrogens=3), _atom(hydrogens=2), _atom(hydrogens=3)],
          [(0, 1, "single"), (1, 2, "single"), (1, 3, "single"), (3, 4, "single")], [(1, "anticlockwise")]), True),
    ("a double bond with a geometry at an atom whose only other bond is a double bond: no bond can carry a mark",
     _mol([_atom(hydrogens=2), _C, _atom(hydrogens=1), _atom("F")],
          [(0, 1, "double"), (1, 2, "double"), (2, 3, "single")], [], [(1, 2, "sameSide")]), True),
    ("three double bonds in a chain, the first and the last with a geometry: the marks would give the middle "
     "one a geometry as well",
     _mol([_atom("F")] + [_atom(hydrogens=1)] * 6 + [_atom("F")],
          [(0, 1, "single"), (1, 2, "double"), (2, 3, "single"), (3, 4, "double"), (4, 5, "single"), (5, 6, "double"),
           (6, 7, "single")], [], [(1, 2, "oppositeSides"), (5, 6, "oppositeSides")]), True),
    ("a ring of four double bonds and four single bonds, as in C/1=C/C=C\\C=C/C=C\\1, with the geometry of the "
     "first double bond turned round: no choice of marks gives every geometry",
     _mol([_atom(hydrogens=1)] * 8,
          [(0, 1, "double"), (0, 7, "single"), (1, 2, "single"), (2, 3, "double"), (3, 4, "single"), (4, 5, "double"),
           (5, 6, "single"), (6, 7, "double")], [],
          [(0, 1, "oppositeSides"), (2, 3, "sameSide"), (4, 5, "sameSide"), (6, 7, "sameSide")]), True),
]

# ----------------------------------------------------------------------------------- renumbered Mols
# The reader numbers the atoms in the order of the text. The writer must also spell a Mol whose atoms are
# numbered in another order, unless it is one that SPEC.md, sections 9.4 and 12.3, lets it refuse. So
# here are the Mols that the model reads from the texts of NCI_TEXTS and of RENUMBERED_STEREO_TEXTS
# (below), with new atom numbers. For nearly all of them that is another Mol than the one that is read
# from the text; check_tests.py counts them.
#
# The rule for a text with n atoms, at place k of the two lists taken together, counted from 0. It
# depends on what is left when k is divided by 3:
#   * 0: the atoms are numbered backwards, so atom i becomes atom n - 1 - i;
#   * 1: atom i becomes atom (i * m) mod n, where m is the smallest number from 2 on that has no common
#     divisor with n. Atoms that stood next to each other then stand far apart;
#   * 2: the first atom becomes the last one, and every other atom moves one place to the front.
#
# The stereo facts are restated for the new numbers by the rule for a stored mark (SPEC.md, section
# 12.1), written out here without the two statements through which the model restates them: an
# orientation turns round when an odd number of swaps puts the new numbers of the neighbours in order,
# and a geometry turns round when the lowest-numbered other neighbour becomes another atom at exactly
# one of the two ends. The function uses nothing of the model but the classes of a Mol. So
# check_canonical.py, check_corpus.py and check_spec.py renumber with it as well, and check_tests.py and
# check_corpus.py hold it against the model's own `arrange`.
def renumbered(mol, order):
    """The Mol with its atoms in a new order: atom j of the result is atom order[j] of `mol`, as in
    `model.arrange`."""
    new = [None] * len(order)
    for place, old in enumerate(order):
        new[old] = place
    bonds = sorted((min(new[b.a], new[b.b]), max(new[b.a], new[b.b]), b.order) for b in mol.bonds)
    neighbours = [[] for _ in mol.atoms]
    for b in mol.bonds:
        neighbours[b.a].append(b.b)
        neighbours[b.b].append(b.a)
    neighbours = [sorted(x) for x in neighbours]
    orientations = []
    for x in mol.orientations:
        image = [new[j] for j in neighbours[x.atom]]            # the old fixed order, in new numbers
        swaps = sum(1 for p in range(len(image)) for q in range(p + 1, len(image)) if image[p] > image[q])
        turned = {"anticlockwise": "clockwise", "clockwise": "anticlockwise"}[x.orientation]
        orientations.append((new[x.atom], turned if swaps % 2 else x.orientation))
    geometries = []
    for g in mol.geometries:
        changed = 0
        for end, partner in ((g.a, g.b), (g.b, g.a)):
            rest = [j for j in neighbours[end] if j != partner]
            changed += new[rest[0]] != min(new[j] for j in rest)
        turned = {"sameSide": "oppositeSides", "oppositeSides": "sameSide"}[g.geometry]
        geometries.append((min(new[g.a], new[g.b]), max(new[g.a], new[g.b]), turned if changed == 1 else g.geometry))
    return Mol(tuple(mol.atoms[old] for old in order), tuple(Bond(a, b, o) for a, b, o in bonds),
               tuple(AtomOrientation(atom, o) for atom, o in sorted(orientations)),
               tuple(BondGeometry(a, b, g) for a, b, g in sorted(geometries)))


def _order_of(new):
    """The order in which the atoms stand when atom i is called new[i]: what `renumbered` takes."""
    order = [None] * len(new)
    for old, number in enumerate(new):
        order[number] = old
    return order


# Texts with stereo marks whose Mols are renumbered as well. Each stands in SPEC_TEXTS or MORE_TEXTS.
RENUMBERED_STEREO_TEXTS = [
    "N[C@@H](C)C(=O)O", "C[C@](F)(Cl)Br", "[C@]12(F)CCC1C2", "C1CC[C@]1(F)Cl", "C[C@@H]1C[C@H]1C",
    "O[C@H]1[C@H](O)[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O", "OC[C@H]1O[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O",
    "C[S@](=O)CC", "C[S@]1(=O)CCCC1", "C[P@](CC)c1ccccc1", "F/C=C/F", "F/C=C\\F", "C/C=C/C=C/C",
    "C/C=C\\C=C/C", "F/C(/F)=C/F", "C/1=C/C=C\\C=C/C=C\\1", "c1ccccc1/C=C/c1ccccc1", "N/C(=N/O)C",
    "C[C@H](F)/C=C/Cl", "F[C@H](Cl)/C=C/C", "F/C=C/C=C\\F",
]


def _renumbered_mols():
    found = []
    for k, text in enumerate(NCI_TEXTS + RENUMBERED_STEREO_TEXTS):
        try:
            mol = read(text)
        except SmilesError:
            continue                        # a text that is not read has no Mol
        n = len(mol.atoms)
        if k % 3 == 0:
            name, new = f"{text}, with its atoms numbered backwards", [n - 1 - i for i in range(n)]
        elif k % 3 == 1:
            m = next(m for m in range(2, n + 2) if math.gcd(m, n) == 1)
            name, new = f"{text}, with atom i numbered (i * {m}) mod {n}", [(i * m) % n for i in range(n)]
        else:
            name, new = f"{text}, with its first atom numbered last", [(i - 1) % n for i in range(n)]
        found.append((name, renumbered(mol, _order_of(new))))       # atom i becomes atom new[i]
    return found


RENUMBERED_MOLS = _renumbered_mols()

# ---------------------------------------------------------------------------- probes for element symbols
# Texts that are tried as the symbol of an element. A symbol must fit letter by letter, with its capital
# letter, so most of these are the symbol of no element.
SYMBOL_PROBES = ["H", "He", "Co", "U", "Og", "", "h", "HE", "hE", "c", "se", "as", "CO", "Xx", "D", "T", "J", "Q",
                 "Uue", "Me", "Ph", "C ", " C", "Cl2", "*", "[C]", "CC"]
