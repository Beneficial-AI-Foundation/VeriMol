"""Check the filter of the Lean program against a search written for RDKit: on the real SMILES texts, on
other spellings of compounds, and on the isomers of the perfluoroalkyl acids.

    .venv/bin/python -I reference/check_filter.py               all texts
    .venv/bin/python -I reference/check_filter.py --limit 3000  a quick look at a sample

Any other argument is refused: a mistyped option must not start the whole run.

Theorems 46 to 49 of CLAIMS.md say that the filter does exactly what SPEC.md, section 16, defines. They do
not say that the program reads a text as a chemist does. This check looks for places where its reading of
a text or its search differs from RDKit's. It cannot show that the definition of the rule is the
chemistry: RDKit is asked for that definition, written a second time (`FLUORINATED`, `SKELETON` and
`rdkit_size`, below). It is a test, and no proof.

The model is left out, as in check_direct.py. The script first builds both programs (`lake build app
answers`). The answers of the Lean program come from the second program, `.lake/build/bin/answers`, which
gives what `VeriMol.run` gives (Answers.lean). The built `app` is not started here.

The Lean program is asked twice about every text, behind the words `filter perfluoro`: with the number 1 and
with the number 6. With the number 1 the filter refuses every sound Mol that has a fluorinated carbon atom at
all, and its message names the size of the largest perfluorinated group. RDKit is asked for that size with
its clean-up on, as a chemist would use it.

  real texts       whether the filter takes the Mol for sound, and if not, which test fails first; for a
                   sound Mol, the size of the largest group, against RDKit's; and with the number 6, what
                   the filter answers, against that size
  other spellings  28 compounds, each as it is written below and as RDKit writes it in 23 other ways
                   (`other_spellings`), and three texts written by hand (`BY_HAND`)
  isomers          every perfluoroalkyl group without a ring of 1 to 10 carbon atoms, as a carboxylic acid
                   and as a sulfonic acid: the filter and RDKit's search must both name the number of its
                   carbon atoms

A run without --limit must be a run on the recorded real texts, all of them, and every one of its numbers
must be the recorded one (`RECORDED`, below). A sample has least counts in their place.

reference/README.md, "Reading the output of `check_filter.py`", says how RDKit is asked, what each
comparison demands, and what the check shows and what it does not. A line in CAPITALS is a failure. The
script then ends with exit code 1.
"""
import collections
import multiprocessing
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_app
import sources
from rdkit import Chem, RDLogger

TEXTS = 100                     # how many texts one worker takes at a time
LIMIT = 6                       # the number of the filter in the second question: the smaller of the two numbers
                                # of the wording for long chains (VeriMol/Proofs/Predicates/FluoroGroup.lean)
RANDOM_ORDERS = 20              # in how many random orders of its atoms RDKit writes each compound
CAPITALS = re.compile(r"\b[A-Z]{2,} [A-Z]{2,}\b")      # two words in capitals, one after the other: a failure

# A fluorinated carbon atom, as RDKit is asked for it (SPEC.md, section 16.3): a carbon atom that is no
# aromatic one, with four connections (X4) and no hydrogen (H0), with a fluorine atom on a single bond,
# and without a hydrogen that stands as an atom of its own on a single bond. What else it is bonded to
# is not asked: chlorine, bromine and iodine are not looked at. With four connections and the valence of
# carbon, each of its bonds is a single bond.
FLUORINATED = Chem.MolFromSmarts("[CX4H0;$(C-F);!$(C-[#1])]")

# An atom that meets the five conditions of section 16.3, as RDKit is asked for it: the same pattern
# without the fluorine atom. A branch carbon atom is such an atom with three neighbours among the carbon
# atoms of the groups (`rdkit_size`).
SKELETON = Chem.MolFromSmarts("[CX4H0;!$(C-[#1])]")

LARGEST_GROUP = 10              # the isomers: perfluoroalkyl groups with 1 to so many carbon atoms
ACIDS = (("carboxylic acid", "OC(=O)"), ("sulfonic acid", "OS(=O)(=O)"))

# Compounds for the other spellings, each as one SMILES: perfluorinated acids and sulfonic acids, three
# branched ones, two of them with a branch carbon atom that carries no fluorine, rings, an ether, an
# alcohol and an amine with a perfluorinated group, an iodide, an ether acid with a chlorine atom at the
# end of its longer group, a compound with a chlorine and a bromine atom on fluorinated carbon atoms,
# medicines with a –CF3, and compounds with fluorine at an aromatic ring or with no fluorine at all.
COMPOUNDS = [
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(C(F)(F)F)C(F)(F)F",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
    "OC(=O)C(C(F)(F)F)(C(F)(F)F)C(C(F)(F)F)(C(F)(F)F)C(F)(F)F",
    "OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OS(=O)(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "OC(=O)C(F)(F)C(F)(F)C(F)(F)F",
    "OC(=O)C(F)(OC(F)(F)C(F)(F)C(F)(F)F)C(F)(F)F",
    "FC1(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C1(F)F",
    "FC1(F)C(F)(F)C(F)(F)C2(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C2(F)C1(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)F",
    "OCCC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)N(C(F)(F)C(F)(F)C(F)(F)C(F)(F)F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)F",
    "FC(F)(F)C(F)(C(F)(F)F)C(F)(C(F)(F)F)C(F)(F)F",
    "FC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)I",
    "OS(=O)(=O)C(F)(F)C(F)(F)OC(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)C(F)(F)Cl",
    "FC1(F)OC(F)(F)C(F)(F)C1(F)F",
    "CNCCC(Oc1ccc(cc1)C(F)(F)F)c1ccccc1",
    "Cc1ccc(cc1)c1cc(nn1c1ccc(cc1)S(N)(=O)=O)C(F)(F)F",
    "FC(F)(F)c1ccccc1",
    "Fc1c(F)c(F)c(F)c(F)c1F",
    "FC(F)(F)C(F)(F)c1ccc(cc1)C(F)(F)C(F)(F)C(F)(F)F",
    "FC(F)=C(F)C(F)(F)C(F)(F)F",
    "CC(F)(F)CC(F)(F)C(F)(Cl)C(F)(F)Br",
    "CC(C)Cc1ccc(cc1)C(C)C(=O)O",
    "CC(=O)Oc1ccccc1C(=O)O",
]

# Texts written by hand for what RDKit does not write itself. The first two have a bond symbol `:` at a
# carbon atom with four bonds. In the third every atom of a ring of –CF2– is written in lowercase.
BY_HAND = ["FC(F)(F):c1ccccc1", "FC(F)(F)C(F)(F):C(F)(F)C(F)(F)F", "Fc1(F)c(F)(F)c(F)(F)c(F)(F)c(F)(F)c1(F)F"]

NOT_READ = "texts that the Lean program does not read"
SOUND = "sound: the filter takes the Mol for sound"
NOT_SOUND = "sound: the filter takes the Mol for not sound"
SAME_SIZE = "size: RDKit's search finds a largest group of the same size as the filter names"
NO_VERDICT = "size: no verdict: RDKit, with its clean-up on, refuses the text"
PASSES = f"the filter, with the number {LIMIT}: the Mol is handed on"
REFUSED_BY_THE_RULE = f"the filter, with the number {LIMIT}: refused, for a group of {LIMIT} or more"

# Every number of a run on all the recorded real texts (see the head of this file). When a number changes
# because the program or SPEC.md was changed on purpose, the number here is changed with it.
RECORDED = {
    'texts that the Lean program reads':
        62075,
    'texts that the Lean program does not read':
        24,
    'sound: the filter takes the Mol for sound':
        52533,
    '    of these, the largest group has no atom: no fluorinated carbon atom':
        50758,
    '    of these, the largest group has 1 carbon atom':
        1690,
    '    of these, the largest group has 2 to 5 carbon atoms':
        51,
    '    of these, the largest group has 6 or more carbon atoms':
        34,
    'sound: the filter takes the Mol for not sound':
        9542,
    '    of these, atom N has a charge':
        7865,
    '    of these, atom N is no atom of B, C, N, O, P, S, F, Cl, Br or I':
        1631,
    '    of these, the bonds and hydrogens of atom N add up to no usual valence of its element':
        41,
    '    of these, atom N has a mass number':
        5,
    "    of these, RDKit's search finds a group of 6 or more (the filter refuses them as not sound)":
        3,
    "size: RDKit's search finds a largest group of the same size as the filter names":
        52530,
    'size: no verdict: RDKit, with its clean-up on, refuses the text':
        3,
    'the filter, with the number 6: the Mol is handed on':
        52499,
    'the filter, with the number 6: refused, for a group of 6 or more':
        34,
    'other spellings: the filter answers as for the compound as written':
        626,
    'other spellings: atoms in a random order':
        560,
    'other spellings: compounds':
        28,
    'other spellings: every hydrogen as an atom of its own':
        28,
    'other spellings: every hydrogen count in square brackets':
        28,
    'other spellings: single and double bonds in the place of aromatic ones':
        28,
    'other spellings: a hydrogen as an atom of its own: refused as not sound, for an atom that is none of the ten elements':
        18,
    'other spellings: written by hand, with a bond symbol : or lowercase symbols at carbon atoms with four bonds':
        3,
    'other spellings: written by hand: refused as not sound':
        2,
    "other spellings: written by hand: sound, and the size that the filter names is not below RDKit's":
        1,
    'isomers: perfluoroalkyl groups without a ring, each as a carboxylic acid and as a sulfonic acid':
        1758,
    'isomers: of these, the isomers of perfluorooctanoic acid':
        39,
    'isomers: of these, the isomers of perfluorooctanesulfonic acid':
        89,
    "isomers: the filter and RDKit's search both name the number of carbon atoms of the group":
        1758,
    'isomers: of these, refused with the number 6, for a group of 6 or more':
        1726,
}


# ------------------------------------------------------------------------------- the two programs
def rdkit_size(text):
    """The size of the largest perfluorinated group that RDKit's search finds in the text, or None if
    RDKit, with its clean-up on, refuses the text. The carbon atoms of the groups are the atoms that fit
    `FLUORINATED` and, added until a round adds none, the atoms that fit `SKELETON` and have three of
    them as neighbours. The bonds that do not join two of these atoms are taken out of a copy of the
    molecule, and the largest piece that then hangs together gives the size."""
    mol = Chem.MolFromSmiles(text)
    if mol is None:
        return None
    members = {match[0] for match in mol.GetSubstructMatches(FLUORINATED, maxMatches=mol.GetNumAtoms() + 1)}
    skeleton = {match[0] for match in mol.GetSubstructMatches(SKELETON, maxMatches=mol.GetNumAtoms() + 1)}
    added = True
    while added:                                        # the branch carbon atoms, until none is added
        added = False
        for atom in sorted(skeleton - members):
            if sum(other.GetIdx() in members for other in mol.GetAtomWithIdx(atom).GetNeighbors()) >= 3:
                members.add(atom)
                added = True
    apart = Chem.RWMol(mol)
    for bond in mol.GetBonds():
        a, b = bond.GetBeginAtomIdx(), bond.GetEndAtomIdx()
        if not (a in members and b in members):
            apart.RemoveBond(a, b)
    pieces = Chem.GetMolFrags(apart)                    # RDKit's own search for the atoms that hang together
    return max((len(piece) for piece in pieces if piece[0] in members), default=0)


def answer_of(answer):
    """What the filter answered behind the number 1, as a pair: ("not read", None), ("not sound", the
    reason with every number of an atom written N), or ("sound", the size of the largest group)."""
    stdout, stderr, code = answer
    if code == 0:
        return "sound", 0
    message = stderr.decode("utf-8")[len("error: "):-1]
    size = re.fullmatch(r"the Mol has a perfluorinated group of size ([0-9]+), and size 1 or more is refused", message)
    if size:
        return "sound", int(size.group(1))
    if message.startswith("the Mol is not sound: "):
        return "not sound", re.sub(r"atom [0-9]+", "atom N", message[len("the Mol is not sound: "):])
    return ("not read", None) if message.startswith("position ") else ("NOT UNDERSTOOD", message)


def filter_answers(texts):
    """For each text, what the Lean program answers behind `filter perfluoro 1` and behind `filter perfluoro
    LIMIT`, as (the pair of `answer_of`, the second answer); or None and why the second program gave no
    answers."""
    lists = [["filter", "perfluoro", number, text] for text in texts for number in ("1", str(LIMIT))]
    answers, problem = check_app.ask(lists)
    if answers is None:
        return None, problem
    return [(answer_of(answers[2 * place]), answers[2 * place + 1]) for place in range(len(texts))], None


def at_the_limit(size, second):
    """Whether the answer behind the number LIMIT is the one that the size of the largest group calls
    for: the Mol is handed on below LIMIT, and refused with the message of the rule from LIMIT on."""
    stdout, stderr, code = second
    if size < LIMIT:
        return code == 0 and stdout.startswith(b"{ atoms := ") and stderr == b""
    wanted = f"error: the Mol has a perfluorinated group of size {size}, and size {LIMIT} or more is refused\n"
    return code == 1 and stdout == b"" and stderr == wanted.encode("utf-8")


# ------------------------------------------------------------------------------- the real texts
def examine(texts):
    """All comparisons for some real texts. Returns a count of what was found, and for each kind of
    finding at most three of the texts concerned."""
    count, shown = collections.Counter(), collections.defaultdict(list)

    def found(kind, text=None):
        count[kind] += 1
        if text is not None and len(shown[kind]) < 3:
            shown[kind].append(text)

    answers, problem = filter_answers(texts)
    if answers is None:
        found(f"THE SECOND PROGRAM GAVE NO ANSWERS FOR {len(texts)} TEXTS: {problem}", texts[0])
        return count, dict(shown)
    for text, ((kind, what), second) in zip(texts, answers):
        if kind == "not read":
            found(NOT_READ)
            continue
        if kind == "NOT UNDERSTOOD":
            found(f"AN ANSWER OF THE FILTER THAT THIS SCRIPT DOES NOT KNOW: {what}", text)
            continue
        found("texts that the Lean program reads")
        theirs = rdkit_size(text)
        if kind == "not sound":
            found(NOT_SOUND)
            found(f"    of these, {what}", text)
            if second[2] != 1 or b"the Mol is not sound: " not in second[1]:
                found(f"THE FILTER REFUSES A MOL AS NOT SOUND WITH THE NUMBER 1 AND NOT WITH THE NUMBER {LIMIT}", text)
            if theirs is not None and theirs >= LIMIT:
                found(f"    of these, RDKit's search finds a group of {LIMIT} or more (the filter refuses them as not sound)", text)
            continue
        # ---- a sound Mol ----
        found(SOUND)
        found("    of these, the largest group has "
              + ("no atom: no fluorinated carbon atom" if what == 0 else "1 carbon atom" if what == 1
                 else f"2 to {LIMIT - 1} carbon atoms" if what < LIMIT else f"{LIMIT} or more carbon atoms"),
              text if what >= LIMIT else None)
        if theirs is None:
            found(NO_VERDICT, text)
        else:
            found(SAME_SIZE if theirs == what else
                  f"size: RDKIT'S SEARCH FINDS ANOTHER SIZE THAN THE FILTER NAMES ({theirs} and {what})",
                  None if theirs == what else text)
        if not at_the_limit(what, second):
            found(f"THE FILTER WITH THE NUMBER {LIMIT} DOES NOT ANSWER AS THE SIZE CALLS FOR THAT IT NAMED WITH THE NUMBER 1", text)
        elif what < LIMIT:
            found(PASSES)
            if theirs is not None and theirs >= LIMIT:
                found(f"THE FILTER HANDS ON A MOL IN WHICH RDKIT'S SEARCH FINDS A GROUP OF {LIMIT} OR MORE", text)
        else:
            found(REFUSED_BY_THE_RULE, text)
    return count, dict(shown)


# ------------------------------------------------------------------------------- other spellings
def other_spellings():
    """For each compound of COMPOUNDS, its spellings, as a list of (the compound, how it is spelled, the
    text): the compound as written, and then the spellings that RDKit makes from its own reading of it. A
    spelling must get the filter's answer for the compound as written, unless hydrogens are written as
    atoms of their own (`examine_spellings`)."""
    out = []
    for compound in COMPOUNDS:
        mol = Chem.MolFromSmiles(compound)
        spellings = [("as written", compound)]
        spellings += [("atoms in a random order", text)
                      for text in Chem.MolToRandomSmilesVect(mol, RANDOM_ORDERS, randomSeed=len(compound))]
        spellings += [("single and double bonds in the place of aromatic ones", Chem.MolToSmiles(mol, kekuleSmiles=True)),
                      ("every hydrogen count in square brackets", Chem.MolToSmiles(mol, allHsExplicit=True)),
                      ("every hydrogen as an atom of its own", Chem.MolToSmiles(Chem.AddHs(mol)))]
        out += [(compound, how, text) for how, text in spellings]
    return out


def examine_spellings():
    """The comparisons for the other spellings. Returns a count of what was found, and examples."""
    count, shown = collections.Counter(), collections.defaultdict(list)

    def found(kind, text=None):
        count[kind] += 1
        if text is not None and len(shown[kind]) < 3:
            shown[kind].append(text)

    spellings = other_spellings()
    texts = [text for _, _, text in spellings] + BY_HAND
    answers, problem = filter_answers(texts)
    if answers is None:
        found(f"THE SECOND PROGRAM GAVE NO ANSWERS FOR THE {len(texts)} OTHER SPELLINGS: {problem}")
        return count, dict(shown)
    as_written = {}
    for (compound, how, text), (answer, _) in zip(spellings, answers):
        kind, what = answer
        theirs = rdkit_size(text)
        if how == "as written":
            as_written[compound] = answer
            found("other spellings: compounds")
            if kind != "sound" or theirs != what:
                found("other spellings: A COMPOUND AS WRITTEN IS NOT SOUND, OR RDKIT'S SEARCH FINDS ANOTHER SIZE", text)
            continue
        found(f"other spellings: {how}")
        if how == "every hydrogen as an atom of its own" and "[H]" in text:
            # another Mol: the filter must refuse it, for the hydrogen atom
            found("other spellings: a hydrogen as an atom of its own: refused as not sound, for an atom that is none of the ten elements"
                  if answer == ("not sound", "atom N is no atom of B, C, N, O, P, S, F, Cl, Br or I")
                  else "other spellings: A HYDROGEN AS AN ATOM OF ITS OWN IS NOT REFUSED AS NOT SOUND", text)
        elif answer == as_written[compound]:
            found("other spellings: the filter answers as for the compound as written")
        else:
            found("other spellings: THE FILTER GIVES ANOTHER ANSWER THAN FOR THE COMPOUND AS WRITTEN", text)
        if kind == "sound" and theirs is not None and theirs > what:
            found("other spellings: THE FILTER NAMES A SMALLER SIZE THAN RDKIT'S SEARCH FINDS", text)
    for text, (answer, _) in zip(BY_HAND, answers[len(spellings):]):
        kind, what = answer
        theirs = rdkit_size(text)
        found("other spellings: written by hand, with a bond symbol : or lowercase symbols at carbon atoms with four bonds")
        if kind == "not sound":
            found("other spellings: written by hand: refused as not sound")
        elif kind == "sound" and theirs is not None and theirs <= what:
            found("other spellings: written by hand: sound, and the size that the filter names is not below RDKit's")
        elif kind == "sound" and theirs is None:
            found("other spellings: written by hand: sound, and RDKit refuses the text")
        else:
            found("other spellings: WRITTEN BY HAND: THE FILTER NAMES A SMALLER SIZE THAN RDKIT'S SEARCH FINDS, OR DOES NOT READ THE TEXT", text)
    return count, dict(shown)


# ------------------------------------------------------------------------------- every isomer
def perfluoroalkyl_groups(n, known={}):
    """Every way to join n carbon atoms into a group without a ring, hung up at the atom where the group
    is attached: that atom has up to three atoms below it, and so has each of them. Each way once, as
    nested tuples: the groups below the first atom. `known` keeps the answers from one call to the
    next."""
    if n not in known:
        ways = set()

        def below(left, room, least):
            # the groups below one atom: at most `room` of them, with `left` atoms in all, in a fixed order
            if left == 0:
                yield ()
            elif room:
                for size in range(1, left + 1):
                    for group in perfluoroalkyl_groups(size):
                        if least is None or (size, group) >= least:
                            for rest in below(left - size, room - 1, (size, group)):
                                yield (group,) + rest

        for parts in below(n - 1, 3, None):
            ways.add(tuple(sorted(parts)))
        known[n] = tuple(sorted(ways))
    return known[n]


def group_text(group):
    """A group as a SMILES text that begins at its attached atom, with a fluorine atom on every free
    place."""
    return "C" + "".join(f"({group_text(part)})" for part in group) + "(F)" * (3 - len(group))


def examine_isomers():
    """The comparisons for every isomer of the perfluoroalkyl acids. Returns a count of what was found,
    and examples."""
    count, shown = collections.Counter(), collections.defaultdict(list)

    def found(kind, text=None):
        count[kind] += 1
        if text is not None and len(shown[kind]) < 3:
            shown[kind].append(text)

    cases = [(n, acid, head + group_text(group)) for n in range(1, LARGEST_GROUP + 1)
             for group in perfluoroalkyl_groups(n) for acid, head in ACIDS]
    for start in range(0, len(cases), TEXTS):
        some = cases[start:start + TEXTS]
        answers, problem = filter_answers([text for _, _, text in some])
        if answers is None:
            found(f"THE SECOND PROGRAM GAVE NO ANSWERS FOR {len(some)} ISOMERS: {problem}", some[0][2])
            continue
        for (n, acid, text), ((kind, what), second) in zip(some, answers):
            found("isomers: perfluoroalkyl groups without a ring, each as a carboxylic acid and as a sulfonic acid")
            if (n, acid) == (7, "carboxylic acid"):
                found("isomers: of these, the isomers of perfluorooctanoic acid")
            if (n, acid) == (8, "sulfonic acid"):
                found("isomers: of these, the isomers of perfluorooctanesulfonic acid")
            theirs = rdkit_size(text)
            if kind != "sound":
                found("isomers: AN ISOMER IS NOT READ, OR ITS MOL IS NOT SOUND", text)
            elif what != n:
                found("isomers: THE FILTER NAMES ANOTHER SIZE THAN THE NUMBER OF CARBON ATOMS OF THE GROUP", text)
            elif theirs != n:
                found("isomers: RDKIT'S SEARCH FINDS ANOTHER SIZE THAN THE NUMBER OF CARBON ATOMS OF THE GROUP", text)
            elif not at_the_limit(what, second):
                found(f"isomers: THE FILTER WITH THE NUMBER {LIMIT} DOES NOT ANSWER AS THE SIZE CALLS FOR", text)
            else:
                found("isomers: the filter and RDKit's search both name the number of carbon atoms of the group")
                if n >= LIMIT:
                    found(f"isomers: of these, refused with the number {LIMIT}, for a group of {LIMIT} or more")
    return count, dict(shown)


# ------------------------------------------------------------------------------- the check
def main():
    limit = sources.limit_of(sys.argv[1:])
    RDLogger.DisableLog("rdApp.*")          # RDKit's own lines about the texts that it refuses
    at_the_start = check_app.built()
    if at_the_start is None:
        return 1
    real = sources.real_texts()
    whole = len(real)
    if limit is not None and limit >= whole:
        print(f"NOT RUN: there are {whole} real texts, so --limit {limit} is no sample. Give no argument for the whole run.")
        return 1
    if limit:
        real = real[::max(1, whole // limit)]
    print(f"Texts: {len(real)} real ones" + (f" of {whole}. This is a sample: at least {limit} texts, evenly spread." if limit else "."))
    workers = sources.workers()             # at most 8, and never more than the threads that the script may use
    print(f"RDKit {Chem.rdBase.rdkitVersion}. {workers} worker{'s' if workers > 1 else ''}.", flush=True)

    count, shown = collections.Counter(), collections.defaultdict(list)
    pieces = [real[i:i + TEXTS] for i in range(0, len(real), TEXTS)]
    with multiprocessing.Pool(workers) as pool:
        for part, examples in pool.imap_unordered(examine, pieces, chunksize=1):
            count += part
            for kind, texts in examples.items():
                shown[kind] += texts
    for examine_more in (examine_spellings, examine_isomers):
        part, examples = examine_more()
        count += part
        for kind, texts in examples.items():
            shown[kind] += texts
    for kind in shown:
        shown[kind] = sorted(shown[kind], key=lambda text: (len(text), text))[:3]

    sections = ["texts that the Lean program", "sound", "size", "the filter", "other spellings", "isomers"]

    def order(kind):
        section = next((i for i, word in enumerate(sections) if kind.startswith(word)), len(sections))
        return section, bool(CAPITALS.search(kind)), -count[kind], kind

    def lines(kind):
        print(f"{count[kind]:8d}  {kind}")
        for text in shown.get(kind, []):
            print(f"              for example: {text[:300]}")

    print()
    for kind in sorted((k for k in count if not k.startswith("    ")), key=order):
        lines(kind)
        # the indented lines: those about the largest group stand under SOUND, the others under NOT_SOUND
        if kind in (SOUND, NOT_SOUND):
            subs = [k for k in count if k.startswith("    ") and ("the largest group" in k) == (kind == SOUND)]
            for sub in sorted(subs, key=lambda k: (-count[k], k)):
                lines(sub)

    short = []
    if limit:
        # ---- a sample: least counts ----
        read, sound = count["texts that the Lean program reads"], count[SOUND]
        floors = [("texts that the Lean program reads", read, 0.95 * len(real)),
                  (SOUND, sound, 0.5 * read),
                  (SAME_SIZE, count[SAME_SIZE], 0.98 * sound),
                  (PASSES, count[PASSES], 0.95 * sound),
                  ("other spellings: the filter answers as for the compound as written",
                   count["other spellings: the filter answers as for the compound as written"],
                   len(COMPOUNDS) * (RANDOM_ORDERS + 2)),
                  ("isomers: the filter and RDKit's search both name the number of carbon atoms of the group",
                   count["isomers: the filter and RDKit's search both name the number of carbon atoms of the group"],
                   2 * sum(len(perfluoroalkyl_groups(n)) for n in range(1, LARGEST_GROUP + 1)))]
        print("\nLeast counts of a sample:")
        for name, value, least in floors:
            ok = value >= least and value > 0
            print(f"{value:8d}  {name} (at least {int(least)})" + ("" if ok else "   TOO FEW"))
            if not ok:
                short.append(name)
    else:
        # ---- all texts: every number is the recorded one ----
        print()
        for kind in sorted(set(count) | set(RECORDED)):
            if count[kind] != RECORDED.get(kind, 0):
                print(f"NOT THE RECORDED NUMBER: {count[kind]}, and {RECORDED.get(kind, 0)} is recorded, for {kind!r}")
                short.append(kind)
        if not short:
            print(f"Every one of the {len(RECORDED)} numbers above is the recorded one.")

    capitals = sorted(kind for kind in count if CAPITALS.search(kind))
    print()
    at_the_end = check_app.checksums()
    changed = [name for name in at_the_start if at_the_start[name] != at_the_end[name]]
    if changed:
        print(f"NOT ONE CHECK: {' and '.join(changed)} changed while the script ran. Run it again.")
        return 1
    if capitals or short:
        print(f"THE CHECK FAILS: {len(capitals)} kind{'' if len(capitals) == 1 else 's'} of finding in capitals above, and "
              f"{len(short)} count{'' if len(short) == 1 else 's'} that {'is' if len(short) == 1 else 'are'} not as "
              f"{'it' if len(short) == 1 else 'they'} must be.")
        return 1
    print("Nothing in capitals. For every real text whose Mol the filter takes for sound and that RDKit reads, RDKit's\n"
          "search finds a largest perfluorinated group of the size that the filter names. The filter hands on no Mol in\n"
          f"which RDKit's search finds a group of {LIMIT} or more. And the filter gives one answer for the spellings of a\n"
          "compound that differ in the order of the atoms, in how aromatic bonds are written, and in whether a\n"
          "hydrogen count stands in square brackets. For every isomer of the perfluoroalkyl carboxylic and sulfonic\n"
          f"acids with a group of 1 to {LARGEST_GROUP} carbon atoms, the filter and RDKit's search both name the number of\n"
          "carbon atoms of the group.")
    if limit:
        print("This was a sample. Run the script without --limit for the whole check.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
