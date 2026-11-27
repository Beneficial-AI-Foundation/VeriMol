"""Check the chosen form of the model (SPEC.md, section 3.2), with as little of the model as possible.

    .venv/bin/python -I reference/check_canonical.py               all real texts that the model reads
    .venv/bin/python -I reference/check_canonical.py --limit 2000  a quick look at a sample

The chosen form of a Mol is the same molecule with its atoms in one chosen order, the same for every
numbering of the molecule. The command `canonical` writes it. The key of a numbering is written out here
again, straight from SPEC.md, and a Mol is renumbered by the function of test_cases.py, which is written out
by the rule for a stored mark and uses no function of the model; the search is the model's. For every real
text that the model reads:

  A  the definition   For a Mol of at most 7 atoms, the key of every numbering is worked out, one by one.
                      The chosen form must have the least of these keys, and every numbering with that key
                      must give the same Mol.
  B  numbering        The same molecule with its atoms renumbered at random must get the same chosen form.
  C  spelling         A random spelling of the molecule by RDKit must get the same chosen form. Left out
                      where the spelling has other atoms or bonds, or fewer stereo marks, than the text,
                      and where RDKit itself, with its clean-up on, takes the spelling for another
                      arrangement in space than the text.
  D  the text         The chosen text is read back as the chosen form, which has the atoms and the bonds of
                      the Mol and is its own chosen form. And the chosen text has no dot inside a piece of
                      the molecule.
  E  other molecules  Two texts must get the same chosen text exactly when RDKit, with its clean-up off and
                      with every hydrogen made an atom of its own, gives what `rewrite` writes for them the
                      same canonical text. And a wrong answer is made on purpose: the same Mol with one
                      hydrogen fewer must get another canonical text from RDKit.
  F  near the limit   Twenty made-up texts, each renumbered at random ten times. The answer must be the
                      same for every numbering: the same chosen form, or the search gives up each time.

At the end, A to C are tried on five wrong searches, on the first 3,000 texts. Each must be reported by
each of A, B and C.

reference/README.md, "Reading the output of `check_canonical.py`", says more about each letter and about
the wrong searches, when the script fails, and what the check does not show. A line in CAPITALS is a
failure. The script then ends with exit code 1. The least counts of a whole run are among the constants
below.
"""
import collections
import concurrent.futures
import itertools
import random
import sys
import zlib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
import others
import sources
from test_cases import renumbered       # a Mol with its atoms in a new order, without a function of the model

SMALL = 7                           # a Mol with at most this many atoms gets the key of every numbering worked out
SAMPLE_FOR_THE_WRONG_SEARCHES = 3000
FEWEST_REPORTS = 10                 # a wrong search must be reported at least so often by each of A, B and C
# What counts as "checked" under each letter: the line that says that a comparison was made and came
# out right. A text that a part leaves out is not a text that it checked.
CHECKED = {"A": f"A  Mols of at most {SMALL} atoms: the chosen form has the least key of all numberings, and every numbering with that key gives it",
           "B": "B  renumbered at random: the same chosen form",
           "C": "C  a random spelling by RDKit: the same chosen form",
           "D": "D  the chosen text is read as the chosen form, which has the atoms and bonds of the Mol and is its own chosen form"}
FEWEST_IN_GROUPS = 61000            # what a whole run must have sorted into groups under E at least
ON_PURPOSE = "E  wrong on purpose, the Mol with one hydrogen fewer: RDKit's canonical text is another one"
FEWEST_ON_PURPOSE = 61000           # so often a whole run must have made that wrong answer and seen it noticed
NUMBERINGS = 10                     # so often each text of part F is renumbered
WORKERS = sources.workers()         # processes: at most 8, and never more than the script may use
# Part F: texts for which the search holds many beginnings. SPEC.md, section 3.2, works out the numbers
# for the molecules of ethane and for the rings beside alanine.
NEAR_THE_LIMIT = [
    ".".join(["CC"] * 9), ".".join(["CC"] * 10),                # 630 beginnings, and 1,260
    ".".join(["CCO"] * 9), ".".join(["CCO"] * 10),              # the same with molecules that have no twins
    ".".join(["C1CCC1"] * 8), ".".join(["C1CCC1"] * 9),         # rings of four: each can be walked in two ways
    "C1CCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O",                 # stereo facts: nothing is alike, exactly 1,000
    "C1CCCCC1.N1NNNN1.O1OOOO1.N[C@@H](C)C(=O)O",                # 1,200
    "C1CCCCC1.N1NNNN1.O1OOOO1", "C1CCCCC1.N1NNNNNN1.O1OOOS1",   # the same rings without stereo facts
    "OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO", "c1ccccc1P(c1ccccc1)c1ccccc1", "CCN(CC)CC",
    "N[Co+3](N)(N)(N)(N)N.Cl[Hg](Cl)Cl", "F/C=C/F.F/C=C/F.F/C=C/F.F/C=C/F",
    "C1CCCCC1.N1NNNNNN1.O1OOOS1.N[C@@H](C)C(=O)O",              # 1,008 on the way, and 336 at the end
    "CC.CC.CC.CC.CC.CC.C[C@H](N)O", "CC.CC.CC.CC.CC.C[C@H](N)O",    # 1,080, and 240
    "[N][N][N]1[N][N][N][N]1", "C=1=[C](=[C])[C]1",             # the two small examples of SPEC.md, section 3.2
]


# ------------------------------------------------------------ the definition of SPEC.md, written out here
BOND_CODE = {"quadruple": 0, "triple": 1, "double": 2, "aromatic": 3, "single": 4, None: 5}


def stereo_code(mol):
    """The stereo facts of a Mol as numbers (SPEC.md, section 3.2): for every atom 0, 1 or 2 (no
    orientation, anticlockwise, clockwise), then for every bond 0, 1 or 2 (no geometry, the same side,
    opposite sides)."""
    orientation = {x.atom: 1 if x.orientation == "anticlockwise" else 2 for x in mol.orientations}
    geometry = {(x.a, x.b): 1 if x.geometry == "sameSide" else 2 for x in mol.geometries}
    return (tuple(orientation.get(i, 0) for i in range(len(mol.atoms)))
            + tuple(geometry.get((b.a, b.b), 0) for b in mol.bonds))


def key_of(mol, order):
    """The key of a numbering (SPEC.md, section 3.2): one entry for every place. The entry says how the
    atom at the place is bonded to the atoms at the places before it, the nearest place first, and then
    what the atom is. For a Mol with stereo facts the entry of the last place says after that the stereo
    facts of the Mol as it is numbered then. (`order` may be the beginning of a numbering: the wrong
    searches below ask for the entries of a beginning.)"""
    between = {}
    for b in mol.bonds:
        between[(b.a, b.b)] = between[(b.b, b.a)] = b.order
    key = []
    for place, atom in enumerate(order):
        a = mol.atoms[atom]
        key.append(tuple(BOND_CODE[between.get((order[before], atom))] for before in range(place - 1, -1, -1))
                   + (model.ELEMENTS.index(a.element),
                      9 - a.hydrogens if a.hydrogens <= 9 else a.hydrogens,
                      0 if a.isotope is None else a.isotope + 1,
                      2 * abs(a.charge) - 1 if a.charge < 0 else 2 * abs(a.charge)))
    if (mol.orientations or mol.geometries) and len(order) == len(mol.atoms):
        key[-1] += stereo_code(renumbered(mol, order))
    return key


def bags(mol):
    """The atoms and the bonds of a Mol without their numbers."""
    def kind(i):
        a = mol.atoms[i]
        return (a.element, a.isotope, a.charge, a.hydrogens)
    return (collections.Counter(kind(i) for i in range(len(mol.atoms))),
            collections.Counter((tuple(sorted((kind(b.a), kind(b.b)), key=str)), b.order) for b in mol.bonds))


# -------------------------------------------------------------------------------- five wrong searches
def first_only(mol):
    """Wrong: keeps only the first of the least beginnings."""
    n, order = len(mol.atoms), []
    for _ in range(n):
        order.append(min((a for a in range(n) if a not in order), key=lambda a: key_of(mol, order + [a])[-1]))
    return order


def as_numbered(mol):
    """Wrong: the atoms stay as they are numbered."""
    return list(range(len(mol.atoms)))


def atoms_only(mol):
    """Wrong: sorts the atoms by what they are and does not look at the bonds."""
    return sorted(range(len(mol.atoms)), key=lambda a: key_of(mol, [a])[0])


def with_a_wrong_rule(mol, twins_by_the_atom_alone, alike_by_the_atoms_placed):
    """The search of SPEC.md, section 3.2, written here apart from the model's search, with one of its two
    rules made wrong.

    With `twins_by_the_atom_alone`, two atoms count as twins as soon as they have the same element,
    isotope, charge and hydrogens. Without it they must also be bonded to every third atom alike. That
    is the rule of SPEC.md for a Mol without stereo facts only: nothing here asks whether an atom takes
    part in a stereo fact.

    With `alike_by_the_atoms_placed`, two beginnings count as alike as soon as they have placed the same
    atoms, and only the first of them is held. Without it this search has no rule for beginnings that
    are alike, and holds every beginning with the least entry.

    The entry of the last place leaves the stereo facts out."""
    n = len(mol.atoms)
    between = {}
    for b in mol.bonds:
        between[(b.a, b.b)] = between[(b.b, b.a)] = b.order
    what = [key_of(mol, [a])[0] for a in range(n)]
    smaller = [[b for b in range(a) if mol.atoms[a] == mol.atoms[b] and (
                    twins_by_the_atom_alone
                    or all(between.get((a, x)) == between.get((b, x)) for x in range(n) if x not in (a, b)))]
               for a in range(n)]
    held = [[]]
    for _ in range(n):
        extended = []
        for beginning in held:
            for a in range(n):
                if a not in beginning:
                    waiting = 1 if any(b not in beginning for b in smaller[a]) else 0
                    entry = tuple(BOND_CODE[between.get((before, a))] for before in reversed(beginning)) + what[a]
                    extended.append(((entry, waiting), beginning + [a]))
        least = min(entry for entry, _ in extended)
        placed, held = set(), []
        for entry, order in extended:
            if entry == least:
                if alike_by_the_atoms_placed:
                    if frozenset(order) in placed:
                        continue
                    placed.add(frozenset(order))
                held.append(order)
        if len(held) > 1000:
            return None
    return held[0]


def twins_too_easily(mol):
    """Wrong: the search of SPEC.md with a wrong rule for twins. Two atoms count as twins as soon as they
    have the same element, isotope, charge and hydrogens, whatever they are bonded to. (`with_a_wrong_rule`
    says what else this search leaves out.)"""
    return with_a_wrong_rule(mol, twins_by_the_atom_alone=True, alike_by_the_atoms_placed=False)


def alike_too_easily(mol):
    """Wrong: the search of SPEC.md with a wrong rule for beginnings that are alike. Two beginnings count as
    alike as soon as they have placed the same atoms, however the atoms that are still to come are bonded to
    them. A Mol with stereo facts has no such rule, so there the model's search is asked."""
    if mol.orientations or mol.geometries:
        return model.chosen_order(mol)
    return with_a_wrong_rule(mol, twins_by_the_atom_alone=False, alike_by_the_atoms_placed=True)


SEARCHES = {None: model.chosen_order, "first only": first_only, "as numbered": as_numbered, "atoms only": atoms_only,
            "twins too easily": twins_too_easily, "alike too easily": alike_too_easily}


def near_the_limit(text):
    """Part F for one text: is the answer of the search the same for the Mol and for ten random
    numberings of it? Returns the text, whether the search gives up for the Mol, and whether all agree."""
    mol = model.read(text)
    order = model.chosen_order(mol)
    chosen = None if order is None else renumbered(mol, order)
    rng = random.Random(zlib.crc32(text.encode()))
    agree = True
    for _ in range(NUMBERINGS):
        shuffled = list(range(len(mol.atoms)))
        rng.shuffle(shuffled)
        other = renumbered(mol, shuffled)
        again = model.chosen_order(other)
        if (again is None) != (order is None) or (again is not None and renumbered(other, again) != chosen):
            agree = False
    return text, order is None, agree


# ---------------------------------------------------------------------------------------- one text
def examine(item):
    """Parts A to E for one text, with the model's search or with the wrong search that `which` names (part
    D for the model's search only). Returns the text, its chosen text, RDKit's canonical text for the groups
    of part E (each of the two None where there is none), a count of what was found, and examples of what
    failed."""
    text, which = item
    search = SEARCHES[which]
    from rdkit import Chem              # its log is switched off already, by others.py
    count, examples = collections.Counter(), []
    mol = model.read(text)
    n = len(mol.atoms)
    rng = random.Random(zlib.crc32(text.encode()))
    shuffled = list(range(n))
    rng.shuffle(shuffled)
    other = renumbered(mol, shuffled)
    order = search(mol)

    def fail(what, example):
        count[what] += 1
        examples.append(f"{what}: {example}")

    stereo = "with" if model.has_stereo(mol) else "without"
    if order is None:
        count["texts on which the search gives up"] += 1
        count[f"texts on which the search gives up: Mols {stereo} stereo facts"] += 1
        return text, None, None, count, examples
    chosen = renumbered(mol, order)
    try:
        written = model.write(chosen)
    except model.WriteError as e:
        count[f"texts whose chosen form the writer refuses ({e})"] += 1
        return text, None, None, count, examples
    count["texts with a chosen text"] += 1
    count[f"texts with a chosen text: Mols {stereo} stereo facts"] += 1

    # A: the definition, for small Mols
    if n <= SMALL:
        keys = {permutation: key_of(mol, permutation) for permutation in itertools.permutations(range(n))}
        least = min(keys.values())
        forms = {renumbered(mol, list(p)) for p, key in keys.items() if key == least}
        if key_of(mol, order) == least and forms == {chosen}:
            count[CHECKED["A"]] += 1
        else:
            fail("A  THE CHOSEN FORM DOES NOT HAVE THE LEAST KEY, OR ANOTHER MOL HAS IT TOO", text)

    # B: another numbering
    again = search(other)
    if again is not None and renumbered(other, again) == chosen:
        count[CHECKED["B"]] += 1
    else:
        fail("B  RENUMBERED AT RANDOM: ANOTHER CHOSEN FORM, OR NONE", text)

    # E: RDKit's own canonical text for the Mol, as `rewrite` spells it, with every hydrogen made an atom
    # of its own first
    canonical_of_rdkit = None
    try:
        rewritten = model.write(mol)
    except model.WriteError:
        rewritten = None
    facts = (len(mol.orientations), len(mol.geometries))
    if rewritten is not None and others.rdkit_mol(rewritten) == others.without_stereo(mol):
        canonical_of_rdkit = others.rdkit_canonical_with_hydrogens(rewritten)
        # A wrong answer on purpose: the same Mol with one hydrogen fewer. RDKit's canonical text must be
        # another one. The plain spelling writes the hydrogens of every atom, so one is taken away there.
        try:
            fewer = others.one_hydrogen_fewer(model.write_plain(mol))[0]
        except model.WriteError:
            fewer = None
        if fewer is not None and canonical_of_rdkit is not None:
            of_fewer = others.rdkit_canonical_with_hydrogens(fewer)
            if of_fewer is None:
                fail("E  WRONG ON PURPOSE, THE MOL WITH ONE HYDROGEN FEWER: RDKIT DOES NOT READ ITS TEXT", text)
            elif of_fewer == canonical_of_rdkit:
                fail("E  WRONG ON PURPOSE, THE MOL WITH ONE HYDROGEN FEWER: RDKIT'S CANONICAL TEXT IS THE SAME", text)
            else:
                count[ON_PURPOSE] += 1
                if others.rdkit_canonical_as_read(fewer) == others.rdkit_canonical_as_read(rewritten):
                    count["E  wrong on purpose, the Mol with one hydrogen fewer: RDKit's canonical text would be the same if the hydrogens were not made atoms"] += 1
        if canonical_of_rdkit is None:
            count["E  texts that hold the mass number which marks a counted hydrogen here: left out of the groups"] += 1
        elif model.has_stereo(mol):
            # RDKit's canonical text must hold as many stereo marks as the Mol has stereo facts. The model
            # counts them: it reads RDKit's canonical text.
            try:
                kept = model.read(canonical_of_rdkit)
                kept = (len(kept.orientations), len(kept.geometries))
            except model.SmilesError:
                kept = None
            if kept != facts:
                count["E  texts with stereo marks of which RDKit's canonical text keeps fewer, or which the model does not read: left out of the groups"] += 1
                canonical_of_rdkit = None
    else:
        count["E  texts whose rewritten text RDKit does not read as the Mol: left out of the groups"] += 1

    # C: another spelling, by RDKit
    theirs = Chem.MolFromSmiles(text, sanitize=False)
    if theirs is not None and others.rdkit_mol(text) == others.without_stereo(mol):
        theirs.UpdatePropertyCache(strict=False)
        spelling = Chem.MolToRandomSmilesVect(theirs, 1, randomSeed=zlib.crc32(text.encode()) % 100000 + 1)[0]
        respelt = model.read_or_none(spelling)
        if respelt is None:
            count["C  a random spelling by RDKit that the model does not read"] += 1
        elif bags(respelt) != bags(mol):
            count["C  a random spelling by RDKit with other atoms or bonds than the text"] += 1
        elif (len(respelt.orientations), len(respelt.geometries)) != facts:
            count["C  a random spelling by RDKit with fewer stereo marks than the text"] += 1
        else:
            again = search(respelt)
            if again is not None and renumbered(respelt, again) == chosen:
                count[CHECKED["C"]] += 1
            elif which is None and model.has_stereo(mol) and others.same_molecule(text, spelling) == "stereo differs":
                # RDKit made the spelling with its clean-up off. With its clean-up on it takes the spelling
                # for another arrangement in space than the text.
                count["C  a random spelling by RDKit that RDKit itself, with its clean-up on, takes for another arrangement in space"] += 1
            else:
                fail("C  A RANDOM SPELLING BY RDKIT: ANOTHER CHOSEN FORM, OR NONE", f"{text}   respelt: {spelling}")
    else:
        count["C  texts that RDKit reads as another Mol than the model, or not at all: no spelling of RDKit is tried"] += 1

    # D: the text, and the chosen form itself
    if which is None:
        same_atoms_and_bonds = (bags(chosen) == bags(mol) and sorted(order) == list(range(n))
                                and (len(chosen.orientations), len(chosen.geometries)) == facts
                                and model.is_well_formed(chosen))
        back = model.read(written)
        own = search(chosen)
        if back == chosen and same_atoms_and_bonds and own is not None and renumbered(chosen, own) == chosen:
            count[CHECKED["D"]] += 1
        else:
            fail("D  THE CHOSEN TEXT OR THE CHOSEN FORM IS NOT RIGHT IN ITSELF", f"{text}   chosen text: {written}")
        # The spelling with round brackets can put a dot inside a piece of the molecule (SPEC.md, section
        # 9.2). SPEC.md, section 3.2, says that none of the chosen texts of the real texts has one. One
        # that had would be reported here.
        if written.count(".") == max(others.pieces(chosen) - 1, 0):
            count["D  the chosen text has no dot inside a piece of the molecule"] += 1
        else:
            fail("D  THE CHOSEN TEXT HAS A DOT INSIDE A PIECE OF THE MOLECULE", f"{text}   chosen text: {written}")
        if written == text:
            count["texts that are their own chosen text"] += 1
    return text, written, canonical_of_rdkit, count, examples


def run(texts, which=None, progress=False):
    """Every text, in processes of their own. If one of them dies, the run ends with an error."""
    total, examples, by_chosen, by_rdkit = collections.Counter(), [], collections.defaultdict(set), collections.defaultdict(set)
    gave_up = []
    with concurrent.futures.ProcessPoolExecutor(WORKERS) as pool:
        for done, (text, written, theirs, count, found) in enumerate(pool.map(examine, [(t, which) for t in texts], chunksize=50), 1):
            total.update(count)
            examples += found[:max(0, 12 - len(examples))]
            if written is not None and theirs is not None:
                by_chosen[written].add(text)
                by_rdkit[theirs].add(text)
            if count["texts on which the search gives up"]:
                gave_up.append(text)
            if progress and done % 10000 == 0:
                print(f"  ... {done} of {len(texts)} texts", flush=True)
        if which is None and gave_up:
            smallest = min(gave_up, key=lambda text: (len(model.read(text).atoms), len(text), text))
            of_what = "of this sample " if len(sys.argv) > 1 else ""
            examples.append(f"the smallest text {of_what}on which the search gives up "
                            f"({len(model.read(smallest).atoms)} atoms): {smallest}")
    return total, examples, {frozenset(g) for g in by_chosen.values()}, {frozenset(g) for g in by_rdkit.values()}


def main():
    limit = sources.limit_of(sys.argv[1:])
    every = []
    for _, text in sources.corpus():
        try:
            model.read(text)
        except model.SmilesError:
            continue
        every.append(text)
    every = list(dict.fromkeys(every))
    texts = every[::max(1, len(every) // limit)] if limit else every
    whole = len(texts) == len(every)
    print(f"Texts: {len(texts)} real ones that the model reads" + ("" if whole else " (a sample)") + ".", flush=True)

    count, examples, ours, theirs = run(texts, progress=True)
    print("\n=== The chosen form of the model ===")
    for what in sorted(count):
        print(f"{count[what]:7d}  {what}")
    in_groups = sum(len(g) for g in ours)
    print(f"{in_groups:7d}  E  texts sorted into groups: {len(ours)} groups by chosen text, {len(theirs)} groups by RDKit's canonical text of the rewritten text, with every hydrogen made an atom of its own")
    differing = ours ^ theirs
    alarms = sum(v for what, v in count.items() if what.isupper() or what[3:].isupper())
    if differing:
        print(f"{len(differing):7d}  E  GROUPS THAT ONLY ONE OF THE TWO WAYS GIVES")
        for group in sorted(differing, key=sorted)[:4]:
            print("      " + "   ".join(sorted(group))[:300])
        alarms += len(differing)
    else:
        print(f"{len(ours):7d}  E  the groups are the same in both ways; groups with more than one text: {sum(1 for g in ours if len(g) > 1)}")
    for example in examples:
        print("      " + example[:300])
    # B, C and D are made for every text with a chosen text; nine in ten of them must have been
    # compared. A is made for the Mols of at most 7 atoms: at least one, and in a whole run 1,000.
    with_chosen_text = count["texts with a chosen text"]
    for letter in "ABCD":
        least = (1000 if whole else 1) if letter == "A" else max(1, (9 * with_chosen_text) // 10)
        if count[CHECKED[letter]] < least:
            print(f"\nNOTHING, OR TOO LITTLE, WAS CHECKED UNDER {letter}: {count[CHECKED[letter]]} TEXTS WERE COMPARED, AND AT LEAST {least} ARE EXPECTED.")
            alarms += 1
    if in_groups == 0 or (whole and in_groups < FEWEST_IN_GROUPS):
        print(f"\nTOO FEW TEXTS WERE SORTED INTO GROUPS UNDER E: {in_groups}"
              + (f", WHERE A WHOLE RUN MUST SORT AT LEAST {FEWEST_IN_GROUPS}." if whole else "."))
        alarms += 1
    if count[ON_PURPOSE] == 0 or (whole and count[ON_PURPOSE] < FEWEST_ON_PURPOSE):
        print(f"\nTHE WRONG ANSWER ON PURPOSE UNDER E WAS NOTICED TOO SELDOM: {count[ON_PURPOSE]} TIMES"
              + (f", WHERE A WHOLE RUN MUST REACH {FEWEST_ON_PURPOSE}." if whole else "."))
        alarms += 1
    if whole and count["texts on which the search gives up"]:
        print(f"\nTHE SEARCH GIVES UP FOR {count['texts on which the search gives up']} REAL TEXTS: SPEC.MD, SECTION 3.2, SAYS FOR NONE.")
        alarms += 1

    print(f"\n=== F  Made-up texts near the limit of the search, each as it is and renumbered at random {NUMBERINGS} times ===")
    with concurrent.futures.ProcessPoolExecutor(WORKERS) as pool:
        outcomes = list(pool.map(near_the_limit, NEAR_THE_LIMIT))
    for text, gives_up, agree in outcomes:
        answer = "the search gives up" if gives_up else "a chosen form"
        print(f"   {'the same answer for every numbering: ' + answer if agree else 'NOT THE SAME ANSWER FOR EVERY NUMBERING'}:  {text[:90]}")
        alarms += not agree
    for gives_up, name in ((False, "A CHOSEN FORM"), (True, "A SEARCH THAT GIVES UP")):
        if sum(1 for _, g, _ in outcomes if g == gives_up) < 3:
            print(f"FEWER THAN 3 TEXTS OF PART F HAVE {name}.")
            alarms += 1

    sample = texts[:SAMPLE_FOR_THE_WRONG_SEARCHES]
    print(f"\n=== Five wrong searches, each on the first {len(sample)} texts ===")
    for which in ("first only", "as numbered", "atoms only", "twins too easily", "alike too easily"):
        wrong, _, _, _ = run(sample, which)
        reported = {letter: sum(v for what, v in wrong.items() if what.startswith(letter + "  ") and what[3:].isupper()) for letter in "ABC"}
        print(f"   {which:16s} reported: " + ", ".join(f"{letter} {n}" for letter, n in reported.items()))
        # Each part must report it by itself. On a sample, where few small Mols are among the texts,
        # one report of each part is asked for.
        least = FEWEST_REPORTS if whole else 1
        for letter, n in reported.items():
            if n < least:
                print(f"THE WRONG SEARCH \"{which.upper()}\" IS REPORTED FEWER THAN {least} TIMES UNDER {letter}.")
                alarms += 1

    print("\n" + (f"{alarms} FINDINGS IN CAPITALS." if alarms else
                  f"Nothing in capitals: for every Mol of at most {SMALL} atoms the chosen form is the one of the "
                  "definition; it is the same for every numbering and spelling that was tried, and it puts the "
                  "texts into the groups of RDKit. Near its limit the search gives the same answer for every "
                  "numbering that was tried."))
    return 1 if alarms else 0


if __name__ == "__main__":
    sys.exit(main())
