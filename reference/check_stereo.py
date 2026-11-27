"""Check the stereo facts that the model stores, with the reader alone.

    .venv/bin/python -I reference/check_stereo.py               all real texts with stereo marks
    .venv/bin/python -I reference/check_stereo.py --limit 300   a quick look at a sample

What `read` stores for a text is compared with two things outside the model: Open Babel's own record of
what each stereo mark says (part 1), and a measurement on coordinates in space that RDKit builds (part 2).
At the end both parts are tried on two wrong models, on the first 300 texts, and each part must report
every atom and every double bond that it compares in them. reference/README.md, "Reading the output of
`check_stereo.py`", says why this check exists, what each part covers, how to read the report and when the
script fails. The Lean program is not started: `reference/check_app.py` holds it against the model.

The stereo facts (SPEC.md, section 12.1):
  orientation  of an atom. The fourth place comes first: the atom's own hydrogen, or the free place. Then
               the neighbours in increasing atom number. (With four neighbours: all four in increasing atom
               number.) Seen from the first towards the atom, do the other three follow each other
               anticlockwise or clockwise?
  geometry     of a double bond. The lowest-numbered other neighbour at each end: on the same side or not.

Neither part uses anything of the model but `read` (and `tokens_of`, to look for the atoms that rule 9
refuses). The neighbours, their order, the translation and the measurement are worked out here, without the
model's helper `parity`. In the first wrong model that helper gives the opposite answer. In the second,
every stored geometry is exchanged for the other one.

A line in CAPITALS is a failure. The script then ends with exit code 1. The least counts of a whole run,
and the most texts that the model may leave unread, are among the constants below.
"""
import collections
import concurrent.futures
import dataclasses
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
import sources

ATTEMPTS = 200                      # RDKit gives up on a molecule after this many attempts to build coordinates.
                                    # A fixed number, and no limit of time, so that a run does not depend on
                                    # how busy the machine is.
LARGEST = 90                        # texts with more atoms than this, hydrogens not counted, get no coordinates
SAMPLE_FOR_THE_WRONG_MODELS = 300   # texts that are checked again with each wrong model
FEWEST_ATOMS, FEWEST_DOUBLE_BONDS = 14000, 1150     # what a whole run must have compared on coordinates at least
FEWEST_IN_RECORD = (16000, 1200)                    # and with Open Babel's record: atoms, double bonds
MOST_UNREAD = 25                    # a whole run fails if more texts than this are not read by the model
                                    # (22 are not: 5 with two marks in a row, 1 with `*`, and 16 with the
                                    # spelling that rule 9 refuses)
FLAT = 1e-6                         # below this, the measurement at an atom says nothing
WORKERS = sources.workers()         # processes: at most 8, and never more than the script may use

# What is counted. The lines in capitals are the failures.
RECORD_ATOM = "atoms: the model stores the orientation of Open Babel's record"
RECORD_ATOM_WRONG = "ATOMS FOR WHICH THE MODEL STORES THE OTHER ORIENTATION THAN OPEN BABEL'S RECORD"
RECORD_ATOM_ONLY_MODEL = "ATOMS WITH AN ORIENTATION IN THE MODEL AND NONE IN OPEN BABEL'S RECORD"
RECORD_ATOM_ONLY_THEIRS = "ATOMS WITH AN ORIENTATION IN OPEN BABEL'S RECORD AND NONE IN THE MODEL"
RECORD_BOND = "double bonds: the model stores the geometry of Open Babel's record"
RECORD_BOND_WRONG = "DOUBLE BONDS FOR WHICH THE MODEL STORES THE OTHER GEOMETRY THAN OPEN BABEL'S RECORD"
RECORD_BOND_ONLY_MODEL = "DOUBLE BONDS WITH A GEOMETRY IN THE MODEL AND NONE IN OPEN BABEL'S RECORD"
RECORD_BOND_ONLY_THEIRS = "DOUBLE BONDS WITH A GEOMETRY IN OPEN BABEL'S RECORD AND NONE IN THE MODEL"
RECORD_UNREAD = "TEXTS THAT THE MODEL READS AND OPEN BABEL READS WITH ANOTHER NUMBER OF ATOMS, OR NOT AT ALL"
SPACE_ATOM = "atoms compared: the model stores the orientation that was measured"
SPACE_ATOM_WRONG = "ATOMS FOR WHICH THE MODEL STORES THE OTHER ORIENTATION THAN WAS MEASURED"
SPACE_BOND = "double bonds compared: the model stores the geometry that was measured"
SPACE_BOND_WRONG = "DOUBLE BONDS FOR WHICH THE MODEL STORES THE OTHER GEOMETRY THAN WAS MEASURED"
RDKIT_ATOM_ONLY = "ATOMS TO WHICH RDKIT GIVES A LABEL AND FOR WHICH THE MODEL STORES NO ORIENTATION"
RDKIT_BOND_ONLY = "DOUBLE BONDS TO WHICH RDKIT GIVES A LABEL AND FOR WHICH THE MODEL STORES NO GEOMETRY"
FAILURES = (RECORD_ATOM_WRONG, RECORD_ATOM_ONLY_MODEL, RECORD_ATOM_ONLY_THEIRS, RECORD_BOND_WRONG,
            RECORD_BOND_ONLY_MODEL, RECORD_BOND_ONLY_THEIRS, RECORD_UNREAD, SPACE_ATOM_WRONG, SPACE_BOND_WRONG,
            RDKIT_ATOM_ONLY, RDKIT_BOND_ONLY)

UNREAD = "texts that the model does not read (SPEC.md, sections 12.2 and 12.4)"
WITH_COORDINATES = "texts with coordinates"
OTHER_ATOMS = "that RDKit reads with other atoms, or not at all"
TOO_LARGE = f"with more than {LARGEST} atoms, which get no coordinates"
NO_COORDINATES = "for which RDKit builds no coordinates"
WITHOUT = (OTHER_ATOMS, TOO_LARGE, NO_COORDINATES)
ATOMS, BONDS = "atoms with an orientation", "double bonds with a geometry"
NOT_ATOM = ("an atom of section 12.4, where RDKit and Open Babel read mirror images of each other",
            "RDKit gives the atom no label from the text",
            "RDKit's label from the text is not its label from the coordinates",
            "RDKit counts other hydrogens at the atom, or the atom has fewer than three neighbours",
            "the coordinates are flat at the atom")
NOT_BOND = ("RDKit gives the bond no label from the text",
            "RDKit's label from the text is not its label from the coordinates")
FREE_PLACE = "atoms with an orientation and a free place"
FREE_WITHOUT = "of these, in texts without coordinates"
FREE_MEASURED = "of these, measured on coordinates in part 2, with the orientation that the model stores"
FREE_WRONG = "of these, measured on coordinates in part 2, with the other orientation (a failure of part 2)"
FREE_NOT = "of these, not compared: "
OF_RULE_9 = "atoms with a free place, one ring number and only single bonds in a text that the model read (none may be)"
OF_RULE_9_LABEL = "of these, RDKit gives the atom a label, so that the difference shows in its labels"
OF_RULE_9_UNKNOWN = "of these, in a text that RDKit reads with other atoms, so that its label is not known"
ELEMENT_OF_RULE_9 = "their elements: "


# ---------------------------------------------------------------------- part 1: Open Babel's own record
def openbabel_record(text, n):
    """What Open Babel holds after reading the text, in the words of SPEC.md, section 12.1: the orientation
    of each atom and the geometry of each double bond for which it keeps a record. None if it does not read
    the text with `n` atoms."""
    from openbabel import openbabel
    openbabel.obErrorLog.SetOutputLevel(0)
    conversion, m = openbabel.OBConversion(), openbabel.OBMol()
    conversion.SetInFormat("smi")
    if not conversion.ReadString(m, text) or m.NumAtoms() != n:
        return None
    facade = openbabel.OBStereoFacade(m)
    free = openbabel.OBStereo.ImplicitRef % 2 ** 32       # how the record names a hydrogen of the atom or a free place
    orientations, geometries = {}, {}
    for atom in openbabel.OBMolAtomIter(m):
        if not facade.HasTetrahedralStereo(atom.GetId()):
            continue
        config = facade.GetTetrahedralStereo(atom.GetId()).GetConfig()
        if not config.specified:
            continue
        # The record: seen from (or towards) the first place, the three others follow each other clockwise
        # (or anticlockwise). Section 12.1 wants the hydrogen or the free place first and then the atom
        # numbers in increasing order. Each exchange of two places turns the answer round.
        theirs = [config.from_or_towards] + list(config.refs)
        ours = sorted(theirs, key=lambda place: (place != free, place))
        if len(set(theirs)) != 4:
            orientations[atom.GetId()] = "a record without four different places"
            continue
        exchanges = sum(1 for i in range(4) for j in range(i + 1, 4) if ours.index(theirs[i]) > ours.index(theirs[j]))
        clockwise = (config.winding == openbabel.OBStereo.Clockwise) == (config.view == openbabel.OBStereo.ViewFrom)
        if exchanges % 2:
            clockwise = not clockwise
        orientations[atom.GetId()] = "clockwise" if clockwise else "anticlockwise"
    for bond in openbabel.OBMolBondIter(m):
        if not facade.HasCisTransStereo(bond.GetId()):
            continue
        record = facade.GetCisTransStereo(bond.GetId())
        if not record.GetConfig().specified:
            continue
        a, b = sorted((bond.GetBeginAtom().GetId(), bond.GetEndAtom().GetId()))
        near_a = min(x.GetId() for x in openbabel.OBAtomAtomIter(m.GetAtomById(a)) if x.GetId() != b)
        near_b = min(x.GetId() for x in openbabel.OBAtomAtomIter(m.GetAtomById(b)) if x.GetId() != a)
        geometries[(a, b)] = ("sameSide" if record.IsCis(near_a, near_b) else
                              "oppositeSides" if record.IsTrans(near_a, near_b) else "a record that says neither")
    return orientations, geometries


def against_the_record(text, mol, count, differs):
    """Part 1 for one text: what the model stores against Open Babel's record. `count` gets the counts, and
    `differs` a line for each atom or double bond for which the two do not say the same, and for a text
    that Open Babel does not read with as many atoms as the model."""
    record = openbabel_record(text, len(mol.atoms))
    if record is None:
        count[RECORD_UNREAD] += 1
        differs.append(f"{text}: Open Babel does not read it with as many atoms as the model")
        return
    for ours, theirs, right, wrong, only_model, only_theirs, what in (
            ({x.atom: x.orientation for x in mol.orientations}, record[0],
             RECORD_ATOM, RECORD_ATOM_WRONG, RECORD_ATOM_ONLY_MODEL, RECORD_ATOM_ONLY_THEIRS, "atom"),
            ({(x.a, x.b): x.geometry for x in mol.geometries}, record[1],
             RECORD_BOND, RECORD_BOND_WRONG, RECORD_BOND_ONLY_MODEL, RECORD_BOND_ONLY_THEIRS, "bond")):
        for key in sorted(set(ours) | set(theirs)):
            which = (only_model if key not in theirs else only_theirs if key not in ours
                     else right if ours[key] == theirs[key] else wrong)
            count[which] += 1
            if which != right:
                differs.append(f"{text}: {what} {key}, the model stores {ours.get(key)}, Open Babel's record says {theirs.get(key)}")


# ------------------------------------------------------------------------ part 2: coordinates in space
def minus(p, q):
    return (p[0] - q[0], p[1] - q[1], p[2] - q[2])


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def turn(first, centre, a, b, c):
    """Seen from the point `first` towards `centre`: above 0 if a, b and c follow each other anticlockwise,
    below 0 if clockwise, and near 0 if the measurement says nothing."""
    return dot(cross(minus(b, a), minus(c, a)), minus(first, centre))


def opposite_the_neighbours(centre, neighbours):
    """The free place of an atom with three neighbours: the point that lies opposite all three."""
    away = (0.0, 0.0, 0.0)
    for p in neighbours:
        d = minus(p, centre)
        length = dot(d, d) ** 0.5
        away = (away[0] - d[0] / length, away[1] - d[1] / length, away[2] - d[2] / length)
    return (centre[0] + away[0], centre[1] + away[1], centre[2] + away[2])


def ring_numbers_at(text):
    """For each atom, in the order of the text: how many ring numbers are written directly at it."""
    numbers, current = [], None
    for token in model.tokens_of(text):
        if token.kind == "atom":
            numbers.append(0)
            current = len(numbers) - 1
        elif token.kind == "ring" and current is not None:
            numbers[current] += 1
        elif token.kind in ("(", ")", "."):
            current = None
    return numbers


def on_coordinates(text, mol, count, differs):
    """Part 2 for one text: what the model stores against a measurement on coordinates that RDKit builds.
    `count` gets what is compared and what is left out and why, and `differs` a line for each difference."""
    from rdkit import Chem, RDLogger
    from rdkit.Chem import AllChem
    RDLogger.DisableLog("rdApp.*")
    n = len(mol.atoms)
    neighbours = [[] for _ in range(n)]
    for bond in mol.bonds:
        neighbours[bond.a].append(bond.b)
        neighbours[bond.b].append(bond.a)
    neighbours = [sorted(x) for x in neighbours]
    orientation = {x.atom: x.orientation for x in mol.orientations}
    with_orientation = sorted(orientation)
    with_geometry = list(mol.geometries)
    free_place = {i for i in with_orientation if mol.atoms[i].hydrogens == 0 and len(neighbours[i]) == 3}
    written_at = ring_numbers_at(text)
    of_rule_9 = {i for i in free_place
               if written_at[i] == 1 and all(b.order == "single" for b in mol.bonds if i in (b.a, b.b))}
    count[ATOMS] += len(with_orientation)
    count[BONDS] += len(with_geometry)
    count[FREE_PLACE] += len(free_place)
    count[OF_RULE_9] += len(of_rule_9)
    for i in of_rule_9:
        count[ELEMENT_OF_RULE_9 + mol.atoms[i].element] += 1

    def without_coordinates(why):
        count[FREE_WITHOUT] += len(free_place)
        count[f"texts {why}"] += 1
        count[f"{ATOMS}, in texts {why}"] += len(with_orientation)
        count[f"{BONDS}, in texts {why}"] += len(with_geometry)

    parameters = Chem.SmilesParserParams()
    parameters.removeHs = False
    m = Chem.MolFromSmiles(text, parameters)
    if m is None or m.GetNumAtoms() != n or any(a.GetSymbol() != b.element for a, b in zip(m.GetAtoms(), mol.atoms)):
        count[OF_RULE_9_UNKNOWN] += len(of_rule_9)
        return without_coordinates(OTHER_ATOMS)
    Chem.AssignStereochemistry(m, cleanIt=True, force=True)
    label_from_text = {a.GetIdx(): a.GetProp("_CIPCode") for a in m.GetAtoms() if a.HasProp("_CIPCode")}
    form_from_text = {b.GetIdx(): str(b.GetStereo()) for b in m.GetBonds() if str(b.GetStereo()) in ("STEREOE", "STEREOZ")}
    count[OF_RULE_9_LABEL] += sum(1 for i in of_rule_9 if i in label_from_text)
    # Facts that RDKit has and the model does not store. This needs no coordinates.
    stored = {(b.a, b.b) for b in with_geometry}
    for b in m.GetBonds():
        ends = tuple(sorted((b.GetBeginAtomIdx(), b.GetEndAtomIdx())))
        if b.GetIdx() in form_from_text and ends not in stored:
            count[RDKIT_BOND_ONLY] += 1
            differs.append(f"{text}: RDKit gives the bond {ends} a label, and the model stores no geometry for it")
    for i in label_from_text:
        if i not in orientation:
            count[RDKIT_ATOM_ONLY] += 1
            differs.append(f"{text}: RDKit gives atom {i} a label, and the model stores no orientation for it")
    if m.GetNumHeavyAtoms() > LARGEST:
        return without_coordinates(TOO_LARGE)
    with_hydrogens = Chem.AddHs(m)
    how = AllChem.ETKDGv3()
    how.randomSeed = 7
    how.maxIterations = ATTEMPTS
    if AllChem.EmbedMolecule(with_hydrogens, how) != 0:
        return without_coordinates(NO_COORDINATES)
    count[WITH_COORDINATES] += 1
    place = [tuple(with_hydrogens.GetConformer().GetAtomPosition(i)) for i in range(with_hydrogens.GetNumAtoms())]
    from_coordinates = Chem.Mol(with_hydrogens)
    Chem.AssignStereochemistryFrom3D(from_coordinates)
    label_from_coordinates = {a.GetIdx(): a.GetProp("_CIPCode") for a in from_coordinates.GetAtoms() if a.HasProp("_CIPCode")}
    form_from_coordinates = {b.GetIdx(): str(b.GetStereo()) for b in from_coordinates.GetBonds()}

    def not_compared(i, why):
        count["atoms not compared: " + why] += 1
        if i in free_place:
            count[FREE_NOT + why] += 1

    for i in with_orientation:
        atom = mol.atoms[i]
        if i in of_rule_9:
            not_compared(i, NOT_ATOM[0])
            continue
        if i not in label_from_text:
            not_compared(i, NOT_ATOM[1])
            continue
        if label_from_coordinates.get(i) != label_from_text[i]:
            not_compared(i, NOT_ATOM[2])
            continue
        if len(neighbours[i]) == 4:
            first, rest = place[neighbours[i][0]], [place[j] for j in neighbours[i][1:]]
        else:
            rest = [place[j] for j in neighbours[i]]
            own_hydrogens = [x.GetIdx() for x in with_hydrogens.GetAtomWithIdx(i).GetNeighbors() if x.GetIdx() >= n]
            if len(rest) == 3 and atom.hydrogens == 1 and len(own_hydrogens) == 1:
                first = place[own_hydrogens[0]]
            elif len(rest) == 3 and atom.hydrogens == 0 and not own_hydrogens:
                first = opposite_the_neighbours(place[i], rest)
            else:
                not_compared(i, NOT_ATOM[3])
                continue
        value = turn(first, place[i], *rest)
        if abs(value) < FLAT:
            not_compared(i, NOT_ATOM[4])
            continue
        measured = "anticlockwise" if value > 0 else "clockwise"
        if measured == orientation[i]:
            count[SPACE_ATOM] += 1
            if i in free_place:
                count[FREE_MEASURED] += 1
        else:
            count[SPACE_ATOM_WRONG] += 1
            if i in free_place:
                count[FREE_WRONG] += 1
            differs.append(f"{text}: atom {i}, the model stores {orientation[i]}, measured {measured}")

    for bond in with_geometry:
        theirs = m.GetBondBetweenAtoms(bond.a, bond.b)
        if theirs is None or theirs.GetIdx() not in form_from_text:
            count["double bonds not compared: " + NOT_BOND[0]] += 1
            continue
        if form_from_coordinates.get(theirs.GetIdx()) != form_from_text[theirs.GetIdx()]:
            count["double bonds not compared: " + NOT_BOND[1]] += 1
            continue
        near_a = min(x for x in neighbours[bond.a] if x != bond.b)
        near_b = min(x for x in neighbours[bond.b] if x != bond.a)
        axis = minus(place[bond.b], place[bond.a])
        u, v = minus(place[near_a], place[bond.a]), minus(place[near_b], place[bond.b])
        # what is left of u and of v when the part along the double bond is taken away
        u = minus(u, tuple(axis[k] * dot(u, axis) / dot(axis, axis) for k in range(3)))
        v = minus(v, tuple(axis[k] * dot(v, axis) / dot(axis, axis) for k in range(3)))
        measured = "sameSide" if dot(u, v) > 0 else "oppositeSides"
        if measured == bond.geometry:
            count[SPACE_BOND] += 1
        else:
            count[SPACE_BOND_WRONG] += 1
            differs.append(f"{text}: bond {bond.a}-{bond.b}, the model stores {bond.geometry}, measured {measured}")


# ------------------------------------------------------------------------------------------ the run
def check_one(item):
    """One text: what was counted, and up to three places where the model differs."""
    text, wrong = item
    if wrong == "orientation" and not getattr(model, "made_wrong", False):
        # Each worker process has its own copy of the model. It is made wrong once, and the processes of a
        # wrong model are never used for the right one (see `run`).
        right = model.parity
        model.parity = lambda source, target: -right(source, target)
        model.made_wrong = True
    count, differs = collections.Counter(), []
    try:
        mol = model.read(text)
    except model.SmilesError:
        count[UNREAD] += 1
        return count, differs
    if wrong == "geometry":
        other = {"sameSide": "oppositeSides", "oppositeSides": "sameSide"}
        mol = model.Mol(mol.atoms, mol.bonds, mol.orientations,
                        tuple(dataclasses.replace(x, geometry=other[x.geometry]) for x in mol.geometries))
    against_the_record(text, mol, count, differs)
    on_coordinates(text, mol, count, differs)
    return count, differs[:3]


def run(texts, wrong=None, progress=False):
    """Every text, in processes of their own for this model. If one of them dies, the run ends with an error."""
    total, examples = collections.Counter(), []
    with concurrent.futures.ProcessPoolExecutor(WORKERS) as pool:
        for done, (count, differs) in enumerate(pool.map(check_one, [(t, wrong) for t in texts], chunksize=20), 1):
            total.update(count)
            examples += differs[:max(0, 10 - len(examples))]
            if progress and done % 1000 == 0:
                print(f"  ... {done} of {len(texts)} texts", flush=True)
    return total, examples


def main():
    limit = sources.limit_of(sys.argv[1:])
    every = list(dict.fromkeys(t for _, t in sources.corpus() if sources.has_marks(t)))
    texts = every[::max(1, len(every) // limit)] if limit else every
    whole = len(texts) == len(every)
    print(f"Texts: {len(texts)} real ones with stereo marks" + ("" if whole else " (a sample)") + ".", flush=True)

    sample = texts[:SAMPLE_FOR_THE_WRONG_MODELS]
    count, examples = run(texts, progress=True)
    wrong_orientation, _ = run(sample, wrong="orientation")
    wrong_geometry, _ = run(sample, wrong="geometry")
    shown = set()

    def line(what, indent=""):
        shown.add(what)
        print(f"{count[what]:7d}  {indent}{what}")

    def failures(*which):
        for what in which:
            shown.add(what)
            if count[what]:
                print(f"{count[what]:7d}  {what}")

    print("\n=== The texts ===")
    line(UNREAD)
    failures(RECORD_UNREAD)
    for why in WITHOUT:
        line(f"texts {why}")
    line(WITH_COORDINATES)

    print("\n=== Part 1: Open Babel's own record, in every text that the model reads ===")
    line(RECORD_ATOM)
    line(RECORD_BOND)
    failures(RECORD_ATOM_WRONG, RECORD_ATOM_ONLY_MODEL, RECORD_ATOM_ONLY_THEIRS,
             RECORD_BOND_WRONG, RECORD_BOND_ONLY_MODEL, RECORD_BOND_ONLY_THEIRS)

    print("\n=== Part 2: coordinates in space. The atoms with an orientation ===")
    line(ATOMS)
    for why in WITHOUT:
        line(f"{ATOMS}, in texts {why}")
    line(SPACE_ATOM)
    print(f"{count[FREE_MEASURED]:7d}      of these, atoms with a free place")      # the count of FREE_MEASURED, once more
    failures(SPACE_ATOM_WRONG)
    for why in NOT_ATOM:
        line("atoms not compared: " + why)
    failures(RDKIT_ATOM_ONLY)

    print("\n=== Part 2: coordinates in space. The double bonds with a geometry ===")
    line(BONDS)
    for why in WITHOUT:
        line(f"{BONDS}, in texts {why}")
    line(SPACE_BOND)
    failures(SPACE_BOND_WRONG)
    for why in NOT_BOND:
        line("double bonds not compared: " + why)
    failures(RDKIT_BOND_ONLY)

    print("\n=== The atoms with an orientation and a free place, in every text that the model reads ===")
    line(FREE_PLACE)
    line(FREE_WITHOUT, "  ")
    line(FREE_MEASURED, "  ")
    line(FREE_WRONG, "  ")
    for why in NOT_ATOM:
        line(FREE_NOT + why, "  ")

    print("\n=== Among them, the atoms of the spelling that rule 9 refuses (SPEC.md, section 12.2): none may be read ===")
    line(OF_RULE_9)
    for what in sorted(w for w in count if w.startswith(ELEMENT_OF_RULE_9)):
        line(what, "  ")
    line(OF_RULE_9_LABEL, "  ")
    line(OF_RULE_9_UNKNOWN, "  ")

    alarms = sum(count[what] for what in FAILURES)
    if count[OF_RULE_9]:
        print(f"{count[OF_RULE_9]:7d}  ATOMS OF THE SPELLING THAT RULE 9 REFUSES STAND IN A MOL THAT THE MODEL READ")
        alarms += count[OF_RULE_9]
    for example in examples:
        print("      " + example)
    left_over = sorted(set(count) - shown)
    for what in left_over:
        print(f"{count[what]:7d}  A COUNT THAT NO LINE ABOVE SHOWS: {what}")
    alarms += len(left_over)

    # Every atom and every double bond must stand in exactly one line of part 2, and in part 1.
    atoms_in_lines = (sum(count[f"{ATOMS}, in texts {why}"] for why in WITHOUT) + count[SPACE_ATOM] + count[SPACE_ATOM_WRONG]
                      + sum(count["atoms not compared: " + why] for why in NOT_ATOM))
    bonds_in_lines = (sum(count[f"{BONDS}, in texts {why}"] for why in WITHOUT) + count[SPACE_BOND] + count[SPACE_BOND_WRONG]
                      + sum(count["double bonds not compared: " + why] for why in NOT_BOND))
    atoms_in_record = count[RECORD_ATOM] + count[RECORD_ATOM_WRONG] + count[RECORD_ATOM_ONLY_MODEL]
    bonds_in_record = count[RECORD_BOND] + count[RECORD_BOND_WRONG] + count[RECORD_BOND_ONLY_MODEL]
    if (atoms_in_lines, bonds_in_lines) != (count[ATOMS], count[BONDS]) or (
            not count[RECORD_UNREAD] and (atoms_in_record, bonds_in_record) != (count[ATOMS], count[BONDS])):
        print(f"\nTHE LINES DO NOT ADD UP: {count[ATOMS]} atoms and {count[BONDS]} double bonds have a stereo fact; the lines "
              f"of part 2 hold {atoms_in_lines} and {bonds_in_lines}, those of part 1 {atoms_in_record} and {bonds_in_record}.")
        alarms += 1
    free_in_lines = (count[FREE_WITHOUT] + count[FREE_MEASURED] + count[FREE_WRONG]
                     + sum(count[FREE_NOT + why] for why in NOT_ATOM))
    if free_in_lines != count[FREE_PLACE]:
        print(f"\nTHE LINES ABOUT THE ATOMS WITH A FREE PLACE HOLD {free_in_lines} ATOMS, NOT {count[FREE_PLACE]}.")
        alarms += 1
    if whole and count[UNREAD] > MOST_UNREAD:
        print(f"\nTHE MODEL DOES NOT READ {count[UNREAD]} OF THE TEXTS, WHERE A WHOLE RUN ALLOWS {MOST_UNREAD} AT MOST.")
        alarms += 1
    if whole and (count[RECORD_ATOM] < FEWEST_IN_RECORD[0] or count[RECORD_BOND] < FEWEST_IN_RECORD[1]):
        print(f"\nTOO LITTLE WAS COMPARED WITH OPEN BABEL'S RECORD: {count[RECORD_ATOM]} atoms and {count[RECORD_BOND]} double bonds, "
              f"where a whole run must compare at least {FEWEST_IN_RECORD[0]} and {FEWEST_IN_RECORD[1]}.")
        alarms += 1
    if whole and (count[SPACE_ATOM] < FEWEST_ATOMS or count[SPACE_BOND] < FEWEST_DOUBLE_BONDS):
        print(f"\nTOO LITTLE WAS COMPARED ON COORDINATES: {count[SPACE_ATOM]} atoms and {count[SPACE_BOND]} double bonds, "
              f"where a whole run must compare at least {FEWEST_ATOMS} and {FEWEST_DOUBLE_BONDS}.")
        alarms += 1
    if count[RECORD_ATOM] == 0 or count[RECORD_BOND] == 0 or count[SPACE_ATOM] == 0 or count[SPACE_BOND] == 0:
        print("\nA PART OF THE CHECK COMPARED NOTHING.")
        alarms += 1

    print(f"\n=== Two wrong models, each on the first {len(sample)} texts ===")
    rows = (("the other orientation is read", wrong_orientation, "atoms", RECORD_ATOM_WRONG, RECORD_ATOM, SPACE_ATOM_WRONG, SPACE_ATOM),
            ("the other geometry is stored", wrong_geometry, "double bonds", RECORD_BOND_WRONG, RECORD_BOND, SPACE_BOND_WRONG, SPACE_BOND))
    for name, counted, things, record_reported, record_missed, space_reported, space_missed in rows:
        print(f"{counted[record_reported]:7d}  {name}: {things} that part 1 reports")
        print(f"{counted[record_missed]:7d}  {name}: {things} that part 1 compares and does not report")
        print(f"{counted[space_reported]:7d}  {name}: {things} that part 2 reports")
        print(f"{counted[space_missed]:7d}  {name}: {things} that part 2 compares and does not report")
        if not counted[record_reported] or counted[record_missed] or not counted[space_reported] or counted[space_missed]:
            print(f"THE CHECK DOES NOT REPORT ALL {things.upper()} OF THE WRONG MODEL IN WHICH {name.upper()}.")
            alarms += 1

    print("\n" + (f"{alarms} FINDINGS IN CAPITALS." if alarms
                  else "Nothing in capitals: the model stores what Open Babel's record says, and what was measured "
                       "on coordinates, for every atom and every double bond that was compared."))
    return 1 if alarms else 0


if __name__ == "__main__":
    sys.exit(main())
