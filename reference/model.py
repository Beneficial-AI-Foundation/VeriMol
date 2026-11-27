"""SPEC.md as a Python program.

This file follows SPEC.md rule by rule. It is NOT the program of this project: that one is written in
Lean. It is a second way of working out what SPEC.md demands, so that the Lean program can be compared
with it text by text. It is not an independent one: both were written from the same SPEC.md by the same
AI coding assistant, so a misreading that both share shows no mismatch (reference/README.md, "What
agreement with the model shows, and what it does not"). Agreement with it is a test, not a proof.

Each of these prints what `app` must print for the same arguments:

    .venv/bin/python -I reference/model.py 'CC(=O)O'
    .venv/bin/python -I reference/model.py rewrite 'CC(=O)O'
    .venv/bin/python -I reference/model.py plain 'CC(=O)O'
    .venv/bin/python -I reference/model.py canonical 'OCC'
    .venv/bin/python -I reference/model.py filter perfluoro 6 'CC(=O)O'

Section numbers in the comments are those of SPEC.md.
"""
import sys
from dataclasses import dataclass
from typing import Optional

ELEMENTS = ("H He Li Be B C N O F Ne Na Mg Al Si P S Cl Ar K Ca Sc Ti V Cr Mn Fe Co Ni Cu Zn Ga Ge As Se Br Kr "
            "Rb Sr Y Zr Nb Mo Tc Ru Rh Pd Ag Cd In Sn Sb Te I Xe Cs Ba La Ce Pr Nd Pm Sm Eu Gd Tb Dy Ho Er Tm Yb "
            "Lu Hf Ta W Re Os Ir Pt Au Hg Tl Pb Bi Po At Rn Fr Ra Ac Th Pa U Np Pu Am Cm Bk Cf Es Fm Md No Lr Rf "
            "Db Sg Bh Hs Mt Ds Rg Cn Nh Fl Mc Lv Ts Og").split()
LOWERCASE = {"b": "B", "c": "C", "n": "N", "o": "O", "p": "P", "s": "S", "se": "Se", "as": "As"}
LOWERCASE_OF = {element: symbol for symbol, element in LOWERCASE.items()}
VALENCES = {"B": (3,), "C": (4,), "N": (3, 5), "O": (2,), "P": (3, 5), "S": (2, 4, 6),
            "F": (1,), "Cl": (1,), "Br": (1,), "I": (1,)}                       # section 5, rule 7
ORDER_OF = {"-": "single", "=": "double", "#": "triple", "$": "quadruple", ":": "aromatic"}
SYMBOL_OF = {order: symbol for symbol, order in ORDER_OF.items()}
WEIGHT = {"single": 1, "double": 2, "triple": 3, "quadruple": 4, "aromatic": 1}
DIGITS = "0123456789"
WHITE = " \t\n\r"
STEREO_CLASSES = ("TH", "AL", "SP", "TB", "OH")
# Section 12.2, rule 9: the message for the second of the two spellings of a stereo centre with a free
# place that are not read. It has a name because check_spec.py asks for it as well.
FREE_PLACE_AND_ONE_RING_NUMBER = "a stereo centre with a free place, one ring number and only single bonds is not read"


# ------------------------------------------------------------------------------------------ the Mol (3)
@dataclass(frozen=True)
class Atom:
    element: str
    isotope: Optional[int]
    charge: int
    hydrogens: int

    def __post_init__(self):
        # A guard against a value in the wrong place.
        whole = lambda value: isinstance(value, int) and not isinstance(value, bool)
        if not (isinstance(self.element, str) and (self.isotope is None or whole(self.isotope)) and whole(self.charge)
                and whole(self.hydrogens)):
            raise TypeError(f"not an Atom: {self!r}")


@dataclass(frozen=True)
class Bond:
    a: int
    b: int
    order: str


@dataclass(frozen=True)
class AtomOrientation:
    """An atom that has an orientation (section 12.1)."""
    atom: int
    orientation: str                        # "anticlockwise" or "clockwise"


@dataclass(frozen=True)
class BondGeometry:
    """A double bond that has a geometry (section 12.1). `a` and `b` are its two atoms, as in `Bond`."""
    a: int
    b: int
    geometry: str                           # "sameSide" or "oppositeSides"


@dataclass(frozen=True)
class Mol:
    atoms: tuple
    bonds: tuple
    orientations: tuple = ()                # the atoms that have an orientation, in increasing order
    geometries: tuple = ()                  # the double bonds that have a geometry, in the order of `bonds`


class SmilesError(Exception):
    """A text that is not read. Printed as "error: position N: <what is wrong>" (section 6)."""

    def __init__(self, position, message):
        super().__init__(f"position {position}: {message}")
        self.position, self.message = position, message


class WriteError(Exception):
    """A Mol that gets no text: the writer refuses it (sections 9.4 and 12.3), or `canonical` works out no
    chosen form for it (section 3.2)."""


def neighbours(n, bonds):
    """For every atom, the atoms it is bonded to, in increasing atom number."""
    out = [[] for _ in range(n)]
    for (a, b) in bonds:
        out[a].append(b)
        out[b].append(a)
    return [sorted(x) for x in out]


def neighbours_of(mol):
    """For every atom of a Mol, the atoms it is bonded to, in increasing atom number."""
    return neighbours(len(mol.atoms), [(b.a, b.b) for b in mol.bonds])


def other_neighbours(nb, atom, partner):
    """The neighbours of `atom` other than `partner`, in increasing atom number."""
    return [x for x in nb[atom] if x != partner]


def has_four_places(how_many_neighbours, hydrogens):
    """Sections 3 and 12.1: an atom has four places when it has four neighbours and no hydrogen of its
    own, or three neighbours and at most one hydrogen of its own."""
    return (how_many_neighbours == 4 and hydrogens == 0) or (how_many_neighbours == 3 and hydrogens <= 1)


def can_have_geometry(nb, a, b):
    """Sections 3 and 12.2, rule 10: each of the two atoms `a` and `b` of a double bond has one or two
    neighbours other than the partner."""
    return 1 <= len(other_neighbours(nb, a, b)) <= 2 and 1 <= len(other_neighbours(nb, b, a)) <= 2


def assumed_order(lowercase_a, lowercase_b):
    """Section 5, rule 5: the order of a bond that is written without a symbol. It is aromatic if both
    atoms are lowercase, and single otherwise."""
    return "aromatic" if lowercase_a and lowercase_b else "single"


def falling_pairs(numbers):
    """How many pairs of the list stand in falling order."""
    return sum(1 for x in range(len(numbers)) for y in range(x + 1, len(numbers)) if numbers[x] > numbers[y])


def parity(src, dst):
    """+1 if an even number of swaps turns the order `src` into the order `dst`, otherwise -1."""
    place = {x: k for k, x in enumerate(dst)}
    return 1 if falling_pairs([place[x] for x in src]) % 2 == 0 else -1


OTHER_ORIENTATION = {"anticlockwise": "clockwise", "clockwise": "anticlockwise"}
OTHER_GEOMETRY = {"sameSide": "oppositeSides", "oppositeSides": "sameSide"}


def fixed_places(nb, atom):
    """Section 12.1: the places of an atom in the fixed order: its fourth place first (None: its own
    hydrogen, or the free place), if it has three neighbours; then its neighbours in increasing atom
    number."""
    return ([None] if len(nb[atom]) == 3 else []) + list(nb[atom])


def orientation_of(mol, nb, atom, places):
    """The first of the two statements of section 12.1: seen from the first of `places`, the other three
    follow each other anticlockwise or clockwise around `atom`. `places` are the four places of the atom
    in some order. None if the atom has no orientation, or if `places` are not its four places.

    The Mol stores the answer for the fixed order. For another order it is the same answer after an even
    number of swaps, and the other one after an odd number."""
    stored = next((x.orientation for x in mol.orientations if x.atom == atom), None)
    fixed = fixed_places(nb, atom)
    if stored is None or len(places) != len(fixed) or set(places) != set(fixed):
        return None
    odd = falling_pairs([fixed.index(place) for place in places]) % 2 == 1
    return OTHER_ORIENTATION[stored] if odd else stored


def geometry_of(mol, nb, a, b, x, y):
    """The second statement of section 12.1: `x`, a neighbour of `a`, and `y`, a neighbour of `b`, lie on
    the same side of the double bond between `a` and `b`, or on opposite sides. None if that bond has no
    geometry, or if `x` or `y` is no such neighbour.

    The Mol stores the answer for the lowest-numbered such neighbour of each of the two atoms. The other
    neighbour of an atom lies on the other side."""
    stored = next((g.geometry for g in mol.geometries if (g.a, g.b) == (min(a, b), max(a, b))), None)
    xs, ys = other_neighbours(nb, a, b), other_neighbours(nb, b, a)
    if stored is None or x not in xs or y not in ys:
        return None
    return OTHER_GEOMETRY[stored] if (x != xs[0]) != (y != ys[0]) else stored


def bare_hydrogens(element, lowercase, total):
    """Section 5, rule 7: the hydrogens of a bare atom whose bonds add up to `total`."""
    valence = next((v for v in VALENCES[element] if v >= total), None)
    if valence is None:
        return 0
    return max(0, valence - total - 1) if lowercase else valence - total


def written_lowercase(mol):
    """Section 9: for every atom of a well formed Mol, whether its symbol is written in lowercase.

    It is, when one of its bonds is aromatic and its element has a lowercase symbol. The Mol does not store
    the case of a symbol: the writer works it out from the bonds.
    """
    aromatic_bond = [False] * len(mol.atoms)
    for b in mol.bonds:
        if b.order == "aromatic":
            aromatic_bond[b.a] = aromatic_bond[b.b] = True
    return [aromatic_bond[i] and atom.element in LOWERCASE_OF for i, atom in enumerate(mol.atoms)]


def is_well_formed(mol):
    """Section 3: its six conditions. Section 12.1 says what the four places of condition 4 are."""
    n = len(mol.atoms)
    if any(not (b.a < b.b < n) for b in mol.bonds):
        return False
    if any(not (x.a < y.a or (x.a == y.a and x.b < y.b)) for x, y in zip(mol.bonds, mol.bonds[1:])):
        return False
    nb = neighbours_of(mol)
    # The atoms with an orientation: in increasing order, each an atom with four places.
    if any(not x.atom < y.atom for x, y in zip(mol.orientations, mol.orientations[1:])):
        return False
    for x in mol.orientations:
        if not x.atom < n:
            return False
        if not has_four_places(len(nb[x.atom]), mol.atoms[x.atom].hydrogens):
            return False
    # The double bonds with a geometry: in the order of `bonds`, each a double bond of the Mol whose two
    # atoms have one or two neighbours other than the partner.
    if any(not (x.a < y.a or (x.a == y.a and x.b < y.b)) for x, y in zip(mol.geometries, mol.geometries[1:])):
        return False
    double = {(b.a, b.b) for b in mol.bonds if b.order == "double"}
    for x in mol.geometries:
        if (x.a, x.b) not in double or not can_have_geometry(nb, x.a, x.b):
            return False
    return True


# --------------------------------------------------------------------------- text to tokens (4, 6, 12.2)
@dataclass
class Token:
    kind: str                               # "atom", "bond", "ring", "(", ")" or "."
    pos: int                                # the position of its first character
    value: object = None                    # atom: a RawAtom; bond: its symbol; ring: its number


@dataclass
class RawAtom:
    element: str
    aromatic: bool
    isotope: Optional[int]
    charge: int
    hydrogens: Optional[int]                # None for a bare atom: worked out later (section 5, rule 7)
    chiral: Optional[str] = None            # "@" or "@@"
    chiral_pos: Optional[int] = None


def bracket_atom(text, start):
    """Read the bracket atom that starts at text[start] == "[". Returns the token and the position behind it."""
    end = text.find("]", start)
    if end < 0:
        raise SmilesError(start, "'[' is never closed")

    def does_not_fit(k):
        c = text[k]
        if c in WHITE:
            return SmilesError(k, "white space is not allowed")
        if c == "*":
            return SmilesError(k, "the wildcard atom is not read")
        if c == ":":
            return SmilesError(k, "atom classes are not read")
        return SmilesError(k, f"'{c}' cannot be read here")

    k = start + 1
    while text[k] in DIGITS:
        k += 1
    isotope = int(text[start + 1:k]) if k > start + 1 else None

    c = text[k]
    if c in WHITE or c == "*":
        raise does_not_fit(k)
    if text[k:k + 2] in ELEMENTS:                   # a symbol of two letters wins over one of one letter
        element, aromatic, k = text[k:k + 2], False, k + 2
    elif c in ELEMENTS:
        element, aromatic, k = c, False, k + 1
    elif text[k:k + 2] in LOWERCASE:
        element, aromatic, k = LOWERCASE[text[k:k + 2]], True, k + 2
    elif c in LOWERCASE:
        element, aromatic, k = LOWERCASE[c], True, k + 1
    else:
        raise SmilesError(k, "an element symbol is expected here")

    chiral = chiral_pos = None
    if text[k] == "@":
        chiral_pos = k
        if text[k + 1] == "@":
            chiral, k = "@@", k + 2
        elif text[k + 1:k + 3] in STEREO_CLASSES:
            raise SmilesError(k, "this stereo class is not read")
        else:
            chiral, k = "@", k + 1

    hydrogens = 0
    if text[k] == "H":
        if element == "H":
            raise SmilesError(k, "a hydrogen atom cannot have a hydrogen count")
        k += 1
        hydrogens = 1
        if text[k] in DIGITS:
            hydrogens, k = int(text[k]), k + 1

    charge = 0
    if text[k] in "+-":
        sign = 1 if text[k] == "+" else -1
        if text[k + 1] == text[k]:
            charge, k = 2 * sign, k + 2
        else:
            k += 1
            first = k
            while k < first + 2 and text[k] in DIGITS:
                k += 1
            charge = sign * (int(text[first:k]) if k > first else 1)

    if k != end:
        raise does_not_fit(k)
    return Token("atom", start, RawAtom(element, aromatic, isotope, charge, hydrogens, chiral, chiral_pos)), end + 1


def tokens_of(text):
    """Cut the text into tokens, one after the other, from left to right.

    The tokens are handed out one at a time. A character or bracket atom that cannot be read raises its error
    only when the reader gets there, so that a problem of structure further to the left is reported first
    (section 6: the first problem met is the one reported).
    """
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in WHITE:
            raise SmilesError(i, "white space is not allowed")
        if c == "[":
            token, i = bracket_atom(text, i)
            yield token
        elif text.startswith(("Cl", "Br"), i):
            yield Token("atom", i, RawAtom(text[i:i + 2], False, None, 0, None))
            i += 2
        elif c in "BCNOPSFI":
            yield Token("atom", i, RawAtom(c, False, None, 0, None))
            i += 1
        elif c in "bcnops":
            yield Token("atom", i, RawAtom(LOWERCASE[c], True, None, 0, None))
            i += 1
        elif c in ORDER_OF or c in "/\\":           # a bond symbol, or a direction mark (12.2, rule 8)
            yield Token("bond", i, c)
            i += 1
        elif c in DIGITS:
            yield Token("ring", i, int(c))
            i += 1
        elif c == "%":
            if i + 2 < n and text[i + 1] in DIGITS and text[i + 2] in DIGITS:
                yield Token("ring", i, int(text[i + 1:i + 3]))
                i += 3
            else:
                raise SmilesError(i, "'%' must be followed by two digits")
        elif c in "().":
            yield Token(c, i)
            i += 1
        elif c == "*":
            raise SmilesError(i, "the wildcard atom is not read")
        else:
            raise SmilesError(i, f"'{c}' cannot be read here")


# ------------------------------------------------------------------------------ tokens to Mol (5, 6, 12.2)
# What was read last (section 6, "what may come next").
START, AFTER_DOT, AFTER_OPEN, BOND_AFTER_OPEN, BOND_AFTER_CLOSE, BOND_AFTER_ATOM, AFTER_ATOM, AFTER_CLOSE = range(8)
MAY_COME_NEXT = {
    START: {"atom"},
    AFTER_DOT: {"atom"},
    AFTER_OPEN: {"atom", "bond", "."},
    BOND_AFTER_OPEN: {"atom"},
    BOND_AFTER_CLOSE: {"atom"},
    BOND_AFTER_ATOM: {"atom", "ring"},
    AFTER_ATOM: {"atom", "bond", "ring", "(", ")", "."},       # after an atom or a ring number
    AFTER_CLOSE: {"atom", "bond", "(", ")", "."},
}


def order_and_direction(token):
    """A bond token -> (the order it names, or None; +1 for "/", -1 for "\\", 0 otherwise)."""
    if token is None:
        return None, 0
    if token.value == "/":
        return None, 1
    if token.value == "\\":
        return None, -1
    return ORDER_OF[token.value], 0


def read(text):
    """Sections 5 and 12.2. Returns the Mol, or raises SmilesError as section 6 demands."""
    tokens = tokens_of(text)

    raw = []                # the atoms as written
    bonds = {}              # (a, b) with a < b  ->  order
    marks = {}              # (a, b) -> (+1 if b lies above a, -1 if below; position of the mark)
    written = []            # written[i]: the neighbours of atom i in the order the text writes them
    has_parent = []         # has_parent[i]: atom i is bonded to an earlier atom along the text
    ring_numbers = []       # ring_numbers[i]: how many ring numbers are written at atom i
    prev, pending, dot_pos = None, None, None
    branches = []           # open round brackets: (the atom the branch hangs on, position of the "(")
    rings = {}              # open ring numbers: number -> (atom, its bond token, its place in written[atom], position)
    state = START

    def add_bond(x, y, order, direction, mark_pos, pos):
        """A bond written at atom x for its bond to atom y."""
        key = (min(x, y), max(x, y))
        if key in bonds:
            raise SmilesError(pos, "these two atoms are already bonded")
        bonds[key] = assumed_order(raw[x].aromatic, raw[y].aromatic) if order is None else order
        if direction:
            marks[key] = (direction if x < y else -direction, mark_pos)

    for t in tokens:
        if t.kind not in MAY_COME_NEXT[state]:
            if t.kind == "ring" and state in (AFTER_CLOSE, BOND_AFTER_CLOSE):
                raise SmilesError(t.pos, "a ring number must come before the branches of its atom")
            if state == BOND_AFTER_ATOM:
                raise SmilesError(t.pos, "an atom or a ring number is expected here")
            raise SmilesError(t.pos, "an atom is expected here")

        if t.kind == "atom":
            i = len(raw)
            raw.append(t.value)
            written.append([])
            has_parent.append(prev is not None)
            ring_numbers.append(0)
            if prev is not None:
                order, direction = order_and_direction(pending)
                add_bond(prev, i, order, direction, pending.pos if pending else None, t.pos)
                written[i].append(prev)
                written[prev].append(i)
            prev, pending, state = i, None, AFTER_ATOM
        elif t.kind == "bond":
            pending = t
            state = {AFTER_ATOM: BOND_AFTER_ATOM, AFTER_OPEN: BOND_AFTER_OPEN, AFTER_CLOSE: BOND_AFTER_CLOSE}[state]
        elif t.kind == "ring":
            number = t.value
            ring_numbers[prev] += 1
            if number in rings:
                partner, opened_with, place, _ = rings.pop(number)
                if partner == prev:
                    raise SmilesError(t.pos, "an atom cannot be bonded to itself")
                (order1, dir1), (order2, dir2) = order_and_direction(opened_with), order_and_direction(pending)
                if (order1 and order2 and order1 != order2) or (dir1 and order2) or (dir2 and order1):
                    raise SmilesError(t.pos, f"the two ends of ring {number} name different bonds")
                if dir1 and dir2 and dir1 == dir2:      # the two ends say the same when one is "/" and the other "\"
                    raise SmilesError(t.pos, f"the two ends of ring {number} name different directions")
                # Where both ends carry a mark, the one at the number that opens the ring is the one that is
                # kept, and its position is the one that a message about the marks names.
                if dir1:                                # written at the atom that opened the ring number
                    add_bond(partner, prev, None, dir1, opened_with.pos, t.pos)
                elif dir2:                              # written at the atom that closes it
                    add_bond(prev, partner, None, dir2, pending.pos, t.pos)
                else:
                    add_bond(partner, prev, order1 or order2, 0, None, t.pos)
                written[prev].append(partner)
                written[partner][place] = prev
            else:
                written[prev].append(None)
                rings[number] = (prev, pending, len(written[prev]) - 1, t.pos)
            pending, state = None, AFTER_ATOM
        elif t.kind == "(":
            branches.append((prev, t.pos))
            state = AFTER_OPEN
        elif t.kind == ")":
            if not branches:
                raise SmilesError(t.pos, "')' has no matching '('")
            prev = branches.pop()[0]
            state = AFTER_CLOSE
        elif t.kind == ".":
            prev, dot_pos, state = None, t.pos, AFTER_DOT

    # The end of the text, in the order of the table of section 6.
    if state in (BOND_AFTER_ATOM, BOND_AFTER_OPEN, BOND_AFTER_CLOSE):
        raise SmilesError(pending.pos, "the text ends after a bond symbol")
    if state == AFTER_DOT:
        raise SmilesError(dot_pos, "the text ends after a dot")
    if branches:
        raise SmilesError(branches[-1][1], "'(' is never closed")
    if rings:
        number, (_, _, _, pos) = min(rings.items(), key=lambda item: item[1][3])
        raise SmilesError(pos, f"ring {number} is opened but never closed")

    n = len(raw)
    nb = neighbours(n, bonds)
    hydrogens = [a.hydrogens if a.hydrogens is not None else
                 bare_hydrogens(a.element, a.aromatic, sum(WEIGHT[bonds[(min(i, j), max(i, j))]] for j in nb[i]))
                 for i, a in enumerate(raw)]

    # ---- the marks become facts (12.2, rules 9 and 10) ----
    problems, orientation, geometry = [], {}, {}
    for i, a in enumerate(raw):
        if a.chiral:
            places = list(written[i])
            if not has_four_places(len(places), hydrogens[i]):
                problems.append((a.chiral_pos, "this atom cannot be a stereo centre"))
                continue
            fourth = ["H"] if len(places) == 3 else []         # its own hydrogen, or the free place
            if fourth and hydrogens[i] == 0 and not has_parent[i]:
                problems.append((a.chiral_pos, "a stereo centre with a free place needs an atom before it"))
                continue
            if (fourth and hydrogens[i] == 0 and ring_numbers[i] == 1
                    and all(bonds[(min(i, j), max(i, j))] == "single" for j in nb[i])):
                problems.append((a.chiral_pos, FREE_PLACE_AND_ONE_RING_NUMBER))
                continue
            if fourth:
                places.insert(1 if has_parent[i] else 0, "H")
            sign = (1 if a.chiral == "@" else -1) * parity(places, fourth + nb[i])
            orientation[i] = "anticlockwise" if sign == 1 else "clockwise"

    def above(x, e):
        """+1 if the text says that x lies above e, -1 if below, None if their bond carries no mark."""
        key = (min(x, e), max(x, e))
        if key not in marks:
            return None
        return marks[key][0] if e < x else -marks[key][0]

    taking_part = set()
    for (a, b) in sorted(bonds):
        if bonds[(a, b)] != "double" or not can_have_geometry(nb, a, b):
            continue
        ends = [(a, other_neighbours(nb, a, b)), (b, other_neighbours(nb, b, a))]
        marked = [[(x, above(x, e)) for x in others if above(x, e) is not None] for e, others in ends]
        if not all(marked):
            continue
        sides, contradiction = [], False
        for (e, others), m in zip(ends, marked):
            taking_part.update((min(x, e), max(x, e)) for x, _ in m)
            if len(m) == 2 and m[0][1] == m[1][1]:
                later = max(marks[(min(x, e), max(x, e))][1] for x, _ in m)
                problems.append((later, "these marks contradict each other"))
                contradiction = True
            x, side = m[0]
            sides.append(side if x == others[0] else -side)     # others[0] is the lowest-numbered neighbour
        if not contradiction:
            geometry[(a, b)] = "sameSide" if sides[0] == sides[1] else "oppositeSides"
    for key, (_, pos) in marks.items():
        if key not in taking_part:
            problems.append((pos, "this mark has no partner on the other side of a double bond"))
    if problems:
        raise SmilesError(*min(problems))

    atoms = tuple(Atom(a.element, a.isotope, a.charge, hydrogens[i]) for i, a in enumerate(raw))
    return Mol(atoms, tuple(Bond(a, b, bonds[(a, b)]) for (a, b) in sorted(bonds)),
               tuple(AtomOrientation(i, orientation[i]) for i in sorted(orientation)),
               tuple(BondGeometry(a, b, geometry[(a, b)]) for (a, b) in sorted(geometry)))


def read_or_none(text):
    """The Mol that `read` returns for a text; None for a text that is not read."""
    try:
        return read(text)
    except SmilesError:
        return None


def problem_of(text):
    """What `read` reports for a text, as (position, message); None for a text that is read."""
    try:
        read(text)
    except SmilesError as e:
        return e.position, e.message
    return None


# ------------------------------------------------------------------------------------- printing (7)
def show(mol):
    """The printed layout of section 7: the four lists of a Mol, each entry on a line of its own."""
    def atom(x):
        isotope = "none" if x.isotope is None else f"some {x.isotope}"
        return f"{{ element := .{x.element}, isotope := {isotope}, charge := {x.charge}, hydrogens := {x.hydrogens} }}"

    def bond(x):
        return f"{{ a := {x.a}, b := {x.b}, order := .{x.order} }}"

    def orientation(x):
        return f"{{ atom := {x.atom}, orientation := .{x.orientation} }}"

    def geometry(x):
        return f"{{ a := {x.a}, b := {x.b}, geometry := .{x.geometry} }}"

    def listed(items):
        return "[]" if not items else "[\n" + ",\n".join("    " + item for item in items) + " ]"

    return (f"{{ atoms := {listed([atom(x) for x in mol.atoms])},\n"
            f"  bonds := {listed([bond(x) for x in mol.bonds])},\n"
            f"  orientations := {listed([orientation(x) for x in mol.orientations])},\n"
            f"  geometries := {listed([geometry(x) for x in mol.geometries])} }}\n")


# ------------------------------------------------------------------------------------ writing (9, 12.3)
def choose_marks(mol, nb):
    """Section 12.3: which bonds carry "/" or "\\". Returns {(u, v): +1 or -1}; +1 means "v lies above u"."""
    bonds = {(b.a, b.b): b.order for b in mol.bonds}
    geometry = {(x.a, x.b): x.geometry for x in mol.geometries}

    def key(x, y):
        return (min(x, y), max(x, y))

    lower = written_lowercase(mol)

    def can_carry_a_mark(k):
        return bonds[k] == assumed_order(lower[k[0]], lower[k[1]])

    def sign(e, x):                         # "x lies above e" is mark[key(e, x)] * sign(e, x)
        return 1 if e < x else -1

    links = {}                              # (k2, rel) in links[k1] means mark[k2] = mark[k1] * rel

    def link(k1, k2, rel):
        links.setdefault(k1, []).append((k2, rel))
        links.setdefault(k2, []).append((k1, rel))

    for (a, b), g in sorted(geometry.items()):
        reference = []
        for e, partner in ((a, b), (b, a)):
            able = [x for x in other_neighbours(nb, e, partner) if can_carry_a_mark(key(e, x))]
            if not able:
                raise WriteError("at one atom of a double bond with a geometry, no bond can carry a mark")
            x = able[0]                     # the lowest-numbered neighbour whose bond can carry a mark
            reference.append((key(e, x), sign(e, x) * (1 if x == other_neighbours(nb, e, partner)[0] else -1)))
        (ka, fa), (kb, fb) = reference
        link(ka, kb, fa * fb * (1 if g == "sameSide" else -1))
    marked = set(links)
    for (a, b) in sorted(geometry):         # two marked bonds at one atom of such a double bond: opposite sides
        for e, partner in ((a, b), (b, a)):
            o = other_neighbours(nb, e, partner)
            if len(o) == 2 and key(e, o[0]) in marked and key(e, o[1]) in marked:
                link(key(e, o[0]), key(e, o[1]), -sign(e, o[0]) * sign(e, o[1]))
    for (a, b), order in bonds.items():     # a double bond without a geometry must not get one
        if order == "double" and (a, b) not in geometry and can_have_geometry(nb, a, b):
            if all(any(key(e, x) in marked for x in other_neighbours(nb, e, p)) for e, p in ((a, b), (b, a))):
                raise WriteError("the marks would give a geometry to a double bond that has none")
    mark = {}
    for start in sorted(marked):            # in each group, the bond that comes first in `bonds` gets "/"
        if start in mark:
            continue
        mark[start] = 1
        todo = [start]
        while todo:
            k = todo.pop()
            for k2, rel in links[k]:
                if k2 not in mark:
                    mark[k2] = mark[k] * rel
                    todo.append(k2)
                elif mark[k2] != mark[k] * rel:
                    raise WriteError("no choice of marks gives every geometry")
    return mark


def parents(n, nb, round_brackets):
    """parent[i]: the earlier atom next to which atom i is written, or None: then a dot comes before it,
    unless it is atom 0."""
    parent, path = [None] * n, []
    for i in range(n):
        if round_brackets:                  # 9.2: the atoms of the path that it is bonded to
            reachable = [a for a in path if a in nb[i]]
        else:                               # 9.1: only the atom just before it
            reachable = [i - 1] if i > 0 and (i - 1) in nb[i] else []
        if reachable:
            parent[i] = reachable[-1]
            path = path[:path.index(parent[i]) + 1] + [i]
        else:
            path = [i]
    return parent


def spell(mol, round_brackets, ring_marks="open"):
    """One of the two spellings of section 9, with the stereo marks of the Mol (12.3): the plain one (9.1)
    or the one with round brackets (9.2).

    The plain spelling writes every atom in square brackets and every bond with its symbol, or with its
    stereo mark in the place of the symbol. The spelling with round brackets writes an atom bare where
    that is safe, and leaves a bond symbol out where a reader assumes it.

    ring_marks says where the "/" or "\\" of a ring bond is written. SPEC.md demands "open": at the ring
    number that opens the bond. "close" and "both" are other correct spellings of the same molecule. Only
    the checks use them, to try rule 8 of the reader.
    """
    if not is_well_formed(mol):
        raise WriteError("the Mol is not well formed")
    n = len(mol.atoms)
    bonds = {(b.a, b.b): b.order for b in mol.bonds}
    nb = neighbours(n, bonds)
    orientation = {x.atom: x.orientation for x in mol.orientations}
    for atom in mol.atoms:
        if atom.hydrogens > 9 or abs(atom.charge) > 99:
            raise WriteError("an atom has more than 9 hydrogens, or a charge beyond +99 or -99")
        if atom.element == "H" and atom.hydrogens > 0:
            raise WriteError("a hydrogen atom has hydrogens of its own")
    mark = choose_marks(mol, nb)
    lower = written_lowercase(mol)

    def symbol(k):
        if k in mark:
            return "/" if mark[k] == 1 else "\\"
        return "" if round_brackets and bonds[k] == assumed_order(lower[k[0]], lower[k[1]]) else SYMBOL_OF[bonds[k]]

    def may_be_bare(i, atom):
        """9.2: an atom is written bare only if reading it gives the same atom back, and only where
        programs agree about the hydrogens of a bare atom."""
        if atom.element not in VALENCES or atom.isotope is not None or atom.charge != 0:
            return False
        orders = [bonds[(min(i, j), max(i, j))] for j in nb[i]]
        total = sum(WEIGHT[o] for o in orders)
        return (bare_hydrogens(atom.element, lower[i], total) == atom.hydrogens
                and (total <= VALENCES[atom.element][0] or total in VALENCES[atom.element])
                and lower[i] == ("aromatic" in orders))

    def ring_number(k):
        return str(k) if k < 10 else "%" + str(k)

    parent = parents(n, nb, round_brackets)
    children = [[] for _ in range(n)]
    for i, p in enumerate(parent):
        if p is not None:
            children[p].append(i)

    out, free, number = [], list(range(1, 100)), {}
    open_at = []                                    # the atoms whose round bracket is open, innermost last
    for i, atom in enumerate(mol.atoms):
        p = parent[i]
        if p is None:
            out.append(")" * len(open_at))
            open_at = []
            if i > 0:
                out.append(".")
        else:
            if p != i - 1:                          # back to the parent: close the round brackets in between
                while True:
                    out.append(")")
                    if open_at.pop() == p:
                        break
            if i != children[p][-1]:                # a later atom has the same parent
                out.append("(")
                open_at.append(p)
            out.append(symbol((p, i)))

        by_ring_number = [j for j in nb[i] if j != p and parent[j] != i]
        tag = ""
        if i in orientation:
            fourth = ["H"] if len(nb[i]) == 3 else []
            if fourth and atom.hydrogens == 0 and p is None:
                raise WriteError("a stereo centre with a free place would be written without an atom before it")
            if (fourth and atom.hydrogens == 0 and len(by_ring_number) == 1
                    and all(bonds[(min(i, j), max(i, j))] == "single" for j in nb[i])):
                raise WriteError("a stereo centre with a free place would be written with one ring number "
                                 "and only single bonds")
            places = ([p] if p is not None else []) + fourth + by_ring_number + children[i]
            sign = (1 if orientation[i] == "anticlockwise" else -1) * parity(places, fourth + nb[i])
            tag = "@" if sign == 1 else "@@"

        name = LOWERCASE_OF[atom.element] if lower[i] else atom.element
        if round_brackets and not tag and may_be_bare(i, atom):
            out.append(name)
        else:                                       # in square brackets: isotope, symbol, mark, hydrogens, charge
            q = atom.charge
            out.append("[" + ("" if atom.isotope is None else str(atom.isotope)) + name + tag
                       + ("" if atom.hydrogens == 0 else "H" if atom.hydrogens == 1 else f"H{atom.hydrogens}")
                       + ("" if q == 0 else ("+" if q > 0 else "-") + ("" if abs(q) == 1 else str(abs(q)))) + "]")

        for j in by_ring_number:
            k = (min(i, j), max(i, j))
            if j < i:
                r = number.pop(k)
                free.append(r)
                free.sort()
                closing = ""
                if k in mark and ring_marks in ("close", "both"):    # written at the higher atom: the lower one
                    closing = "\\" if mark[k] == 1 else "/"           # lies below it when the mark is +1
                out.append(closing + ring_number(r))
            else:
                if not free:
                    raise WriteError("more than 99 ring numbers are needed at the same time")
                r = free.pop(0)
                number[k] = r
                out.append(("" if k in mark and ring_marks == "close" else symbol(k)) + ring_number(r))
    out.append(")" * len(open_at))
    return "".join(out)


def has_stereo(mol):
    return bool(mol.orientations) or bool(mol.geometries)


def write_plain(mol):
    """What `plain` writes: the plain spelling (sections 9.1 and 12.3). The text is not read back before
    it is returned (section 9.3): that reading it gives the Mol back is theorem 12, proven for the Lean
    program."""
    return spell(mol, False)


def write(mol):
    """What `rewrite` writes: the spelling with round brackets (sections 9.2 and 12.3). Theorem 11 says
    the same of it."""
    return spell(mol, True)


# ---------------------------------------------------------------------------------- the chosen form (3.2)
BOND_CODE = {"quadruple": 0, "triple": 1, "double": 2, "aromatic": 3, "single": 4, None: 5}
SEARCH_LIMIT = 1000
ATOM_LIMIT = 1000       # `canonical` refuses a Mol with more atoms than this, before the search begins


def atom_code(atom):
    """An atom as four numbers: its element, its hydrogens (more hydrogens give the smaller number), its
    isotope and its charge."""
    return (ELEMENTS.index(atom.element),
            9 - atom.hydrogens if atom.hydrogens <= 9 else atom.hydrogens,
            0 if atom.isotope is None else atom.isotope + 1,
            2 * abs(atom.charge) - 1 if atom.charge < 0 else 2 * abs(atom.charge))


def stereo_code(mol):
    """The stereo facts of a Mol as numbers, for its key: for every atom 0, 1 or 2 (no orientation,
    anticlockwise, clockwise), and then for every bond 0, 1 or 2 (no geometry, the same side, opposite
    sides)."""
    orientation = {x.atom: x.orientation for x in mol.orientations}
    geometry = {(x.a, x.b): x.geometry for x in mol.geometries}
    return (tuple({None: 0, "anticlockwise": 1, "clockwise": 2}[orientation.get(i)] for i in range(len(mol.atoms)))
            + tuple({None: 0, "sameSide": 1, "oppositeSides": 2}[geometry.get((b.a, b.b))] for b in mol.bonds))


def chosen_order(mol):
    """The chosen numbering of a well formed Mol (section 3.2): its old atom numbers in their new order.
    None if the search gives up. The search fills the places one after the other and holds the
    beginnings whose new entry is the least; twins are placed in the order of their numbers; for a Mol
    without stereo facts, of the beginnings that are alike only the first is held; it gives up when a
    round would leave more than SEARCH_LIMIT beginnings."""
    n = len(mol.atoms)
    between = {}
    for b in mol.bonds:
        between[(b.a, b.b)] = between[(b.b, b.a)] = b.order
    codes = [atom_code(atom) for atom in mol.atoms]
    nb = neighbours_of(mol)
    in_a_stereo_fact = set()
    for x in mol.orientations:
        in_a_stereo_fact.update([x.atom] + nb[x.atom])
    for x in mol.geometries:
        in_a_stereo_fact.update([x.a, x.b] + nb[x.a] + nb[x.b])
    with_stereo = has_stereo(mol)

    def twins(a, b):
        return (mol.atoms[a] == mol.atoms[b] and a not in in_a_stereo_fact and b not in in_a_stereo_fact
                and all(between.get((a, x)) == between.get((b, x)) for x in range(n) if x != a and x != b))

    def outline(beginning):
        """What two beginnings that are alike have in common: for every atom, None if it is placed, and
        otherwise at which places it is bonded, and by which kind of bond."""
        place = {atom: i for i, atom in enumerate(beginning)}
        return tuple(None if u in place else
                     tuple(sorted((place[v], BOND_CODE[between[(u, v)]]) for v in nb[u] if v in place))
                     for u in range(n))

    smaller_twins = [[b for b in range(a) if twins(a, b)] for a in range(n)]
    held = [[]]
    for _ in range(n):
        # `kept` holds the extensions with the least entry so far, each as a beginning and the atom that
        # extends it. They are counted before the beginnings of the next round are made: in the round
        # in which the search gives up they can be very many.
        least, kept = None, []
        for beginning in held:
            placed = set(beginning)
            for a in range(n):
                if a not in placed:
                    waiting = 1 if any(b not in placed for b in smaller_twins[a]) else 0
                    entry = tuple(BOND_CODE[between.get((before, a))] for before in reversed(beginning)) + codes[a]
                    if with_stereo and len(beginning) + 1 == n:
                        entry += stereo_code(arrange(mol, beginning + [a]))
                    entry = (entry, waiting)
                    if least is None or entry < least:
                        least, kept = entry, [(beginning, a)]
                    elif entry == least:
                        kept.append((beginning, a))
        if not with_stereo and len(kept) > 1:
            # of the beginnings that are alike, only the first is kept; they are counted while that is done
            seen, first = set(), []
            for beginning, a in kept:
                its_outline = outline(beginning + [a])
                if its_outline not in seen:
                    if len(first) == SEARCH_LIMIT:
                        return None
                    seen.add(its_outline)
                    first.append((beginning, a))
            kept = first
        if len(kept) > SEARCH_LIMIT:
            return None
        held = [beginning + [a] for beginning, a in kept]
    return held[0]


def arrange(mol, order):
    """The Mol with its atoms in a new order: atom j of the result is atom order[j] of `mol`.

    The stereo facts are said anew for the new numbers, through the two statements of section 12.1: the
    new orientation of an atom is what the old Mol says for its places in the order of their new numbers,
    and the new geometry of a double bond is what the old Mol says for the neighbours that have the
    lowest new numbers."""
    place = {old: new for new, old in enumerate(order)}
    bonds = sorted((min(place[b.a], place[b.b]), max(place[b.a], place[b.b]), b.order) for b in mol.bonds)
    nb = neighbours_of(mol)
    orientations = []
    for x in mol.orientations:
        places = ([None] if len(nb[x.atom]) == 3 else []) + sorted(nb[x.atom], key=place.get)
        orientations.append((place[x.atom], orientation_of(mol, nb, x.atom, places)))
    geometries = []
    for g in mol.geometries:
        x = min(other_neighbours(nb, g.a, g.b), key=place.get)
        y = min(other_neighbours(nb, g.b, g.a), key=place.get)
        geometries.append((min(place[g.a], place[g.b]), max(place[g.a], place[g.b]), geometry_of(mol, nb, g.a, g.b, x, y)))
    return Mol(tuple(mol.atoms[old] for old in order), tuple(Bond(a, b, kind) for a, b, kind in bonds),
               tuple(AtomOrientation(atom, o) for atom, o in sorted(orientations)),
               tuple(BondGeometry(a, b, g) for a, b, g in sorted(geometries)))


def chosen_form(mol):
    """The chosen form of a Mol, as the command `canonical` works it out: the same molecule with its atoms
    in the chosen order. A Mol with more than ATOM_LIMIT atoms is refused before the search begins."""
    if not is_well_formed(mol):
        raise WriteError("the Mol is not well formed")
    if len(mol.atoms) > ATOM_LIMIT:
        raise WriteError(f"the chosen form is not worked out: more than {ATOM_LIMIT} atoms")
    order = chosen_order(mol)
    if order is None:
        raise WriteError("the chosen form is not worked out: too many numberings of this molecule look alike")
    return arrange(mol, order)


def write_chosen(mol):
    """What the command `canonical` writes: the chosen form in the spelling with round brackets."""
    return write(chosen_form(mol))


# --------------------------------------------------------------------------------------- the filter (16)
class FilterError(Exception):
    """A Mol that the filter refuses: it is not sound (section 16.2), or the rule refuses it (16.3)."""


def sound_problem(mol):
    """Section 16.2: the first reason why a Mol is not sound, or None if it is sound."""
    if not is_well_formed(mol):
        return "the Mol is not well formed"
    for i, atom in enumerate(mol.atoms):
        orders = [b.order for b in mol.bonds if i in (b.a, b.b)]
        total = sum(WEIGHT[order] for order in orders) + atom.hydrogens
        aromatic = orders.count("aromatic")
        usual = VALENCES.get(atom.element, ())
        if atom.element not in VALENCES:                                                        # test 1
            return f"the Mol is not sound: atom {i} is no atom of B, C, N, O, P, S, F, Cl, Br or I"
        if atom.isotope is not None:                                                            # test 2
            return f"the Mol is not sound: atom {i} has a mass number"
        if atom.charge != 0:                                                                    # test 3
            return f"the Mol is not sound: atom {i} has a charge"
        if aromatic == 1:                                                                       # test 4
            return f"the Mol is not sound: atom {i} has exactly one aromatic bond"
        if total not in usual and not (aromatic and total + 1 in usual):                        # test 5
            return (f"the Mol is not sound: the bonds and hydrogens of atom {i} add up to no usual valence of its "
                    f"element")
    return None


def meets_the_five_conditions(mol):
    """Section 16.3: for every atom of a well formed Mol, whether it meets the five conditions of a carbon
    atom of a perfluorinated group."""
    nb = neighbours_of(mol)
    multiple = [False] * len(mol.atoms)
    for b in mol.bonds:
        if b.order in ("double", "triple", "quadruple"):
            multiple[b.a] = multiple[b.b] = True
    found = []
    for i, atom in enumerate(mol.atoms):
        around = [mol.atoms[j].element for j in nb[i]]
        found.append(atom.element == "C" and atom.hydrogens == 0 and not multiple[i] and len(around) == 4
                     and "H" not in around)
    return found


def fluorinated_carbons(mol):
    """Section 16.3: for every atom of a well formed Mol, whether it is a fluorinated carbon atom."""
    nb = neighbours_of(mol)
    return [meets and any(mol.atoms[j].element == "F" for j in nb[i])
            for i, meets in enumerate(meets_the_five_conditions(mol))]


def group_carbons(mol):
    """Section 16.3: for every atom of a well formed Mol, whether it is a carbon atom of a perfluorinated
    group: a fluorinated carbon atom, or a branch carbon atom.

    Worked out from the fluorinated carbon atoms inwards. Whenever an atom becomes one, the atoms that it is
    bonded to are looked at again: one of them that meets the five conditions and is now bonded to three
    such atoms becomes one as well. (The Lean program goes through all atoms, round after round, until a
    round adds none.)
    """
    nb = neighbours_of(mol)
    meets = meets_the_five_conditions(mol)
    member = fluorinated_carbons(mol)
    to_look_around = [i for i, yes in enumerate(member) if yes]
    while to_look_around:
        i = to_look_around.pop()
        for j in nb[i]:
            if not member[j] and meets[j] and len({k for k in nb[j] if member[k]}) >= 3:
                member[j] = True
                to_look_around.append(j)
    return member


def perfluorinated_groups(mol):
    """Section 16.3: the perfluorinated groups of a well formed Mol, each as the list of its atoms in
    increasing order, in the order of the lowest atom of each group.

    Every bond between two carbon atoms of the groups joins the groups of its two atoms into one. (The Lean
    program finds the groups in another way: it spreads from one atom along the bonds.)
    """
    member = group_carbons(mol)
    group_of = {i: [i] for i, yes in enumerate(member) if yes}
    for b in mol.bonds:
        if member[b.a] and member[b.b] and group_of[b.a] is not group_of[b.b]:
            joined = group_of[b.a] + group_of[b.b]
            for i in joined:
                group_of[i] = joined
    return sorted({id(g): sorted(g) for g in group_of.values()}.values())


def group_size(text):
    """Section 16.1: the number behind `filter perfluoro`, or None if the text is no such number."""
    if text == "" or any(c not in DIGITS for c in text) or text.strip("0") == "":
        return None
    n = 0
    for c in text:
        n = n * 10 + DIGITS.index(c)
    return n


def decimal(n):
    """A number in decimal digits. (Python refuses to print a number of many thousand digits with `str`.)"""
    digits = ""
    while n:
        n, last = divmod(n, 10)
        digits = DIGITS[last] + digits
    return digits or "0"


def filter_perfluoro(n, mol):
    """Sections 16.1 to 16.3: the Mol itself, if it is sound and has no perfluorinated group of `n` or more
    carbon atoms. Otherwise a FilterError with the reason."""
    problem = sound_problem(mol)
    if problem is not None:
        raise FilterError(problem)
    largest = max((len(group) for group in perfluorinated_groups(mol)), default=0)
    if largest >= n:
        raise FilterError(f"the Mol has a perfluorinated group of size {largest}, and size {decimal(n)} or more "
                          f"is refused")
    return mol


# ------------------------------------------------------------------------------------ the program (8)
WORDS = ("rewrite", "plain", "canonical")
USAGE = ("expected a SMILES text, or one of the words rewrite, plain and canonical followed by a SMILES text, "
         "or the words filter perfluoro followed by a number from 1 on and a SMILES text")


def run(args):
    """The whole program: command-line arguments -> (standard output, standard error, exit code)."""
    def error(message):
        return "", f"error: {message}\n", 1

    try:
        if len(args) == 1 and args[0] not in WORDS:
            return show(read(args[0])), "", 0
        if len(args) == 2 and args[0] == "rewrite":
            return write(read(args[1])) + "\n", "", 0
        if len(args) == 2 and args[0] == "plain":
            return write_plain(read(args[1])) + "\n", "", 0
        if len(args) == 2 and args[0] == "canonical":
            return write_chosen(read(args[1])) + "\n", "", 0
        if len(args) == 4 and args[:2] == ["filter", "perfluoro"] and group_size(args[2]) is not None:
            return show(filter_perfluoro(group_size(args[2]), read(args[3]))), "", 0
    except (SmilesError, WriteError, FilterError) as e:
        return error(str(e))
    return error(USAGE)


if __name__ == "__main__":
    stdout, stderr, code = run(sys.argv[1:])
    sys.stdout.write(stdout)
    sys.stderr.write(stderr)
    sys.exit(code)
