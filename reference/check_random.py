"""Attack SPEC.md and the model with random texts and random Mols.

    .venv/bin/python -I reference/check_random.py

Four attacks, each with fixed random seeds, so that every run tries the same things:

  A  grammar      a recogniser written from the grammar of sections 4 and 12.2 alone, sharing no code with
                  the model, against the reader
  B  first error  nothing inside a text is wrong before the reported position (section 6)
  C  RDKit        where the model and RDKit (clean-up off) part ways, it is in one of the ways that
                  sections 11.2 and 12.4 list
  D  round trip   random well formed Mols that are made without any text are written and read back
                  (theorems 11 and 12 as a test); and Mols near the limit of 99 ring numbers (section 9.4)

reference/README.md, "Reading the output of `check_random.py`", says what each attack demands, what it sets
aside and which least counts it has. A line in CAPITALS is a failure. The script then ends with exit code 1.
"""
import collections
import random
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
import others
import sources

REAL = sources.real_texts()
PIECES = list("CCCCNOPSFIcnosb[]()()==#$:..%0112345H+-@/\\* ") + [
    "Cl", "Br", "[nH]", "[O-]", "[N+]", "%10", "%01", "[13C]", "[013C]", "[0C]", "[Fe++]", "[Fe+2]", "[HH]", "[se]", "[te]",
    "[si]", "[CH3:1]", "[C+0]", "[CH0]", "[C--]", "[C+++]", "[2H]", "[CH10]", "->", "[Xx]", "[Og]", "[Nh]"]
# Pieces for the kinds of text that section 11.2 names and that the pieces above cannot make: the other
# digits, `~`, white space that is no space, characters from outside ASCII, a charge of three digits and
# one with a zero in front, mass numbers from 65,536 on, one just above what RDKit takes and one of 20
# digits, an atomic number behind `#`, a ring number in round brackets, the arrow `<-`, and two of the old
# names of the elements 110 to 118. The pieces `[C-H3]` and `[C+H]` are for section 4.1: a charge in front
# of the hydrogens, which both programs refuse.
PIECES += list("6789~\t\n\r") + ["\N{LATIN SMALL LETTER E WITH ACUTE}", "\N{SUPERSCRIPT TWO}", "[C+100]", "[C+07]", "[65549C]",
                                 "[65536C]", "[#6]", "%(100)", "[12345678901234567890C]", "[C-H3]", "[C+H]"]
PIECES += ["<-", "[Uuo]", "[Uub]", f"[{others.MOST_THAT_RDKIT_TAKES + 1}C]"]
# Pieces with stereo marks (section 12.2): atoms with `@` and `@@`, with and without a hydrogen, one with a
# charge, a stereo class that is not read, and a mark too many. The marks `/` and `\` are single pieces above.
PIECES += ["[C@H]", "[C@@H]", "[C@]", "[C@@]", "[N@]", "[S@+]", "[P@@]", "[C@TH1]", "[C@@@]", "[C@H2]"]
failures = []


def texts(seed, how_many):
    """Half random strings of the pieces above, half real texts, cut off after 5 to 60 characters, with one
    to three random changes."""
    rng = random.Random(seed)
    for _ in range(how_many // 2):
        yield "".join(rng.choice(PIECES) for _ in range(rng.randint(0, 9)))
    for _ in range(how_many // 2):
        s = rng.choice(REAL)[:rng.randint(5, 60)]
        for _ in range(rng.randint(1, 3)):
            i = rng.randint(0, len(s))
            s = s[:i] + (rng.choice(PIECES) if rng.random() < 0.6 else "") + s[i + rng.randint(0, 1):]
        yield s


def fail(attack, what, example):
    failures.append(attack)
    print(f"   {attack}: {what.upper()}: {example!r}")


def show(title, count):
    print(f"\n{title}")
    for key in sorted(count):
        print(f"{count[key]:8d}  {key}")


# --------------------------------------------------------------- A: the grammar of sections 4 and 12.2, on its own
SYMBOL = "|".join(sorted(others.RDKIT_ELEMENTS, key=len, reverse=True) + ["se", "as", "b", "c", "n", "o", "p", "s"])
BRACKET = re.compile(r"\[([0-9]+)?(%s)(@@?)?(H[0-9]?)?(\+\+|--|\+[0-9][0-9]?|-[0-9][0-9]?|\+|-)?\]" % SYMBOL)
DIGITS, BONDS = "0123456789", "-=#$:/\\"


# Each of the four functions below returns the position behind what it recognises at position `i` of the
# text `s`, or None if no such thing stands there.
def atom(s, i):
    if i < len(s) and s[i] == "[":
        m = BRACKET.match(s, i)
        return m.end() if m else None
    if s.startswith(("Cl", "Br"), i):
        return i + 2
    return i + 1 if i < len(s) and s[i] in "BCNOPSFIbcnops" else None


def ringbond(s, i):
    j = i + 1 if i < len(s) and s[i] in BONDS else i
    if j < len(s) and s[j] in DIGITS:
        return j + 1
    if j + 2 < len(s) and s[j] == "%" and s[j + 1] in DIGITS and s[j + 2] in DIGITS:
        return j + 3
    return None


def branched_atom(s, i):
    i = atom(s, i)
    if i is None:
        return None
    while (j := ringbond(s, i)) is not None:
        i = j
    while i < len(s) and s[i] == "(":
        j = i + 1
        if j < len(s) and (s[j] in BONDS or s[j] == "."):
            j += 1
        j = chain(s, j)
        if j is None or j >= len(s) or s[j] != ")":
            return None
        i = j + 1
    return i


def chain(s, i):
    i = branched_atom(s, i)
    if i is None:
        return None
    while i < len(s):
        k = branched_atom(s, i + 1 if s[i] == "." or s[i] in BONDS else i)
        if k is None:
            break
        i = k
    return i


def in_the_grammar(s):
    return s == "" or chain(s, 0) == len(s)


# A text of the grammar may still be refused for what it says.
FOR_WHAT_IT_SAYS = ("a hydrogen atom cannot have a hydrogen count", "an atom cannot be bonded to itself", "name different bonds",
                    "these two atoms are already bonded", "is opened but never closed")
# The messages about stereo marks that are looked for when the text has no other problem (section 12.2):
# five messages, two of which begin alike.
STEREO_AT_THE_END = ("this atom cannot be a stereo centre", "a stereo centre with a free place",
                     "these marks contradict each other", "this mark has no partner")
FOR_WHAT_IT_SAYS += ("name different directions",) + STEREO_AT_THE_END
count = collections.Counter()
for s in texts(11, 400000):
    r, g = model.problem_of(s), in_the_grammar(s)
    verdict = "read" if r is None else "refused for what it says" if any(m in r[1] for m in FOR_WHAT_IT_SAYS) else "refused as text"
    count[("in the grammar: " if g else "not in the grammar: ") + verdict] += 1
    if (g and verdict == "refused as text") or (not g and verdict == "read"):
        fail("A", "the grammar and the reader disagree", s)
show("A  The grammar of sections 4 and 12.2 against the reader", count)

# --------------------------------------------------------------- B: the first problem is the one reported
AT_THE_END = ("the text ends after", "is never closed", "is opened but never closed") + STEREO_AT_THE_END
count = collections.Counter()
rng = random.Random(5)
for s in texts(5, 300000):
    r = model.problem_of(s)
    if r is None or any(m in r[1] for m in AT_THE_END):
        count["texts that are read, or set aside: the report is one of the end of the text, or one about stereo marks that is looked for last"] += 1
        continue
    count["texts with a problem inside"] += 1
    before = model.problem_of(s[:r[0]])
    if before is not None and not any(m in before[1] for m in AT_THE_END):
        fail("B", "there is a problem before the reported position", s)
    # A report that a `%` lacks its two digits is left out: at the end of a text, what is added can be the digits.
    if "'%' must" not in r[1] and model.problem_of(s + "".join(rng.choice(PIECES) for _ in range(rng.randint(1, 4)))) != r:
        fail("B", "the report depends on what follows", s)
show("B  Nothing inside the text is wrong before the reported position", count)

# --------------------------------------------------------------- C: every difference from RDKit is a listed one
count, seen = collections.Counter(), set()
for s in texts(23, 400000):
    if s in seen:
        continue
    seen.add(s)
    theirs, r = others.rdkit_mol(s), model.problem_of(s)
    if r is not None:
        position, message = r
        if theirs is None:
            count["both refuse the text"] += 1
            continue
        here = s[position:position + 2]
        listed = (message in ("white space is not allowed", "the wildcard atom is not read", "atom classes are not read",
                              "a hydrogen atom cannot have a hydrogen count", "a ring number must come before the branches of its atom")
                  or "name different bonds" in message
                  # section 12.4: what the model refuses about stereo marks, and RDKit reads or ignores
                  or message == "this stereo class is not read" or "name different directions" in message
                  or any(m in message for m in STEREO_AT_THE_END)
                  # two `\` in a row, which RDKit reads as one (of the pairs that are tried here it reads no other)
                  or (message in ("an atom is expected here", "an atom or a ring number is expected here")
                      and s[position - 1:position + 1] == "\\\\")
                  or (message == "an element symbol is expected here" and here == "te")
                  or (message == "an element symbol is expected here" and here[:1] == "#")      # an atomic number
                  or (message == "'%' must be followed by two digits" and here == "%(")        # a ring number in round brackets
                  or ("cannot be read here" in message and (
                      here[0] in "<>" or here[0] == "i" and s[position - 1] == "s"
                      or here[0] in DIGITS and re.search(r"H[0-9]$", s[:position])             # a second digit of hydrogens
                      or here[0] in DIGITS and re.search(r"[+-][0-9][0-9]$", s[:position])     # a third digit of a charge
                      or here[0] == "~" or ord(here[0]) > 126                                  # `~`; outside ASCII
                      or s[position - 2:position + 2] in tuple("[" + name for name in others.OLD_NAMES))))   # an old name
        count["the model refuses, RDKit reads: " + ("'X' cannot be read here" if "cannot be read here" in message else re.sub(r"ring \d+", "ring N", message))] += 1
        if not listed:
            fail("C", "the model refuses a text that RDKit reads, in a way sections 11.2 and 12.4 do not list", s)
        continue
    ours = others.without_stereo(model.read(s))
    without_zeros = ""                  # set where RDKit refuses the text and reads it without its zeros
    if theirs is None:
        # Three of the listed kinds can be written in a way that RDKit reads: a mass number without the
        # zeros in front of it ("[013C]" becomes "[13C]"), a ring number without `%0` ("%01" becomes
        # "1"), a charge without its zero in front ("[C+07]" becomes "[C+7]"; only inside square
        # brackets, since behind a bond symbol a 0 is a ring number). Written so, the text must give
        # RDKit the Mol that the model reads; that is asked below. For two kinds there is no such
        # rewriting, and a text that holds one is set aside whole: a branch that starts with a dot, and
        # a mass number above the most that RDKit takes.
        plainer = re.sub(r"\[0+(?=[0-9])", "[", s)
        plainer = re.sub(r"%0([0-9])", r"\1", plainer)
        plainer = re.sub(r"\[[^\[\]]*\]", lambda inside: re.sub(r"(?<=[+-])0+(?=[0-9])", "", inside.group(0)), plainer)
        theirs = others.rdkit_mol(plainer) if plainer != s else None
        if theirs is not None:
            without_zeros = "the model reads, RDKit refuses: a zero in front of a mass number, a ring number or a charge. Without it, "
        elif "(." in s or any(int(number) > others.MOST_THAT_RDKIT_TAKES for number in re.findall(r"\[([0-9]+)", s)):
            count["the model reads, RDKit refuses: a branch that starts with a dot, or a mass number above 2,147,483,639"] += 1
            continue
        else:
            count["the model reads, RDKit refuses"] += 1
            fail("C", "the model reads a text that RDKit refuses, in a way section 11.2 does not list", s)
            continue
    if ours == theirs:
        count[without_zeros + "RDKit reads the same atoms and bonds" if without_zeros else "both read the same atoms and bonds"] += 1
    else:
        raw = [t.value for t in model.tokens_of(s) if t.kind == "atom"]
        listed = len(ours.atoms) == len(theirs.atoms) and ours.bonds == theirs.bonds
        if listed:
            nb = model.neighbours_of(ours)
            order = {(b.a, b.b): b.order for b in ours.bonds}
            for i, (a, b, r_) in enumerate(zip(ours.atoms, theirs.atoms, raw)):
                if (a.element, a.charge) != (b.element, b.charge):
                    listed = False
                if a.hydrogens != b.hydrogens:                  # only at a bare atom, in one of the five situations
                    orders = [order[(min(i, j), max(i, j))] for j in nb[i]]
                    total = sum(model.WEIGHT[o] for o in orders)
                    if not (r_.hydrogens is None and others.one_of_the_five(a.element, r_.aromatic, total, "aromatic" in orders)):
                        listed = False
                if a.isotope != b.isotope and not (a.isotope == 0 and b.isotope is None) and not (
                        a.isotope is not None and a.isotope >= 65536 and (a.isotope % 65536 or None) == b.isotope):
                    listed = False                              # isotope 0; a mass number from 65,536 on
        count[(without_zeros + "RDKit reads it differently" if without_zeros else "both read, but differently")
              + ": hydrogens of a bare atom, isotope 0, or a mass number from 65,536 on"] += 1
        if not listed:
            fail("C", "both read the text, but differ in a way section 11.2 does not list", s)
print(f"\n({len(seen)} different texts)", end="")
show("C  The model against RDKit, clean-up off", count)

# --------------------------------------------------------------- D: the round trip on random Mols
POOL = ["C"] * 8 + ["N", "O", "S", "P", "B", "F", "Cl", "Br", "I", "H", "Se", "As", "Fe", "Na", "Si", "Co", "Sc", "Cn", "Hf", "U"]


def random_mol(rng, with_stereo):
    """A well formed Mol that need not make any chemical sense."""
    n = rng.randint(0, 7)
    density = rng.choice([0.2, 0.4, 0.7])
    bonds = {(a, b): rng.choice(["single"] * 5 + ["double", "double", "triple", "quadruple", "aromatic"])
             for a in range(n) for b in range(a + 1, n) if rng.random() < density}
    nb = model.neighbours(n, bonds)
    atoms, orientations = [], []
    for i in range(n):
        element = rng.choice(POOL)
        orders = [bonds[(min(i, j), max(i, j))] for j in nb[i]]
        total = sum(model.WEIGHT[order] for order in orders)
        lowercase = "aromatic" in orders and element in model.LOWERCASE_OF     # as the writer will write it
        if element in model.VALENCES and rng.random() < 0.6:
            h = model.bare_hydrogens(element, lowercase, total)         # often just what a bare atom would get
        else:
            h = rng.choice([0, 0, 0, 1, 1, 2, 3, 4, 9, 10])
        if with_stereo and rng.random() < 0.5 and ((len(nb[i]) == 4 and h == 0) or (len(nb[i]) == 3 and h <= 1)):
            orientations.append(model.AtomOrientation(i, rng.choice(["anticlockwise", "clockwise"])))
        atoms.append(model.Atom(element, rng.choice([None] * 6 + [0, 13, 255]),
                                rng.choice([0] * 8 + [1, -1, 2, -2, 10, 99, -99, 100]), h))
    out, geometries = [], []
    for (a, b), order in sorted(bonds.items()):
        if with_stereo and order == "double" and rng.random() < 0.6 and 2 <= len(nb[a]) <= 3 and 2 <= len(nb[b]) <= 3:
            geometries.append(model.BondGeometry(a, b, rng.choice(["sameSide", "oppositeSides"])))
        out.append(model.Bond(a, b, order))
    return model.Mol(tuple(atoms), tuple(out), tuple(orientations), tuple(geometries))


for with_stereo in (False, True):
    # With stereo facts: an atom or a double bond that can have one gets one at random, so not every Mol
    # holds one. The Mols that do are counted.
    which = "in which stereo facts are given at random" if with_stereo else "without stereo facts"
    count, rng = collections.Counter(), random.Random(2028 if with_stereo else 2027)
    for _ in range(100000):
        mol = random_mol(rng, with_stereo)
        if not model.is_well_formed(mol):
            fail("D", "a random Mol is not well formed", mol.bonds[:5])
            continue
        if model.has_stereo(mol):
            count["Mols that hold a stereo fact"] += 1
        for round_brackets in (False, True):
            name = "round brackets: " if round_brackets else "plain spelling: "
            try:
                text = model.spell(mol, round_brackets)
            except model.WriteError:
                count[name + "refused by the writer"] += 1
                continue
            back = model.read_or_none(text)
            if back != mol:
                fail("D", "reading the written text does not return the Mol", text)
                continue
            count[name + "a text came out, and reading it returns exactly the Mol"] += 1
            if not with_stereo:
                theirs = others.rdkit_mol(text)
                # RDKit reads no isotope where 0 is written (SPEC.md, section 11.2). Only that is excused.
                if theirs is None or theirs.bonds != mol.bonds or len(theirs.atoms) != len(mol.atoms) or any(
                        a != b and not (a.isotope == 0 and b == model.Atom(a.element, None, a.charge, a.hydrogens))
                        for a, b in zip(mol.atoms, theirs.atoms)):
                    fail("D", "RDKit reads something else from the written text", text)
                elif others.rdkit_lowercase(text) != others.lowercase_by_rule(mol):
                    fail("D", "a symbol of the written text is in another case than section 9 says, as RDKit reads it", text)
                else:
                    count[name + "RDKit reads that Mol, with a lowercase symbol exactly where section 9 asks for one"] += 1
    show(f"D  The round trip on 100,000 random well formed Mols {which}", count)
    # Least counts: a writer that refuses nearly every Mol makes no round trip, and nothing above fails.
    for name in ("plain spelling: ", "round brackets: "):
        kinds = ["a text came out, and reading it returns exactly the Mol"]
        kinds += ["RDKit reads that Mol, with a lowercase symbol exactly where section 9 asks for one"] if not with_stereo else []
        for kind in kinds:
            if count[name + kind] < 40000:
                fail("D", f"too few of the 100,000 Mols {which}: at least 40,000 are expected", f"{count[name + kind]}  {name}{kind}")
    if with_stereo and count["Mols that hold a stereo fact"] < 10000:
        fail("D", "too few of the 100,000 Mols hold a stereo fact: at least 10,000 are expected", count["Mols that hold a stereo fact"])

# ------------------------------------------------- D, second part: Mols near the limit of 99 ring numbers
RING_MESSAGE = "more than 99 ring numbers are needed at the same time"
NEAR_ELEMENTS = ["C"] * 6 + ["N", "O", "S", "P", "Fe", "Si"]
NEAR_ORDERS = ["single"] * 6 + ["double", "triple", "aromatic"]


def mol_near_the_limit(rng):
    """A well formed Mol in which one atom, the hub, has about 100 neighbours before it, or behind it, or
    both. Where the hub stands among the atom numbers decides how many ring numbers a spelling needs: about
    99, or none."""
    k = rng.randint(96, 103)                                # the neighbours of the hub that count
    shape = rng.randrange(5)
    if shape == 0:                                          # the hub first, then its neighbours
        n, bonds = 1 + k, {(0, j) for j in range(1, 1 + k)}
    elif shape == 1:                                        # the hub first, then an atom that is not bonded to it
        n, bonds = 2 + k, {(0, j) for j in range(2, 2 + k)}
    elif shape == 2:                                        # the hub last
        n, bonds = k + 1, {(j, k) for j in range(k)}
    elif shape == 3:                                        # the hub first, and a chain behind it that it is bonded to
        n = 1 + k + rng.randint(0, 6)
        bonds = {(j - 1, j) for j in range(1, n)} | {(0, j) for j in rng.sample(range(2, n), k - 1)}
    else:                                                   # the hub in the middle: about 100 before it, about 100 behind
        behind = rng.randint(96, 103)
        n, bonds = k + 1 + behind, {(j, k) for j in range(k)} | {(k, j) for j in range(k + 1, k + 1 + behind)}
    for _ in range(rng.choice([0, 0, 1, 2, 3])):            # a few atoms more at the end, each bonded to an earlier atom
        bonds.add((rng.randrange(n), n))
        n += 1
    for _ in range(rng.choice([0, 0, 1, 2])):               # a few bonds more
        bonds.add(tuple(sorted(rng.sample(range(n), 2))))
    return model.Mol(tuple(model.Atom(rng.choice(NEAR_ELEMENTS), None, 0, 0) for _ in range(n)),
                     tuple(model.Bond(a, b, rng.choice(NEAR_ORDERS)) for a, b in sorted(bonds)))


def ring_numbers_needed(mol):
    """How many ring numbers the two spellings of a Mol need at the same time: (plain, with round brackets).
    Counted from SPEC.md, sections 9.1 and 9.2, without the model's writer."""
    n, bonded = len(mol.atoms), {(b.a, b.b) for b in mol.bonds}
    # 9.1: a bond gets a ring number, unless it joins an atom and the atom just before it.
    plain = [(a, b) for a, b in bonded if b != a + 1]
    # 9.2: a bond gets a ring number, unless it joins an atom and its parent. Among the atoms of the path that an
    # atom is bonded to, the one written last is its parent; the path is cut back to the parent and goes on with
    # the atom. Without a parent, the path starts again with the atom.
    path, to_a_parent = [], set()
    for i in range(n):
        parent = next((p for p in reversed(path) if (p, i) in bonded), None)
        if parent is None:
            path = [i]
        else:
            to_a_parent.add((parent, i))
            path = path[:path.index(parent) + 1] + [i]
    brackets = [bond for bond in bonded if bond not in to_a_parent]

    def most_at_once(with_a_number):
        most = now = 0
        for i in range(n):
            now -= sum(1 for _, b in with_a_number if b == i)         # an atom first closes the numbers that end at it
            now += sum(1 for a, _ in with_a_number if a == i)         # and then opens those that begin at it
            most = max(most, now)
        return most
    return most_at_once(plain), most_at_once(brackets)


count, rng = collections.Counter(), random.Random(2029)
for _ in range(3000):
    mol = mol_near_the_limit(rng)
    if not model.is_well_formed(mol):
        fail("D", "a Mol near the limit is not well formed", mol.bonds[:5])
        continue
    for round_brackets, needed in zip((False, True), ring_numbers_needed(mol)):
        name = "round brackets: " if round_brackets else "plain spelling: "
        if needed in (99, 100):
            count[name + f"Mols whose spelling needs exactly {needed} ring numbers"] += 1
        try:
            text = model.spell(mol, round_brackets)
        except model.WriteError as e:
            if needed <= 99 or str(e) != RING_MESSAGE:
                fail("D", f"{name}the writer refuses with \"{e}\", and the spelling needs {needed} ring numbers", mol.bonds[:5])
            else:
                count[name + "more than 99 are needed, and the writer refuses with the message about ring numbers"] += 1
            continue
        if needed > 99:
            fail("D", f"{name}a text came out, although the spelling needs {needed} ring numbers", text)
            continue
        back = model.read_or_none(text)
        if back != mol:
            fail("D", "reading the written text does not return the Mol", text)
            continue
        count[name + "at most 99 are needed, a text came out, and reading it returns exactly the Mol"] += 1
show("D  Near the limit of 99 ring numbers: 3,000 well formed Mols in which one atom has about 100 neighbours", count)
# Least counts: the limit must be met from both sides, in both spellings.
for name in ("plain spelling: ", "round brackets: "):
    for kind, least in (("Mols whose spelling needs exactly 99 ring numbers", 200),
                        ("Mols whose spelling needs exactly 100 ring numbers", 200),
                        ("at most 99 are needed, a text came out, and reading it returns exactly the Mol", 1000),
                        ("more than 99 are needed, and the writer refuses with the message about ring numbers", 1000)):
        if count[name + kind] < least:
            fail("D", f"too few of the 3,000 Mols near the limit: at least {least} are expected", f"{count[name + kind]}  {name}{kind}")

print("\n" + (f"{len(failures)} FAILURES" if failures else "No failure in any of the four attacks."))
sys.exit(1 if failures else 0)
