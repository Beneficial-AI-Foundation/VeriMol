"""Check the Lean program against the model, text by text.

    .venv/bin/python -I reference/check_app.py                 all texts
    .venv/bin/python -I reference/check_app.py --limit 3000    a quick look at a sample
    .venv/bin/python -I reference/check_app.py --every-start   all texts, and the program itself is started
                                                               for every one of them, which takes far longer

`--workers` and a number says how many workers the first part starts. Any other argument is refused: a
mistyped option must not start the whole run.

What is asked is a list of command-line arguments: what stands behind `app` when the program is called.
Here that is a text alone, or one of the words `rewrite`, `plain` and `canonical` and a text, or the words
`filter perfluoro`, a number and a text (SPEC.md, sections 8 and 16). An answer is three things: the text
for standard output, the text for standard error and the exit code. All three must be exactly what the
model gives (model.py, which is SPEC.md as a Python program), character for character.

The check has two parts. Both programs are built first, by `lake build app answers`.

The first part asks about every list of arguments. It compares what `VeriMol.run` gives, the function that is
the whole program, with what the model gives. `VeriMol.run` is asked through a second small program,
`.lake/build/bin/answers`, which answers up to a thousand lists of arguments in one start (Answers.lean).

The second part starts the program itself, `.lake/build/bin/app`, once for one list of arguments, as a user
does, and compares what it prints on standard output, what it prints on standard error and its exit code
with what the model gives. It does so for a sample (the function `sample_of` says which lists), or, with
`--every-start`, for every list.

The texts come in seven groups, which the function `all_texts` makes. Four of them (`WRITTEN`) are also
given behind the words `rewrite`, `plain` and `canonical`, and `main` says which stand behind the words
`filter perfluoro`, and with which number. The random choices are fixed, so every run tries the same
texts, and starts the program itself for the same ones.

reference/README.md, "Reading the output of `check_app.py`", says the rest: why the check has two parts,
what the first part takes for granted and what stands against a mistake there, what each group of texts
holds, how the sample is taken, what happens when a start of the second program goes wrong, how many
workers run, and how to read the report.

While it runs, the script prints a line now and then. A line in CAPITALS is a failure. The script then ends
with exit code 1.
"""
import collections
import multiprocessing
import os
import random
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model
import sources

ROOT = HERE.parent
APP = ROOT / ".lake" / "build" / "bin" / "app"              # the program itself
ANSWERS = ROOT / ".lake" / "build" / "bin" / "answers"      # the second program (Answers.lean)
SECONDS = 600                   # how long one start may take, of either program
SAMPLE = 1000                   # for about how many lists of each part of the report the program itself is
                                # started
LISTS, BYTES = 1000, 100000     # the most lists of arguments, and the most bytes of arguments, that one start
                                # of the second program gets: a system hands a program only so many bytes
MOST_REFUSED = 20               # after more than so many starts of the second program that did not end as
                                # they must, the first part stops
COMPARERS = 8                   # how many workers the first part starts, unless --workers asks for another
                                # number
STARTERS = 2                    # how many workers the second part starts: two, so that the machine stays
                                # usable while the check runs
PER_SECOND = 80                 # a rough guess, from one desktop machine, of how many starts a second the
                                # second part gets through with its two workers; used only to say about how
                                # long a run may take
MODEL_AS_LOADED = sources.sha256_of(HERE / "model.py")      # taken when the model was loaded
DAMAGED, MIXED, INVENTED, TURNED, NEAR, FLUORINATED = 400000, 50000, 50000, 20000, 400, 30000
WORDS = model.WORDS             # the commands that take a text (SPEC.md, section 8)
WRITTEN = ("real", "invented", "turned", "near-limit")    # the groups whose texts are also given to these commands
SHIFTS = len(WORDS) + 3         # the parts of the report for one group of texts begin their samples at so
                                # many different places (the function `sample_of`)
# The three errors that `canonical` can give for a Mol without stereo facts, beyond those of the reader
# (SPEC.md, sections 3.2 and 8), as this script counts them. A whole run must have seen each behind the
# word `canonical`.
ERRORS_OF_CANONICAL = [
    "the chosen form is not worked out: too many numberings of this molecule look alike",
    "the chosen form is not worked out: more than 1000 atoms",
    "more than 99 ring numbers are needed at the same time"]

# The messages of SPEC.md, sections 6 and 12.2, as this script counts them: every ring number is written N,
# and every character that cannot be read is written X.
MESSAGES = [
    "white space is not allowed", "the wildcard atom is not read",
    "atom classes are not read", "an element symbol is expected here", "a hydrogen atom cannot have a hydrogen count",
    "'[' is never closed", "'%' must be followed by two digits", "'X' cannot be read here",
    "an atom is expected here", "an atom or a ring number is expected here",
    "a ring number must come before the branches of its atom", "')' has no matching '('",
    "an atom cannot be bonded to itself", "the two ends of ring N name different bonds",
    "these two atoms are already bonded", "the text ends after a bond symbol", "the text ends after a dot",
    "'(' is never closed", "ring N is opened but never closed",
    # the messages about stereo marks (section 12.2)
    "this stereo class is not read", "the two ends of ring N name different directions",
    "this atom cannot be a stereo centre", "a stereo centre with a free place needs an atom before it",
    "a stereo centre with a free place, one ring number and only single bonds is not read",
    "these marks contradict each other", "this mark has no partner on the other side of a double bond"]
# The messages of the filter (SPEC.md, sections 16.2 and 16.3), as this script counts them: every number of
# an atom and every size is written N. A whole run must have seen each behind the words `filter perfluoro`.
# (The message for a Mol that is not well formed is not here: the reader gives no such Mol, theorem 8.)
MESSAGES_OF_THE_FILTER = [
    "the Mol is not sound: atom N is no atom of B, C, N, O, P, S, F, Cl, Br or I",
    "the Mol is not sound: atom N has a mass number",
    "the Mol is not sound: atom N has a charge",
    "the Mol is not sound: atom N has exactly one aromatic bond",
    "the Mol is not sound: the bonds and hydrogens of atom N add up to no usual valence of its element",
    "the Mol has a perfluorinated group of size N, and size N or more is refused"]
PASSED = "the Mol is sound and the rule holds: it passes the filter, and is printed"
READ = "the text is read, and the Mol is printed"
SAME = "the text is written back as it stands, character for character"
OTHER = "the text is written back in another spelling"


# ------------------------------------------------------------------------------- pieces of SMILES
# What is frequent in real texts stands in a list several times.
ATOMS = list("CCCCCCCCCCNNNOOOOSPFIBccccccccnnosbp") + [
    "Cl", "Br", "[nH]", "[O-]", "[N+]", "[NH4+]", "[Na+]", "[13C]", "[013C]", "[0C]", "[2H]", "[Fe++]", "[Fe+2]",
    "[C+0]", "[C--]", "[CH0]", "[H]", "[H+]", "[se]", "[as]", "[Se]", "[Og]", "[Nh]", "[CH3]", "[OH-]", "[cH]"]
BONDS = list("--===##$::")
MARKS = ["/", "\\"]            # the two direction marks (SPEC.md, section 12.2)
RING_NUMBERS = list("1111222233445678900") + ["%10", "%11", "%01", "%99", "%12"]
BRANCHES = ["(", ")", "(", ")", "(", ")", "(C)", "(=O)", "C(", "C)", "()", "(."]
# Pieces that are wrong anywhere, or wrong at most places: a stereo mark is read only where it fits.
WRONG = list("@/\\*%[]H+>~?!&,;'\"ADEGLMRTXZadeghilmrtux") + [
    "[Fe+++]", "[CH10]", "[HH]", "[te]", "[si]", "[Xx]", "[CH3:1]", "[C@H]", "[C@@H]", "[C@TH1]", "[C@", "[C@@", "[H",
    "[H@", "[Cl", "[Br", "[se", "[as", "@@", "@TH1", "H2", "+2", "+99", "-12", "--", "++", "se", "as", "99", "->", "<-",
    ">>", "[]", "[*]", "*"]
# Characters that no SMILES text contains. The character number 0 is not among them: no program can be
# given it in an argument.
ODD = [
    " ", "\t", "\n", "\r",                              # the four kinds of white space of SPEC.md, section 2
    "\x0b", "\x0c", "\x01", "\x1b", "\x7f",             # other control characters
    # spaces that are not white space in SPEC.md
    "\N{NO-BREAK SPACE}", "\N{EM SPACE}", "\N{IDEOGRAPHIC SPACE}", "\N{ZERO WIDTH SPACE}",
    # letters that are not letters of SMILES; three of them look like C
    "\N{LATIN SMALL LETTER E WITH ACUTE}", "\N{CYRILLIC CAPITAL LETTER ES}", "\N{FULLWIDTH LATIN CAPITAL LETTER C}",
    "\N{MATHEMATICAL BOLD CAPITAL C}", "\N{COMBINING ACUTE ACCENT}",
    # digits that are not 0 to 9
    "\N{SUPERSCRIPT TWO}", "\N{ARABIC-INDIC DIGIT THREE}", "\N{FULLWIDTH DIGIT THREE}",
    # a byte order mark, the replacement character, an emoji, and six characters of ASCII
    "\N{ZERO WIDTH NO-BREAK SPACE}", "\N{REPLACEMENT CHARACTER}", "\N{GRINNING FACE}",
    "`", "|", "{", "}", "^", "_"]

# The parts of an atom in square brackets, in the order in which they are written. For each part: forms
# that are read, and forms that are not. One atom in ten gets `@` or `@@`, which is read where the atom
# has four places (SPEC.md, section 12.2, rule 9).
BRACKET_PARTS = [
    (["", "", "", "", "", "", "1", "2", "13", "0", "00", "013", "235", "999", "12345678901234567890"], []),
    (model.ELEMENTS + ["b", "c", "n", "o", "p", "s", "se", "as"] * 4,
     ["", "te", "si", "cl", "CL", "hE", "h", "X", "Xx", "R", "D", "T", "*", "13", " ", "?"]),
    ([""] * 18 + ["@", "@@"], ["@@@", "@TH1", "@SP1", "/"]),
    (["", "", "", "H", "H", "H2", "H3", "H4", "H9", "H0", "H1"], ["H10", "HH", "h", "H-"]),
    (["", "", "", "+", "-", "++", "--", "+2", "-2", "+1", "-1", "+0", "-0", "+10", "-10", "+99", "-99"],
     ["+100", "+++", "---", "+-", "-+", "++2", "2+", "+ ", "+H"]),
    (["]"], [":1]", ":]", " ]", "X]", "]]", "*]", "(]", ""])]


def bracket_atom(rng, wrong):
    """Square brackets with a random inside. Each part is a form that is not read with probability `wrong`."""
    return "[" + "".join(rng.choice(bad if bad and rng.random() < wrong else good) for good, bad in BRACKET_PARTS)


def piece(rng):
    """One piece: most often an atom, now and then something wrong."""
    dice = rng.random()
    if dice < 0.48:
        return rng.choice(ATOMS)
    if dice < 0.58:
        return rng.choice(BONDS)
    if dice < 0.70:
        return rng.choice(RING_NUMBERS)
    if dice < 0.82:
        return rng.choice(BRANCHES)
    if dice < 0.86:
        return "."
    if dice < 0.92:
        return bracket_atom(rng, 0.1)
    if dice < 0.935:
        return rng.choice(ODD)
    return rng.choice(WRONG)


# ------------------------------------------------------------------------------- damaged texts
# Each damage takes a text and returns it changed in one place. It returns the text as it is where it
# finds nothing to change.
def place(rng, s):
    """The place of one character of the text. None if the text is empty."""
    return rng.randrange(len(s)) if s else None


def change_an_atom(rng, s):
    """A letter that can be an atom on its own becomes another atom."""
    letters = [i for i, c in enumerate(s) if c in "BCNOPSFIbcnops"]
    if not letters:
        return s
    i = rng.choice(letters)
    return s[:i] + rng.choice(ATOMS) + s[i + 1:]


def change_a_bond(rng, s):
    """A bond symbol becomes another one, or one more is put in."""
    symbols = [i for i, c in enumerate(s) if c in model.ORDER_OF]
    if symbols and rng.random() < 0.6:
        i = rng.choice(symbols)
        return s[:i] + rng.choice(BONDS) + s[i + 1:]
    i = rng.randint(0, len(s))
    return s[:i] + rng.choice(BONDS) + s[i:]


def renumber_a_ring(rng, s):
    """One digit becomes another ring number wherever it stands, also a number written with %."""
    digits = sorted({c for c in s if c in model.DIGITS})
    return s.replace(rng.choice(digits), rng.choice(RING_NUMBERS)) if digits else s


def bond_symbols_at_a_ring(rng, s):
    """A bond symbol in front of the first two places of one digit: the same symbol twice, or two symbols."""
    twice = sorted({c for c in s if c in model.DIGITS and s.count(c) > 1})
    if not twice:
        return s
    digit = rng.choice(twice)
    i = s.index(digit)
    j = s.index(digit, i + 1)
    first = rng.choice(BONDS)
    second = first if rng.random() < 0.5 else rng.choice(BONDS)
    return s[:i] + first + s[i:j] + second + s[j:]


def turn_a_mark_round(rng, s):
    """One stereo mark becomes the other one: `@` and `@@` are exchanged, or `/` and `\\`."""
    marks = [(found.start(), found.end(), {"@@": "@", "@": "@@", "/": "\\", "\\": "/"}[found.group()])
             for found in re.finditer(r"@@|@|/|\\", s)]
    if not marks:
        return s
    start, end, other = rng.choice(marks)
    return s[:start] + other + s[end:]


def direction_marks_at_a_ring(rng, s):
    """A direction mark in front of the first two places of one digit: the same mark twice, the two marks, a
    mark and a bond symbol, or a mark at the first place only."""
    twice = sorted({c for c in s if c in model.DIGITS and s.count(c) > 1})
    if not twice:
        return s
    digit = rng.choice(twice)
    i = s.index(digit)
    j = s.index(digit, i + 1)
    first = rng.choice(MARKS)
    second = rng.choice([first, first, "/", "\\", rng.choice(BONDS), ""])
    return s[:i] + first + s[i:j] + second + s[j:]


def remove_a_character(rng, s):
    i = place(rng, s)
    return s if i is None else s[:i] + s[i + 1:]


def double_a_character(rng, s):
    i = place(rng, s)
    return s if i is None else s[:i] + s[i] + s[i:]


def replace_by_a_piece(rng, s):
    i = place(rng, s)
    return s if i is None else s[:i] + piece(rng) + s[i + 1:]


def put_in_a_piece(rng, s):
    i = rng.randint(0, len(s))
    return s[:i] + piece(rng) + s[i:]


def cut_off_the_end(rng, s):
    return s[:rng.randint(0, max(0, len(s) - 1))]


def cut_off_the_start(rng, s):
    return s[rng.randint(1, max(1, len(s))):]


def remove_a_stretch(rng, s):
    i = place(rng, s)
    return s if i is None else s[:i] + s[i + rng.randint(2, 6):]


def copy_a_stretch(rng, s):
    i, j = place(rng, s), rng.randint(0, len(s))
    return s if i is None else s[:j] + s[i:i + rng.randint(1, 6)] + s[j:]


def swap_two_neighbours(rng, s):
    if len(s) < 2:
        return s
    i = rng.randrange(len(s) - 1)
    return s[:i] + s[i + 1] + s[i] + s[i + 2:]


def change_the_case_of_a_letter(rng, s):
    letters = [i for i, c in enumerate(s) if c.isalpha()]
    if not letters:
        return s
    i = rng.choice(letters)
    return s[:i] + s[i].swapcase() + s[i + 1:]


def change_a_digit(rng, s):
    digits = [i for i, c in enumerate(s) if c in model.DIGITS]
    if not digits:
        return s
    i = rng.choice(digits)
    return s[:i] + rng.choice([d for d in model.DIGITS if d != s[i]]) + s[i + 1:]


def put_in_an_odd_character(rng, s):
    i = rng.randint(0, len(s))
    return s[:i] + rng.choice(ODD) + s[i + rng.randint(0, 1):]


def put_in_a_bracket_atom(rng, s):
    i = rng.randint(0, len(s))
    return s[:i] + bracket_atom(rng, 0.15) + s[i + rng.randint(0, 1):]


# The first ten damages are gentle: the text is often still read afterwards, as another molecule. They
# stand in the list twice, so that they are chosen twice as often as the others.
DAMAGES = 2 * [change_an_atom, change_a_bond, renumber_a_ring, bond_symbols_at_a_ring, turn_a_mark_round,
               direction_marks_at_a_ring, remove_a_character, double_a_character, replace_by_a_piece,
               put_in_a_piece] + [
    cut_off_the_end, cut_off_the_start, remove_a_stretch, copy_a_stretch, swap_two_neighbours,
    change_the_case_of_a_letter, change_a_digit, put_in_an_odd_character, put_in_a_bracket_atom]


def damaged_text(rng, whole):
    """One of the texts of `whole` after one to three damages."""
    text = rng.choice(whole)
    for _ in range(rng.choice((1, 1, 2, 3))):
        text = rng.choice(DAMAGES)(rng, text)
    return text


def turned_text(rng, marked):
    """One of the texts of `marked`, which all carry stereo marks, with one to three of its marks turned
    round."""
    text = rng.choice(marked)
    for _ in range(rng.choice((1, 1, 2, 3))):
        text = turn_a_mark_round(rng, text)
    return text


# ------------------------------------------------------------------------------- mixed and invented texts
def mixed_text(rng):
    """One to ten pieces in random order. Nine times in ten the first piece is an atom."""
    first = rng.choice(ATOMS) if rng.random() < 0.9 else piece(rng)
    return first + "".join(piece(rng) for _ in range(rng.randint(0, 9)))


def ring_number(rng, number):
    """A ring number as it is written: 7, or %07. From 10 on it needs the %."""
    return f"%{number:02d}" if number > 9 or rng.random() < 0.1 else str(number)


def invented_text(rng):
    """A random text of the grammar of SPEC.md, sections 4 and 12.2 (of the stereo marks it has `@` and
    `@@` only). While writing, it keeps track of which atoms are bonded, so that a ring number never closes
    at its own atom or between two atoms that are bonded already. So most of these texts are read."""
    out, bonded, open_numbers, atoms = [], set(), {}, 0

    def atom(previous):
        """Writes one atom with its ring numbers. `previous` is the atom it is bonded to, or None."""
        nonlocal atoms
        this, atoms = atoms, atoms + 1
        if previous is not None:
            bonded.add((previous, this))
        out.append(bracket_atom(rng, 0) if rng.random() < 0.15 else rng.choice(ATOMS))
        while rng.random() < 0.3:
            closable = [n for n, other in open_numbers.items() if other != this and (other, this) not in bonded]
            if closable and rng.random() < 0.6:
                number = rng.choice(closable)
                bonded.add((open_numbers.pop(number), this))
            else:
                number = rng.choice([n for n in 5 * list(range(10)) + list(range(10, 100)) if n not in open_numbers])
                open_numbers[number] = this
            out.append((rng.choice(BONDS) if rng.random() < 0.25 else "") + ring_number(rng, number))
        return this

    def chain(depth, previous):
        """Writes a chain. `previous` is the atom its first atom is bonded to, or None. Returns its last atom."""
        for k in range(rng.choice((1, 1, 2, 2, 3, 4, 6))):
            if k > 0:
                dice = rng.random()
                out.append(rng.choice(BONDS) if dice < 0.3 else "." if dice < 0.36 else "")
                previous = None if out[-1] == "." else previous
            previous = atom(previous)
            while depth < 3 and rng.random() < 0.2:
                dice = rng.random()
                first = rng.choice(BONDS) if dice < 0.3 else "." if dice < 0.35 else ""
                out.append("(" + first)
                chain(depth + 1, None if first == "." else previous)
                out.append(")")
        return previous

    last = chain(0, None)
    for number, other in list(open_numbers.items()):    # what is still open is closed, at one more atom each
        out.append("" if other != last and rng.random() < 0.5 else ".")
        last = atoms
        atoms += 1
        out.append(rng.choice(ATOMS) + ring_number(rng, number))
    return "".join(out)


def fluorinated_text(rng):
    """An invented compound for the filter (SPEC.md, section 16): a skeleton of carbon atoms, with an oxygen,
    nitrogen or sulfur atom here and there, a ring now and then, and on the carbon atoms mostly fluorine.

    The skeleton is a random tree of 1 to 18 atoms with up to two bonds more, which close rings. Each
    carbon atom then gets something for every bond that it has left: most often a fluorine atom; less often
    nothing, which the reader takes for a hydrogen; and now and then chlorine, bromine, iodine, a methyl
    group, a hydroxy group, an oxygen atom with a double bond, or one of three things that make the Mol
    not sound (a hydrogen as an atom of its own, a charged oxygen atom, a carbon atom with a mass number).
    The text is written from a random atom, with the bonds of each atom in a random order: so a ring
    number can close a perfluorinated group from behind, and a group can be entered at any of its atoms.
    Most of these texts are read as a sound Mol."""
    size = rng.choice((1, 2, 2, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10, 12, 14, 18))
    kinds = [rng.choice("C" * 27 + "ONS") for _ in range(size)]
    free = [{"C": 4, "O": 2, "N": 3, "S": 2}[kind] for kind in kinds]
    joined = {i: [] for i in range(size)}

    def join(a, b):
        joined[a].append(b)
        joined[b].append(a)
        free[a] -= 1
        free[b] -= 1

    for i in range(1, size):                # the tree: each atom is joined to an earlier atom that has room
        earlier = [j for j in range(i) if free[j] > 0]
        if earlier:
            join(rng.choice(earlier), i)
    for _ in range(rng.choice((0, 0, 0, 1, 1, 2))):         # the rings
        pairs = [(a, b) for a in range(size) for b in range(a + 1, size)
                 if free[a] > 0 and free[b] > 0 and b not in joined[a]]
        if pairs:
            join(*rng.choice(pairs))
    hanging = []                            # what hangs on each atom of the skeleton, beside the skeleton
    for i, kind in enumerate(kinds):
        on_it = []
        while kind == "C" and free[i] > 0:
            dice = rng.random()
            what = ("F" if dice < 0.8 else "" if dice < 0.86
                    else rng.choice(["Cl", "Cl", "Br", "I", "C", "C", "O", "=O"]) if dice < 0.985
                    else rng.choice(["[H]", "[O-]", "[13CH3]"]))
            if what == "=O" and free[i] < 2:
                continue
            free[i] -= 2 if what == "=O" else 1
            on_it.append(what)
        hanging.append([what for what in on_it if what])

    # Written from a random atom. A first walk says which bonds lead to a new atom; every other bond gets
    # a ring number, which is written at both of its atoms.
    written, pieces = set(), []
    for start in rng.sample(range(size), size):
        if start in written:
            continue
        children, numbers, walk = {}, {}, [(start, None)]
        while walk:
            i, parent = walk.pop()
            if i in written:
                continue
            written.add(i)
            children[i] = []
            if parent is not None:
                children[parent].append(i)
            walk += [(j, i) for j in rng.sample(joined[i], len(joined[i])) if j not in written]
        in_tree = {(i, j) for i in children for j in children[i]}
        for i in children:
            for j in joined[i]:
                if i < j and j in children and (i, j) not in in_tree and (j, i) not in in_tree:
                    numbers.setdefault(i, []).append(len({number for ns in numbers.values() for number in ns}) + 1)
                    numbers.setdefault(j, []).append(numbers[i][-1])

        def text_of(i):
            out = kinds[i] + "".join(str(number) for number in numbers.get(i, []))
            branches = hanging[i] + [text_of(j) for j in children[i]]
            rng.shuffle(branches)
            return out + "".join(f"({branch})" for branch in branches[:-1]) + "".join(branches[-1:])

        pieces.append(text_of(start))
    return ".".join(pieces)


def different(make, seed, how_many, taken):
    """`how_many` different texts made by `make`, none of them in the set `taken`. They are added to it."""
    rng = random.Random(seed)
    found = []
    while len(found) < how_many:
        text = make(rng)
        if text not in taken:
            taken.add(text)
            found.append(text)
    return found


def near_the_limit():
    """Texts that are made up near the limit of the search for the chosen form (SPEC.md, section 3.2), in
    a fixed order: more than NEAR of them. Nothing is random here. For many of them the search holds
    hundreds of beginnings, and for some of them it gives up."""
    small = ["C", "CC", "CO", "CN", "CCl", "C=C", "C#C", "C=O", "C#N", "CCC", "CCO", "CC=O", "OO", "N=N",
             "C1CC1", "C1CCC1", "[Na+].[Cl-]", "O=C=O", "CS", "FCF", "CBr", "CI", "CF"]
    with_a_stereo_fact = ["C[C@H](N)O", "N[C@@H](C)C(=O)O"]

    def ring(atom, size):
        return atom + "1" + atom * (size - 1) + "1"

    # examples of SPEC.md, section 3.2; texts that get two of the three errors of `ERRORS_OF_CANONICAL`
    # (more than 1,000 atoms, more than 99 ring numbers); and molecules whose arms can be exchanged
    texts = ["C" * 1001, ".".join(["CC"] * 10) + "." + "C" * 981, "C1NN2C1" + "C1N2N2C1" * 49 + "C1N2NC1",
             "C=1=[C](=[C])[C]1", "[N][N][N]1[N][N][N][N]1", "OC[P+](CO)(CO)CO.OC[P+](CO)(CO)CO",
             "c1ccccc1P(c1ccccc1)c1ccccc1", "CCN(CC)CC", "N[Co+3](N)(N)(N)(N)N.Cl[Hg](Cl)Cl", "S(C)(C)(C)(C)(C)(C)C"]
    # molecules of one kind side by side: six to eleven of them
    texts += [".".join([molecule] * count) for count in range(6, 12) for molecule in small[:20]]
    # the same beside a molecule with a stereo fact, for which no beginning is taken out
    texts += [".".join([molecule] * count + [other]) for count in range(3, 8) for molecule in small[:14]
              for other in with_a_stereo_fact]
    # three rings of different atoms, alone and beside alanine
    for sizes in [(a, b, c) for a in (4, 5, 6, 7) for b in (4, 5, 6) for c in (4, 5, 6)]:
        rings = ".".join(ring(atom, size) for atom, size in zip("CNO", sizes))
        texts += [rings, rings + ".N[C@@H](C)C(=O)O"]
    # rings of one kind side by side, two kinds of molecules mixed, stars, and molecules with a geometry
    texts += [".".join([ring("C", size)] * count) for size in (5, 6, 8, 9) for count in range(2, 8)]
    texts += [".".join(["CC"] * one + ["CO"] * other) for one in range(3, 7) for other in range(3, 7)]
    texts += [".".join(["CC(C)(C)C"] * count) for count in range(2, 10)]
    texts += [".".join(["F/C=C/F"] * count) for count in range(2, 9)]
    texts += [".".join([molecule] * count) for count in (9, 10) for molecule in small[20:]]
    return list(dict.fromkeys(texts))


def all_texts():
    """The seven groups, as a dictionary from the name of a group to its texts. No text is in two groups."""
    real = sources.real_texts()
    marked = [t for t in real if sources.has_marks(t)]
    taken = set(real)
    groups = {"real": real,
              "damaged": different(lambda rng: damaged_text(rng, real), 7, DAMAGED, taken),
              "mixed": different(mixed_text, 77, MIXED, taken),
              "invented": different(invented_text, 777, INVENTED, taken),
              "turned": different(lambda rng: turned_text(rng, marked), 7777, TURNED, taken)}
    # The made-up texts come after the random groups above, so that those do not depend on them. One that
    # is a text of another group already is left out.
    near = [text for text in near_the_limit() if text not in taken]
    assert len(near) >= NEAR, f"only {len(near)} made-up texts near the limit, and {NEAR} are needed"
    groups["near-limit"] = near[:NEAR]
    # The fluorinated texts are made last, so that the texts of the other groups do not depend on them.
    groups["fluorinated"] = different(fluorinated_text, 77777, FLUORINATED, taken)
    return groups


# ------------------------------------------------------------------------------- one answer
def message_in(error_line):
    """The message of a line `error: ...` of the program: the line without the word `error` and without
    its position."""
    return re.sub(r"\Aerror: (position [0-9]+: )?", "", error_line)


def kind_of(arguments, answer):
    """What the model answers, as one of a few kinds: the text is read, it is written back as it stands or
    in another spelling, its Mol passes the filter, or one of the messages."""
    stdout, stderr, code = answer
    if code == 0:
        if len(arguments) == 4:
            return PASSED
        return READ if len(arguments) == 1 else SAME if stdout == arguments[1] + "\n" else OTHER
    message = message_in(stderr[:-1])
    message = re.sub(r"(ring|atom|size) [0-9]+", r"\1 N", message)
    return "'X' cannot be read here" if message.endswith("' cannot be read here") else message


def as_bytes(answer):
    """An answer of the model as a program gives it: standard output and standard error as bytes, and the
    exit code."""
    return answer[0].encode("utf-8"), answer[1].encode("utf-8"), answer[2]


def shown(result):
    """An answer, shortened, for a line of the report."""
    stdout, stderr, code = result
    cut = lambda data: repr(data.decode("utf-8", "replace"))[:160]
    ended = "no exit code" if code is None else f"ended by signal {-code}" if code < 0 else f"exit code {code}"
    return f"{ended}, standard output {cut(stdout)}, standard error {cut(stderr)}"


# ------------------------------------------------------------------------------- the first part
def in_starts(lists):
    """Lists of arguments, cut into pieces for one start of the second program each: at most LISTS lists
    and at most BYTES bytes of arguments in a piece, unless one list alone has more. Each piece comes
    with the place of its first list among `lists`."""
    pieces, piece, size = [], [], 0
    for place, arguments in enumerate(lists):
        weight = sum(len(argument.encode("utf-8")) + 1 for argument in arguments) + 3
        if piece and (len(piece) == LISTS or size + weight > BYTES):
            pieces.append((place - len(piece), piece))
            piece, size = [], 0
        piece.append(arguments)
        size += weight
    return pieces + ([(len(lists) - len(piece), piece)] if piece else [])


def answers_in(data):
    """The answers at the beginning of what the second program printed, each as (standard output,
    standard error, exit code), and whether the data holds these answers and nothing else. The program
    prints an answer as one line with three numbers, the exit code and the numbers of bytes of the two
    texts, and then the two texts (Answers.lean)."""
    found, at = [], 0
    while at < len(data):
        end = data.find(b"\n", at)
        numbers = data[at:end].split(b" ") if end >= 0 else []
        if len(numbers) != 3 or not all(number.isdigit() for number in numbers):
            return found, False
        code, for_output, for_error = (int(number) for number in numbers)
        middle = end + 1 + for_output
        if middle + for_error > len(data):
            return found, False
        found.append((data[end + 1:middle], data[middle:middle + for_error], code))
        at = middle + for_error
    return found, True


def ask(lists):
    """One start of the second program for some lists of arguments. Each list is handed over as the
    number of its arguments, followed by the arguments. Returns the answers, one for each list, and
    None; or None and a few words on why the start is refused: it took too long or could not be made,
    it did not end with exit code 0, the program wrote on its own standard error, or it did not print
    exactly one answer for each list."""
    command = [os.fsencode(ANSWERS)]
    for arguments in lists:
        command.append(str(len(arguments)).encode("ascii"))
        command.extend(argument.encode("utf-8") for argument in arguments)
    try:
        run = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=SECONDS)
    except subprocess.TimeoutExpired:
        return None, f"(no answer from the second program after {SECONDS} seconds)"
    except OSError as problem:
        return None, f"(the second program could not be started: {problem})"
    found, nothing_else = answers_in(run.stdout)
    if run.returncode == 0 and not run.stderr and nothing_else and len(found) == len(lists):
        return found, None
    ended = f"ended by signal {-run.returncode}" if run.returncode < 0 else f"exit code {run.returncode}"
    return None, (f"(the second program: {ended}, {len(found)} whole answer{'' if len(found) == 1 else 's'} for "
                  f"{len(lists)} list{'' if len(lists) == 1 else 's'} of arguments"
                  + ("" if nothing_else else ", and more that is no answer")
                  + (f", on its own standard error {run.stderr[:120].decode('utf-8', 'replace')!r})" if run.stderr else ")"))


def compare(item):
    """The first part, for one start of the second program: what `VeriMol.run` gives for some lists of
    arguments of one part of the report, against what the model gives. `start` is the place of the first
    of these lists in its part. Returns the title of the part and that place; how often the model gave
    each kind of answer; for each kind, the place of the first list that got it; how many lists were
    compared; what differs; and None, or a few words on why the start is refused. A start that is refused
    compares nothing: main() says so and asks its lists again."""
    title, start, lists = item
    wanted = [model.run(arguments) for arguments in lists]
    kinds, first = collections.Counter(), {}
    for place, (arguments, answer) in enumerate(zip(lists, wanted)):
        kind = kind_of(arguments, answer)
        kinds[kind] += 1
        first.setdefault(kind, start + place)
    got, problem = ask(lists)               # one answer for each list, or none at all
    if got is None:
        return title, start, kinds, first, 0, [], problem
    wrong = [(arguments, given, as_bytes(answer)) for arguments, answer, given in zip(lists, wanted, got)
             if given != as_bytes(answer)]
    return title, start, kinds, first, len(got), wrong, None


# ------------------------------------------------------------------------------- the second part
def sample_of(runs, first, every):
    """The lists of arguments for which the program itself is started, each with the title of its part of
    the report. With `every`, all of them. Otherwise, of each part:
      - every n-th list, where n is chosen so that about SAMPLE lists are taken. For the parts of the
        three words and of the filter the count begins at another place each, so that the program itself
        gets other texts behind a word than alone;
      - and the first list for each kind of answer that the model gives in that part (`first` holds
        their places), so that the program itself prints every kind of answer at least once.
    The real texts stand in the order of their characters, and the texts of the other groups in the
    order in which they were made."""
    sample = []
    for title, lists, shift in runs:
        if every:
            places = range(len(lists))
        else:
            step = max(1, len(lists) // SAMPLE)
            places = sorted(set(range(shift * step // SHIFTS, len(lists), step))
                            | {place for (part, _), place in first.items() if part == title})
        sample += [(title, lists[place]) for place in places]
    return sample


def examine(item):
    """The second part, for one list of arguments: start the program itself, and compare with the model.
    Returns the part of the report, the kind of the model's answer, and None, or what differs."""
    title, arguments = item
    answer = model.run(arguments)
    expected = as_bytes(answer)
    try:
        run = subprocess.run([os.fsencode(APP)] + [a.encode("utf-8") for a in arguments],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=SECONDS)
        got = (run.stdout, run.stderr, run.returncode)
    except subprocess.TimeoutExpired:
        got = (b"", f"(no answer after {SECONDS} seconds)".encode(), None)
    except OSError as problem:
        got = (b"", f"(the program could not be started: {problem})".encode(), None)
    return title, kind_of(arguments, answer), None if got == expected else (arguments, got, expected)


# ------------------------------------------------------------------------------- the check
def checksums():
    """The sha256 of the two built programs and of the model, as they are on disk now. A file that is
    gone has the checksum "missing"."""
    return {name: sources.sha256_of(path) if path.exists() else "missing"
            for name, path in (("the program", APP), ("the second program", ANSWERS), ("the model", HERE / "model.py"))}


def linked_from(program):
    """What Lake handed to the linker when it made a program, entry by entry: the compiled files, and
    behind them the libraries of Lean and the settings. Lake writes it into the file `<program>.rsp`
    beside the program. An empty list if that file cannot be read."""
    try:
        return re.findall(r'"([^"]*)"', Path(str(program) + ".rsp").read_text())
    except OSError:
        return []


def options(arguments):
    """What the arguments ask for: the numbers behind --limit and --workers, each None if it is not given,
    and whether --every-start is given. None for arguments that are not understood."""
    found = {"--limit": None, "--workers": None, "--every-start": False}
    rest = list(arguments)
    while rest:
        name = rest.pop(0)
        if name == "--every-start" and not found[name]:
            found[name] = True
        elif (name in ("--limit", "--workers") and found[name] is None and rest
              and rest[0].isascii() and rest[0].isdigit() and int(rest[0]) > 0):
            found[name] = int(rest.pop(0))
        else:
            return None
    return found


def built():
    """Builds the two programs from the current files, prints their checksums and that of the model, and
    makes sure that both programs hold the same compiled code of Core. Returns the checksums, or None if
    a check of the Lean program cannot run on what was found; it has then said why."""
    try:
        build = subprocess.run(["lake", "build", "app", "answers"], cwd=ROOT, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
    except FileNotFoundError:
        print("THE PROGRAMS COULD NOT BE BUILT: the command `lake` was not found.")
        return None
    if build.returncode != 0 or not APP.exists() or not ANSWERS.exists():
        print(build.stdout)
        print("THE PROGRAMS COULD NOT BE BUILT: `lake build app answers` failed, see above.")
        return None
    print("The program: .lake/build/bin/app. The second program: .lake/build/bin/answers. Both are built from the "
          "current files by `lake build app answers`.")
    at_the_start = checksums()
    for name, checksum in at_the_start.items():
        print(f"sha256 of {name}: {checksum}")
    if at_the_start["the model"] != MODEL_AS_LOADED:
        print("NOT RUN: THE MODEL ON DISK IS NOT THE MODEL THAT THIS SCRIPT LOADED. It was changed in the last seconds.")
        return None
    # Both programs must hold the same compiled code of Core: what Lake handed to the linker may differ
    # in its first entry only, which is the compiled Main.lean for the one and Answers.lean for the other.
    for_app, for_answers = linked_from(APP), linked_from(ANSWERS)
    of_core = [entry for entry in for_app[1:] if re.search(r"[/\\]ir[/\\]VeriMol[/\\]Core\b", entry)]
    if not (of_core and for_app[1:] == for_answers[1:] and re.search(r"[/\\]Main\.c\.o", for_app[0])
            and re.search(r"[/\\]Answers\.c\.o", for_answers[0])):
        print("NOT RUN: THE TWO PROGRAMS ARE NOT MADE FROM THE SAME COMPILED FILES OF CORE, as far as this script can see. "
              "It reads what Lake handed to the linker, in .lake/build/bin/app.rsp and .lake/build/bin/answers.rsp: the two "
              "must differ in their first entry only, the compiled Main.lean and the compiled Answers.lean.")
        return None
    print(f"Both programs are made from the same {len(of_core)} compiled files of Core: what Lake handed to the linker "
          "differs in the first entry only, the compiled Main.lean and the compiled Answers.lean.")
    return at_the_start


def about(seconds):
    """A number of seconds in words, for a line that says how long something takes."""
    minutes = round(seconds / 60)
    return f"about {minutes} minutes" if minutes > 1 else "about a minute" if minutes == 1 else "under a minute"


def main():
    given = options(sys.argv[1:])
    if given is None:
        print(f"NOT RUN: the arguments {sys.argv[1:]} are not understood. Give none, or any of these: --limit and a "
              "number, --workers and a number, --every-start.")
        return 1
    limit, every = given["--limit"], given["--every-start"]

    at_the_start = built()
    if at_the_start is None:
        return 1

    groups = all_texts()
    if limit:
        groups = {name: texts[::max(1, len(texts) // limit)] for name, texts in groups.items()}
    # What the program is asked: every text alone, and the texts of some groups behind a word. Each
    # entry is a part of the report: its title, its lists of arguments, and a number that says where
    # the sample of the second part begins (0 for a text alone, 1 to 3 for the three words, 4 and 5 for
    # the filter).
    runs = [(f"the {len(texts)} {name} texts", [[text] for text in texts], 0) for name, texts in groups.items()]
    runs += [(f"the {len(groups[name])} {name} texts behind the word {word}", [[word, text] for text in groups[name]], shift)
             for shift, word in enumerate(WORDS, 1) for name in WRITTEN]
    # The filter (SPEC.md, section 16). The real texts with the number 6 and with the number 1. The
    # fluorinated texts with a number from 1 to 8 each, which the length of the text picks. The other
    # groups of `WRITTEN` with the number 1.
    behind_filter = lambda number, text: ["filter", "perfluoro", number, text]
    runs += [(f"the {len(groups['real'])} real texts behind the words filter perfluoro 6",
              [behind_filter("6", text) for text in groups["real"]], 4),
             (f"the {len(groups['real'])} real texts behind the words filter perfluoro 1",
              [behind_filter("1", text) for text in groups["real"]], 5),
             (f"the {len(groups['fluorinated'])} fluorinated texts behind the words filter perfluoro and a number from 1 to 8",
              [behind_filter(str(1 + len(text) % 8), text) for text in groups["fluorinated"]], 4)]
    runs += [(f"the {len(groups[name])} {name} texts behind the words filter perfluoro 1",
              [behind_filter("1", text) for text in groups[name]], 5) for name in WRITTEN[1:]]
    total = sum(len(lists) for _, lists, _ in runs)
    print("Texts: " + ", ".join(f"{len(texts)} {name} ones" for name, texts in groups.items())
          + (f". This is a sample: about {limit} texts of each group, evenly spread, or the whole group where "
             "it has fewer." if limit else "."))

    # How many workers. If the script may use all the processor threads that the machine has, one is left
    # free; if it is fenced in (as with `taskset`), the fence does that already.
    comparers, starters = sources.workers(given["--workers"] or COMPARERS), sources.workers(STARTERS)
    may_use, machine = sources.processor_threads()
    print(f"This script may use {may_use} of the {machine} processor threads.")

    # ---- The first part: every list of arguments, through the second program.
    pieces = [(title, start, piece) for title, lists, _ in runs for start, piece in in_starts(lists)]
    lists_of = {(title, start): piece for title, start, piece in pieces}
    print(f"\nThe first part: {total} lists of arguments, each a text alone, a word and a text, or the words filter "
          f"perfluoro, a number and a text. The second program is "
          f"started {len(pieces)} times for them. {comparers} worker{'s' if comparers > 1 else ''}"
          + ("." if given["--workers"] else f" (--workers and a number asks for another number than {COMPARERS})."),
          flush=True)
    count = collections.Counter()                       # how often the model gave each kind of answer, part by part
    first = {}                                          # the place of the first list of each kind, part by part
    differs = collections.defaultdict(list)             # what differs in the first part, part by part
    refused, stopped, compared = [], False, 0
    with multiprocessing.Pool(comparers) as pool:
        done = 0
        for title, start, kinds, firsts, how_many, wrong, problem in pool.imap_unordered(compare, pieces, chunksize=1):
            for kind, number in kinds.items():
                count[(title, kind)] += number
            for kind, place in firsts.items():
                first[(title, kind)] = min(place, first.get((title, kind), place))
            compared += how_many
            differs[title] += wrong
            if problem is not None:
                refused.append((title, start, problem))
                print(f"A START OF THE SECOND PROGRAM DID NOT END AS IT MUST, for {len(lists_of[(title, start)])} lists of "
                      f"arguments of {title}: {problem}", flush=True)
                if len(refused) > MOST_REFUSED:
                    stopped = True
                    print(f"THE FIRST PART IS STOPPED: MORE THAN {MOST_REFUSED} STARTS OF THE SECOND PROGRAM DID NOT END AS "
                          "THEY MUST.", flush=True)
                    break                               # leaving the block ends the workers
            before, done = done, done + sum(kinds.values())
            if done // 50000 != before // 50000:        # a sign of life
                found = sum(len(m) for m in differs.values())
                print(f"{done:8d} lists of arguments done, " + (f"{found} MISMATCHES SO FAR" if found else "no mismatch so far"),
                      flush=True)
    # The lists of a start that was refused are asked again, alone and one after the other, in this one
    # process: never many starts at the same time. So the report names the lists concerned, and the
    # others are compared all the same.
    if refused and not stopped:
        print(f"The lists of arguments of {'that start' if len(refused) == 1 else 'these starts'} are now asked one by "
              "one.", flush=True)
        for title, start, _ in refused:
            for arguments in lists_of[(title, start)]:
                expected = as_bytes(model.run(arguments))
                alone, problem = ask([arguments])
                given_back = alone[0] if alone else (b"", problem.encode("utf-8"), None)
                compared += 1
                if given_back != expected:
                    differs[title].append((arguments, given_back, expected))

    # ---- The second part: the program itself, for a sample, or for every list with --every-start.
    sample = sample_of(runs, first, every)
    print(f"\nThe second part: the program itself is started {len(sample)} times, "
          + ("once for every one of these lists of arguments" if every else
             f"for about {SAMPLE} lists of arguments of each of the {len(runs)} parts of the report below, evenly "
             "spread (for all of them where a part has fewer), and for at least one of every kind of answer")
          + f". {starters} worker{'s' if starters > 1 else ''}. A rough guess: that takes "
          f"{about(len(sample) / PER_SECOND)}, at {PER_SECOND} starts a second.", flush=True)
    started = collections.Counter()                     # how often the program itself was started, part by part and kind by kind
    starts_differ = collections.defaultdict(list)       # what differs in the second part, part by part
    step = 50000 if every else 5000
    with multiprocessing.Pool(starters) as pool:
        done = 0
        for title, kind, mismatch in pool.imap_unordered(examine, sample, chunksize=100):
            started[(title, kind)] += 1
            if mismatch is not None:
                starts_differ[title].append(mismatch)
            done += 1
            if done % step == 0:                        # a sign of life
                found = sum(len(m) for m in starts_differ.values())
                print(f"{done:8d} starts done, " + (f"{found} MISMATCHES SO FAR" if found else "no mismatch so far"), flush=True)

    # ---- The report.
    def examples(mismatches, who):
        for arguments, got, expected in sorted(mismatches, key=lambda m: (len(m[0][-1]), m[0]))[:10]:
            print(f"          MISMATCH for the arguments {arguments!r}")
            print(f"              {who} {shown(got)}")
            print(f"              the model:   {shown(expected)}")

    for name, _, _ in runs:
        print(f"\n=== {name}, by what the model answers; in square brackets, for how many of them the program itself was started ===")
        kinds = sorted((k for g, k in count if g == name), key=lambda k: (k not in (READ, SAME, OTHER), -count[(name, k)], k))
        for kind in kinds:
            print(f"{count[(name, kind)]:8d}  {kind}  [{started[(name, kind)]}]")
        if differs[name]:
            print(f"{len(differs[name]):8d}  OF THESE GET ANOTHER ANSWER FROM THE SECOND PROGRAM THAN FROM THE MODEL")
            examples(differs[name], "the second program:")
        if starts_differ[name]:
            print(f"{len(starts_differ[name]):8d}  STARTS OF THE PROGRAM ITSELF GAVE ANOTHER ANSWER THAN THE MODEL")
            examples(starts_differ[name], "the program:")

    failed = sum(len(found) for found in differs.values())
    starts_failed = sum(len(found) for found in starts_differ.values())
    missing = [m for m in MESSAGES if not any(count[(name, m)] for name, _, _ in runs)]
    not_started = [m for m in MESSAGES if not any(started[(name, m)] for name, _, _ in runs)]
    too_few = [] if limit else [name for name, lists, _ in runs
                                if sum(n for (part, _), n in started.items() if part == name) < min(SAMPLE, len(lists))]
    behind_canonical = [name for name, _, _ in runs if name.endswith("behind the word canonical")]
    not_given = [m for m in ERRORS_OF_CANONICAL if not any(count[(name, m)] for name in behind_canonical)]
    not_printed = [m for m in ERRORS_OF_CANONICAL if not any(started[(name, m)] for name in behind_canonical)]
    behind_the_filter = [name for name, _, _ in runs if "behind the words filter perfluoro" in name]
    of_the_filter = MESSAGES_OF_THE_FILTER + [PASSED]
    filter_not_given = [m for m in of_the_filter if not any(count[(name, m)] for name in behind_the_filter)]
    filter_not_printed = [m for m in of_the_filter if not any(started[(name, m)] for name in behind_the_filter)]
    print()
    at_the_end = checksums()
    changed = [name for name in at_the_start if at_the_start[name] != at_the_end[name]]
    for name, checksum in at_the_end.items():
        print(f"sha256 of {name} at the end: {checksum}" + ("   CHANGED DURING THE RUN" if name in changed else ""))
    if changed:
        print(f"NOT ONE CHECK: {' and '.join(changed)} changed while the script ran. Run it again.")
        return 1
    if refused:
        print(f"{len(refused)} START{'' if len(refused) == 1 else 'S'} OF THE SECOND PROGRAM DID NOT END AS "
              f"{'IT' if len(refused) == 1 else 'THEY'} MUST (the lines above say why). The check fails for that alone. "
              "Run it again when the machine is less busy; if it happens again, look at the second program.")
    if compared != total:
        print(f"NOT ALL COMPARED: {compared} OF THE {total} LISTS OF ARGUMENTS WERE COMPARED IN THE FIRST PART.")
    if too_few:
        print(f"TOO FEW STARTS: THE PROGRAM ITSELF WAS STARTED FOR FEWER THAN {SAMPLE} LISTS OF {too_few}.")
    if failed:
        print(f"{failed} OF THE {total} LISTS OF ARGUMENTS GOT ANOTHER ANSWER FROM THE SECOND PROGRAM THAN FROM THE MODEL.")
    if starts_failed:
        print(f"{starts_failed} OF THE {len(sample)} STARTS OF THE PROGRAM ITSELF GAVE ANOTHER ANSWER THAN THE MODEL.")
    all_compared = compared == total
    if all_compared and not failed and not starts_failed:
        print(f"No mismatch. For each of the {total} lists of arguments, the function that is the whole program, asked\n"
              "through the second program, gave exactly what the model gives: the text for standard output, the text for\n"
              f"standard error and the exit code. And in each of the {len(sample)} starts of the program itself, it printed\n"
              "exactly that on standard output and on standard error, and ended with that exit code.")
    if limit:
        print("This was a sample. Run the script without --limit for the whole check.")
    else:
        if missing:
            print(f"NOT TRIED: no text got the message {missing}. Every message of SPEC.md, sections 6 and 12.2, must be tried.")
        if not_started:
            print(f"NOT TRIED WITH THE PROGRAM ITSELF: no start of the program itself got the message {not_started}.")
        if not missing and not not_started:
            print(f"Each of the {len(MESSAGES)} messages of SPEC.md, sections 6 and 12.2, was the answer to at least one text, "
                  "and to at least one start of the program itself.")
        if not_given:
            print(f"NOT TRIED: `canonical` never answered with {not_given}. Each of the three errors that it can give for "
                  "a Mol without stereo facts must be tried.")
        if not_printed:
            print(f"NOT TRIED WITH THE PROGRAM ITSELF: no start of the program itself behind `canonical` answered with {not_printed}.")
        if not not_given and not not_printed:
            print("Each of the three errors that `canonical` can give for a Mol without stereo facts (the search gives up; "
                  "more than 1,000 atoms; the writer refuses the chosen form for its ring numbers) was the answer to at "
                  "least one text, and to at least one start of the program itself.")
        if filter_not_given:
            print(f"NOT TRIED: the filter never answered with {filter_not_given}. Each answer that it can give for a text "
                  "that is read must be tried.")
        if filter_not_printed:
            print(f"NOT TRIED WITH THE PROGRAM ITSELF: no start of the program itself behind `filter` answered with {filter_not_printed}.")
        if not filter_not_given and not filter_not_printed:
            print(f"Each of the {len(MESSAGES_OF_THE_FILTER)} messages of the filter (SPEC.md, sections 16.2 and 16.3), and a Mol "
                  "that passes, was the answer to at least one text, and to at least one start of the program itself.")
    bad = (failed or starts_failed or refused or not all_compared or too_few
           or (not limit and (missing or not_started or not_given or not_printed or filter_not_given or filter_not_printed)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
