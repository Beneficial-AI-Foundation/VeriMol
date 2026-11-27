"""Check the Lean program against RDKit and Open Babel directly, on the real SMILES texts.

    .venv/bin/python -I reference/check_direct.py               all texts
    .venv/bin/python -I reference/check_direct.py --limit 3000  a quick look at a sample

Any other argument is refused: a mistyped option must not start the whole run.

check_app.py holds the Lean program against the model, and other checks hold the model against RDKit and
Open Babel. This one leaves the model out, as check_filter.py does. It takes the answers of the Lean
program and holds them against two programs that other people wrote. It never asks the model's reader or
writer; of model.py it uses only the form in which others.py hands over what those programs read.

The script first builds both programs (`lake build app answers`). The answers of the Lean program then come
from the second program, `.lake/build/bin/answers`, which gives what `VeriMol.run` gives (Answers.lean). The
built `app` is not started here. The Mol that the program prints is read from its printed layout (SPEC.md,
section 7) by the function `printed_mol`. Only its atoms and its bonds are read from that layout: the
stereo facts are compared through the texts.

For every real text that the Lean program reads:
  reading    what RDKit, with its clean-up off, and Open Babel read from the text, against the Mol that the
             Lean program prints
  writing    what the two read from the texts that the Lean program writes for `rewrite` and for `plain`
  stereo     for a text with stereo marks: whether RDKit, with its clean-up on, takes the original and each
             written text for the same molecule, stereo included
  canonical  what RDKit reads from the text that the Lean program writes for `canonical`, and whether it
             takes that text and the rewritten one for the same atoms and bonds, hydrogens included (the
             function `same_atoms_and_bonds` of others.py)

The script also hands five wrong answers to its own comparisons on purpose, and counts how often each is
noticed. A run without --limit must be a run on the recorded real texts, all of them, and every one of its
numbers must be the recorded one (`RECORDED`, below). A sample has least counts in their place.

reference/README.md, "Reading the output of `check_direct.py`", says what each comparison demands and what
it lets through, how RDKit is asked whether two texts are the same atoms and bonds, what the wrong answers
are, and what the check does not show. A line in CAPITALS is something that SPEC.md does not explain. The
script then ends with exit code 1.
"""
import collections
import multiprocessing
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_app
import others
import sources
from rdkit import Chem

TEXTS = 100                     # how many texts one worker takes at a time
WEIGHT = {"single": 1, "double": 2, "triple": 3, "quadruple": 4, "aromatic": 1}     # SPEC.md, section 5, rule 7
# Where RDKit counts other hydrogens at an atom without square brackets (SPEC.md, section 11.2, the first
# table): the element, what the bonds of the atom add up to, the hydrogens here, the hydrogens in RDKit.
# The two rows of that table about a lowercase symbol and about the bond symbol `:` are not here: no real
# text has them, and one that had would be reported. An atom without square brackets has no mass number
# and no charge, so the excuse is given to such an atom only.
OTHER_HYDROGENS = {("N", 4, 1, 0), ("P", 6, 0, 1), ("I", 2, 0, 1), ("I", 4, 0, 1)}

SAME = "the same atoms and bonds as RDKit"
EXCUSED = "other hydrogens than RDKit at an atom without square brackets, as SPEC.md, section 11.2, lists"
EXACT = "RDKit reads the written text as exactly the atoms and bonds that the Lean program printed"
REFUSED = "reading: the Lean program refuses the text, and RDKit reads it"
CAPITALS = re.compile(r"\b[A-Z]{2,} [A-Z]{2,}\b")      # two words in capitals, one after the other: a failure

# Every number of a run on all the recorded real texts (see the head of this file). When a number changes
# because the program or SPEC.md was changed on purpose, the number here is changed with it.
RECORDED = {
    'texts that the Lean program reads, without stereo marks':
        57547,
    'texts that the Lean program reads, with stereo marks':
        4528,
    'reading: the same atoms and bonds as RDKit':
        62070,
    'reading: the same atoms and bonds as Open Babel':
        54739,
    'reading: the same atoms, and the same atoms are bonded, as in Open Babel, which calls other bonds aromatic':
        7336,
    'reading: the Lean program refuses the text, and RDKit reads it':
        24,
    '    of these, with the message: a stereo centre with a free place, one ring number and only single bonds is not read':
        16,
    '    of these, with the message: an atom or a ring number is expected here':
        4,
    '    of these, with the message: an element symbol is expected here':
        2,
    '    of these, with the message: an atom is expected here':
        1,
    '    of these, with the message: the wildcard atom is not read':
        1,
    'reading: other hydrogens than RDKit at an atom without square brackets, as SPEC.md, section 11.2, lists':
        5,
    'writing, rewrite: Open Babel reads the written text as it reads the original one':
        62075,
    'writing, rewrite: RDKit reads the written text as exactly the atoms and bonds that the Lean program printed':
        62075,
    'writing, plain: Open Babel reads the written text as it reads the original one':
        62069,
    'writing, plain: RDKit reads the written text as exactly the atoms and bonds that the Lean program printed':
        62069,
    'writing, rewrite: the written text is the original text, character for character':
        47446,
    'writing, plain: the written text is the original text, character for character':
        48,
    'writing, plain: the Lean program refuses the Mol: a stereo centre with a free place would be written with one ring number and only single bonds':
        5,
    'writing, plain: the Lean program refuses the Mol: a stereo centre with a free place would be written without an atom before it':
        1,
    'stereo, rewrite: the original and the written text are to RDKit, with its clean-up on: the same molecule, stereo included':
        4517,
    'stereo, canonical: the original and the canonical text are to RDKit, with its clean-up on: the same molecule, stereo included':
        4515,
    'stereo, plain: the original and the written text are to RDKit, with its clean-up on: the same molecule, stereo included':
        4511,
    'stereo, canonical: the original and the canonical text are to RDKit, with its clean-up on: no verdict: its clean-up refuses the original text or the written one':
        11,
    'stereo, plain: the original and the written text are to RDKit, with its clean-up on: no verdict: its clean-up refuses the original text or the written one':
        11,
    'stereo, rewrite: the original and the written text are to RDKit, with its clean-up on: no verdict: its clean-up refuses the original text or the written one':
        11,
    'canonical: RDKit reads the canonical text as exactly the atoms and bonds that the Lean program reads from it':
        62073,
    'canonical: the rewritten and the canonical text are the same atoms and bonds to RDKit, hydrogens included, by its own canonical text':
        62072,
    'canonical: the canonical text is the rewritten text, character for character':
        6223,
    'canonical: no text: a stereo centre with a free place would be written with one ring number and only single bonds':
        2,
    'canonical: the rewritten and the canonical text are the same atoms and bonds to RDKit, hydrogens included, asked in the second way; its own canonical text differs for these two numberings':
        1,
    'wrong on purpose, a Mol with one hydrogen more at its first atom: reported as a failure':
        62075,
    'wrong on purpose, a text with one hydrogen fewer in the place of the canonical text: noticed':
        61825,
    'wrong on purpose, the text that was written for another molecule: noticed':
        61288,
    'wrong on purpose, a text in which a counted hydrogen is an atom of its own, in the place of the canonical text: noticed':
        50072,
    'wrong on purpose, the rewritten text with its first stereo mark turned round: reported as another arrangement in space':
        4515,
    'wrong on purpose, the rewritten text with its first stereo mark turned round: no verdict of RDKit':
        11,
    'wrong on purpose, the rewritten text with its first stereo mark turned round: RDKit takes the turned text for the same molecule':
        2,
}


def printed_mol(text):
    """The atoms and the bonds of a Mol in the printed layout of SPEC.md, section 7: each atom as (element,
    mass number or None, charge, hydrogens), each bond as (a, b, order)."""
    atoms = [(element, None if isotope == "none" else int(number), int(charge), int(hydrogens))
             for element, isotope, number, charge, hydrogens in others.PRINTED_ATOM.findall(text)]
    bonds = [(int(a), int(b), order) for a, b, order in others.PRINTED_BOND.findall(text)]
    return atoms, bonds


def as_read(mol):
    """What another program read (others.py), in the form of `printed_mol`. None stays None."""
    if mol is None:
        return None
    return [(a.element, a.isotope, a.charge, a.hydrogens) for a in mol.atoms], [(b.a, b.b, b.order) for b in mol.bonds]


def but_for_mass_number_0(ours, theirs):
    """Are two atoms the same but for a mass number 0, which RDKit and Open Babel do not keep?"""
    return ours[1] == 0 and theirs[1] is None and (ours[0], ours[2], ours[3]) == (theirs[0], theirs[2], theirs[3])


def against_rdkit(mol, seen):
    """How the Mol that the Lean program printed stands to what RDKit reads from the same text, with its
    clean-up off. Capitals: SPEC.md does not explain it."""
    if seen is None:
        return "THE LEAN PROGRAM READS THE TEXT, RDKIT DOES NOT"
    if seen == mol:
        return SAME
    (atoms, bonds), (their_atoms, their_bonds) = mol, seen
    if len(atoms) != len(their_atoms):
        return "ANOTHER NUMBER OF ATOMS THAN RDKIT"
    if bonds != their_bonds:
        return "OTHER BONDS THAN RDKIT"
    kinds = set()
    for number, (ours, theirs) in enumerate(zip(atoms, their_atoms)):
        if ours == theirs:
            continue
        total = sum(WEIGHT[order] for a, b, order in bonds if number in (a, b))
        if (ours[:3] == theirs[:3] and ours[1] is None and ours[2] == 0
                and (ours[0], total, ours[3], theirs[3]) in OTHER_HYDROGENS):
            kinds.add(EXCUSED)
        elif but_for_mass_number_0(ours, theirs):
            kinds.add("a mass number 0 is kept, and RDKit reads no mass number")
        else:
            return "AN ATOM DIFFERS FROM RDKIT IN A WAY THAT SPEC.MD DOES NOT LIST"
    return "; ".join(sorted(kinds))


def against_openbabel(mol, seen):
    """How the Mol that the Lean program printed stands to what Open Babel reads from the same text."""
    if seen is None:
        return "THE LEAN PROGRAM READS THE TEXT, OPEN BABEL DOES NOT"
    if seen == mol:
        return "the same atoms and bonds as Open Babel"
    (atoms, bonds), (their_atoms, their_bonds) = mol, seen
    if len(atoms) != len(their_atoms) or any(a != b and not but_for_mass_number_0(a, b) for a, b in zip(atoms, their_atoms)):
        return "OTHER ATOMS THAN OPEN BABEL"
    if [(a, b) for a, b, _ in bonds] != [(a, b) for a, b, _ in their_bonds]:
        return "OTHER ATOMS ARE BONDED THAN IN OPEN BABEL"
    if any(ours != theirs and not ("aromatic" in (ours, theirs) and {ours, theirs} <= {"aromatic", "single", "double"})
           for (_, _, ours), (_, _, theirs) in zip(bonds, their_bonds)):
        return "A BOND HAS ANOTHER ORDER THAN IN OPEN BABEL, AND NOT ONLY AROMATIC AGAINST SINGLE OR DOUBLE"
    if bonds == their_bonds:
        return "the same atoms and bonds as Open Babel, but for a mass number 0, which Open Babel does not keep"
    return "the same atoms, and the same atoms are bonded, as in Open Babel, which calls other bonds aromatic"


def exactly(mol, seen):
    """Does RDKit read exactly these atoms and bonds? A mass number 0, which RDKit does not keep, is let
    through."""
    return seen is not None and seen[1] == mol[1] and len(seen[0]) == len(mol[0]) and all(
        a == b or but_for_mass_number_0(a, b) for a, b in zip(mol[0], seen[0]))


def one_mark_turned(text):
    """The text with its first stereo mark turned round: `@` for `@@` and `@@` for `@`, or, in a text
    without them, `/` for `\\` and `\\` for `/`. None if the text has no stereo mark."""
    place = text.find("@")
    if place >= 0:
        return text[:place] + ("@" if text[place:place + 2] == "@@" else "@@") + text[place:].lstrip("@")
    for place, character in enumerate(text):
        if character in "/\\":
            return text[:place] + ("\\" if character == "/" else "/") + text[place + 1:]
    return None


STEREO = {"same": "the same molecule, stereo included",
          None: "no verdict: its clean-up refuses the original text or the written one",
          "picture differs": "no verdict: its clean-up gives the two texts two canonical texts that differ in more than stereo",
          "stereo differs": "ANOTHER ARRANGEMENT IN SPACE"}


def text_of(answer):
    return answer[0].decode("utf-8").rstrip("\n")


def message_of(answer):
    return check_app.message_in(answer[1].decode("utf-8").strip())


def examine(texts):
    """All comparisons for some texts. Returns a count of what was found, and for each kind of finding
    at most three of the texts concerned."""
    count, shown = collections.Counter(), collections.defaultdict(list)

    def found(kind, text=None):
        count[kind] += 1
        if text is not None and len(shown[kind]) < 3:
            shown[kind].append(text)

    lists = [arguments for text in texts for arguments in ([text], ["rewrite", text], ["plain", text], ["canonical", text])]
    answers, problem = check_app.ask(lists)
    if answers is None:
        found(f"THE SECOND PROGRAM GAVE NO ANSWERS FOR {len(texts)} TEXTS: {problem}", texts[0])
        return count, dict(shown)
    chosen_texts = [text_of(answers[4 * place + 3]) for place in range(len(texts)) if answers[4 * place + 3][2] == 0]
    read_again, problem = check_app.ask([[text] for text in chosen_texts]) if chosen_texts else ([], None)
    if read_again is None:
        found(f"THE SECOND PROGRAM GAVE NO ANSWERS FOR {len(chosen_texts)} CANONICAL TEXTS: {problem}", texts[0])
        return count, dict(shown)
    read_again = dict(zip(chosen_texts, read_again))
    previous = None                         # the Mol and the rewritten text of the text before, for the wrong answers on purpose

    for place, text in enumerate(texts):
        alone, rewritten, plain, chosen = answers[4 * place:4 * place + 4]
        seen = as_read(others.rdkit_mol(text))
        marks = sources.has_marks(text)
        if alone[2] != 0:
            if seen is None:
                found("reading: the Lean program refuses the text, and so does RDKit", text)
            else:
                found(REFUSED)
                found(f"    of these, with the message: {message_of(alone)}", text)
            continue
        mol = printed_mol(alone[0].decode("utf-8"))
        found("texts that the Lean program reads" + (", with stereo marks" if marks else ", without stereo marks"))

        # ---- reading ----
        verdict = against_rdkit(mol, seen)
        found(f"reading: {verdict}", None if verdict == SAME else text)
        their = as_read(others.openbabel_mol(text))
        verdict = against_openbabel(mol, their)
        found(f"reading: {verdict}", text if CAPITALS.search(verdict) else None)
        # a wrong answer on purpose: one hydrogen more at the first atom
        if mol[0] and seen is not None:
            wrong = ([mol[0][0][:3] + (mol[0][0][3] + 1,)] + mol[0][1:], mol[1])
            verdict = against_rdkit(wrong, seen)
            found("wrong on purpose, a Mol with one hydrogen more at its first atom: "
                  + ("reported as a failure" if CAPITALS.search(verdict)
                     else "NOT NOTICED" if verdict == SAME
                     else "taken for a difference that SPEC.md lists, which it is for this atom"))

        # ---- writing ----
        for word, answer in (("rewrite", rewritten), ("plain", plain)):
            if answer[2] != 0:
                found(f"writing, {word}: the Lean program refuses the Mol: {message_of(answer)}", text)
                continue
            written = text_of(answer)
            if written == text:
                found(f"writing, {word}: the written text is the original text, character for character")
            if any(character.isspace() for character in written):
                found(f"writing, {word}: THE WRITTEN TEXT HOLDS WHITE SPACE", f"{text}   ->   {written!r}")
            ok = exactly(mol, as_read(others.rdkit_mol(written)))
            found(f"writing, {word}: " + (EXACT if ok else "RDKIT READS THE WRITTEN TEXT AS OTHER ATOMS AND BONDS"),
                  None if ok else f"{text}   ->   {written}")
            again = as_read(others.openbabel_mol(written))
            if their is not None:
                found(f"writing, {word}: " + ("Open Babel reads the written text as it reads the original one" if again == their
                                               else "OPEN BABEL READS THE WRITTEN TEXT AND THE ORIGINAL ONE DIFFERENTLY"),
                      None if again == their else f"{text}   ->   {written}")
            if marks:
                verdict = STEREO[others.same_molecule(text, written)]
                found(f"stereo, {word}: the original and the written text are to RDKit, with its clean-up on: {verdict}",
                      f"{text}   ->   {written}" if CAPITALS.search(verdict) else None)
        # a wrong answer on purpose: the text that was written for the molecule before
        if previous is not None and rewritten[2] == 0 and previous[0] != mol:
            found("wrong on purpose, the text that was written for another molecule: "
                  + ("NOT NOTICED" if exactly(mol, as_read(others.rdkit_mol(previous[1]))) else "noticed"))
        if rewritten[2] == 0:
            previous = (mol, text_of(rewritten))
        # a wrong answer on purpose: one stereo mark of the rewritten text turned round
        if marks and rewritten[2] == 0:
            turned = one_mark_turned(text_of(rewritten))
            if turned is not None:
                verdict = others.same_molecule(text, turned)
                found("wrong on purpose, the rewritten text with its first stereo mark turned round: "
                      + {"stereo differs": "reported as another arrangement in space",
                         "same": "RDKit takes the turned text for the same molecule",
                         }.get(verdict, "no verdict of RDKit"))

        # ---- canonical ----
        if chosen[2] != 0:
            found(f"canonical: no text: {message_of(chosen)}", text)
            continue
        canonical = text_of(chosen)
        if any(character.isspace() for character in canonical):
            found("canonical: THE CANONICAL TEXT HOLDS WHITE SPACE", f"{text}   ->   {canonical!r}")
        again = read_again[canonical]
        if again[2] != 0:
            found("canonical: THE LEAN PROGRAM DOES NOT READ ITS OWN CANONICAL TEXT", f"{text}   ->   {canonical}")
            continue
        ok = exactly(printed_mol(again[0].decode("utf-8")), as_read(others.rdkit_mol(canonical)))
        found("canonical: " + ("RDKit reads the canonical text as exactly the atoms and bonds that the Lean program reads from it" if ok
                               else "RDKIT READS THE CANONICAL TEXT AS OTHER ATOMS AND BONDS THAN THE LEAN PROGRAM"),
              None if ok else f"{text}   ->   {canonical}")
        if rewritten[2] == 0:
            written = text_of(rewritten)
            if written == canonical:
                found("canonical: the canonical text is the rewritten text, character for character")
            how = others.same_atoms_and_bonds(written, canonical)
            if how is None:
                found("canonical: THE REWRITTEN AND THE CANONICAL TEXT ARE NOT THE SAME ATOMS AND BONDS TO RDKIT",
                      f"{written}   and   {canonical}")
            else:
                found(f"canonical: the rewritten and the canonical text are the same atoms and bonds to RDKit, hydrogens included, {how}",
                      None if how.startswith("by") else f"{written}   and   {canonical}")
            # two wrong answers on purpose: a text with one hydrogen fewer, and one with a counted hydrogen as an atom
            if plain[2] == 0:
                fewer, as_an_atom = others.one_hydrogen_fewer(text_of(plain))
                if fewer is not None:
                    found("wrong on purpose, a text with one hydrogen fewer in the place of the canonical text: "
                          + ("noticed" if others.same_atoms_and_bonds(written, fewer) is None else "NOT NOTICED"))
                if as_an_atom is not None:
                    found("wrong on purpose, a text in which a counted hydrogen is an atom of its own, in the place of the canonical text: "
                          + ("noticed" if others.same_atoms_and_bonds(written, as_an_atom) is None else "NOT NOTICED"))
        if marks:
            verdict = STEREO[others.same_molecule(text, canonical)]
            found(f"stereo, canonical: the original and the canonical text are to RDKit, with its clean-up on: {verdict}",
                  f"{text}   ->   {canonical}" if CAPITALS.search(verdict) else None)
    return count, dict(shown)


def main():
    limit = sources.limit_of(sys.argv[1:])
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
    print(f"RDKit {Chem.rdBase.rdkitVersion}, and Open Babel. {workers} worker{'s' if workers > 1 else ''}.", flush=True)

    count, shown = collections.Counter(), collections.defaultdict(list)
    pieces = [real[i:i + TEXTS] for i in range(0, len(real), TEXTS)]
    with multiprocessing.Pool(workers) as pool:
        for part, examples in pool.imap_unordered(examine, pieces, chunksize=1):
            count += part
            for kind, texts in examples.items():
                shown[kind] += texts
    for kind in shown:
        shown[kind] = sorted(shown[kind], key=lambda text: (len(text), text))[:3]

    sections = ["texts that the Lean program reads", "reading", "writing", "stereo", "canonical", "wrong on purpose"]

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
        if kind == REFUSED:
            for sub in sorted((k for k in count if k.startswith("    ")), key=lambda k: (-count[k], k)):
                lines(sub)

    short = []
    if limit:
        # ---- a sample: least counts, and one greatest count ----
        read = sum(n for kind, n in count.items() if kind.startswith("texts that the Lean program reads"))
        marked = count["texts that the Lean program reads, with stereo marks"]
        with_text = sum(n for kind, n in count.items() if kind.startswith("canonical: RDKit reads the canonical text as exactly"))
        same = STEREO["same"]
        floors = [
            ("texts that the Lean program reads", read, 0.95 * len(real)),
            (f"reading: {SAME}", count[f"reading: {SAME}"], 0.98 * read),
            ("reading: compared with Open Babel", sum(n for kind, n in count.items() if kind.startswith("reading: the same atoms")
                                                       and "Open Babel" in kind), 0.98 * read),
            (f"writing, rewrite: {EXACT}", count[f"writing, rewrite: {EXACT}"], 0.98 * read),
            (f"writing, plain: {EXACT}", count[f"writing, plain: {EXACT}"], 0.98 * read),
            ("writing, rewrite: Open Babel reads the written text as it reads the original one",
             count["writing, rewrite: Open Babel reads the written text as it reads the original one"], 0.98 * read),
            ("writing, plain: Open Babel reads the written text as it reads the original one",
             count["writing, plain: Open Babel reads the written text as it reads the original one"], 0.98 * read),
        ] + [
            (f"stereo, {word}: {same}, to RDKit with its clean-up on",
             count[f"stereo, {word}: the original and the {'canonical' if word == 'canonical' else 'written'} text are to RDKit, "
                   f"with its clean-up on: {same}"], 0.95 * marked)
            for word in ("rewrite", "plain", "canonical")
        ] + [
            ("canonical: texts with a canonical text that RDKit reads as the Lean program does", with_text, 0.95 * read),
            ("canonical: the same atoms and bonds to RDKit, hydrogens included", sum(n for kind, n in count.items() if kind.startswith(
                "canonical: the rewritten and the canonical text are the same atoms and bonds")), 0.95 * read),
            ("wrong on purpose, a Mol with one hydrogen more at its first atom: reported as a failure",
             count["wrong on purpose, a Mol with one hydrogen more at its first atom: reported as a failure"], 0.98 * read),
            ("wrong on purpose, the text that was written for another molecule: noticed",
             count["wrong on purpose, the text that was written for another molecule: noticed"], 0.9 * read),
            ("wrong on purpose, a text with one hydrogen fewer in the place of the canonical text: noticed",
             count["wrong on purpose, a text with one hydrogen fewer in the place of the canonical text: noticed"], 0.9 * with_text),
            ("wrong on purpose, a text in which a counted hydrogen is an atom of its own, in the place of the canonical text: noticed",
             count["wrong on purpose, a text in which a counted hydrogen is an atom of its own, in the place of the canonical text: noticed"],
             0.5 * with_text),
            ("wrong on purpose, the rewritten text with its first stereo mark turned round: reported as another arrangement in space",
             count["wrong on purpose, the rewritten text with its first stereo mark turned round: reported as another arrangement in space"],
             0.8 * marked),
        ]
        print("\nLeast counts of a sample:")
        for name, value, least in floors:
            ok = value >= least and value > 0
            print(f"{value:8d}  {name} (at least {int(least)})" + ("" if ok else "   TOO FEW"))
            if not ok:
                short.append(name)
        most = 5 + len(real) // 1000
        if count[REFUSED] > most:
            print(f"{count[REFUSED]:8d}  TOO MANY TEXTS THAT THE LEAN PROGRAM REFUSES AND RDKIT READS (at most {most} in a sample of this size)")
            short.append("too many texts refused")
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
    print("Nothing in capitals: on these texts the Lean program reads the atoms and bonds that RDKit reads, apart from\n"
          "the differences that SPEC.md lists, and Open Babel reads the same atoms, with the same atoms bonded. RDKit\n"
          "reads what the Lean program writes as the atoms and bonds that it read, and Open Babel reads it as it reads\n"
          "the original text. And RDKit takes the canonical text for the same atoms and bonds as the rewritten one,\n"
          "hydrogens included.")
    if limit:
        print("This was a sample. Run the script without --limit for the whole check.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
