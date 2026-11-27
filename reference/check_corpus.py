"""Check the model against RDKit on the real SMILES texts. Where the two count other hydrogens, Open Babel's
count is shown beside them.

    .venv/bin/python -I reference/check_corpus.py               all texts
    .venv/bin/python -I reference/check_corpus.py --limit 3000  a quick look at a sample

reference/README.md, "Reading the output of `check_corpus.py`", says what is compared for every text and
how to read the report.

A line in CAPITALS is something SPEC.md does not explain. The script then ends with exit code 1.

A count of nothing is no success. If the model's reader refused every text, or its writer every Mol, no
round trip would be made and no line would be in capitals. So the counts that carry this check each
have a least value, as a part of the texts that were tried; a count below it is reported in capitals.
The real texts are held against their recorded numbers when they are loaded (sources.py), so a run
without --limit is a run on all of them.
"""
import collections
import multiprocessing
import random
import re
import sys
import zlib
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import model
import others
import sources
import test_cases

# Texts for notation that hardly occurs in the real data: isotopes, "$", ":", "%", every way to write a charge.
RARE_NOTATION = """[13CH4] [2H]O[2H] [3H] [14C] [235U] [18O]=C=[18O] [13C]([2H])([2H])([2H])Cl [0C]
[Rh]$[Rh] C$C [Mo]$[Mo] C:C c:c c1:c:c:c:c:c1 C1:C:C:C:C:C:1 c1ccccc1-c1ccccc1 c1ccccc1c1ccccc1 C-C C=C C#C
C%10CCCCC%10 C%99CC%99 C%05CC5 C1CC%01 C%10%11%12C.C%10.C%11.C%12 C12CC1C2 C1.C1 C1=CC=1 C=1CC1 C1CC=1
[OH-] [O-] [O--] [O-2] [Fe+] [Fe++] [Fe+2] [Fe+3] [Fe+10] [Fe-10] [NH4+] [NH3+][O-] [N+](=O)[O-] [CH4+0] [C-]#[O+]
[H] [H+] [H-] [H][H] [CH0] [CH] [CH2] [CH9] [nH]1cccc1 [se]1cccc1 c1cc[se]cc1 [as]1cccc1 b1ccccc1 [b-]1ccccc1
B BB N NN O OO P S F Cl Br I ClBr FI OS(=O)(=O)O O=P(O)(O)O FS(F)(F)(F)(F)F CS(C)(C)(C)(C)C CN(C)(C)C CIC CBr(C)C
c1ccncc1 c1ccoc1 c1ccsc1 c1cc[nH]c1 c1ccpcc1 n1ccccc1 o1cccc1 s1cccc1 p1ccccc1 c C(.C)C C(C.C)C [Co] [Cn]
Cl[I]Cl F[P](F)(F)(F)(F)F CS(C)C CP(C)(C)C""".split()
RARE_NOTATION += [f"[{e}]" for e in model.ELEMENTS]


def difference(ours, theirs):
    """In which respect the atoms and the bonds of two Mols differ, as a short word; "" if they are the same."""
    if len(ours.atoms) != len(theirs.atoms):
        return "number of atoms"
    if ours.bonds != theirs.bonds:
        return "bonds"
    return "+".join(field for field in ("element", "isotope", "charge", "hydrogens")
                    if any(getattr(a, field) != getattr(b, field) for a, b in zip(ours.atoms, theirs.atoms)))


def without_ring_numbers(text):
    """The tokens of a text without its ring numbers: what is left when two texts are to be compared
    apart from the numbers that they use for their rings. Where a stereo mark stands in the text is left
    out as well: a ring number of another width moves it."""
    return [(t.kind, replace(t.value, chiral_pos=None) if t.kind == "atom" else t.value)
            for t in model.tokens_of(text) if t.kind != "ring"]


def spelling_checks(mol, original, agreed, part, found, ring_marks="open", spellings=(False, True)):
    """Write `mol` in the given spellings and check each text. `agreed`: RDKit read the original as the model did."""
    for round_brackets in spellings:
        name = part + (" round brackets" if round_brackets else " plain spelling")
        try:
            written = model.spell(mol, round_brackets, ring_marks)
        except model.WriteError as e:
            found.append((name + f": the writer refuses ({e})", original))
            continue
        example = original + "   written: " + written
        back = model.read_or_none(written)
        if back != mol:
            found.append((name + ": READING THE WRITTEN TEXT DOES NOT RETURN THE SAME MOL", example))
            continue
        if round_brackets and part == "as it is:" and ring_marks == "open":
            stereo = "with" if sources.has_marks(original) else "without"
            found.append((f"as it is: round brackets, texts {stereo} stereo marks: written", None))
            if written == original:
                found.append((f"as it is: round brackets, texts {stereo} stereo marks: the same as the text read, character for character", None))
            elif without_ring_numbers(written) == without_ring_numbers(original):
                found.append((f"as it is: round brackets, texts {stereo} stereo marks: another text than the one read, "
                              "which differs from it in its ring numbers only (the same charge or the same count, "
                              "spelled in another way, is no difference here)", None))
            if written.count(".") > others.pieces(mol) - 1:
                found.append(("as it is: round brackets: a dot was needed inside one piece", example))
        theirs = others.rdkit_mol(written)
        diff = "refused" if theirs is None else difference(mol, theirs)
        if diff == "isotope" and "[0" in written:
            found.append((name + ": exact round trip; RDKit reads no isotope where 0 is written (known)", example))
            continue
        if diff:
            found.append((name + f": RDKIT READS ANOTHER MOL FROM THE WRITTEN TEXT ({diff})", example))
            continue
        if others.rdkit_lowercase(written) != others.lowercase_by_rule(mol):
            # No round trip shows this for the plain spelling, where the case of a symbol does not change the
            # Mol that is read, apart from a bond that carries a mark.
            found.append((name + ": A SYMBOL OF THE WRITTEN TEXT IS IN ANOTHER CASE THAN SECTION 9 SAYS, AS RDKIT READS IT", example))
            continue
        if not agreed:
            found.append((name + ": exact round trip; RDKit reads the written text as exactly this Mol (it had read the original differently)", example))
            continue
        same = others.same_molecule(original, written)
        if same is None:
            # Two cases that must not share a line: the clean-up refuses the text that was read (then
            # nothing can be compared), or it refuses the written text alone.
            same = "refused" if others.rdkit_canonical(original) is None else "written refused"
        found.append((name + ": exact round trip; RDKit reads the written text as exactly this Mol, and "
                      + {"same": "as the same molecule, stereo included",
                         "stereo differs": "WITH ANOTHER ARRANGEMENT IN SPACE",
                         "picture differs": "its clean-up gives the two texts two canonical texts that differ in more than "
                                            "stereo (not a stereo matter)",
                         "refused": "its clean-up refuses the molecule, the text that was read as well",
                         "written refused": "its clean-up refuses the written text, and not the text that was read"}[same],
                      example))


def examine(item):
    """All checks for one text. Returns (kind, [(what was found, example or None)], [rows for the hydrogen
    table]). An entry of the second list that counts more than one has that number as a third part."""
    kind, text = item
    found, table = [], []
    stereo_text = sources.has_marks(text)

    # ---- the reader ----
    theirs = others.rdkit_mol(text)
    try:
        mol = model.read(text)
    except model.SmilesError as e:
        message = e.message if "cannot be read here" not in e.message else "'X' cannot be read here"
        found.append((f"reader: the model answers \"{message}\"; RDKit "
                      + ("reads the text" if theirs is not None else "refuses it too")
                      + "; partialsmiles: " + others.syntax_verdict(text), text))
        return kind, found, table
    if kind == "real":
        found.append(("stereo facts read: atoms with an orientation", None, len(mol.orientations)))
        found.append(("stereo facts read: of these, atoms with a free place", None,
                      sum(mol.atoms[x.atom].hydrogens == 0 and sum(x.atom in (b.a, b.b) for b in mol.bonds) == 3
                          for x in mol.orientations)))
        found.append(("stereo facts read: double bonds with a geometry", None, len(mol.geometries)))
        found.append(("texts read: " + ("with stereo marks" if stereo_text else "without stereo marks"), None))
    if not stereo_text and model.has_stereo(mol):
        found.append(("READER: A TEXT WITHOUT STEREO MARKS GETS A STEREO FACT", text))
    diff = "refused" if theirs is None else difference(mol, theirs)
    agreed = not diff
    if agreed:
        found.append(("reader: the same atoms and bonds as RDKit", None))
    elif diff == "refused":
        found.append(("reader: the model reads the text; RDKit does not", text))
    elif diff == "hydrogens":
        raw = [t.value for t in model.tokens_of(text) if t.kind == "atom"]
        second = others.openbabel_mol(text)
        nb = model.neighbours_of(mol)
        order = {(b.a, b.b): b.order for b in mol.bonds}
        all_bare = True
        for i, (a, b) in enumerate(zip(mol.atoms, theirs.atoms)):
            if a.hydrogens != b.hydrogens:
                total = sum(model.WEIGHT[order[(min(i, j), max(i, j))]] for j in nb[i])
                ob = second.atoms[i].hydrogens if second is not None and len(second.atoms) == len(mol.atoms) else "?"
                all_bare = all_bare and raw[i].hydrogens is None
                table.append(((a.element, "lowercase" if raw[i].aromatic else "uppercase",
                               "bare" if raw[i].hydrogens is None else "in brackets", total, a.hydrogens, b.hydrogens, ob), text))
        found.append(("reader: other hydrogens than RDKit at a bare atom (see the table)" if all_bare
                      else "READER: OTHER HYDROGENS THAN RDKIT AT A BRACKET ATOM", text))
    elif diff == "isotope" and "[0" in text:
        found.append(("reader: isotope 0 is kept; RDKit reads no isotope", text))
    else:
        found.append((f"READER: DIFFERS FROM RDKIT IN: {diff}", text))

    # ---- the two spellings ----
    spelling_checks(mol, text, agreed, "as it is:", found)

    # ---- the same with the atoms renumbered at random ----
    if kind != "respelt by RDKit":
        new = list(range(len(mol.atoms)))
        random.Random(zlib.crc32(text.encode())).shuffle(new)
        order = [None] * len(new)                   # atom i becomes atom new[i]
        for old, number in enumerate(new):
            order[number] = old
        # by the rule for a stored mark, without the two statements of the model; held against
        # `model.arrange` below
        other = test_cases.renumbered(mol, order)
        if model.arrange(mol, order) != other:
            found.append(("renumbered: THE MODEL'S `arrange` AND THE RULE FOR A STORED MARK GIVE TWO MOLS", text))
        elif model.has_stereo(mol):
            found.append(("renumbered: the model's `arrange` gives the Mol that the rule for a stored mark gives (Mols with stereo facts)", None))
        if not model.is_well_formed(other):
            found.append(("renumbered: THE RENUMBERED MOL IS NOT WELL FORMED", text))
        spelling_checks(other, text, agreed, "renumbered:", found)
        if stereo_text:
            for where in ("close", "both"):
                spelling_checks(other, text, agreed,
                                f"renumbered, ring-bond marks at '{where}':", found, where, spellings=(False,))

    # ---- a wrong text on purpose: does the check notice? ----
    if "@" in text and agreed:
        try:
            written = model.spell(mol, True)
            swapped = written.replace("@@", "\0").replace("@", "@@").replace("\0", "@")
            verdict = others.same_molecule(text, swapped)
            found.append(("wrong on purpose (@ and @@ swapped in the written text): RDKit "
                          + {"same": "calls it the same molecule (it is its own mirror image, or the marks say nothing)",
                             "stereo differs": "notices: another arrangement in space",
                             "picture differs": "gives no verdict", None: "gives no verdict"}[verdict], None))
        except model.WriteError:
            pass
    return kind, found, table


def main():
    limit = sources.limit_of(sys.argv[1:])
    texts = sources.real_texts()            # held against the recorded numbers of texts when they are loaded
    if limit:
        texts = texts[::max(1, len(texts) // limit)]
    from rdkit import Chem
    respelt = []
    for index, text in enumerate(texts):
        if sources.has_marks(text):
            m = Chem.MolFromSmiles(text)
            if m is not None:
                respelt += list(Chem.MolToRandomSmilesVect(m, 3, randomSeed=index + 1))
    items = ([("real", t) for t in texts] + [("rare notation", t) for t in RARE_NOTATION]
             + [("respelt by RDKit", t) for t in respelt])
    print("Data sets:", ", ".join(f"{name} {number}" for name, number in sources.PER_SET.items()))
    print(f"Texts: {len(texts)} real ones ({sum(sources.has_marks(t) for t in texts)} with stereo marks), "
          f"{len(RARE_NOTATION)} with rare notation, {len(respelt)} random spellings by RDKit of the real texts with stereo marks.")

    count = collections.Counter()
    examples = collections.defaultdict(list)
    hydrogens = collections.Counter()
    hydrogen_example = {}
    with multiprocessing.Pool(sources.workers()) as pool:
        for kind, found, table in pool.imap(examine, items, chunksize=200):
            for what, example, *amount in found:
                count[(kind, what)] += amount[0] if amount else 1
                if example is not None and len(examples[(kind, what)]) < 2:
                    examples[(kind, what)].append(example)
            for key, example in dict(table).items():      # a text counts once for each kind of atom
                hydrogens[key] += 1
                hydrogen_example.setdefault(key, example)

    alarms = 0
    for kind in ("real", "respelt by RDKit", "rare notation"):
        print(f"\n=== {kind} ===")
        for (k, what) in sorted(count):
            if k == kind and count[(k, what)]:
                print(f"{count[(k, what)]:7d}  {what}")
                if re.search(r"\b[A-Z]{4,}\b", what):
                    alarms += count[(k, what)]
    if hydrogens:
        print("\n=== Hydrogens that differ from RDKit, by kind of atom (Open Babel is the second opinion) ===")
        print("  texts  element  written                 bonds add up to  model  RDKit  Open Babel  example")
        for key in sorted(hydrogens, key=lambda k: (-hydrogens[k], str(k))):
            element, case, how, total, ours, rdkit, ob = key
            print(f"{hydrogens[key]:7d}  {element:7s}  {case:9s} {how:11s} {total:10d} {ours:11d} {rdkit:6d} {str(ob):>8s}      {hydrogen_example[key][:70]}")
    # ---- least counts ----
    def total(kind, *words):
        return sum(n for (k, what), n in count.items() if k == kind and all(word in what for word in words))

    stereo_included = "as the same molecule, stereo included"
    swapped_noticed = total("real", "wrong on purpose", "notices")
    swapped = total("real", "wrong on purpose")
    floors = [
        ("real texts that the model reads as RDKit does", total("real", "reader: the same atoms and bonds as RDKit"), 0.95 * len(texts)),
        ("real texts with stereo marks whose renumbered Mol is the same by the rule for a stored mark and by `arrange`",
         total("real", "the model's `arrange` gives the Mol that the rule"), 0.9 * total("real", "texts read: with stereo marks")),
        ("real texts with an exact round trip in the plain spelling, which RDKit calls the same molecule",
         total("real", "as it is: plain spelling", stereo_included), 0.95 * len(texts)),
        ("real texts with an exact round trip with round brackets, which RDKit calls the same molecule",
         total("real", "as it is: round brackets", stereo_included), 0.95 * len(texts)),
        ("the same after renumbering, plain spelling", total("real", "renumbered: plain spelling", stereo_included), 0.95 * len(texts)),
        ("the same after renumbering, round brackets", total("real", "renumbered: round brackets", stereo_included), 0.95 * len(texts)),
        ("random spellings by RDKit with an exact round trip with round brackets, which RDKit calls the same molecule",
         total("respelt by RDKit", "as it is: round brackets", stereo_included), 0.95 * len(respelt)),
        # On a small sample only a handful of texts are swapped, and a single one that RDKit does not tell
        # apart would bring the count below nine in ten. So this least count holds from 50 swapped texts on.
        ("texts with @ and @@ swapped on purpose in which RDKit notices another arrangement in space", swapped_noticed,
         0.9 * swapped if swapped >= 50 else 0),
    ]
    print("\n=== Least counts: a count of nothing is no success ===")
    for what, number, least in floors:
        short = number < least
        print(f"{number:7d}  {what} (at least {int(least + 0.999)})" + ("   TOO FEW" if short else ""))
        alarms += short
    # A written text that RDKit's clean-up refuses, where it takes the text that was read, would be a text
    # of the writer that another program cannot use. Asked only where RDKit reads the text as the model
    # does. Where it counts other hydrogens (SPEC.md, section 11.2) the comparison ends before this
    # question; check_direct.py counts those.
    refused_written = total("real", "its clean-up refuses the written text, and not the text that was read")
    print(f"{refused_written:7d}  real texts that RDKit reads as the model does, and whose written text its clean-up refuses "
          "although it takes the text that was read (none is expected)" + ("   TOO MANY" if refused_written else ""))
    alarms += bool(refused_written)
    if any("@" in text for text in texts) and not swapped:
        print("      0  NO TEXT WAS TRIED WITH @ AND @@ SWAPPED ON PURPOSE")
        alarms += 1

    print("\n=== Examples of everything that is not a plain success ===")
    for (kind, what) in sorted(examples):
        if stereo_included in what:
            continue
        for example in examples[(kind, what)]:
            print(f"[{kind}] {what}\n      {example[:230]}")
    print("\n" + (f"{alarms} FINDINGS IN CAPITALS ARE NOT EXPLAINED BY SPEC.md." if alarms else
                  "Nothing in capitals. The differences from RDKit are counted in the lines above, without capitals; "
                  "SPEC.md, sections 11.2 and 12.4, names their kinds."))
    return 1 if alarms else 0


if __name__ == "__main__":
    sys.exit(main())
