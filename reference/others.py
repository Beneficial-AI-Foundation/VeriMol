"""What other programs read from a SMILES text, in the form of the model's Mol, and a few small things that
several checks share.

    rdkit_mol(text)              RDKit with its clean-up switched off, so that it reports what is written
    openbabel_mol(text)          Open Babel, an independent second reader
    syntax_verdict(text)         partialsmiles, a strict reader: is the text grammatical SMILES at all?
    same_molecule(a, b)          does RDKit, with its clean-up on, take two texts for the same molecule,
                                 stereo included?
    with_hydrogens(text)         what RDKit reads, with its clean-up off and every hydrogen made an atom
                                 of its own
    same_atoms_and_bonds(a, b)   does RDKit take two texts for the same atoms and bonds, hydrogens included?

Only the atoms and the bonds are compared atom by atom: element, isotope, charge, hydrogens, bonds. The
stereo facts of a Mol are compared by `reference/check_stereo.py`.

The file also holds RDKit's canonical texts (`rdkit_canonical`, `rdkit_canonical_as_read`,
`rdkit_canonical_with_hydrogens`), two wrong texts that are made on purpose (`one_hydrogen_fewer`), and what
several checks share: what SPEC.md, section 11.2, says of RDKit (`OLD_NAMES`, `MOST_THAT_RDKIT_TAKES`,
`one_of_the_five`), RDKit's element symbols, the rule for a lowercase symbol (`lowercase_by_rule`), the
printed layout as two patterns, and two questions about a Mol (`without_stereo`, `pieces`).
"""
import re

from rdkit import Chem, RDLogger

import model

RDLogger.DisableLog("rdApp.*")

# RDKit's symbols of the elements 1 to 118.
RDKIT_ELEMENTS = [Chem.GetPeriodicTable().GetElementSymbol(n) for n in range(1, 119)]
# SPEC.md, section 11.2: the old names of the elements 110 to 118, which RDKit reads; and the largest mass
# number that RDKit takes: one above it makes RDKit refuse the text.
OLD_NAMES = ("Uun", "Uuu", "Uub", "Uut", "Uuq", "Uup", "Uuh", "Uus", "Uuo")
MOST_THAT_RDKIT_TAKES = 2147483639

# The printed layout of SPEC.md, section 7, as two patterns: an atom, with its mass number a second time
# as digits alone, and a bond.
PRINTED_ATOM = re.compile(r"\{ element := \.(\w+), isotope := (none|some (\d+)), charge := (-?\d+), hydrogens := (\d+) \}")
PRINTED_BOND = re.compile(r"\{ a := (\d+), b := (\d+), order := \.(\w+) \}")

_RDKIT_ORDER = {Chem.BondType.SINGLE: "single", Chem.BondType.DOUBLE: "double", Chem.BondType.TRIPLE: "triple",
                Chem.BondType.QUADRUPLE: "quadruple", Chem.BondType.AROMATIC: "aromatic"}


def rdkit_mol(text):
    m = Chem.MolFromSmiles(text, sanitize=False)
    if m is None:
        return None
    m.UpdatePropertyCache(strict=False)
    atoms = tuple(model.Atom(a.GetSymbol(), a.GetIsotope() or None, a.GetFormalCharge(), a.GetTotalNumHs())
                  for a in m.GetAtoms())
    bonds = sorted((min(b.GetBeginAtomIdx(), b.GetEndAtomIdx()), max(b.GetBeginAtomIdx(), b.GetEndAtomIdx()),
                    _RDKIT_ORDER.get(b.GetBondType(), str(b.GetBondType()))) for b in m.GetBonds())
    return model.Mol(atoms, tuple(model.Bond(a, b, o) for a, b, o in bonds))


WITH_A_LOWERCASE_SYMBOL = {"B", "C", "N", "O", "P", "S", "Se", "As"}     # these elements have one (SPEC.md, section 4)


def rdkit_lowercase(text):
    """For each atom of the text, in the order of the text: whether RDKit, with its clean-up off, reads its
    symbol as a lowercase one. None if RDKit does not read the text."""
    m = Chem.MolFromSmiles(text, sanitize=False)
    return None if m is None else [a.GetIsAromatic() for a in m.GetAtoms()]


def lowercase_by_rule(mol):
    """For each atom of the Mol: whether SPEC.md, section 9, has the writer write its symbol in lowercase. That
    is so when one of its bonds is aromatic and its element has a lowercase symbol. The rule is written out
    here, so that a check can hold a written text against it without asking the model's writer."""
    with_aromatic_bond = {i for b in mol.bonds if b.order == "aromatic" for i in (b.a, b.b)}
    return [i in with_aromatic_bond and a.element in WITH_A_LOWERCASE_SYMBOL for i, a in enumerate(mol.atoms)]


def rdkit_canonical_as_read(text):
    """RDKit's own canonical text for the atoms and bonds of a text as it reads them, with its clean-up off,
    which is not the way RDKit is meant to make a canonical text. Asked so, RDKit 2024.03.3 does not give
    every two numberings of the same atoms and bonds the same text (reference/README.md names a real
    text), so the checks of the real texts do not rest on it alone: see `rdkit_canonical_with_hydrogens`
    and `same_atoms_and_bonds`. check_spec.py asks it about four small texts.
    None if RDKit does not read the text."""
    m = Chem.MolFromSmiles(text, sanitize=False)
    if m is None:
        return None
    m.UpdatePropertyCache(strict=False)
    return Chem.MolToSmiles(m)


# The mark of a hydrogen that a text counts at its atom: a mass number that no real text has (for a text
# that has it, `with_hydrogens` gives None).
COUNTED = 7777


def with_hydrogens(text):
    """What RDKit reads from a text with its clean-up off, with every hydrogen made an atom of its own. A
    hydrogen that the text counts at its atom gets the mark `COUNTED` as its mass number, which tells it
    from a hydrogen that the text writes as an atom. None if RDKit does not read the text, or if the text
    itself holds an atom with that mass number."""
    m = Chem.MolFromSmiles(text, sanitize=False)
    if m is None or any(atom.GetIsotope() == COUNTED for atom in m.GetAtoms()):
        return None
    m.UpdatePropertyCache(strict=False)
    written = m.GetNumAtoms()
    m = Chem.AddHs(m)               # the new atoms stand behind the atoms of the text
    for number in range(written, m.GetNumAtoms()):
        m.GetAtomWithIdx(number).SetIsotope(COUNTED)
    return m


def same_atoms_and_bonds(a, b):
    """Are two texts the same atoms and bonds to RDKit, hydrogens included, numbered differently? Its
    clean-up is off. The answer says how RDKit was asked: "by its own canonical text"; or one that begins
    "asked in the second way", which does not go through its canonical text: as many atoms, as many
    bonds, and each of the two found whole inside the other. None if they are not the same, or if RDKit
    does not read one."""
    first, second = with_hydrogens(a), with_hydrogens(b)
    if first is None or second is None:
        return None
    if Chem.MolToSmiles(first) == Chem.MolToSmiles(second):
        return "by its own canonical text"

    def census(m):
        """What can be counted without a search: the atoms by kind and by number of bonds, the bonds by kind."""
        return (sorted((a.GetAtomicNum(), a.GetIsotope(), a.GetFormalCharge(), a.GetDegree()) for a in m.GetAtoms()),
                sorted((str(b.GetBondType()),) + tuple(sorted((b.GetBeginAtom().GetAtomicNum(), b.GetEndAtom().GetAtomicNum())))
                       for b in m.GetBonds()))

    if census(first) != census(second):     # asked first: a search for one molecule inside another can take very long before it says no
        return None
    for m in (first, second):
        m.UpdatePropertyCache(strict=False)
        Chem.FastFindRings(m)
    if first.HasSubstructMatch(second) and second.HasSubstructMatch(first):
        return "asked in the second way; its own canonical text differs for these two numberings"
    return None


# An atom in square brackets with hydrogens and without a stereo mark, as the plain spelling writes it:
# the mass number and the symbol, the number of hydrogens, the charge.
ATOM_WITH_HYDROGENS = re.compile(r"\[(\d*(?:[A-Z][a-z]?|[a-z]{1,2}))H(\d*)([+-]\d*)?\]")


def one_hydrogen_fewer(plain):
    """Two wrong texts, made from a text in the plain spelling: the first atom that has hydrogens and no
    stereo mark gets one hydrogen fewer; and, if that atom is the first atom of the text, one of its
    hydrogens becomes an atom of its own in front of it. None where there is no such atom."""
    found = ATOM_WITH_HYDROGENS.search(plain)
    if found is None:
        return None, None
    symbol, number, charge = found.group(1), int(found.group(2) or 1), found.group(3) or ""
    less = "" if number == 1 else "H" if number == 2 else f"H{number - 1}"
    atom = f"[{symbol}{less}{charge}]"
    fewer = plain[:found.start()] + atom + plain[found.end():]
    return fewer, ("[H]" + fewer if found.start() == 0 else None)


def rdkit_canonical_with_hydrogens(text):
    """RDKit's own canonical text, with its clean-up off, for a text of which every hydrogen is made an atom
    of its own first (`with_hydrogens`). Without that step, and with the clean-up off, the canonical text
    of RDKit 2024.03.3 is the same for `CC[O]` and `CCO`. None where `with_hydrogens` gives None."""
    m = with_hydrogens(text)
    return None if m is None else Chem.MolToSmiles(m)


def rdkit_canonical(text, stereo=True):
    """RDKit's own standard spelling, with its clean-up on. None if RDKit refuses the molecule."""
    m = Chem.MolFromSmiles(text)
    return None if m is None else Chem.MolToSmiles(m, isomericSmiles=stereo)


def same_molecule(a, b):
    """Does RDKit, with its clean-up on, take the two texts for the same molecule?

    "same"            yes, stereo included
    "stereo differs"  the same atoms and bonds, but another arrangement in space
    "picture differs" its clean-up gives the two texts two canonical texts that differ in more than stereo,
                      although the two have the same atoms and bonds with its clean-up off (the caller has
                      to make sure of that). No verdict about stereo
    None              its clean-up refuses one of the two
    """
    ca, cb = rdkit_canonical(a), rdkit_canonical(b)
    if ca is None or cb is None:
        return None
    if ca == cb:
        return "same"
    return "stereo differs" if rdkit_canonical(a, False) == rdkit_canonical(b, False) else "picture differs"


def openbabel_mol(text):
    from openbabel import openbabel as ob
    ob.obErrorLog.StopLogging()
    conversion, m = ob.OBConversion(), ob.OBMol()
    conversion.SetInFormat("smi")
    if not conversion.ReadString(m, text):
        return None
    atoms = tuple(model.Atom(ob.GetSymbol(a.GetAtomicNum()), a.GetIsotope() or None, a.GetFormalCharge(),
                             a.GetImplicitHCount()) for a in ob.OBMolAtomIter(m))
    orders = {1: "single", 2: "double", 3: "triple", 4: "quadruple"}
    bonds = sorted((min(b.GetBeginAtomIdx(), b.GetEndAtomIdx()) - 1, max(b.GetBeginAtomIdx(), b.GetEndAtomIdx()) - 1,
                    "aromatic" if b.IsAromatic() else orders.get(b.GetBondOrder(), str(b.GetBondOrder())))
                   for b in ob.OBMolBondIter(m))
    return model.Mol(atoms, tuple(model.Bond(a, b, o) for a, b, o in bonds))


def syntax_verdict(text):
    """One of "accepted", "syntax error" and "other error" (partialsmiles raised an error of another kind)."""
    import partialsmiles
    try:
        partialsmiles.ParseSmiles(text, partial=False)
    except partialsmiles.SMILESSyntaxError:
        return "syntax error"
    except (partialsmiles.ValenceError, partialsmiles.KekulizationFailure):
        return "accepted"               # grammatical; the objection is to a valence or to an aromatic ring
    except Exception:
        return "other error"
    return "accepted"


def without_stereo(mol):
    """The atoms and the bonds of a Mol: its two lists of stereo facts left out."""
    return model.Mol(mol.atoms, mol.bonds)


def pieces(mol):
    """How many separate pieces the Mol has."""
    group = list(range(len(mol.atoms)))

    def find(x):
        while group[x] != x:
            x = group[x]
        return x
    for b in mol.bonds:
        group[find(b.a)] = find(b.b)
    return len({find(x) for x in range(len(mol.atoms))})


def one_of_the_five(element, lowercase, total, aromatic_bond):
    """The five situations of SPEC.md, section 11.2, in which RDKit counts other hydrogens at a bare atom.
    `element` is the element of the atom, `lowercase` says whether its symbol is written in lowercase,
    `total` is what its bonds add up to, and `aromatic_bond` whether one of them is aromatic. The three
    situations that name an element are taken for an uppercase atom only, as the table shows them."""
    return ((not lowercase and aromatic_bond) or (lowercase and not aromatic_bond)
            or (not lowercase and (element, total) in (("N", 4), ("P", 6), ("I", 2), ("I", 4))))
