import VeriMol.Core.Hydrogens
import VeriMol.Core.Problem
import VeriMol.Core.Rings
import VeriMol.Core.Spell

/-!
# What a spelling is made of: atoms, bond symbols, ring numbers (SPEC.md, section 9)

The writer turns a `Mol` into tokens, and `spell` turns the tokens into text
(`VeriMol/Core/Spell.lean`). This file holds what the two spellings of
`VeriMol/Core/Write.lean` are made of:

* **Atoms.** Which atoms cannot be written (section 9.4), when a symbol is
  written in lowercase, and when an atom stands without square brackets
  (section 9.2).
* **Bond symbols.** Written out, or left out where a reader assumes them.
* **Ring numbers.** While it writes, the writer keeps a table of the open ring
  numbers (`VeriMol/Core/Rings.lean`): for every number in use, the bond that
  the number stands for.
-/

namespace VeriMol

/-! ## Atoms -/

/-- Why this atom cannot be written, if it cannot (SPEC.md, section 9.4). -/
def Atom.refusal (atom : Atom) : Option (List Char) :=
  if 9 < atom.hydrogens ∨ 99 < atom.charge.natAbs then some Message.hydrogensOrCharge
  else if atom.element = .H ∧ 0 < atom.hydrogens then some Message.hydrogenWithHydrogens
  else none

/-- Whether atom number `number` is written with a lowercase symbol: it has an
aromatic bond, and its element has a lowercase symbol (SPEC.md, section 9). The
`Mol` does not store the case of a symbol, so the writer works it out here. -/
def writtenLowercase (bonds : List Bond) (number : Nat) (atom : Atom) : Bool :=
  hasAromaticBond bonds number && atom.element.lowercaseSymbol?.isSome

/-- Whether atom number `atom` of a `Mol` is written with a lowercase symbol. -/
def lowercaseAt (mol : Mol) (atom : Nat) : Bool :=
  match mol.atoms[atom]? with
  | some found => writtenLowercase mol.bonds atom found
  | none => false

/-- The order that a reader assumes for a bond without a symbol between these
two atoms, as they are written (SPEC.md, section 5, rule 5): aromatic between
two atoms that are written in lowercase, and single between any other two. -/
def Mol.assumedOrder (mol : Mol) (a b : Nat) : BondOrder :=
  if lowercaseAt mol a && lowercaseAt mol b then .aromatic else .single

/-- An atom as it is written in square brackets: everything about it is
written out. `lower` says whether its symbol is the lowercase one. -/
def Atom.inBrackets (lower : Bool) (atom : Atom) : WrittenAtom :=
  { element := atom.element, aromatic := lower, isotope := atom.isotope,
    charge := atom.charge, hydrogens := some atom.hydrogens, mark := none }

/-- Whether an atom is written without square brackets. All five conditions of
SPEC.md, section 9.2, must hold. The first three make sure that reading the
bare atom gives the same atom back. The last two keep the square brackets in
the situations in which this program and RDKit count the hydrogens of a bare
atom differently (section 11.2). -/
def writtenBare (bonds : List Bond) (number : Nat) (atom : Atom) : Bool :=
  let sum := bondSum bonds number
  let lower := writtenLowercase bonds number atom
  -- 1. the element may stand without square brackets
  (bareSymbol? atom.element lower).isSome
  -- 2. no isotope and no charge
  && atom.isotope.isNone && atom.charge == 0
  -- 3. the hydrogens are what a reader works out for a bare atom
  && bareHydrogens atom.element lower sum == atom.hydrogens
  -- 4. the bonds add up to at most the smallest normal valence, or to
  --    exactly one of the normal valences
  && (match atom.element.valences with
      | smallest :: _ => sum ≤ smallest || atom.element.valences.contains sum
      | [] => false)
  -- 5. none of its bonds is aromatic, or it is written in lowercase
  && lower == hasAromaticBond bonds number

/-- The token of an atom: bare where that is safe, otherwise in square
brackets. -/
def shortAtom (bonds : List Bond) (number : Nat) (atom : Atom) : Token :=
  let lower := writtenLowercase bonds number atom
  .atom (if writtenBare bonds number atom then .bare atom.element lower else atom.inBrackets lower)

/-! ## Bond symbols -/

/-- The symbol of a bond, always written. -/
def plainSymbol (bond : Bond) : List Token :=
  [.bond (.order bond.order)]

/-- The symbol of a bond, left out if it is the one a reader assumes. -/
def shortSymbol (mol : Mol) (bond : Bond) : List Token :=
  if bond.order = mol.assumedOrder bond.a bond.b then [] else plainSymbol bond

/-! ## Ring numbers -/

/-- The ring numbers that the writer uses: 1 to 99. -/
def ringNumbers : List Nat :=
  List.range' 1 99

/-- The smallest ring number that is not in use. `none` if all 99 are. -/
def freeNumber (rings : List (Nat × Bond)) : Option Nat :=
  ringNumbers.find? fun number => (ringAt number rings).isNone

/-- The ring number that this bond was given. -/
def numberOf (rings : List (Nat × Bond)) (bond : Bond) : Option Nat :=
  ringNumbers.find? fun number =>
    match ringAt number rings with
    | some other => other.a == bond.a && other.b == bond.b
    | none => false

/-- Closes the given bonds, one after the other: each with the ring number it
was given. Returns the tokens and the table without these numbers. `none` if
one of the bonds has no number. That does not happen: the writer spells well
formed `Mol`s only, and for them every ring bond gets a number when it opens
and is found again when it closes (`closeRings_counted` and
`tokensFrom_tooManyRingNumbers` in `VeriMol/Proofs/RingNumbers.lean`). -/
def closeRings (rings : List (Nat × Bond)) :
    List Bond → Option (List Token × List (Nat × Bond))
  | [] => some ([], rings)
  | bond :: rest =>
    match numberOf rings bond with
    | none => none
    | some number =>
      match closeRings (withoutRing number rings) rest with
      | none => none
      | some (tokens, left) => some (.ring number :: tokens, left)

/-- Opens the given bonds, one after the other: each gets the smallest ring
number that is not in use. `symbol` says what is written in front of the
number. Returns the tokens and the table with these numbers. `none` if more
than 99 numbers are needed at the same time. -/
def openRings (symbol : Bond → List Token) (rings : List (Nat × Bond)) :
    List Bond → Option (List Token × List (Nat × Bond))
  | [] => some ([], rings)
  | bond :: rest =>
    match freeNumber rings with
    | none => none
    | some number =>
      match openRings symbol ((number, bond) :: rings) rest with
      | none => none
      | some (tokens, left) => some (symbol bond ++ .ring number :: tokens, left)

end VeriMol
