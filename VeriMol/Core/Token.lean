import VeriMol.Core.Mol

/-!
# Tokens: the pieces a SMILES text is made of

A token is one atom, one bond symbol, one ring number, one round bracket or
one dot. A token says what is written. What it means for the molecule is the
business of the reader.

The tokens include the stereo marks `@`, `@@`, `/` and `\` (SPEC.md, section
12.2). What a mark says about the molecule depends on the order in which the
text writes the atoms: the reader in `VeriMol/Core/Read.lean` notes the marks,
and `VeriMol/Core/ReadMarks.lean` works out what they say.
-/

namespace VeriMol

/-- What can stand where a bond symbol stands. -/
inductive BondSymbol where
  /-- one of the five bond symbols `-`, `=`, `#`, `$` and `:` -/
  | order (order : BondOrder)
  /-- the direction mark `/` -/
  | up
  /-- the direction mark `\` -/
  | down
  deriving DecidableEq, Repr

/-- An atom as it is written. -/
structure WrittenAtom where
  element   : Element
  /-- whether it is written with a lowercase symbol (an "aromatic symbol" in
  OpenSMILES; the name says how the atom is written, not that it is aromatic) -/
  aromatic  : Bool
  isotope   : Option Nat
  charge    : Int
  /-- `none` for an atom without square brackets: its hydrogens are worked out
  later, from its bonds (SPEC.md, section 5, rule 7). In square brackets the
  hydrogens are always given, 0 if none are written. -/
  hydrogens : Option Nat
  /-- the stereo mark, which only an atom in square brackets can have: `@` is
  `anticlockwise` and `@@` is `clockwise`, said for the places of the atom in
  the order in which the text writes them -/
  mark      : Option Orientation
  deriving DecidableEq, Repr

/-- An atom without square brackets. -/
def WrittenAtom.bare (element : Element) (aromatic : Bool) : WrittenAtom :=
  { element, aromatic, isotope := none, charge := 0, hydrogens := none, mark := none }

/-- One token of a SMILES text. -/
inductive Token where
  | atom (atom : WrittenAtom)
  | bond (symbol : BondSymbol)
  | ring (number : Nat)
  /-- `(` -/
  | branchOpen
  /-- `)` -/
  | branchClose
  /-- `.` -/
  | dot
  deriving DecidableEq, Repr

/-- A token together with its place in the text.

`position` is where a problem with this token is reported: the position of its
first character. The one exception is an atom with a stereo mark, where it is
the position of the `@` (SPEC.md, section 12.2). -/
structure Placed where
  token : Token
  position : Nat
  deriving DecidableEq, Repr

end VeriMol
