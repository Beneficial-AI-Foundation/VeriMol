import VeriMol.Core.WriteMarks

/-!
# The writer: from a `Mol` to a text (SPEC.md, sections 9 and 12.3)

The writer writes the atoms in the order of their numbers, so that reading
the text gives every atom its number back. An atom can be written next to an
earlier atom that it is bonded to, its parent: the bond between the two is
then written by position. Every other bond is written with a ring number.

There are two spellings (`Spelling`), and one writer for both. They differ
in the bonds along which the text may run, and in how much is left to what
a reader assumes:

* the **spelling with round brackets** (section 9.2), the usual one, which
  `rewrite` and `canonical` print (`write`). The text may run along every
  bond, so the parent of an atom can stand further back, and round brackets
  say where. An atom stands without square brackets where that is safe, and
  a bond symbol is left out where a reader assumes it;
* the **plain spelling** (section 9.1), which the command `plain` prints
  (`writePlain`). The text runs only along the bonds between two atoms that
  follow each other, so the parent of an atom can only be the atom just
  before it, and no round bracket is ever written. Every atom stands in
  square brackets, and every bond has its symbol, or its stereo mark in the
  place of the symbol.

Both are made of the parts of `VeriMol/Core/WriteParts.lean`, and both write
the stereo marks of the `Mol` in the way of `VeriMol/Core/WriteMarks.lean`
(section 12.3).

No text is read back before it is returned: that reading it gives the `Mol`
back is proven for both spellings (`read_write` and `read_writePlain` in
`VeriMol/Proofs/RoundTrip.lean`).
-/

namespace VeriMol

/-- The two spellings of a `Mol` (SPEC.md, section 9). -/
inductive Spelling where
  /-- no round brackets, every atom in square brackets, every bond symbol
  written (section 9.1) -/
  | plain
  /-- the usual spelling, with round brackets (section 9.2) -/
  | brackets

/-- Whether the text of this spelling may run along a bond: an atom can be
written next to an earlier atom only if such a bond joins the two. -/
def Spelling.runsAlong : Spelling → Bond → Bool
  | .plain, bond => bond.b == bond.a + 1
  | .brackets, _ => true

/-- The token of an atom that has no orientation. -/
def Spelling.atom : Spelling → List Bond → Nat → Atom → Token
  | .plain, bonds, number, atom => .atom (atom.inBrackets (writtenLowercase bonds number atom))
  | .brackets, bonds, number, atom => shortAtom bonds number atom

/-- The symbol of a bond that carries no mark. -/
def Spelling.symbol : Spelling → Mol → Bond → List Token
  | .plain, _, bond => plainSymbol bond
  | .brackets, mol, bond => shortSymbol mol bond

/-! ## Parents -/

/-- Whether these two atoms are joined by one of `bonds`. `first` is the one
with the smaller number. -/
def bonded (bonds : List Bond) (first second : Nat) : Bool :=
  bonds.any fun bond => bond.a == first && bond.b == second

/-- The parents of the atoms from number `atom` on, for a text that runs along
`bonds`. An atom is written next to its parent. An atom without a parent has
a dot in front of it, unless it is the first atom. The list of atoms is only
counted: it says how many atoms follow.

`path` holds the atoms from which the text can still go on, the one written
last first. The parent of an atom is the first atom of the path that it is
bonded to. The path is then cut back to the parent, and the atom is put in
front. With no such atom, the path starts again with this atom. -/
def parentsFrom (bonds : List Bond) (atom : Nat) (path : List Nat) :
    List Atom → List (Option Nat)
  | [] => []
  | _ :: rest =>
    match path.find? fun earlier => bonded bonds earlier atom with
    | some parent =>
      some parent :: parentsFrom bonds (atom + 1) (atom :: path.dropWhile (· != parent)) rest
    | none => none :: parentsFrom bonds (atom + 1) [atom] rest

/-- The parent of every atom of a `Mol`, as a spelling writes it: the parents
for a text that runs along the bonds which `Spelling.runsAlong` allows. -/
def Spelling.parents (spelling : Spelling) (mol : Mol) : List (Option Nat) :=
  parentsFrom (mol.bonds.filter spelling.runsAlong) 0 [] mol.atoms

/-- The parent of atom number `atom`, if it has one. -/
def parentOf (parents : List (Option Nat)) (atom : Nat) : Option Nat :=
  parents[atom]?.getD none

/-- Whether a bond is written with a ring number: its later atom is not
written next to its earlier atom. -/
def ringBond (parents : List (Option Nat)) (bond : Bond) : Bool :=
  parentOf parents bond.b != some bond.a

/-- Where a spelling writes a place of atom `atom`: its parent, its fourth
place, its ring numbers in the order of the other atom's number, the later
atoms whose parent it is. -/
def placeKey (parents : List (Option Nat)) (atom : Nat) : Place → Nat × Nat
  | none => (1, 0)
  | some other =>
    if parentOf parents atom = some other then (0, 0)
    else if parentOf parents other = some atom then (3, other)
    else (2, other)

/-! ## The tokens -/

/-- What stands in front of atom number `number`. `later` holds the parents of
the atoms that follow.

* An atom without a parent: a dot, unless it is the first atom.
* An atom with a parent: a `)` if the parent is not the atom just before it.
  Then a `(` if a later atom has the same parent. Then the symbol of its bond
  to the parent: the mark of the bond if it carries one, and otherwise the
  bond symbol, if it is written.

No list of the open round brackets is kept. A `(` stands in front of an atom
whose parent has another atom to come, and the next atom with that parent
closes it: when the text comes back to a parent, the innermost round bracket
that is open is the one of this parent (`openOn_parent` in
`VeriMol/Proofs/Brackets.lean`). So one `)` is enough there, and no round
bracket is open in front of a dot or at the end of the text. That this gives
the same tokens as closing round brackets by the rules of SPEC.md, section
9.2, with their list of the open round brackets, is proven in
`VeriMol/Proofs/BracketRules.lean`. In the plain spelling the parent of an
atom is the atom just before it, so neither a `)` nor a `(` is written. -/
def beforeAtom (spelling : Spelling) (mol : Mol) (marks : Marks) (number : Nat)
    (parent : Option Nat) (later : List (Option Nat)) : List Token :=
  match parent with
  | none => if number = 0 then [] else [.dot]
  | some parent =>
    let closing := if parent + 1 = number then [] else [Token.branchClose]
    let opening := if later.contains (some parent) then [Token.branchOpen] else []
    let symbol :=
      match mol.bonds.find? fun bond => bond.a == parent && bond.b == number with
      | some bond => markedSymbol marks (spelling.symbol mol) bond
      -- Cannot happen for the parents of `Spelling.parents`: an atom is bonded
      -- to its parent (`parentOf_parent` in `VeriMol/Proofs/RoundTrip.lean`).
      | none => []
    closing ++ opening ++ symbol

/-- The tokens of a spelling for the atoms from number `number` on. Each atom
comes with its parent. `parents` holds the parents of all atoms, and `rings`
the open ring numbers.

For every atom, in the order of the atom numbers, the writer writes what
stands in front of it (`beforeAtom`), the atom itself, and then a ring number
for each of its bonds to an atom that is neither its parent nor has it as
its parent. First come the bonds to earlier atoms, which close the number
they were given. Then come the bonds to later atoms, which open the smallest
number that is not in use, with the symbol of the bond in front.

The bonds of a well formed `Mol` are in order. So the bonds that close at an
atom come out of the list in the order of their earlier atom, and the bonds
that open there in the order of their later atom, as SPEC.md, section 9.1,
wants them. -/
def tokensFrom (spelling : Spelling) (mol : Mol) (marks : Marks) (parents : List (Option Nat)) :
    Nat → List (Atom × Option Nat) → List (Nat × Bond) → Except (List Char) (List Token)
  | _, [], _ => .ok []
  | number, (atom, parent) :: rest, rings =>
    let closes := mol.bonds.filter fun bond => bond.b == number && ringBond parents bond
    let opens := mol.bonds.filter fun bond => bond.a == number && ringBond parents bond
    let token : Except (List Char) Token :=
      match mol.orientationAt number with
      | none => .ok (spelling.atom mol.bonds number atom)
      | some stored =>
        match centreRefusal mol number parent.isSome (closes.length + opens.length) with
        | some message => .error message
        | none => .ok (orientedAtom mol number atom stored (placeKey parents number))
    match token with
    | .error message => .error message
    | .ok token =>
      match closeRings rings closes with
      -- Cannot happen for a well formed `Mol`: see `closeRings`.
      | none => .error Message.tooManyRingNumbers
      | some (closing, afterClosing) =>
        match openRings (markedSymbol marks (spelling.symbol mol)) afterClosing opens with
        | none => .error Message.tooManyRingNumbers
        | some (opening, afterOpening) =>
          match tokensFrom spelling mol marks parents (number + 1) rest afterOpening with
          | .error message => .error message
          | .ok behind =>
            .ok (beforeAtom spelling mol marks number parent (rest.map (·.2))
              ++ token :: closing ++ opening ++ behind)

/-- The tokens of a spelling, with the marks `marks` at its bonds, or the
reason why the `Mol` cannot be spelled so. The message about ring numbers
comes if the writer finds no free ring number: more than 99 are needed at
the same time. (It would come as well if a ring bond that is to close had no
number. For a well formed `Mol` that does not happen: see `closeRings`.) -/
def Spelling.tokens (spelling : Spelling) (mol : Mol) (marks : Marks) :
    Except (List Char) (List Token) :=
  tokensFrom spelling mol marks (spelling.parents mol) 0
    (mol.atoms.zip (spelling.parents mol)) []

/-! ## From the tokens to the text -/

/-- A `Mol` in one of the two spellings, as text, or the reason why it cannot
be spelled so (SPEC.md, sections 9.4 and 12.3). The questions are asked in
this order: whether the `Mol` is well formed; its atoms (section 9.4); which
bonds carry a mark; and then, atom by atom, whether an atom with an
orientation can be written where it stands, and whether a ring number is
free. -/
def Spelling.write (spelling : Spelling) (mol : Mol) : Except (List Char) (List Char) :=
  if ¬ mol.WellFormed then .error Message.notWellFormed
  else
    match mol.atoms.findSome? Atom.refusal with
    | some message => .error message
    | none =>
      match chooseMarks mol with
      | .error message => .error message
      | .ok marks =>
        match spelling.tokens mol marks with
        | .error message => .error message
        | .ok written =>
          match spell written with
          | some text => .ok text
          -- Cannot happen: the tokens that a spelling makes for a `Mol` whose
          -- atoms can all be written can be spelled (`Spelling.tokens_spelled`
          -- in `VeriMol/Proofs/Spelled.lean`).
          | none => .error Message.tooManyRingNumbers

/-- What the command `plain` writes: the plain spelling of a `Mol`, with its
stereo marks (SPEC.md, sections 9.1 and 12.3), or the reason why the `Mol`
cannot be spelled so. -/
def writePlain (mol : Mol) : Except (List Char) (List Char) :=
  Spelling.plain.write mol

/-- What the command `rewrite` writes: the spelling of a `Mol` with round
brackets, with its stereo marks (SPEC.md, sections 9.2 and 12.3), or the
reason why the `Mol` cannot be spelled so. -/
def write (mol : Mol) : Except (List Char) (List Char) :=
  Spelling.brackets.write mol

end VeriMol
