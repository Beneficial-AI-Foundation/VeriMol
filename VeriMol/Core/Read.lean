import VeriMol.Core.Cut
import VeriMol.Core.Hydrogens
import VeriMol.Core.ReadMarks
import VeriMol.Core.Rings

/-!
# The reader: from a text to a `Mol` (SPEC.md, sections 5 and 6)

The text is cut into tokens (`VeriMol/Core/Cut.lean`), and the reader goes
through the tokens once, from left to right. While it does, it keeps a
`Reading`: the atoms and bonds found so far, and what it has to remember for
the tokens that follow. `step` takes one token, `steps` takes them all, and
`finish` makes the checks that belong to the end of the text and works out the
hydrogens.

The first problem that is met is the one that is reported. A problem with a
token comes first. Then comes the problem that `cut` found in the characters,
because it stands further right than every token. Then come the problems that
only show at the end of the text. Last come the problems with the stereo
marks, which are looked for when the text has no other problem.

The stereo marks `@`, `@@`, `/` and `\` do not change which atoms and bonds
are read: a bond with `/` or `\` gets the order that it would have without a
symbol. The reader only notes the marks and where they stand. `finish` hands
these notes to `stereoFacts` (`VeriMol/Core/ReadMarks.lean`), which works out
what they say (SPEC.md, section 12.2).
-/

namespace VeriMol

/-! ## Bonds in order -/

/-- The order in which the bonds of a `Mol` are listed: by `a` first, then by
`b`. -/
def Bond.before (x y : Bond) : Prop :=
  x.a < y.a ∨ (x.a = y.a ∧ x.b < y.b)

instance (x y : Bond) : Decidable (x.before y) :=
  show Decidable (_ ∨ _) from inferInstance

/-- Puts a bond at its place in a list of bonds that is in order. So the bonds
are in order all the time, and nothing has to be sorted at the end. -/
def insertBond (new : Bond) : List Bond → List Bond
  | [] => [new]
  | bond :: rest =>
    if new.before bond then new :: bond :: rest else bond :: insertBond new rest

/-! ## Bonds without a symbol -/

/-- Whether atom number `atom` is written with a lowercase symbol. -/
def isLowercase (atoms : List WrittenAtom) (atom : Nat) : Bool :=
  match atoms[atom]? with
  | some written => written.aromatic
  | none => false

/-- The order of a bond that is written without a symbol: aromatic between
two lowercase atoms, single otherwise (SPEC.md, section 5, rule 5). -/
def assumedOrder (atoms : List WrittenAtom) (first second : Nat) : BondOrder :=
  if isLowercase atoms first && isLowercase atoms second then .aromatic else .single

/-! ## Ring numbers -/

/-- A ring number that is written once so far. -/
structure OpenRing where
  /-- the atom it is written at -/
  atom : Nat
  /-- the bond symbol in front of it, if there is one -/
  order : Option BondOrder
  /-- where it stands in the text -/
  position : Nat
  /-- its place among the ring numbers of its atom, counted from 0 -/
  place : Nat
  /-- the direction mark in front of it, if there is one: whether it is `/`,
  and the position of the mark -/
  mark : Option (Bool × Nat)

/-! The open ring numbers are kept in a table of `VeriMol/Core/Rings.lean`:
`ringAt` looks a number up, and `withoutRing` takes one out. -/

/-- Of the open rings, the one that stands first in the text. -/
def firstOpened : List (Nat × OpenRing) → Option (Nat × OpenRing)
  | [] => none
  | entry :: rest =>
    match firstOpened rest with
    | none => some entry
    | some other => if entry.2.position < other.2.position then some entry else some other

/-- The order of a ring bond. Each of its two ends may carry a bond symbol.
`none` if they carry different ones. If neither carries one, the order is
`assumed`. -/
def ringOrder (first second : Option BondOrder) (assumed : BondOrder) : Option BondOrder :=
  match first, second with
  | some first, some second => if first = second then some first else none
  | some first, none => some first
  | none, some second => some second
  | none, none => some assumed

/-! ## What may come next -/

/-- What was read last. It decides what may come next. -/
inductive Last where
  /-- nothing yet -/
  | nothing
  /-- a dot, at this position -/
  | dot (position : Nat)
  /-- `(` -/
  | branchOpen
  /-- a bond symbol after `(` -/
  | bondAfterOpen
  /-- a bond symbol after `)` -/
  | bondAfterClose
  /-- a bond symbol after an atom or a ring number -/
  | bondAfterAtom
  /-- an atom or a ring number -/
  | atom
  /-- `)` -/
  | branchClose

/-- The table "What may come next" of SPEC.md, section 6. -/
def Last.allows (last : Last) : Token → Bool
  | .atom _ => true
  | .bond _ => (last matches .branchOpen | .atom | .branchClose)
  | .ring _ => (last matches .atom | .bondAfterAtom)
  | .branchOpen => (last matches .atom | .branchClose)
  | .branchClose => (last matches .atom | .branchClose)
  | .dot => (last matches .branchOpen | .atom | .branchClose)

/-- The message for a token that may not come at its place. -/
def outOfPlace (last : Last) (token : Token) : List Char :=
  match token, last with
  | .ring _, .branchClose => Message.ringAfterBranch
  | .ring _, .bondAfterClose => Message.ringAfterBranch
  | _, .bondAfterAtom => Message.atomOrRingExpected
  | _, _ => Message.atomExpected

/-! ## Reading token by token -/

/-- What the reader knows after some of the tokens. -/
structure Reading where
  /-- the atoms so far, as they are written -/
  atoms : List WrittenAtom
  /-- the bonds so far, in the order of a `Mol` -/
  bonds : List Bond
  /-- the atom that the next atom is bonded to, if there is one -/
  previous : Option Nat
  /-- one of the five bond symbols that is read and not used yet, with its
  position (a `/` or `\` waits in `mark`) -/
  pending : Option (BondOrder × Nat)
  last : Last
  /-- the ring numbers that are open -/
  rings : List (Nat × OpenRing)
  /-- the round brackets that are open, the innermost first: for each one, what
  `previous` was in front of it, and the position of its `(` -/
  branches : List (Option Nat × Nat)
  /-- a direction mark that is read and not used yet: whether it is `/`, and
  its position -/
  mark : Option (Bool × Nat)
  /-- how many ring numbers were read since the last atom -/
  numbersAtAtom : Nat
  /-- the ring bonds so far, as they were written -/
  ringBonds : List RingBond
  /-- the direction marks so far, each with its bond -/
  directions : List Direction
  /-- the atoms so far that carry `@` or `@@` -/
  marked : List MarkedAtom

/-- Before the first token. -/
def Reading.start : Reading :=
  { atoms := [], bonds := [], previous := none, pending := none, last := .nothing,
    rings := [], branches := [], mark := none, numbersAtAtom := 0, ringBonds := [],
    directions := [], marked := [] }

/-- A direction mark as a note for the bond that it stands at. The mark is
written at atom `here` for its bond to atom `other`: `/` says that `other`
lies above `here`. The note says it for the two atoms with the smaller one
first. -/
def directionAt (here other : Nat) (mark : Bool × Nat) : Direction :=
  if here < other then ⟨here, other, mark.1, mark.2⟩ else ⟨other, here, !mark.1, mark.2⟩

/-- A ring number is written for the second time, at atom `atom`. It joins that
atom to the atom where it was opened. The things that can be wrong are
checked in the order of SPEC.md, sections 6 and 12.2: an atom bonded to
itself; two ends that name different bonds, which a direction mark at one end
and a bond symbol at the other do as well; two ends with the same direction
mark, which name different directions; two atoms that are bonded already. -/
def closeRing (reading : Reading) (number : Nat) (opened : OpenRing) (atom position : Nat) :
    Except Problem Reading :=
  if opened.atom = atom then .error ⟨position, Message.bondedToItself⟩
  else
    match ringOrder opened.order (reading.pending.map (·.1))
        (assumedOrder reading.atoms opened.atom atom) with
    | none => .error ⟨position, Message.differentBonds number⟩
    | some order =>
      if (opened.mark.isSome && reading.pending.isSome)
          || (reading.mark.isSome && opened.order.isSome) then
        .error ⟨position, Message.differentBonds number⟩
      else if (match opened.mark, reading.mark with
          | some first, some second => first.1 == second.1
          | _, _ => false) then
        .error ⟨position, Message.differentDirections number⟩
      else
        let a := min opened.atom atom
        let b := max opened.atom atom
        if reading.bonds.any (fun bond => bond.a = a ∧ bond.b = b) then
          .error ⟨position, Message.alreadyBonded⟩
        else
          .ok { reading with
            bonds := insertBond ⟨a, b, order⟩ reading.bonds
            rings := withoutRing number reading.rings
            pending := none
            last := .atom
            mark := none
            numbersAtAtom := reading.numbersAtAtom + 1
            ringBonds :=
              (if opened.atom < atom then
                  ⟨opened.atom, atom, opened.place, reading.numbersAtAtom⟩
                else ⟨atom, opened.atom, reading.numbersAtAtom, opened.place⟩)
                :: reading.ringBonds
            directions :=
              match opened.mark, reading.mark with
              -- a mark at the number that opened the ring: written at that atom
              | some mark, _ => directionAt opened.atom atom mark :: reading.directions
              -- a mark at the number that closes it: written at this atom
              | none, some mark => directionAt atom opened.atom mark :: reading.directions
              | none, none => reading.directions }

/-- Takes one token. -/
def step (reading : Reading) (placed : Placed) : Except Problem Reading :=
  let position := placed.position
  if !reading.last.allows placed.token then
    .error ⟨position, outOfPlace reading.last placed.token⟩
  else
    match placed.token with
    | .atom written =>
      let number := reading.atoms.length
      let atoms := reading.atoms ++ [written]
      .ok { reading with
        atoms := atoms
        bonds :=
          match reading.previous with
          | none => reading.bonds
          | some previous =>
            let order :=
              match reading.pending with
              | some (order, _) => order
              | none => assumedOrder atoms previous number
            insertBond ⟨previous, number, order⟩ reading.bonds
        previous := some number
        pending := none
        last := .atom
        mark := none
        numbersAtAtom := 0
        -- A direction mark in front of the atom stands at its bond to the
        -- atom that it is bonded to along the text.
        directions :=
          match reading.previous, reading.mark with
          | some previous, some mark => directionAt previous number mark :: reading.directions
          | _, _ => reading.directions
        marked :=
          match written.mark with
          | some mark => reading.marked ++ [⟨number, mark, position⟩]
          | none => reading.marked }
    | .bond symbol =>
      let last : Last :=
        match reading.last with
        | .atom => .bondAfterAtom
        | .branchOpen => .bondAfterOpen
        | _ => .bondAfterClose
      match symbol with
      | .order order => .ok { reading with pending := some (order, position), last := last }
      -- A direction mark stands where a bond symbol stands. The bond gets the
      -- order that it would have without a symbol, so no order is noted.
      | .up => .ok { reading with mark := some (true, position), last := last }
      | .down => .ok { reading with mark := some (false, position), last := last }
    | .ring number =>
      match reading.previous with
      -- Cannot happen: a ring number is only allowed where the reader knows
      -- the atom that it belongs to (`steps_previous` in
      -- `VeriMol/Proofs/Read.lean`).
      | none => .error ⟨position, Message.atomExpected⟩
      | some atom =>
        match ringAt number reading.rings with
        | none =>
          .ok { reading with
            rings :=
              (number,
                ⟨atom, reading.pending.map (·.1), position, reading.numbersAtAtom, reading.mark⟩)
                :: reading.rings
            pending := none
            last := .atom
            mark := none
            numbersAtAtom := reading.numbersAtAtom + 1 }
        | some opened => closeRing reading number opened atom position
    | .branchOpen =>
      .ok { reading with
        branches := (reading.previous, position) :: reading.branches
        last := .branchOpen }
    | .branchClose =>
      match reading.branches with
      | [] => .error ⟨position, Message.noMatchingOpen⟩
      | (previous, _) :: rest =>
        .ok { reading with previous := previous, branches := rest, last := .branchClose }
    | .dot => .ok { reading with previous := none, last := .dot position }

/-- Takes the tokens one after the other, and stops at the first problem. -/
def steps (reading : Reading) : List Placed → Except Problem Reading
  | [] => .ok reading
  | placed :: rest =>
    match step reading placed with
    | .error problem => .error problem
    | .ok next => steps next rest

/-! ## The end of the text -/

/-- An atom of the `Mol`, from the atom as it is written. `sum` is what its
bonds add up to, which gives an atom without square brackets its hydrogens. -/
def WrittenAtom.toAtom (written : WrittenAtom) (sum : Nat) : Atom :=
  { element := written.element
    isotope := written.isotope
    charge := written.charge
    hydrogens :=
      match written.hydrogens with
      | some hydrogens => hydrogens
      | none => bareHydrogens written.element written.aromatic sum }

/-- The atoms of the `Mol`. `number` is the number of the first atom of the
list. -/
def finishAtoms (bonds : List Bond) (number : Nat) : List WrittenAtom → List Atom
  | [] => []
  | written :: rest =>
    written.toAtom (bondSum bonds number) :: finishAtoms bonds (number + 1) rest

/-- The atoms and the bonds that were read, as a `Mol` without stereo facts. -/
def Reading.graph (reading : Reading) : Mol :=
  { atoms := finishAtoms reading.bonds 0 reading.atoms, bonds := reading.bonds }

/-- The `Mol` of a text whose atoms and bonds are read: the stereo marks are
turned into stereo facts, or the first problem with them is reported (SPEC.md,
section 12.2). -/
def withStereo (reading : Reading) : Except Problem Mol :=
  match stereoFacts reading.graph reading.ringBonds reading.directions reading.marked with
  | .error problem => .error problem
  | .ok facts => .ok { reading.graph with orientations := facts.1, geometries := facts.2 }

/-- The checks at the end of the text, in the order of SPEC.md, section 6, and
then the `Mol`. A direction mark at the end of the text is a bond symbol
there. -/
def finish (reading : Reading) : Except Problem Mol :=
  match reading.pending with
  | some (_, position) => .error ⟨position, Message.endsAfterBond⟩
  | none =>
    match reading.mark with
    | some (_, position) => .error ⟨position, Message.endsAfterBond⟩
    | none =>
      match reading.last with
      | .dot position => .error ⟨position, Message.endsAfterDot⟩
      | _ =>
        match reading.branches with
        | (_, position) :: _ => .error ⟨position, Message.branchNeverClosed⟩
        | [] =>
          match firstOpened reading.rings with
          | some (number, ring) => .error ⟨ring.position, Message.ringNeverClosed number⟩
          | none => withStereo reading

/-! ## The reader -/

/-- The `Mol` of a text that is cut into tokens. -/
def readCut (c : Cut) : Except Problem Mol :=
  match steps Reading.start c.tokens with
  | .error problem => .error problem
  | .ok reading =>
    match c.problem with
    | some problem => .error problem
    | none => finish reading

/-- Reads a SMILES text: the `Mol` it describes, or the first problem in it. -/
def read (text : List Char) : Except Problem Mol :=
  readCut (cut text)

end VeriMol
