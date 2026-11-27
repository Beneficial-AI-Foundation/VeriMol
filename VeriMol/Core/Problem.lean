import VeriMol.Core.Text

/-!
# Problems in a text, and the messages of the program

The messages are those of SPEC.md, sections 3.2, 6, 8, 9.4, 12.2, 12.3 and 16.
-/

namespace VeriMol

/-- Why a text is not read: the position of the problem, counted from 0, and
what is wrong there. The program prints it as
"error: position 3: <what is wrong>". -/
structure Problem where
  position : Nat
  message : List Char
  deriving DecidableEq, Repr

/-- A problem as it is printed: "position 3: <what is wrong>". -/
def Problem.text (problem : Problem) : List Char :=
  "position ".toList ++ natText problem.position ++ ": ".toList ++ problem.message

/-- Space, tab, line feed and carriage return. -/
def isWhite (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

namespace Message

/-! Characters and atoms in square brackets. -/

def whiteSpace : List Char := "white space is not allowed".toList
def stereoClass : List Char := "this stereo class is not read".toList
def wildcard : List Char := "the wildcard atom is not read".toList
def atomClass : List Char := "atom classes are not read".toList
def elementExpected : List Char := "an element symbol is expected here".toList
def hydrogenCount : List Char := "a hydrogen atom cannot have a hydrogen count".toList
def bracketNeverClosed : List Char := "'[' is never closed".toList
def percent : List Char := "'%' must be followed by two digits".toList
def cannotRead (c : Char) : List Char := ['\'', c, '\''] ++ " cannot be read here".toList

/-- The message for a character that does not fit where it stands: the first
of these that applies. -/
def doesNotFit (c : Char) : List Char :=
  if isWhite c then whiteSpace
  else if c = '*' then wildcard
  else if c = ':' then atomClass
  else cannotRead c

/-! Structure: an atom, symbol or number that is not allowed at its place. -/

def atomExpected : List Char := "an atom is expected here".toList
def atomOrRingExpected : List Char := "an atom or a ring number is expected here".toList
def ringAfterBranch : List Char :=
  "a ring number must come before the branches of its atom".toList
def noMatchingOpen : List Char := "')' has no matching '('".toList
def bondedToItself : List Char := "an atom cannot be bonded to itself".toList
def differentBonds (ring : Nat) : List Char :=
  "the two ends of ring ".toList ++ natText ring ++ " name different bonds".toList
def differentDirections (ring : Nat) : List Char :=
  "the two ends of ring ".toList ++ natText ring ++ " name different directions".toList
def alreadyBonded : List Char := "these two atoms are already bonded".toList

/-! The end of the text. -/

def endsAfterBond : List Char := "the text ends after a bond symbol".toList
def endsAfterDot : List Char := "the text ends after a dot".toList
def branchNeverClosed : List Char := "'(' is never closed".toList
def ringNeverClosed (ring : Nat) : List Char :=
  "ring ".toList ++ natText ring ++ " is opened but never closed".toList

/-! Stereo marks (SPEC.md, section 12.2). These are looked for when the text
has no other problem. -/

def notAStereoCentre : List Char := "this atom cannot be a stereo centre".toList
def freePlaceNeedsAtom : List Char :=
  "a stereo centre with a free place needs an atom before it".toList
def freePlaceAndOneRing : List Char :=
  "a stereo centre with a free place, one ring number and only single bonds is not read".toList
def marksContradict : List Char := "these marks contradict each other".toList
def markWithoutPartner : List Char :=
  "this mark has no partner on the other side of a double bond".toList

/-! Why the writer refuses a `Mol` (SPEC.md, sections 9.4 and 12.3). -/

def notWellFormed : List Char := "the Mol is not well formed".toList
def hydrogensOrCharge : List Char :=
  "an atom has more than 9 hydrogens, or a charge beyond +99 or -99".toList
def hydrogenWithHydrogens : List Char := "a hydrogen atom has hydrogens of its own".toList
def tooManyRingNumbers : List Char :=
  "more than 99 ring numbers are needed at the same time".toList
def freePlaceWithoutAtom : List Char :=
  "a stereo centre with a free place would be written without an atom before it".toList
def freePlaceWithOneRing : List Char :=
  "a stereo centre with a free place would be written with one ring number and only single bonds".toList
def noBondForAMark : List Char :=
  "at one atom of a double bond with a geometry, no bond can carry a mark".toList
def marksGiveAGeometry : List Char :=
  "the marks would give a geometry to a double bond that has none".toList
def noChoiceOfMarks : List Char := "no choice of marks gives every geometry".toList

/-! Why `canonical` gives no text for a `Mol` that it read (SPEC.md, section
3.2). -/

def tooManyAtoms (limit : Nat) : List Char :=
  "the chosen form is not worked out: more than ".toList ++ natText limit ++ " atoms".toList
def searchGivesUp : List Char :=
  "the chosen form is not worked out: too many numberings of this molecule look alike".toList

/-! Why the filter refuses a `Mol` that was read (SPEC.md, section 16). A `Mol`
that is not sound gets the first of these that applies, with the number of the
atom, or the message `notWellFormed` above. -/

def unsoundElement (atom : Nat) : List Char :=
  "the Mol is not sound: atom ".toList ++ natText atom
    ++ " is no atom of B, C, N, O, P, S, F, Cl, Br or I".toList
def unsoundIsotope (atom : Nat) : List Char :=
  "the Mol is not sound: atom ".toList ++ natText atom ++ " has a mass number".toList
def unsoundCharge (atom : Nat) : List Char :=
  "the Mol is not sound: atom ".toList ++ natText atom ++ " has a charge".toList
def unsoundAromatic (atom : Nat) : List Char :=
  "the Mol is not sound: atom ".toList ++ natText atom ++ " has exactly one aromatic bond".toList
def unsoundValence (atom : Nat) : List Char :=
  "the Mol is not sound: the bonds and hydrogens of atom ".toList ++ natText atom
    ++ " add up to no usual valence of its element".toList

/-- The rule `perfluoro` refuses a `Mol`: its largest perfluorinated group has
`size` carbon atoms, and `limit` or more are refused. -/
def fluoroGroup (size limit : Nat) : List Char :=
  "the Mol has a perfluorinated group of size ".toList ++ natText size
    ++ ", and size ".toList ++ natText limit ++ " or more is refused".toList

/-! The program (SPEC.md, section 8). -/

def usage : List Char :=
  "expected a SMILES text, or one of the words rewrite, plain and canonical followed by a SMILES text, ".toList
    ++ "or the words filter perfluoro followed by a number from 1 on and a SMILES text".toList

end Message

end VeriMol
