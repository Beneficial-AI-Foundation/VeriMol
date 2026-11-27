import VeriMol.Core.Problem
import VeriMol.Core.Token

/-!
# Cutting a text into tokens (SPEC.md, sections 4 and 6)

`cut` goes through the text once, from left to right. It returns the tokens it
found and, if it met a character or a pair of square brackets that it cannot
read, that problem. Whether a token is allowed at its place is not decided
here: that is the business of the reader.

How it works: `firstToken` reads the one token a text begins with and says how
many characters it takes. `cutFrom` uses it again and again, skipping the
characters of each token it has read.
-/

namespace VeriMol

/-- The value of a digit character: 7 for `'7'`. -/
def digitValue (c : Char) : Nat :=
  c.toNat - 48

/-! ## What stands inside square brackets -/

/-- The digits at the start are the isotope. Returns the isotope, if there is
one, and the text behind it. -/
def readIsotope (text : List Char) : Option Nat × List Char :=
  let digits := text.takeWhile Char.isDigit
  (if digits.isEmpty then none else some (Nat.ofDigitChars 10 digits 0),
    text.dropWhile Char.isDigit)

/-- The first `length` characters, taken as the symbol of an element: as a
lowercase symbol if `aromatic`. -/
def symbolOfLength (length : Nat) (aromatic : Bool) (text : List Char) :
    Option (Element × Bool × List Char) :=
  (if aromatic then Element.ofLowercaseSymbol? (text.take length)
    else Element.ofSymbol? (text.take length)).map
    fun element => (element, aromatic, text.drop length)

/-- The symbol at the start: its element, whether it is a lowercase symbol,
and the text behind it. A symbol of two letters wins over one of one letter,
and the usual symbols are tried before the lowercase ones. -/
def readSymbol (text : List Char) : Option (Element × Bool × List Char) :=
  (symbolOfLength 2 false text).or ((symbolOfLength 1 false text).or
    ((symbolOfLength 2 true text).or (symbolOfLength 1 true text)))

/-- The stereo mark at the start, if there is one, and the text behind it. -/
def readMark : List Char → Option Orientation × List Char
  | '@' :: '@' :: rest => (some .clockwise, rest)
  | '@' :: rest => (some .anticlockwise, rest)
  | text => (none, text)

/-- The hydrogen count at the start, and the text behind it: `H` is 1, `H3` is
3, and no `H` is 0. `none` if a hydrogen atom has a hydrogen count. -/
def readHydrogens (element : Element) : List Char → Option (Nat × List Char)
  | 'H' :: rest =>
    if element = .H then none
    else
      match rest with
      | digit :: rest' =>
        if digit.isDigit then some (digitValue digit, rest') else some (1, rest)
      | [] => some (1, [])
  | text => some (0, text)

/-- One or two digits at the start, as a number, and the text behind them.
`none` if the text does not start with a digit. -/
def readUpToTwoDigits : List Char → Option Nat × List Char
  | first :: second :: rest =>
    if first.isDigit ∧ second.isDigit then
      (some (10 * digitValue first + digitValue second), rest)
    else if first.isDigit then (some (digitValue first), second :: rest)
    else (none, first :: second :: rest)
  | [only] => if only.isDigit then (some (digitValue only), []) else (none, [only])
  | [] => (none, [])

/-- The charge at the start, and the text behind it: `+` is 1, `++` is 2, `+2`
is 2, and the same with `-`. No sign is charge 0. -/
def readCharge : List Char → Int × List Char
  | '+' :: '+' :: rest => (2, rest)
  | '-' :: '-' :: rest => (-2, rest)
  | '+' :: rest => ((readUpToTwoDigits rest).1.getD 1, (readUpToTwoDigits rest).2)
  | '-' :: rest => (-((readUpToTwoDigits rest).1.getD 1 : Nat), (readUpToTwoDigits rest).2)
  | text => (0, text)

/-- Whether the text begins with the letters of a stereo class that is written
behind `@`: `TH`, `AL`, `SP`, `TB` or `OH` (SPEC.md, section 12.4). -/
def startsWithStereoClass : List Char → Bool
  | 'T' :: 'H' :: _ => true
  | 'A' :: 'L' :: _ => true
  | 'S' :: 'P' :: _ => true
  | 'T' :: 'B' :: _ => true
  | 'O' :: 'H' :: _ => true
  | _ => false

/-- What follows the symbol and the stereo mark: the hydrogen count, the
charge, and then nothing more. If there is a problem, it returns what is left
of the text at that place, and the message. -/
def readCountAndCharge (element : Element) (text : List Char) :
    Except (List Char × List Char) (Nat × Int) :=
  match readHydrogens element text with
  | none => .error (text, Message.hydrogenCount)
  | some (hydrogens, afterHydrogens) =>
    match readCharge afterHydrogens with
    | (charge, []) => .ok (hydrogens, charge)
    | (_, c :: rest) => .error (c :: rest, Message.doesNotFit c)

/-- An atom in square brackets. `inside` is what stands between `[` and `]`,
and `start` is the position of the `[`. Returns the atom and the position
that goes with it (see `Placed`).

The inside is gone through from left to right: isotope, symbol, stereo mark,
hydrogen count, charge. -/
def bracketAtom (start : Nat) (inside : List Char) : Except Problem (WrittenAtom × Nat) :=
  -- The position of the first character of `rest`, which is an end piece of
  -- `inside`. For the empty end piece it is the position of the `]`.
  let positionOf (rest : List Char) : Nat := start + 1 + (inside.length - rest.length)
  let (isotope, afterIsotope) := readIsotope inside
  match afterIsotope with
  | [] => .error ⟨positionOf [], Message.elementExpected⟩
  | c :: _ =>
    if isWhite c ∨ c = '*' then .error ⟨positionOf afterIsotope, Message.doesNotFit c⟩
    else
      match readSymbol afterIsotope with
      | none => .error ⟨positionOf afterIsotope, Message.elementExpected⟩
      | some (element, aromatic, afterSymbol) =>
        let (mark, afterMark) := readMark afterSymbol
        -- `@` with the letters of a stereo class behind it is not read.
        if mark = some .anticlockwise ∧ startsWithStereoClass afterMark then
          .error ⟨positionOf afterSymbol, Message.stereoClass⟩
        else
          match readCountAndCharge element afterMark with
          | .error (rest, message) => .error ⟨positionOf rest, message⟩
          | .ok (hydrogens, charge) =>
            .ok ({ element, aromatic, isotope, charge, hydrogens := some hydrogens, mark },
              if mark.isSome then positionOf afterSymbol else start)

/-! ## One token -/

/-- The characters before the first `]`. `none` if there is no `]`. -/
def beforeClose : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c = ']' then some [] else (beforeClose rest).map (c :: ·)

/-- The token that consists of this one character, if there is one. -/
def oneCharacter : Char → Option Token
  | 'B' => some (.atom (.bare .B false))
  | 'C' => some (.atom (.bare .C false))
  | 'N' => some (.atom (.bare .N false))
  | 'O' => some (.atom (.bare .O false))
  | 'P' => some (.atom (.bare .P false))
  | 'S' => some (.atom (.bare .S false))
  | 'F' => some (.atom (.bare .F false))
  | 'I' => some (.atom (.bare .I false))
  | 'b' => some (.atom (.bare .B true))
  | 'c' => some (.atom (.bare .C true))
  | 'n' => some (.atom (.bare .N true))
  | 'o' => some (.atom (.bare .O true))
  | 'p' => some (.atom (.bare .P true))
  | 's' => some (.atom (.bare .S true))
  | '-' => some (.bond (.order .single))
  | '=' => some (.bond (.order .double))
  | '#' => some (.bond (.order .triple))
  | '$' => some (.bond (.order .quadruple))
  | ':' => some (.bond (.order .aromatic))
  | '/' => some (.bond .up)
  | '\\' => some (.bond .down)
  | '(' => some .branchOpen
  | ')' => some .branchClose
  | '.' => some .dot
  | c => if c.isDigit then some (.ring (digitValue c)) else none

/-- The token that a text begins with, and how many characters it takes. The
text is `c` followed by `rest`, and `c` stands at position `start`. -/
def firstToken (start : Nat) (c : Char) (rest : List Char) : Except Problem (Placed × Nat) :=
  if c = '[' then
    match beforeClose rest with
    | none => .error ⟨start, Message.bracketNeverClosed⟩
    | some inside =>
      match bracketAtom start inside with
      | .error problem => .error problem
      | .ok (atom, position) => .ok (⟨.atom atom, position⟩, inside.length + 2)
  else if c = 'C' ∧ rest.head? = some 'l' then .ok (⟨.atom (.bare .Cl false), start⟩, 2)
  else if c = 'B' ∧ rest.head? = some 'r' then .ok (⟨.atom (.bare .Br false), start⟩, 2)
  else if c = '%' then
    match rest with
    | first :: second :: _ =>
      if first.isDigit ∧ second.isDigit then
        .ok (⟨.ring (10 * digitValue first + digitValue second), start⟩, 3)
      else .error ⟨start, Message.percent⟩
    | _ => .error ⟨start, Message.percent⟩
  else
    match oneCharacter c with
    | some token => .ok (⟨token, start⟩, 1)
    | none => .error ⟨start, Message.doesNotFit c⟩

/-! ## The whole text -/

/-- A text cut into tokens. If the text could not be cut to its end, `problem`
says why, and `tokens` holds the tokens before that place. -/
structure Cut where
  tokens : List Placed
  problem : Option Problem

/-- Cuts the text that begins at position `position`. The first `skip`
characters belong to a token that is already read, and are passed over. -/
def cutFrom (position skip : Nat) : List Char → Cut
  | [] => ⟨[], none⟩
  | c :: rest =>
    match skip with
    | skip + 1 => cutFrom (position + 1) skip rest
    | 0 =>
      match firstToken position c rest with
      | .error problem => ⟨[], some problem⟩
      | .ok (token, length) =>
        let behind := cutFrom (position + 1) (length - 1) rest
        ⟨token :: behind.tokens, behind.problem⟩

/-- Cuts a text into tokens. -/
def cut (text : List Char) : Cut :=
  cutFrom 0 0 text

end VeriMol
