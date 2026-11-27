/-!
# Numbers as text
-/

namespace VeriMol

/-- A natural number in decimal digits: `['1', '3']` for 13. -/
def natText (n : Nat) : List Char :=
  Nat.toDigits 10 n

/-- An integer in decimal digits, with `-` in front if it is negative:
`['-', '1']` for -1. -/
def intText (i : Int) : List Char :=
  if i < 0 then '-' :: natText i.natAbs else natText i.natAbs

end VeriMol
