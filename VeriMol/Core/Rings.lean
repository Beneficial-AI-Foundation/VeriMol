/-!
# The table of open ring numbers

A ring number is open from the atom where it is written first to the atom
where it is written again. The reader and the writer both keep a table of the
ring numbers that are open: a list of pairs, each a number and what is known
about it.

The table is used in three ways while a text is read or written: a number is
looked up (`ringAt`), a number is added by putting a pair in front of the
list, and a number is taken out (`withoutRing`). At the end of a text the
reader also looks through the table, for the number that was opened first
and never closed (`firstOpened` in `VeriMol/Core/Read.lean`).
-/

namespace VeriMol

/-- What the table holds for this ring number, if the number is open. -/
def ringAt {α : Type} (number : Nat) : List (Nat × α) → Option α
  | [] => none
  | (other, value) :: rest => if other = number then some value else ringAt number rest

/-- The table without this ring number. -/
def withoutRing {α : Type} (number : Nat) (rings : List (Nat × α)) : List (Nat × α) :=
  rings.filter fun entry => entry.1 != number

end VeriMol
