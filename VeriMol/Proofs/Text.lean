import VeriMol.Core

/-!
# Numbers as text: what the proofs need to know

`natText` writes a number in decimal digits. These lemmas say what the digits
are for a number below 10 and for one from 10 to 99, that every character of
such a text is a digit, and that the character for a number below 10 is a
digit whose value is that number. They rest on lemmas about `Nat.toDigits`
and `Nat.digitChar` that come with Lean.
-/

namespace VeriMol

theorem natText_of_lt_ten {n : Nat} (h : n < 10) : natText n = [Nat.digitChar n] :=
  Nat.toDigits_of_lt_base h

theorem natText_of_two_digits {n : Nat} (h₁ : 10 ≤ n) (h₂ : n < 100) :
    natText n = [Nat.digitChar (n / 10), Nat.digitChar (n % 10)] := by
  rw [natText, Nat.toDigits_of_base_le (by decide) h₁, Nat.toDigits_of_lt_base (by omega)]
  rfl

theorem isDigit_digitChar {n : Nat} (h : n < 10) : (Nat.digitChar n).isDigit = true := by
  simp [Nat.isDigit_digitChar, h]

theorem digitValue_digitChar {n : Nat} (h : n < 10) : digitValue (Nat.digitChar n) = n :=
  Nat.toNat_digitChar_sub_48_of_lt_ten h

theorem isDigit_of_mem_natText {n : Nat} {c : Char} (h : c ∈ natText n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

end VeriMol
