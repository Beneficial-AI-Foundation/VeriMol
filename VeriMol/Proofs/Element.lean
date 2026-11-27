import VeriMol.Core

/-!
# The element symbols

Theorem 6 of CLAIMS.md says that reading the symbol of an element gives the
element back (`Element.ofSymbol?_symbol`). The rest of the file says what the
characters of a symbol are, as far as the proofs of theorems 2 and 7 need it
(`VeriMol/Proofs/Printed.lean`, `VeriMol/Proofs/Spell.lean`): a symbol begins
with a capital letter, a lowercase symbol does not, and a second character is
a small letter.
-/

namespace VeriMol

/-- Theorem 6 of CLAIMS.md: for every element, reading its symbol gives that
element back.

So no two elements have the same symbol (`Element.symbol_injective` in
`VeriMol/Proofs/Printed.lean`), and the list `Element.all` leaves no element
out. -/
theorem Element.ofSymbol?_symbol (e : Element) :
    Element.ofSymbol? e.symbol = some e := by
  cases e <;> rfl

/-- The other direction: a text is read as an element only if it is the symbol
of that element. -/
theorem Element.symbol_of_ofSymbol? {symbol : List Char} {e : Element}
    (h : Element.ofSymbol? symbol = some e) : e.symbol = symbol := by
  simpa using List.find?_some h

/-! ## The characters of the element symbols -/

/-- What the proofs need to know about the first character of a symbol. -/
def firstOK (c : Char) : Bool :=
  !isWhite c && c != '*' && !c.isDigit && c != ']'

/-- A usual symbol: a capital letter, or a capital and a small letter. -/
def upperSymbolOK : List Char → Bool
  | [c] => c.isUpper && firstOK c
  | [c, d] => c.isUpper && firstOK c && d.isLower && d != ']'
  | _ => false

/-- A lowercase symbol, as far as the proofs need it: its first character is
no capital letter, and a second one is a small letter. -/
def lowerSymbolOK : List Char → Bool
  | [c] => !c.isUpper && firstOK c
  | [c, d] => !c.isUpper && firstOK c && d.isLower && d != ']'
  | _ => false

theorem Element.symbol_ok (e : Element) : upperSymbolOK e.symbol = true := by
  cases e <;> rfl

theorem Element.lowercaseSymbol?_ok {e : Element} {s : List Char}
    (h : e.lowercaseSymbol? = some s) : lowerSymbolOK s = true := by
  cases e <;> simp [Element.lowercaseSymbol?] at h <;> subst h <;> rfl

theorem Element.ofLowercaseSymbol?_lowercaseSymbol? {e : Element} {s : List Char}
    (h : e.lowercaseSymbol? = some s) : Element.ofLowercaseSymbol? s = some e := by
  cases e <;> simp [Element.lowercaseSymbol?] at h <;> subst h <;> rfl

theorem Element.lowercaseSymbol?_of_ofLowercaseSymbol? {s : List Char} {e : Element}
    (h : Element.ofLowercaseSymbol? s = some e) : e.lowercaseSymbol? = some s := by
  simpa using List.find?_some h

theorem upperSymbolOK_cases {s : List Char} (h : upperSymbolOK s = true) :
    (∃ c, s = [c] ∧ c.isUpper = true ∧ firstOK c = true) ∨
    (∃ c d, s = [c, d] ∧ c.isUpper = true ∧ firstOK c = true ∧ d.isLower = true ∧ d ≠ ']') := by
  match s, h with
  | [c], h =>
    simp only [upperSymbolOK, Bool.and_eq_true] at h
    exact .inl ⟨c, rfl, h.1, h.2⟩
  | [c, d], h =>
    simp only [upperSymbolOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact .inr ⟨c, d, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem lowerSymbolOK_cases {s : List Char} (h : lowerSymbolOK s = true) :
    (∃ c, s = [c] ∧ c.isUpper = false ∧ firstOK c = true) ∨
    (∃ c d, s = [c, d] ∧ c.isUpper = false ∧ firstOK c = true ∧ d.isLower = true ∧ d ≠ ']') := by
  match s, h with
  | [c], h =>
    simp only [lowerSymbolOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact .inl ⟨c, rfl, h.1, h.2⟩
  | [c, d], h =>
    simp only [lowerSymbolOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    exact .inr ⟨c, d, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A text that is read as an element begins with a capital letter. -/
theorem Element.ofSymbol?_head {c : Char} {t : List Char} {e : Element}
    (h : Element.ofSymbol? (c :: t) = some e) : c.isUpper = true := by
  have hs := Element.symbol_of_ofSymbol? h
  rcases upperSymbolOK_cases (Element.symbol_ok e) with ⟨x, hx, hu, -⟩ | ⟨x, y, hx, hu, -⟩ <;>
    (rw [hx] at hs; cases hs; exact hu)

/-- The second letter of a symbol of two letters is a small letter. -/
theorem Element.ofSymbol?_second {c d : Char} {e : Element}
    (h : Element.ofSymbol? [c, d] = some e) : d.isLower = true := by
  have hs := Element.symbol_of_ofSymbol? h
  rcases upperSymbolOK_cases (Element.symbol_ok e) with ⟨x, hx, -⟩ | ⟨x, y, hx, -, -, hl, -⟩
  · rw [hx] at hs; cases hs
  · rw [hx] at hs; cases hs; exact hl

theorem Element.ofLowercaseSymbol?_second {c d : Char} {e : Element}
    (h : Element.ofLowercaseSymbol? [c, d] = some e) : d.isLower = true := by
  have hs := Element.lowercaseSymbol?_of_ofLowercaseSymbol? h
  rcases lowerSymbolOK_cases (Element.lowercaseSymbol?_ok hs) with
    ⟨x, hx, -⟩ | ⟨x, y, hx, -, -, hl, -⟩
  · cases hx
  · cases hx; exact hl

theorem Element.ofSymbol?_eq_none {c : Char} {t : List Char} (h : c.isUpper = false) :
    Element.ofSymbol? (c :: t) = none := by
  cases h' : Element.ofSymbol? (c :: t) with
  | none => rfl
  | some e => rw [Element.ofSymbol?_head h'] at h; cases h

end VeriMol
