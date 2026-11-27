import VeriMol.Core
import VeriMol.Proofs.Element
import VeriMol.Proofs.Text

/-!
# Spelling tokens and cutting the text again gives the tokens back

This file proves theorem 7 of CLAIMS.md. It is the last theorem of the file,
`cut_spell`. Everything before it is a step on the way:

1. Each part of an atom in square brackets is read back as it was written:
   the isotope, the symbol, the stereo mark, the hydrogen count, the charge.
2. So a whole atom in square brackets is read back (`bracketAtom_spell`).
3. So is every other token, and each token is the first token of its own
   spelling, whatever follows it, as long as that is no `l` and no `r`: they
   would turn `C` into `Cl` and `B` into `Br` (`firstToken_spell`). No
   spelling begins with one of the two (`Token.spell_head`).
4. So a whole list of tokens is read back, token by token (`cutFrom_spell`).
-/

namespace VeriMol

/-! ## Reading the parts of an atom in square brackets -/

theorem takeWhile_append_stop {p : Char → Bool} {xs rest : List Char} (hx : ∀ c ∈ xs, p c = true)
    (hr : ∀ c, rest.head? = some c → p c = false) :
    (xs ++ rest).takeWhile p = xs ∧ (xs ++ rest).dropWhile p = rest := by
  rw [List.takeWhile_append_of_pos hx, List.dropWhile_append_of_pos hx]
  cases rest with
  | nil => simp
  | cons c r => simp [hr c rfl]

theorem readIsotope_none {rest : List Char} (hr : ∀ c, rest.head? = some c → c.isDigit = false) :
    readIsotope rest = (none, rest) := by
  have h := takeWhile_append_stop (xs := []) (p := Char.isDigit) (by simp) hr
  simp only [List.nil_append] at h
  simp [readIsotope, h.1, h.2]

theorem readIsotope_natText (n : Nat) {rest : List Char}
    (hr : ∀ c, rest.head? = some c → c.isDigit = false) :
    readIsotope (natText n ++ rest) = (some n, rest) := by
  have h := takeWhile_append_stop (xs := natText n) (p := Char.isDigit)
    (fun c hc => isDigit_of_mem_natText hc) hr
  unfold readIsotope
  simp only [h.1, h.2]
  simp [natText, Nat.toDigits_ne_nil]

theorem readUpToTwoDigits_natText {n : Nat} (h : n < 100) :
    readUpToTwoDigits (natText n) = (some n, []) := by
  by_cases h₁ : n < 10
  · simp [natText_of_lt_ten h₁, readUpToTwoDigits, isDigit_digitChar h₁, digitValue_digitChar h₁]
  · have ha : n / 10 < 10 := by omega
    have hb : n % 10 < 10 := by omega
    simp [natText_of_two_digits (by omega) h, readUpToTwoDigits, isDigit_digitChar ha,
      isDigit_digitChar hb, digitValue_digitChar ha, digitValue_digitChar hb]
    omega

theorem readCharge_plus {rest : List Char} (h : rest.head? ≠ some '+') :
    readCharge ('+' :: rest)
      = ((((readUpToTwoDigits rest).1.getD 1 : Nat) : Int), (readUpToTwoDigits rest).2) := by
  cases rest with
  | nil => rfl
  | cons c r =>
    have hc : c ≠ '+' := fun hc => h (by simp [hc])
    unfold readCharge
    split <;> simp_all

theorem readCharge_minus {rest : List Char} (h : rest.head? ≠ some '-') :
    readCharge ('-' :: rest)
      = (-(((readUpToTwoDigits rest).1.getD 1 : Nat) : Int), (readUpToTwoDigits rest).2) := by
  cases rest with
  | nil => rfl
  | cons c r =>
    have hc : c ≠ '-' := fun hc => h (by simp [hc])
    unfold readCharge
    split <;> simp_all

theorem head?_natText_isDigit {n : Nat} {c : Char} (h : (natText n).head? = some c) :
    c.isDigit = true :=
  isDigit_of_mem_natText (n := n) (List.mem_of_mem_head? h)

theorem readCharge_spellCharge {charge : Int} (h : charge.natAbs ≤ 99) :
    readCharge (spellCharge charge) = (charge, []) := by
  by_cases h0 : charge = 0
  · subst h0; rfl
  by_cases h1 : charge = 1
  · subst h1; rfl
  by_cases h2 : charge = -1
  · subst h2; rfl
  have hn : charge.natAbs < 100 := by omega
  have h1' : charge.natAbs ≠ 1 := by omega
  by_cases hneg : charge < 0
  · have hd : (natText charge.natAbs).head? ≠ some '-' := fun hc =>
      absurd (head?_natText_isDigit hc) (by decide)
    have hs : spellCharge charge = '-' :: natText charge.natAbs := by
      simp [spellCharge, h0, hneg, h1']
    rw [hs, readCharge_minus hd, readUpToTwoDigits_natText hn]
    simp
    omega
  · have hd : (natText charge.natAbs).head? ≠ some '+' := fun hc =>
      absurd (head?_natText_isDigit hc) (by decide)
    have hs : spellCharge charge = '+' :: natText charge.natAbs := by
      simp [spellCharge, h0, hneg, h1']
    rw [hs, readCharge_plus hd, readUpToTwoDigits_natText hn]
    simp
    omega

theorem readMark_none {rest : List Char} (hr : rest.head? ≠ some '@') :
    readMark rest = (none, rest) := by
  unfold readMark
  split <;> simp_all

theorem readMark_spell (mark : Orientation) {rest : List Char} (hr : rest.head? ≠ some '@') :
    readMark (mark.spell ++ rest) = (some mark, rest) := by
  cases mark with
  | clockwise => rfl
  | anticlockwise =>
    cases rest with
    | nil => rfl
    | cons c r =>
      have hc : c ≠ '@' := fun hc => hr (by simp [hc])
      simp only [Orientation.spell, List.cons_append, List.nil_append]
      unfold readMark
      split <;> simp_all

theorem readHydrogens_spell {element : Element} {hydrogens : Nat} {rest : List Char}
    (h₁ : hydrogens ≤ 9) (h₂ : element = .H → hydrogens = 0)
    (hr : ∀ c, rest.head? = some c → c ≠ 'H' ∧ c.isDigit = false) :
    readHydrogens element (spellHydrogens hydrogens ++ rest) = some (hydrogens, rest) := by
  unfold spellHydrogens
  by_cases h0 : hydrogens = 0
  · subst h0
    simp only [↓reduceIte, List.nil_append]
    unfold readHydrogens
    split
    · exact absurd rfl (hr 'H' rfl).1
    · rfl
  · have hne : element ≠ .H := fun he => h0 (h₂ he)
    by_cases h1 : hydrogens = 1
    · subst h1
      cases rest with
      | nil => simp [readHydrogens, hne]
      | cons c r => simp [readHydrogens, hne, (hr c rfl).2]
    · have hlt : hydrogens < 10 := by omega
      simp [h0, h1, natText_of_lt_ten hlt, readHydrogens, hne, isDigit_digitChar hlt,
        digitValue_digitChar hlt]

theorem head?_spellCharge {charge : Int} {c : Char} (h : (spellCharge charge).head? = some c) :
    c = '+' ∨ c = '-' := by
  unfold spellCharge at h
  by_cases h0 : charge = 0
  · simp [h0] at h
  · by_cases hneg : charge < 0 <;> simp [h0, hneg] at h <;> simp [← h]

theorem readCountAndCharge_spell {element : Element} {hydrogens : Nat} {charge : Int}
    (h₁ : hydrogens ≤ 9) (h₂ : element = .H → hydrogens = 0) (h₃ : charge.natAbs ≤ 99) :
    readCountAndCharge element (spellHydrogens hydrogens ++ spellCharge charge)
      = .ok (hydrogens, charge) := by
  have hr : ∀ c, (spellCharge charge).head? = some c → c ≠ 'H' ∧ c.isDigit = false := by
    intro c hc
    rcases head?_spellCharge hc with rfl | rfl <;> decide
  simp [readCountAndCharge, readHydrogens_spell h₁ h₂ hr, readCharge_spellCharge h₃]

/-! ## Reading a symbol -/

theorem readSymbol_symbol (e : Element) {rest : List Char}
    (hr : ∀ c, rest.head? = some c → c.isLower = false) :
    readSymbol (e.symbol ++ rest) = some (e, false, rest) := by
  have hfull := Element.ofSymbol?_symbol e
  rcases upperSymbolOK_cases (Element.symbol_ok e) with ⟨c, hs, -⟩ | ⟨c, d, hs, -⟩
  · rw [hs] at hfull ⊢
    cases rest with
    | nil => simp [readSymbol, symbolOfLength, hfull]
    | cons r rest' =>
      have hnone : Element.ofSymbol? [c, r] = none := by
        cases h : Element.ofSymbol? [c, r] with
        | none => rfl
        | some e' =>
          have hl := hr r rfl
          rw [Element.ofSymbol?_second h] at hl
          cases hl
      simp [readSymbol, symbolOfLength, hnone, hfull]
  · rw [hs] at hfull ⊢
    simp [readSymbol, symbolOfLength, hfull]

theorem readSymbol_lowercase {e : Element} {s : List Char} (hs : e.lowercaseSymbol? = some s)
    {rest : List Char} (hr : ∀ c, rest.head? = some c → c.isLower = false) :
    readSymbol (s ++ rest) = some (e, true, rest) := by
  have hfull := Element.ofLowercaseSymbol?_lowercaseSymbol? hs
  rcases lowerSymbolOK_cases (Element.lowercaseSymbol?_ok hs) with
    ⟨c, rfl, hu, -⟩ | ⟨c, d, rfl, hu, -⟩
  · cases rest with
    | nil => simp [readSymbol, symbolOfLength, hfull, Element.ofSymbol?_eq_none hu]
    | cons r rest' =>
      have hnone : Element.ofLowercaseSymbol? [c, r] = none := by
        cases h : Element.ofLowercaseSymbol? [c, r] with
        | none => rfl
        | some e' =>
          have hl := hr r rfl
          rw [Element.ofLowercaseSymbol?_second h] at hl
          cases hl
      simp [readSymbol, symbolOfLength, hnone, hfull, Element.ofSymbol?_eq_none hu]
  · simp [readSymbol, symbolOfLength, hfull, Element.ofSymbol?_eq_none hu]

/-! ## An atom in square brackets -/

theorem head?_hydrogens_charge {hydrogens : Nat} {charge : Int} {c : Char}
    (h : (spellHydrogens hydrogens ++ spellCharge charge).head? = some c) :
    c = 'H' ∨ c = '+' ∨ c = '-' := by
  unfold spellHydrogens at h
  by_cases h0 : hydrogens = 0
  · simp only [h0, ↓reduceIte, List.nil_append] at h
    exact .inr (head?_spellCharge h)
  · by_cases h1 : hydrogens = 1 <;> simp [h0, h1] at h <;> exact .inl h.symm

/-- What stands behind a stereo mark in a spelled atom, the hydrogens and the
charge, never begins with the letters of a stereo class. -/
theorem startsWithStereoClass_hydrogens_charge (hydrogens : Nat) (charge : Int) :
    startsWithStereoClass (spellHydrogens hydrogens ++ spellCharge charge) = false := by
  cases htext : spellHydrogens hydrogens ++ spellCharge charge with
  | nil => rfl
  | cons c rest =>
    have hc := head?_hydrogens_charge (hydrogens := hydrogens) (charge := charge) (c := c)
      (by rw [htext]; rfl)
    rcases hc with rfl | rfl | rfl <;> simp [startsWithStereoClass]

theorem head?_mark_hydrogens_charge {mark : Option Orientation} {hydrogens : Nat} {charge : Int}
    {c : Char}
    (h : (spellMark mark ++ (spellHydrogens hydrogens ++ spellCharge charge)).head? = some c) :
    c = '@' ∨ c = 'H' ∨ c = '+' ∨ c = '-' := by
  cases mark with
  | none => exact .inr (head?_hydrogens_charge h)
  | some mark => cases mark <;> simp [spellMark, Orientation.spell] at h <;> exact .inl h.symm

theorem readMark_spellMark (mark : Option Orientation) {rest : List Char}
    (hr : rest.head? ≠ some '@') : readMark (spellMark mark ++ rest) = (mark, rest) := by
  cases mark with
  | none => exact readMark_none hr
  | some mark => exact readMark_spell mark hr

theorem readIsotope_spellIsotope (isotope : Option Nat) {rest : List Char}
    (hr : ∀ c, rest.head? = some c → c.isDigit = false) :
    readIsotope (spellIsotope isotope ++ rest) = (isotope, rest) := by
  cases isotope with
  | none => exact readIsotope_none hr
  | some isotope => exact readIsotope_natText isotope hr

theorem bracketAtom_spell {atom : WrittenAtom} {hydrogens : Nat} {symbol : List Char}
    (start : Nat) (hh : atom.hydrogens = some hydrogens)
    (h₁ : hydrogens ≤ 9) (h₂ : atom.element = .H → hydrogens = 0) (h₃ : atom.charge.natAbs ≤ 99)
    (hs : (if atom.aromatic then atom.element.lowercaseSymbol? else some atom.element.symbol)
      = some symbol) :
    ∃ position, bracketAtom start (spellIsotope atom.isotope ++ (symbol ++ (spellMark atom.mark ++
        (spellHydrogens hydrogens ++ spellCharge atom.charge)))) = .ok (atom, position) := by
  obtain ⟨element, aromatic, isotope, charge, hyd, mark⟩ := atom
  dsimp only at hh h₂ h₃ hs ⊢
  subst hh
  have hcount := readCountAndCharge_spell (element := element) h₁ h₂ h₃
  have h3 : (spellHydrogens hydrogens ++ spellCharge charge).head? ≠ some '@' := by
    intro hc
    rcases head?_hydrogens_charge hc with h | h | h <;> cases h
  have hmark := readMark_spellMark mark h3
  have h2 : ∀ c, (spellMark mark ++ (spellHydrogens hydrogens ++ spellCharge charge)).head?
      = some c → c.isLower = false := by
    intro c hc
    rcases head?_mark_hydrogens_charge hc with rfl | rfl | rfl | rfl <;> decide
  have hsymbol : readSymbol (symbol ++ (spellMark mark ++
        (spellHydrogens hydrogens ++ spellCharge charge)))
      = some (element, aromatic, spellMark mark ++ (spellHydrogens hydrogens ++ spellCharge charge))
      ∧ ∃ c s', symbol = c :: s' ∧ firstOK c = true := by
    cases aromatic with
    | true =>
      simp only [↓reduceIte] at hs
      refine ⟨readSymbol_lowercase hs h2, ?_⟩
      rcases lowerSymbolOK_cases (Element.lowercaseSymbol?_ok hs) with
        ⟨c, rfl, -, hf⟩ | ⟨c, d, rfl, -, hf, -⟩ <;> exact ⟨_, _, rfl, hf⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      refine ⟨readSymbol_symbol _ h2, ?_⟩
      rcases upperSymbolOK_cases (Element.symbol_ok element) with
        ⟨c, hc, -, hf⟩ | ⟨c, d, hc, -, hf, -⟩ <;> exact ⟨_, _, hc, hf⟩
  obtain ⟨hread, c, s', rfl, hf⟩ := hsymbol
  simp only [firstOK, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hf
  have hiso := readIsotope_spellIsotope isotope
    (rest := (c :: s') ++ (spellMark mark ++ (spellHydrogens hydrogens ++ spellCharge charge)))
    (by intro x hx; simp at hx; subst hx; exact hf.1.2)
  rw [List.cons_append] at hread hiso
  unfold bracketAtom
  simp only [hiso, List.cons_append, hf.1.1.1, hf.1.1.2, Bool.false_eq_true, or_self, ↓reduceIte,
    hread, hmark]
  cases mark <;>
    simp only [hcount, startsWithStereoClass_hydrogens_charge, Bool.false_eq_true, and_false,
      ↓reduceIte] <;> exact ⟨_, rfl⟩

/-! ## One token -/

theorem beforeClose_append {inside rest : List Char} (h : ∀ c ∈ inside, c ≠ ']') :
    beforeClose (inside ++ ']' :: rest) = some inside := by
  induction inside with
  | nil => simp [beforeClose]
  | cons c inside ih =>
    have hc : c ≠ ']' := h c (by simp)
    simp [beforeClose, hc, ih (fun x hx => h x (by simp [hx]))]

theorem ne_close_of_isDigit {c : Char} (h : c.isDigit = true) : c ≠ ']' := by
  intro hc
  subst hc
  exact absurd h (by decide)

theorem ne_close_of_mem_natText {n : Nat} {c : Char} (h : c ∈ natText n) : c ≠ ']' :=
  ne_close_of_isDigit (isDigit_of_mem_natText h)

/-- No `]` stands between the square brackets of a spelled atom. -/
theorem ne_close_of_mem_inside {element : Element} {aromatic : Bool} {isotope : Option Nat}
    {mark : Option Orientation} {hydrogens : Nat} {charge : Int} {symbol : List Char}
    (hs : (if aromatic then element.lowercaseSymbol? else some element.symbol) = some symbol) :
    ∀ c ∈ spellIsotope isotope ++ (symbol ++ (spellMark mark ++
      (spellHydrogens hydrogens ++ spellCharge charge))), c ≠ ']' := by
  have hsymbol : ∀ c ∈ symbol, c ≠ ']' := by
    cases aromatic with
    | true =>
      simp only [↓reduceIte] at hs
      rcases lowerSymbolOK_cases (Element.lowercaseSymbol?_ok hs) with
        ⟨x, rfl, -, hf⟩ | ⟨x, y, rfl, -, hf, -, hy⟩ <;>
        simp only [firstOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf <;> simp [hf.2, *]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      subst hs
      rcases upperSymbolOK_cases (Element.symbol_ok element) with
        ⟨x, hx, -, hf⟩ | ⟨x, y, hx, -, hf, -, hy⟩ <;>
        simp only [firstOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf <;> simp [hf.2, *]
  have hisotope : ∀ c ∈ spellIsotope isotope, c ≠ ']' := by
    cases isotope with
    | none => simp [spellIsotope]
    | some isotope => exact fun c hc => ne_close_of_mem_natText hc
  have hmark : ∀ c ∈ spellMark mark, c ≠ ']' := by
    cases mark with
    | none => simp [spellMark]
    | some mark => cases mark <;> simp [spellMark, Orientation.spell]
  have hhydrogens : ∀ c ∈ spellHydrogens hydrogens, c ≠ ']' := by
    intro c hc
    unfold spellHydrogens at hc
    by_cases h0 : hydrogens = 0
    · simp [h0] at hc
    · by_cases h1 : hydrogens = 1
      · simp [h1] at hc; subst hc; decide
      · simp only [h0, h1, ↓reduceIte, List.mem_cons] at hc
        rcases hc with rfl | hc
        · decide
        · exact ne_close_of_mem_natText hc
  have hcharge : ∀ c ∈ spellCharge charge, c ≠ ']' := by
    intro c hc
    unfold spellCharge at hc
    by_cases h0 : charge = 0
    · simp [h0] at hc
    · simp only [h0, ↓reduceIte, List.mem_cons] at hc
      rcases hc with rfl | hc
      · split <;> decide
      · split at hc
        · simp at hc
        · exact ne_close_of_mem_natText hc
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc | hc | hc | hc
  · exact hisotope c hc
  · exact hsymbol c hc
  · exact hmark c hc
  · exact hhydrogens c hc
  · exact hcharge c hc

theorem firstToken_bare {element : Element} {aromatic : Bool} {c : Char} {s rest : List Char}
    (start : Nat) (hs : bareSymbol? element aromatic = some (c :: s))
    (hr : rest.head? ≠ some 'l' ∧ rest.head? ≠ some 'r') :
    firstToken start c (s ++ rest)
      = .ok (⟨.atom (.bare element aromatic), start⟩, s.length + 1) := by
  cases aromatic <;> cases element <;>
    simp [bareSymbol?, Element.bare, Element.lowercaseSymbol?, Element.symbol] at hs <;>
    (obtain ⟨rfl, rfl⟩ := hs; simp [firstToken, oneCharacter, hr.1, hr.2])

theorem oneCharacter_digitChar : ∀ n, n < 10 →
    oneCharacter (Nat.digitChar n) = some (.ring n) ∧ Nat.digitChar n ≠ '[' ∧
      Nat.digitChar n ≠ 'C' ∧ Nat.digitChar n ≠ 'B' ∧ Nat.digitChar n ≠ '%' := by
  decide

theorem firstToken_spell {token : Token} {c : Char} {s rest : List Char} (start : Nat)
    (hs : token.spell = some (c :: s))
    (hr : rest.head? ≠ some 'l' ∧ rest.head? ≠ some 'r') :
    ∃ position, firstToken start c (s ++ rest) = .ok (⟨token, position⟩, s.length + 1) := by
  cases token with
  | atom written =>
    obtain ⟨element, aromatic, isotope, charge, hydrogens, mark⟩ := written
    simp only [Token.spell, WrittenAtom.spell] at hs
    cases hydrogens with
    | none =>
      simp only at hs
      split at hs
      · rename_i hcond
        obtain ⟨rfl, rfl, rfl⟩ := hcond
        exact ⟨start, firstToken_bare start hs hr⟩
      · cases hs
    | some hydrogens =>
      simp only at hs
      split at hs
      · cases hs
      · rename_i hcond
        obtain ⟨symbol, hsymbol, hspelled⟩ := Option.map_eq_some_iff.mp hs
        obtain ⟨rfl, rfl⟩ := List.cons.inj hspelled
        have hinside := ne_close_of_mem_inside (isotope := isotope) (mark := mark)
          (hydrogens := hydrogens) (charge := charge) hsymbol
        obtain ⟨position, hbracket⟩ := bracketAtom_spell
          (atom := ⟨element, aromatic, isotope, charge, some hydrogens, mark⟩) start rfl
          (by omega)
          (by
            intro he
            simp only at he
            by_cases h0 : hydrogens = 0
            · exact h0
            · exact absurd (Or.inr (Or.inr ⟨he, by omega⟩)) hcond)
          (by simp only; omega) hsymbol
        refine ⟨position, ?_⟩
        have hjoin : spellIsotope isotope ++ symbol ++ spellMark mark ++ spellHydrogens hydrogens
              ++ spellCharge charge ++ [']'] ++ rest
            = (spellIsotope isotope ++ (symbol ++ (spellMark mark ++
              (spellHydrogens hydrogens ++ spellCharge charge)))) ++ ']' :: rest := by
          simp [List.append_assoc]
        rw [hjoin]
        simp only at hbracket
        simp only [firstToken, ↓reduceIte, beforeClose_append hinside, hbracket]
        simp [List.length_append]
        omega
  | bond symbol =>
    cases symbol with
    | order kind =>
      cases kind <;> simp [Token.spell, BondSymbol.character, BondOrder.symbol] at hs <;>
        (obtain ⟨rfl, rfl⟩ := hs; exact ⟨start, by simp [firstToken, oneCharacter]⟩)
    | up =>
      simp [Token.spell, BondSymbol.character] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨start, by simp [firstToken, oneCharacter]⟩
    | down =>
      simp [Token.spell, BondSymbol.character] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨start, by simp [firstToken, oneCharacter]⟩
  | ring number =>
    simp only [Token.spell] at hs
    by_cases h10 : number < 10
    · simp only [h10, ↓reduceIte, natText_of_lt_ten h10, Option.some.injEq, List.cons.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hone, h1, h2, h3, h4⟩ := oneCharacter_digitChar number h10
      exact ⟨start, by simp [firstToken, h1, h2, h3, h4, hone]⟩
    · by_cases h100 : number < 100
      · have ha : number / 10 < 10 := by omega
        have hb : number % 10 < 10 := by omega
        simp only [h10, h100, ↓reduceIte, natText_of_two_digits (by omega) h100, Option.some.injEq,
          List.cons.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨start, ?_⟩
        simp [firstToken, isDigit_digitChar ha, isDigit_digitChar hb, digitValue_digitChar ha,
          digitValue_digitChar hb]
        omega
      · simp [h10, h100] at hs
  | branchOpen =>
    simp [Token.spell] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨start, by simp [firstToken, oneCharacter]⟩
  | branchClose =>
    simp [Token.spell] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨start, by simp [firstToken, oneCharacter]⟩
  | dot =>
    simp [Token.spell] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨start, by simp [firstToken, oneCharacter]⟩

/-! ## A whole text -/

/-- The spelling of a token is never empty, and it never begins with `l` or
`r`. So a token cannot turn the `C` or `B` before it into `Cl` or `Br`. -/
theorem Token.spell_head {token : Token} {s : List Char} (h : token.spell = some s) :
    ∃ c s', s = c :: s' ∧ c ≠ 'l' ∧ c ≠ 'r' := by
  cases s with
  | nil =>
    exfalso
    cases token with
    | atom written =>
      obtain ⟨element, aromatic, isotope, charge, hydrogens, mark⟩ := written
      simp only [Token.spell, WrittenAtom.spell] at h
      cases hydrogens with
      | none =>
        simp only at h
        split at h
        · cases aromatic <;> cases element <;>
            simp [bareSymbol?, Element.bare, Element.lowercaseSymbol?, Element.symbol] at h
        · cases h
      | some hydrogens =>
        simp only at h
        split at h
        · cases h
        · obtain ⟨symbol, -, hspelled⟩ := Option.map_eq_some_iff.mp h
          cases hspelled
    | bond symbol => simp [Token.spell] at h
    | ring number =>
      simp only [Token.spell] at h
      split at h
      · exact Nat.toDigits_ne_nil (Option.some.inj h)
      · split at h <;> simp at h
    | branchOpen => simp [Token.spell] at h
    | branchClose => simp [Token.spell] at h
    | dot => simp [Token.spell] at h
  | cons c s' =>
    refine ⟨c, s', rfl, ?_, ?_⟩ <;>
    · intro hc
      subst hc
      obtain ⟨position, hfirst⟩ := firstToken_spell (rest := []) 0 h (by simp)
      simp [firstToken, oneCharacter] at hfirst

theorem spell_head {tokens : List Token} {text : List Char} (h : spell tokens = some text) :
    text.head? ≠ some 'l' ∧ text.head? ≠ some 'r' := by
  cases tokens with
  | nil =>
    simp only [spell, Option.some.injEq] at h
    subst h
    simp
  | cons token tokens =>
    simp only [spell] at h
    cases hfirst : token.spell with
    | none => simp [hfirst] at h
    | some first =>
      cases hbehind : spell tokens with
      | none => simp [hfirst, hbehind] at h
      | some behind =>
        simp only [hfirst, hbehind, Option.some.injEq] at h
        subst h
        obtain ⟨c, s', rfl, hl, hr⟩ := Token.spell_head hfirst
        simp [hl, hr]

theorem cutFrom_skip (position : Nat) (skipped rest : List Char) :
    cutFrom position skipped.length (skipped ++ rest)
      = cutFrom (position + skipped.length) 0 rest := by
  induction skipped generalizing position with
  | nil => rfl
  | cons c skipped ih =>
    simp only [List.length_cons, List.cons_append, cutFrom]
    rw [ih]
    congr 1
    omega

theorem cutFrom_spell (tokens : List Token) : ∀ (text : List Char) (position : Nat),
    spell tokens = some text →
      (cutFrom position 0 text).problem = none
        ∧ (cutFrom position 0 text).tokens.map Placed.token = tokens := by
  induction tokens with
  | nil =>
    intro text position h
    simp only [spell, Option.some.injEq] at h
    subst h
    simp [cutFrom]
  | cons token tokens ih =>
    intro text position h
    simp only [spell] at h
    cases hfirst : token.spell with
    | none => simp [hfirst] at h
    | some first =>
      cases hbehind : spell tokens with
      | none => simp [hfirst, hbehind] at h
      | some behind =>
        simp only [hfirst, hbehind, Option.some.injEq] at h
        subst h
        obtain ⟨c, s, rfl, -, -⟩ := Token.spell_head hfirst
        obtain ⟨place, hplace⟩ := firstToken_spell position hfirst (spell_head hbehind)
        have hrest := ih behind (position + 1 + s.length) hbehind
        simp only [List.cons_append, cutFrom, hplace, Nat.add_sub_cancel, cutFrom_skip,
          List.map_cons]
        exact ⟨hrest.1, by rw [hrest.2]⟩

/-- Theorem 7 of CLAIMS.md: for every list of tokens that can be spelled,
spelling it and cutting the text into tokens again gives the same list. -/
theorem cut_spell (tokens : List Token) (text : List Char) (h : spell tokens = some text) :
    (cut text).problem = none ∧ (cut text).tokens.map Placed.token = tokens :=
  cutFrom_spell tokens text 0 h

end VeriMol
