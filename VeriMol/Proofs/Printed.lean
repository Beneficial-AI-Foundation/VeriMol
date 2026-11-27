import VeriMol.Proofs.Element
import VeriMol.Proofs.Run
import VeriMol.Proofs.Text

/-!
# The printed layout tells two `Mol`s apart

The second and the third statement of theorem 2 of CLAIMS.md. `Mol.printed`
is the text in which the program prints a `Mol` (SPEC.md, section 7). This
file proves that the text says everything about the `Mol`: two `Mol`s that
are printed alike are equal (`Mol.printed_injective`). That holds for every
`Mol`, well formed or not.

The program answers a text that is read with the printed layout of its `Mol`
(`run_read` in `VeriMol/Proofs/Run.lean`). So two texts that are read get the
same answer from the program exactly when they are read as the same `Mol`
(`run_eq_iff`).

The proof shows that a printed text can be taken apart in one way only, from
left to right. Every step is a lemma of one shape: if a piece with some text
behind it is equal to a piece of the same kind with some text behind it, then
the two pieces are equal, and so are the two texts behind them.

1. A number ends where a character follows that is no digit, and two numbers
   with the same digits are equal (`natText_append_inj`). A charge is a
   number with or without `-` in front (`intText_append_inj`).
2. An element symbol ends where a character follows that is no small letter
   (`Element.symbol_append_inj`). The names of the five kinds of bond begin
   with five different letters (`BondOrder.name_append_inj`), and so do the
   two names of an orientation and the two names of a geometry.
3. In the line of an atom, of a bond or of a stereo fact, every value is
   followed by a fixed text that begins with `,` or with a space. So such a
   line gives its values back, whatever follows it (`Atom.printed_append_inj`
   and the three lemmas like it).
4. In a list, a line is followed by `,` and the next line, or by ` ]`, which
   ends the list, and the empty list is `[]`. So a list gives its items back,
   whatever follows it (`printedList_append_inj`).
5. A `Mol` is printed as its four lists, with fixed texts between them.
-/

namespace VeriMol

/-! ## Numbers -/

/-- Two numbers that are written with the same digits are equal: Lean's own
library reads the digits of a number back as that number. -/
theorem natText_injective {a b : Nat} (h : natText a = natText b) : a = b :=
  calc a = Nat.ofDigitChars 10 (natText a) 0 := Nat.ofDigitChars_ten_toDigits.symm
    _ = Nat.ofDigitChars 10 (natText b) 0 := by rw [h]
    _ = b := Nat.ofDigitChars_ten_toDigits

/-- Digits end where a character follows that is no digit. If some digits, the
character `c` and a rest are the same text as other digits, `c` and another
rest, then the digits are the same, and so are the two rests. -/
theorem digits_append_inj {xs ys r₁ r₂ : List Char} {c : Char}
    (hxs : ∀ x ∈ xs, x.isDigit = true) (hys : ∀ y ∈ ys, y.isDigit = true)
    (hc : c.isDigit = false) (h : xs ++ c :: r₁ = ys ++ c :: r₂) : xs = ys ∧ r₁ = r₂ := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, (List.cons.inj h).2⟩
    | cons y ys =>
      -- `c` would be the digit `y`
      have hy := hys y List.mem_cons_self
      rw [← (List.cons.inj h).1, hc] at hy
      cases hy
  | cons x xs ih =>
    cases ys with
    | nil =>
      -- `c` would be the digit `x`
      have hx := hxs x List.mem_cons_self
      rw [(List.cons.inj h).1, hc] at hx
      cases hx
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := List.cons.inj h
      obtain ⟨hrest, hr⟩ := ih (fun z hz => hxs z (List.mem_cons_of_mem _ hz))
        (fun z hz => hys z (List.mem_cons_of_mem _ hz)) htail
      exact ⟨by rw [hxy, hrest], hr⟩

/-- A number is read off a text in one way only when a character follows it
that is no digit. -/
theorem natText_append_inj {a b : Nat} {c : Char} {r₁ r₂ : List Char} (hc : c.isDigit = false)
    (h : natText a ++ c :: r₁ = natText b ++ c :: r₂) : a = b ∧ r₁ = r₂ := by
  obtain ⟨hab, hr⟩ := digits_append_inj (fun _ => isDigit_of_mem_natText)
    (fun _ => isDigit_of_mem_natText) hc h
  exact ⟨natText_injective hab, hr⟩

/-- No number begins with `-`. -/
theorem natText_append_ne_minus {n : Nat} {r₁ r₂ : List Char} : natText n ++ r₁ ≠ '-' :: r₂ := by
  intro h
  cases hn : natText n with
  | nil => exact Nat.toDigits_ne_nil hn
  | cons d t =>
    have hd : d.isDigit = true := isDigit_of_mem_natText (n := n) (hn ▸ List.mem_cons_self)
    rw [hn] at h
    rw [(List.cons.inj h).1] at hd
    exact absurd hd (by decide)

/-- A whole number, which has `-` in front if it is negative, is read off a
text in one way only when a character follows it that is no digit. -/
theorem intText_append_inj {i j : Int} {c : Char} {r₁ r₂ : List Char} (hc : c.isDigit = false)
    (h : intText i ++ c :: r₁ = intText j ++ c :: r₂) : i = j ∧ r₁ = r₂ := by
  unfold intText at h
  by_cases hi : i < 0 <;> by_cases hj : j < 0 <;> simp only [hi, hj, ↓reduceIte] at h
  -- both negative: behind the two `-` stand two numbers
  · obtain ⟨hn, hr⟩ := natText_append_inj hc (List.cons.inj h).2
    exact ⟨by omega, hr⟩
  -- one of the two negative: a number would begin with `-`
  · exact absurd h.symm natText_append_ne_minus
  · exact absurd h natText_append_ne_minus
  -- neither negative: two numbers
  · obtain ⟨hn, hr⟩ := natText_append_inj hc h
    exact ⟨by omega, hr⟩

/-! ## Symbols and names -/

/-- No two elements have the same symbol. -/
theorem Element.symbol_injective {e₁ e₂ : Element} (h : e₁.symbol = e₂.symbol) : e₁ = e₂ := by
  have h₁ := Element.ofSymbol?_symbol e₁
  rw [h, Element.ofSymbol?_symbol e₂] at h₁
  exact (Option.some.inj h₁).symm

/-- An element symbol is read off a text in one way only when a character
follows it that is no small letter: a symbol is a capital letter, or a capital
letter and a small one. -/
theorem Element.symbol_append_inj {e₁ e₂ : Element} {c : Char} {r₁ r₂ : List Char}
    (hc : c.isLower = false) (h : e₁.symbol ++ c :: r₁ = e₂.symbol ++ c :: r₂) :
    e₁ = e₂ ∧ r₁ = r₂ := by
  rcases upperSymbolOK_cases (Element.symbol_ok e₁) with
    ⟨x, hx, -, -⟩ | ⟨x, x', hx, -, -, hx', -⟩ <;>
  rcases upperSymbolOK_cases (Element.symbol_ok e₂) with
    ⟨y, hy, -, -⟩ | ⟨y, y', hy, -, -, hy', -⟩ <;>
  rw [hx, hy] at h <;>
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
  -- one letter and one letter
  · exact ⟨Element.symbol_injective (by rw [hx, hy, h.1]), h.2⟩
  -- one letter and two letters: the small letter `y'` would be `c`
  · rw [← h.2.1, hc] at hy'
    cases hy'
  -- two letters and one letter: the small letter `x'` would be `c`
  · rw [h.2.1, hc] at hx'
    cases hx'
  -- two letters and two letters
  · exact ⟨Element.symbol_injective (by rw [hx, hy, h.1, h.2.1]), h.2.2⟩

/-- The names of the five kinds of bond begin with five different letters. So
a name is read off a text in one way only, whatever follows it. -/
theorem BondOrder.name_append_inj {o₁ o₂ : BondOrder} {r₁ r₂ : List Char}
    (h : o₁.name ++ r₁ = o₂.name ++ r₂) : o₁ = o₂ ∧ r₁ = r₂ := by
  cases o₁ <;> cases o₂ <;>
    simp only [BondOrder.name, String.reduceToList, List.cons_append, List.nil_append,
      List.cons.injEq, true_and, Char.reduceEq, false_and] at h <;>
    exact ⟨rfl, h⟩

/-! ## One line: an atom, a bond, a stereo fact

Each proof first writes every fixed text of the line as its characters, so
that the two lines can be compared character by character. Then it goes
through the line from left to right, value by value. -/

/-- The isotope of an atom as `Atom.printed` writes it, `none` or `some` and a
number, is read off a text in one way only when a character follows it that is
no digit. The two words begin with different letters. -/
theorem printedIsotope_append_inj {i₁ i₂ : Option Nat} {c : Char} {r₁ r₂ : List Char}
    (hc : c.isDigit = false)
    (h : (match i₁ with
          | none => "none".toList
          | some n => "some ".toList ++ natText n) ++ c :: r₁ =
        (match i₂ with
          | none => "none".toList
          | some n => "some ".toList ++ natText n) ++ c :: r₂) :
    i₁ = i₂ ∧ r₁ = r₂ := by
  cases i₁ <;> cases i₂ <;>
    simp only [String.reduceToList, List.cons_append, List.nil_append, List.cons.injEq,
      true_and, Char.reduceEq, false_and] at h
  -- `none` and `none`
  · exact ⟨rfl, h⟩
  -- a number and a number
  · obtain ⟨hn, hr⟩ := natText_append_inj hc h
    exact ⟨by rw [hn], hr⟩

/-- The line of an atom gives the atom back, whatever follows it. -/
theorem Atom.printed_append_inj {x y : Atom} {r₁ r₂ : List Char}
    (h : x.printed ++ r₁ = y.printed ++ r₂) : x = y ∧ r₁ = r₂ := by
  obtain ⟨element₁, isotope₁, charge₁, hydrogens₁⟩ := x
  obtain ⟨element₂, isotope₂, charge₂, hydrogens₂⟩ := y
  simp only [Atom.printed, List.append_assoc, String.reduceToList, List.cons_append,
    List.nil_append, List.cons.injEq, true_and] at h
  -- the symbol, the isotope, the charge and the hydrogens, each with the fixed text behind it
  obtain ⟨helement, h⟩ := Element.symbol_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hisotope, h⟩ := printedIsotope_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hcharge, h⟩ := intText_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hhydrogens, h⟩ := natText_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  exact ⟨by rw [helement, hisotope, hcharge, hhydrogens], h⟩

/-- The line of a bond gives the bond back, whatever follows it. -/
theorem Bond.printed_append_inj {x y : Bond} {r₁ r₂ : List Char}
    (h : x.printed ++ r₁ = y.printed ++ r₂) : x = y ∧ r₁ = r₂ := by
  obtain ⟨a₁, b₁, order₁⟩ := x
  obtain ⟨a₂, b₂, order₂⟩ := y
  simp only [Bond.printed, List.append_assoc, String.reduceToList, List.cons_append,
    List.nil_append, List.cons.injEq, true_and] at h
  -- the two atom numbers and the kind of bond, each with the fixed text behind it
  obtain ⟨ha, h⟩ := natText_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := natText_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨horder, h⟩ := BondOrder.name_append_inj h
  simp only [List.cons.injEq, true_and] at h
  exact ⟨by rw [ha, hb, horder], h⟩

/-- The line of an atom that has an orientation gives the stereo fact back,
whatever follows it. The two names of an orientation begin with different
letters. -/
theorem AtomOrientation.printed_append_inj {x y : AtomOrientation} {r₁ r₂ : List Char}
    (h : x.printed ++ r₁ = y.printed ++ r₂) : x = y ∧ r₁ = r₂ := by
  obtain ⟨atom₁, orientation₁⟩ := x
  obtain ⟨atom₂, orientation₂⟩ := y
  simp only [AtomOrientation.printed, List.append_assoc, String.reduceToList, List.cons_append,
    List.nil_append, List.cons.injEq, true_and] at h
  -- the atom number with the fixed text behind it, and then the name
  obtain ⟨hatom, h⟩ := natText_append_inj (by decide) h
  cases orientation₁ <;> cases orientation₂ <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and, Char.reduceEq,
      false_and] at h <;>
    exact ⟨by rw [hatom], h⟩

/-- The line of a double bond that has a geometry gives the stereo fact back,
whatever follows it. The two names of a geometry begin with different
letters. -/
theorem BondGeometry.printed_append_inj {x y : BondGeometry} {r₁ r₂ : List Char}
    (h : x.printed ++ r₁ = y.printed ++ r₂) : x = y ∧ r₁ = r₂ := by
  obtain ⟨a₁, b₁, geometry₁⟩ := x
  obtain ⟨a₂, b₂, geometry₂⟩ := y
  simp only [BondGeometry.printed, List.append_assoc, String.reduceToList, List.cons_append,
    List.nil_append, List.cons.injEq, true_and] at h
  -- the two atom numbers, each with the fixed text behind it, and then the name
  obtain ⟨ha, h⟩ := natText_append_inj (by decide) h
  simp only [List.cons.injEq, true_and] at h
  obtain ⟨hb, h⟩ := natText_append_inj (by decide) h
  cases geometry₁ <;> cases geometry₂ <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and, Char.reduceEq,
      false_and] at h <;>
    exact ⟨by rw [ha, hb], h⟩

/-! ## A list

In this part `p` is the way in which one item is written, and `hp` says that
an item is read off a text in one way only, whatever follows it. -/

/-- The lines of a list that is not empty: every item behind four spaces, `,`
and a line break between two items, and ` ]` behind the last one. They give
the items back, whatever follows them: behind an item stands `,` if another
item follows, and the space of ` ]` if none does. -/
theorem printedLines_append_inj {α : Type} {p : α → List Char}
    (hp : ∀ {x y : α} {r₁ r₂ : List Char}, p x ++ r₁ = p y ++ r₂ → x = y ∧ r₁ = r₂)
    {l₁ l₂ : List α} {a b : α} {r₁ r₂ : List Char}
    (h : ",\n".toList.intercalate (((a :: l₁).map p).map ("    ".toList ++ ·))
          ++ (" ]".toList ++ r₁) =
        ",\n".toList.intercalate (((b :: l₂).map p).map ("    ".toList ++ ·))
          ++ (" ]".toList ++ r₂)) :
    a :: l₁ = b :: l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing a b l₂ with
  | nil =>
    cases l₂ with
    | nil =>
      -- one item and one item
      simp only [List.map_cons, List.map_nil, List.intercalate_singleton, List.append_assoc] at h
      obtain ⟨hab, h⟩ := hp (List.append_cancel_left h)
      exact ⟨by rw [hab], List.append_cancel_left h⟩
    | cons b' l₂ =>
      -- one item and more than one: the space of ` ]` would be `,`
      simp only [List.map_cons, List.map_nil, List.intercalate_singleton,
        List.intercalate_cons_cons, List.append_assoc] at h
      have h' := (hp (List.append_cancel_left h)).2
      simp only [String.reduceToList, List.cons_append, List.cons.injEq, Char.reduceEq,
        false_and] at h'
  | cons a' l₁ ih =>
    cases l₂ with
    | nil =>
      -- more than one item and one: `,` would be the space of ` ]`
      simp only [List.map_cons, List.map_nil, List.intercalate_singleton,
        List.intercalate_cons_cons, List.append_assoc] at h
      have h' := (hp (List.append_cancel_left h)).2
      simp only [String.reduceToList, List.cons_append, List.cons.injEq, Char.reduceEq,
        false_and] at h'
    | cons b' l₂ =>
      -- the first items are the same, and so are the lines that follow them
      simp only [List.map_cons, List.intercalate_cons_cons, List.append_assoc] at h
      obtain ⟨hab, h⟩ := hp (List.append_cancel_left h)
      obtain ⟨hl, h⟩ := ih (List.append_cancel_left h)
      exact ⟨by rw [hab, hl], h⟩

/-- A list that is not empty in the layout: `[`, a line break, its lines, and
` ]`. -/
theorem printedList_map_cons {α : Type} (p : α → List Char) (a : α) (l : List α) :
    printedList ((a :: l).map p) =
      "[\n".toList ++ ",\n".toList.intercalate (((a :: l).map p).map ("    ".toList ++ ·))
        ++ " ]".toList :=
  rfl

/-- A list in the layout gives its items back, whatever follows it. The empty
list is `[]`, and a list that is not empty goes on with a line break behind
its `[`. -/
theorem printedList_append_inj {α : Type} {p : α → List Char}
    (hp : ∀ {x y : α} {r₁ r₂ : List Char}, p x ++ r₁ = p y ++ r₂ → x = y ∧ r₁ = r₂)
    {l₁ l₂ : List α} {r₁ r₂ : List Char}
    (h : printedList (l₁.map p) ++ r₁ = printedList (l₂.map p) ++ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => exact ⟨rfl, List.append_cancel_left h⟩
    | cons b l₂ =>
      -- `[]` and `[` with a line break behind it
      rw [printedList_map_cons] at h
      simp only [List.map_nil, printedList, String.reduceToList, List.cons_append,
        List.cons.injEq, true_and, Char.reduceEq, false_and] at h
  | cons a l₁ =>
    cases l₂ with
    | nil =>
      -- `[` with a line break behind it and `[]`
      rw [printedList_map_cons] at h
      simp only [List.map_nil, printedList, String.reduceToList, List.cons_append,
        List.cons.injEq, true_and, Char.reduceEq, false_and] at h
    | cons b l₂ =>
      rw [printedList_map_cons, printedList_map_cons] at h
      simp only [List.append_assoc] at h
      exact printedLines_append_inj hp (List.append_cancel_left h)

/-! ## The whole `Mol` -/

/-- Theorem 2 of CLAIMS.md, its second statement. The printed layout tells two
`Mol`s apart: two `Mol`s that are printed alike are equal, whether they are
well formed or not. -/
theorem Mol.printed_injective (m₁ m₂ : Mol) (h : m₁.printed = m₂.printed) : m₁ = m₂ := by
  obtain ⟨atoms₁, bonds₁, orientations₁, geometries₁⟩ := m₁
  obtain ⟨atoms₂, bonds₂, orientations₂, geometries₂⟩ := m₂
  simp only [Mol.printed, List.append_assoc] at h
  -- list by list: the fixed text in front is taken away, and the list gives its items
  obtain ⟨hatoms, h⟩ :=
    printedList_append_inj Atom.printed_append_inj (List.append_cancel_left h)
  obtain ⟨hbonds, h⟩ :=
    printedList_append_inj Bond.printed_append_inj (List.append_cancel_left h)
  obtain ⟨horientations, h⟩ :=
    printedList_append_inj AtomOrientation.printed_append_inj (List.append_cancel_left h)
  obtain ⟨hgeometries, -⟩ :=
    printedList_append_inj BondGeometry.printed_append_inj (List.append_cancel_left h)
  rw [hatoms, hbonds, horientations, hgeometries]

/-- Theorem 2 of CLAIMS.md, its third statement. Two texts that are read get
the same answer from the program, each given alone, exactly when they are
read as the same `Mol`. -/
theorem run_eq_iff (t₁ t₂ : List Char) (m₁ m₂ : Mol)
    (h₁ : read t₁ = .ok m₁) (h₂ : read t₂ = .ok m₂) :
    run [t₁] = run [t₂] ↔ m₁ = m₂ := by
  -- the answer for a text that is read is the printed layout of its `Mol` (`run_read`)
  rw [run_read t₁ m₁ h₁, run_read t₂ m₂ h₂]
  constructor
  · intro h
    exact Mol.printed_injective m₁ m₂ (congrArg Output.stdout h)
  · intro h
    rw [h]

end VeriMol
