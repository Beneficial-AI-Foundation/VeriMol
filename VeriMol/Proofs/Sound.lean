import VeriMol.Core.Sound
import VeriMol.Proofs.Predicates.Sound
import VeriMol.Proofs.Stereo

/-!
# `Sound`: its checker is right, and every numbering gets the same answer

`Mol.Sound`, in `VeriMol/Proofs/Predicates/Sound.lean`, says which `Mol`s are
sound. This file proves theorem 46 of CLAIMS.md, in two statements.

1. The checker of `VeriMol/Core/Sound.lean`, `Mol.isSound`, says yes exactly
   when a `Mol` is sound (`Mol.isSound_iff`). The filter asks it through
   `Mol.soundProblem`, which also gives the reason, and which finds none
   exactly for a sound `Mol` (`Mol.soundProblem_eq_none_iff`). With that Lean
   can work out whether a given `Mol` is sound: it runs the checker (the
   instance of `Decidable`).
2. `Sound` gives the same answer for every numbering of the atoms of a
   molecule (`Mol.Renumbered.sound_iff`).
-/

namespace VeriMol

/-! ## The checker is right -/

/-- A chain of tests, each with its reason, gives no reason exactly when none
of the tests applies. -/
theorem ite_some_eq_none {α : Type} {c : Prop} [Decidable c] {x : α} {rest : Option α} :
    (if c then some x else rest) = none ↔ ¬ c ∧ rest = none := by
  split <;> simp_all

/-- The checker finds no reason against an atom exactly when the atom passes
the five tests of `Mol.SoundAtom`. -/
theorem Mol.atomProblem_eq_none_iff (m : Mol) (i : Nat) (atom : Atom) :
    m.atomProblem i atom = none ↔ m.SoundAtom i atom := by
  have count : (m.bonds.filter fun bond =>
      (bond.a == i || bond.b == i) && bond.order == .aromatic).length = m.aromaticBonds i := by
    unfold Mol.aromaticBonds
    congr 1
  unfold Mol.atomProblem Mol.SoundAtom
  simp only [count, ite_some_eq_none, and_true]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · rw [Bool.not_eq_true', Bool.not_eq_false, List.contains_iff_mem]
    exact Iff.rfl
  · cases atom.isotope <;> simp
  · simp
  · simp
  · rw [Bool.not_eq_true', Bool.not_eq_false, Bool.or_eq_true, Bool.and_eq_true,
      List.contains_iff_mem, List.contains_iff_mem, bne_iff_ne, Nat.pos_iff_ne_zero]

/-- The atoms of a list beside their numbers: the pair of a number and an
atom stands there exactly when the atom stands at that number. -/
theorem mem_zip_range {α : Type} (l : List α) (i : Nat) (x : α) :
    (i, x) ∈ (List.range l.length).zip l ↔ l[i]? = some x := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [List.getElem?_zip_eq_some] at hk
    obtain ⟨h₁, h₂⟩ := hk
    obtain ⟨_, same⟩ := List.getElem?_eq_some_iff.1 h₁
    rw [List.getElem_range] at same
    simp only at same h₂
    subst same
    exact h₂
  · intro h
    refine ⟨i, List.getElem?_zip_eq_some.2 ⟨?_, h⟩⟩
    have := (List.getElem?_eq_some_iff.1 h).1
    simp [this]

/-- The checker finds no reason against a `Mol` exactly when the `Mol` is
sound. -/
theorem Mol.soundProblem_eq_none_iff (m : Mol) : m.soundProblem = none ↔ m.Sound := by
  unfold Mol.soundProblem Mol.Sound
  rw [ite_some_eq_none, Decidable.not_not, List.findSome?_eq_none_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h i atom hi
    exact (Mol.atomProblem_eq_none_iff m i atom).1
      (h (i, atom) ((mem_zip_range m.atoms i atom).2 hi))
  · rintro h ⟨i, atom⟩ hmem
    exact (Mol.atomProblem_eq_none_iff m i atom).2
      (h i atom ((mem_zip_range m.atoms i atom).1 hmem))

/-- Theorem 46 of CLAIMS.md, for the checker. The checker of soundness is
right: for every `Mol`, it says yes exactly when the `Mol` is sound. -/
theorem Mol.isSound_iff (m : Mol) : m.isSound = true ↔ m.Sound := by
  unfold Mol.isSound
  rw [Option.isNone_iff_eq_none, Mol.soundProblem_eq_none_iff]

/-- Whether a `Mol` is sound can be worked out: Lean runs the checker, which
is right by the theorem above. -/
instance (m : Mol) : Decidable m.Sound :=
  decidable_of_iff _ (Mol.isSound_iff m)

/-! ## The same answer for every numbering of the atoms

The five tests ask about an atom, its bonds and the orders of those bonds,
and about nothing that depends on the numbers of the atoms. The proof walks
through the bonds of an atom as a list of pairs: for each bond the atom at
its other end, and its order. -/

/-- The bonds of atom number `c`: for each of them the atom at its other end,
and its order. -/
def Mol.linksOf (m : Mol) (c : Nat) : List (Nat × BondOrder) :=
  m.bonds.filterMap fun bond =>
    if bond.b = c then some (bond.a, bond.order)
    else if bond.a = c then some (bond.b, bond.order) else none

theorem Mol.mem_linksOf {m : Mol} {c x : Nat} {order : BondOrder} :
    (x, order) ∈ m.linksOf c ↔ m.Joined c x order := by
  unfold Mol.linksOf Mol.Joined
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨bond, hbond, hx⟩
    obtain ⟨a, b, o⟩ := bond
    simp only at hx
    split at hx
    · rename_i hb
      cases hx
      subst hb
      exact Or.inr hbond
    · split at hx
      · rename_i ha
        cases hx
        subst ha
        exact Or.inl hbond
      · cases hx
  · rintro (h | h)
    · refine ⟨_, h, ?_⟩
      by_cases hx : x = c
      · simp [hx]
      · simp [hx]
    · exact ⟨_, h, by simp⟩

/-- The atoms at the other ends of the bonds of an atom are its neighbours. -/
theorem Mol.linksOf_map_fst (m : Mol) (c : Nat) : (m.linksOf c).map (·.1) = m.neighbours c := by
  unfold Mol.linksOf Mol.neighbours
  rw [List.map_filterMap]
  congr 1
  funext bond
  by_cases hb : bond.b = c
  · simp [hb]
  · by_cases ha : bond.a = c
    · simp [ha, hb]
    · simp [ha, hb]

/-- In a well formed `Mol` no atom has two bonds to the same atom. -/
theorem Mol.linksOf_nodup {m : Mol} (w : m.GraphWellFormed) (c : Nat) : (m.linksOf c).Nodup := by
  have := Mol.neighbours_nodup w c
  rw [← Mol.linksOf_map_fst] at this
  exact List.Pairwise.of_map (·.1) (fun a b hab e => hab (by rw [e])) this

/-- The orders of the bonds of an atom, in the order in which `bondSum` and
`Mol.aromaticBonds` go through them. -/
theorem Mol.linksOf_map_snd (m : Mol) (c : Nat) :
    (m.linksOf c).map (·.2)
      = (m.bonds.filter fun bond => bond.a = c ∨ bond.b = c).map (·.order) := by
  unfold Mol.linksOf
  induction m.bonds with
  | nil => rfl
  | cons bond rest ih =>
    by_cases hb : bond.b = c
    · simp [hb, ih]
    · by_cases ha : bond.a = c
      · simp [ha, hb, ih]
      · simp [ha, hb, ih]

theorem Mol.bondSum_eq (m : Mol) (c : Nat) :
    bondSum m.bonds c = (((m.linksOf c).map (·.2)).map BondOrder.weight).sum := by
  rw [Mol.linksOf_map_snd, List.map_map]
  rfl

theorem Mol.aromaticBonds_eq (m : Mol) (c : Nat) :
    m.aromaticBonds c = ((m.linksOf c).map (·.2)).countP (· == .aromatic) := by
  rw [Mol.linksOf_map_snd, List.countP_map, List.countP_eq_length_filter, List.filter_filter]
  unfold Mol.aromaticBonds
  congr 1
  apply List.filter_congr
  intro bond _
  simp only [Bool.decide_and, Bool.decide_or]
  rw [Bool.and_comm]
  rfl

/-- The bonds of an atom are its bonds at the new numbers, in another order. -/
theorem Mol.SameGraphBy.linksOf_perm {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : c < m₁.atoms.length) :
    (m₂.linksOf (f c)).Perm ((m₁.linksOf c).map fun link => (f link.1, link.2)) := by
  have inside : ∀ link ∈ m₁.linksOf c, link.1 < m₁.atoms.length := by
    rintro ⟨x, order⟩ hx
    exact (Mol.Joined.lt w₁ (Mol.mem_linksOf.1 hx)).2
  have nodup : ((m₁.linksOf c).map fun link => (f link.1, link.2)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine (Mol.linksOf_nodup w₁ c).imp_of_mem ?_
    rintro ⟨x, o⟩ ⟨y, o'⟩ hx hy hxy e
    simp only [Prod.mk.injEq] at e
    have := h.injective (inside _ hx) (inside _ hy) e.1
    simp only at this
    exact hxy (by rw [this, e.2])
  rw [List.perm_ext_iff_of_nodup (Mol.linksOf_nodup w₂ _) nodup]
  rintro ⟨y, order⟩
  constructor
  · intro hy
    have hj := Mol.mem_linksOf.1 hy
    obtain ⟨back, same⟩ := h.back y (Mol.Joined.lt w₂ hj).2
    rw [← same] at hj
    exact List.mem_map.2 ⟨(g y, order),
      Mol.mem_linksOf.2 ((h.bonds c (g y) order hc back).2 hj), by rw [same]⟩
  · intro hy
    obtain ⟨⟨x, o⟩, hx, e⟩ := List.mem_map.1 hy
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact Mol.mem_linksOf.2 ((h.bonds c x o hc (inside _ hx)).1 (Mol.mem_linksOf.1 hx))

/-- The orders of the bonds of an atom are the same at its new number, in
another order. -/
theorem Mol.SameGraphBy.orders_perm {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : c < m₁.atoms.length) :
    ((m₂.linksOf (f c)).map (·.2)).Perm ((m₁.linksOf c).map (·.2)) := by
  have := (h.linksOf_perm w₁ w₂ hc).map (·.2)
  rwa [List.map_map] at this

/-- An atom that passes the five tests passes them at its new number. -/
theorem Mol.SameGraphBy.soundAtom {f g : Nat → Nat} {m₁ m₂ : Mol}
    (h : Mol.SameGraphBy f g m₁ m₂) (w₁ : m₁.GraphWellFormed) (w₂ : m₂.GraphWellFormed)
    {c : Nat} (hc : c < m₁.atoms.length) (atom : Atom) (sound : m₁.SoundAtom c atom) :
    m₂.SoundAtom (f c) atom := by
  have orders := h.orders_perm w₁ w₂ hc
  have sum : bondSum m₂.bonds (f c) = bondSum m₁.bonds c := by
    rw [Mol.bondSum_eq, Mol.bondSum_eq]
    exact (orders.map _).sum_nat
  have aromatic : m₂.aromaticBonds (f c) = m₁.aromaticBonds c := by
    rw [Mol.aromaticBonds_eq, Mol.aromaticBonds_eq]
    exact orders.countP_eq _
  unfold Mol.SoundAtom
  rw [sum, aromatic]
  exact sound

/-- A sound `Mol` is sound with its atoms numbered differently, if it is well
formed under the new numbers. -/
theorem Mol.SameGraphBy.sound {f g : Nat → Nat} {m₁ m₂ : Mol} (h : Mol.SameGraphBy f g m₁ m₂)
    (w₂ : m₂.WellFormed) (sound : m₁.Sound) : m₂.Sound := by
  refine ⟨w₂, fun j atom hj => ?_⟩
  obtain ⟨back, same⟩ := h.back j (List.getElem?_eq_some_iff.1 hj).1
  have := h.soundAtom sound.1.graph w₂.graph back atom
    (sound.2 (g j) atom (by rw [← h.atoms (g j) back, same]; exact hj))
  rwa [same] at this

/-- Theorem 46 of CLAIMS.md, second statement. `Sound` gives the same answer
for every numbering of the atoms of a molecule: of two well formed `Mol`s
that are the same molecule, numbered differently, both are sound or neither
is. -/
theorem Mol.Renumbered.sound_iff {m₁ m₂ : Mol} (w₁ : m₁.WellFormed) (w₂ : m₂.WellFormed)
    (h : m₁.Renumbered m₂) : m₁.Sound ↔ m₂.Sound := by
  obtain ⟨f, g, by'⟩ := h
  exact ⟨by'.sameGraph.sound w₂, by'.sameGraph.symm.sound w₁⟩

end VeriMol
