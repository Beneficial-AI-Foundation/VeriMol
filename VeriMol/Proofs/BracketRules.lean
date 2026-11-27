import VeriMol.Proofs.Brackets

/-!
# Closing round brackets without a list changes no text

SPEC.md, section 9.2, gives the rules for round brackets with a list of the
round brackets that are open. By the rules the writer closes round brackets in
three places: on the way back to a parent, the innermost ones until the one of
that parent is closed; all of them in front of an atom without a parent; and
all of them at the end of the text.

The writer of `VeriMol/Core/Write.lean` keeps no such list. It writes one `)`
when the text comes back to a parent, and none in the two other places.

This file holds a writer that closes round brackets as the rules say, with the
list and the three places (`BracketRules.tokens`). And it proves that the two
writers give the same tokens for every `Mol`, with or without stereo facts,
whatever its numbering, well formed or not (`tokens_eq_rules`). It is stated
for both spellings; the plain spelling writes no round bracket, so there it
says little.

The two writers differ in the closing of round brackets and in nothing else.
The parents, the ring numbers, the atoms, the bond symbols and the stereo
marks are the functions of Core in both, and both open a round bracket by
the same test. So the theorem says that keeping no list changes no text. It
does not say that the writer finds the parents, opens its round brackets or
writes the atoms as SPEC.md asks: there both writers would be wrong together.
And it has no line in the ledger: the writer of the rules is a definition of
this file, and no fingerprint would hold it in place.

The proof is short, because `VeriMol/Proofs/Brackets.lean` already knows which
round brackets are open at any point of the text (`openOn`): when the text
comes back to a parent, the innermost of them is the one of that parent
(`openOn_parent`), and in front of an atom without a parent there is none
(`openOn_none`).
-/

namespace VeriMol

namespace BracketRules

/-- Closes round brackets, the innermost first, until the one that was opened
at `atom` is closed. The list holds, for every round bracket that is open,
the atom it was opened at, the innermost first. Returns the `)` and the round
brackets that stay open. Where the writer calls it, the round bracket of
`atom` is open (`openOn_parent`). -/
def closeBackTo (atom : Nat) : List Nat → List Token × List Nat
  | [] => ([], [])
  | opened :: rest =>
    if opened = atom then ([.branchClose], rest)
    else
      let (tokens, left) := closeBackTo atom rest
      (.branchClose :: tokens, left)

/-- What stands in front of atom number `number`, and the round brackets that
are open after it. `later` holds the parents of the atoms that follow.

* An atom without a parent: every open round bracket is closed, and a dot is
  written unless it is the first atom.
* An atom with a parent: if the parent is not the atom just before it, the
  round brackets that were opened since the parent are closed. (If it is the
  atom just before, none was opened since.) A `(` is written if a later atom
  has the same parent. Then comes the symbol of the bond to the parent, as
  `VeriMol.beforeAtom` writes it. -/
def beforeAtom (spelling : Spelling) (mol : Mol) (marks : Marks) (number : Nat)
    (parent : Option Nat) (later : List (Option Nat)) (openedAt : List Nat) :
    List Token × List Nat :=
  match parent with
  | none =>
    (List.replicate openedAt.length Token.branchClose ++ (if number = 0 then [] else [.dot]), [])
  | some parent =>
    let (closing, stillOpen) :=
      if parent + 1 = number then ([], openedAt) else closeBackTo parent openedAt
    let (opening, nowOpen) :=
      if later.contains (some parent) then ([Token.branchOpen], parent :: stillOpen)
      else ([], stillOpen)
    let symbol :=
      match mol.bonds.find? fun bond => bond.a == parent && bond.b == number with
      | some bond => markedSymbol marks (spelling.symbol mol) bond
      | none => []
    (closing ++ opening ++ symbol, nowOpen)

/-- The tokens for the atoms from number `number` on, with the list `openedAt`
of the open round brackets. At the end of the text all of them are closed.
Everything but the round brackets is as in `VeriMol.tokensFrom`. -/
def tokensFrom (spelling : Spelling) (mol : Mol) (marks : Marks) (parents : List (Option Nat)) :
    Nat → List (Atom × Option Nat) → List (Nat × Bond) → List Nat →
      Except (List Char) (List Token)
  | _, [], _, openedAt => .ok (List.replicate openedAt.length .branchClose)
  | number, (atom, parent) :: rest, rings, openedAt =>
    let (before, nowOpen) := beforeAtom spelling mol marks number parent (rest.map (·.2)) openedAt
    let closes := mol.bonds.filter fun bond => bond.b == number && ringBond parents bond
    let opens := mol.bonds.filter fun bond => bond.a == number && ringBond parents bond
    let token : Except (List Char) Token :=
      match mol.orientationAt number with
      | none => .ok (spelling.atom mol.bonds number atom)
      | some stored =>
        match centreRefusal mol number parent.isSome (closes.length + opens.length) with
        | some message => .error message
        | none => .ok (orientedAtom mol number atom stored (placeKey parents number))
    match token with
    | .error message => .error message
    | .ok token =>
      match closeRings rings closes with
      | none => .error Message.tooManyRingNumbers
      | some (closing, afterClosing) =>
        match openRings (markedSymbol marks (spelling.symbol mol)) afterClosing opens with
        | none => .error Message.tooManyRingNumbers
        | some (opening, afterOpening) =>
          match tokensFrom spelling mol marks parents (number + 1) rest afterOpening nowOpen with
          | .error message => .error message
          | .ok behind => .ok (before ++ token :: closing ++ opening ++ behind)

/-- The tokens of a spelling, with its round brackets closed as the rules of
SPEC.md, section 9.2, say: with the list, and in three places. Everything
else is the writer of `VeriMol/Core/Write.lean`. -/
def tokens (spelling : Spelling) (mol : Mol) (marks : Marks) : Except (List Char) (List Token) :=
  tokensFrom spelling mol marks (spelling.parents mol) 0
    (mol.atoms.zip (spelling.parents mol)) [] []

end BracketRules

/-- What stands in front of one atom: the writer of the rules, given the list
of the round brackets that are open there, writes what the writer of
`VeriMol/Core/Write.lean` writes, and its list afterwards is again the list of
the round brackets that are open. -/
theorem beforeAtom_eq_rules (spelling : Spelling) (mol : Mol) (marks : Marks) (bonds : List Bond)
    {i : Nat} {path : List Nat} {parent : Option Nat} {laterP : List (Option Nat)}
    (h : PathAt i path)
    (hparent : parent = path.find? (fun earlier => bonded bonds earlier i))
    (hlater : ∀ q, some q ∈ laterP → q ∈ nextPath i path parent ∨ i + 1 ≤ q) :
    BracketRules.beforeAtom spelling mol marks i parent laterP (openOn path (parent :: laterP))
      = (beforeAtom spelling mol marks i parent laterP,
          openOn (nextPath i path parent) laterP) := by
  cases parent with
  | none =>
    rw [openOn_none h hlater]
    simp [BracketRules.beforeAtom, beforeAtom, nextPath, openOn]
  | some p =>
    have hp : p ∈ path := List.mem_of_find?_eq_some hparent.symm
    obtain ⟨Y, hY1, hY2, hY3⟩ := openOn_parent laterP h hp hlater
    by_cases hnext : p + 1 = i
    · rw [hY1 hnext, hY3]
      by_cases hc : some p ∈ laterP <;>
        simp [BracketRules.beforeAtom, beforeAtom, hnext, hc] <;> rfl
    · rw [hY2 hnext, hY3]
      by_cases hc : some p ∈ laterP <;>
        simp [BracketRules.beforeAtom, beforeAtom, hnext, hc, BracketRules.closeBackTo] <;> rfl

/-- All atoms from number `i` on: the two writers give the same tokens. `bonds`
are the bonds along which the text runs. -/
theorem tokensFrom_eq_rules (spelling : Spelling) (mol : Mol) (marks : Marks) (bonds : List Bond)
    (P : List (Option Nat)) :
    ∀ (rest : List (Atom × Option Nat)) (i : Nat) (path : List Nat) (W : List (Nat × Bond)),
      PathAt i path →
      rest.map (·.2) = parentsFrom bonds i path (rest.map (·.1)) →
      BracketRules.tokensFrom spelling mol marks P i rest W (openOn path (rest.map (·.2)))
        = tokensFrom spelling mol marks P i rest W := by
  intro rest
  induction rest with
  | nil =>
    intro i path W _ _
    simp [BracketRules.tokensFrom, tokensFrom, openOn]
  | cons head rest ih =>
    obtain ⟨atom, parent⟩ := head
    intro i path W hpath hpar
    simp only [List.map_cons] at hpar
    obtain ⟨hparent, hlater⟩ := parentsFrom_cons_eq hpar.symm
    have hlaterMem : ∀ q, some q ∈ rest.map (·.2) → q ∈ nextPath i path parent ∨ i + 1 ≤ q := by
      intro q hq
      rw [hlater] at hq
      exact mem_parentsFrom bonds _ (i + 1) _ q hq
    have hb := beforeAtom_eq_rules spelling mol marks bonds hpath hparent hlaterMem
    have hih : ∀ W, BracketRules.tokensFrom spelling mol marks P (i + 1) rest W
          (openOn (nextPath i path parent) (rest.map (·.2)))
        = tokensFrom spelling mol marks P (i + 1) rest W :=
      fun W => ih _ _ W (hpath.next parent) hlater
    simp only [List.map_cons, BracketRules.tokensFrom, tokensFrom, hb, hih]
    rfl

/-- The writer of `VeriMol/Core/Write.lean` gives the same tokens as
`BracketRules.tokens`: in both spellings, for every `Mol`, whatever its
numbering, well formed or not, and whichever marks its bonds carry. The head
of this file says what that means and what it does not. -/
theorem tokens_eq_rules (spelling : Spelling) (mol : Mol) (marks : Marks) :
    spelling.tokens mol marks = BracketRules.tokens spelling mol marks := by
  have hlenP : (spelling.parents mol).length = mol.atoms.length := parentsFrom_length _ _ _ _
  have h1 : (mol.atoms.zip (spelling.parents mol)).map (·.1) = mol.atoms := by
    simp [List.map_fst_zip, hlenP]
  have h2 : (mol.atoms.zip (spelling.parents mol)).map (·.2) = spelling.parents mol := by
    simp [List.map_snd_zip, hlenP]
  have h := tokensFrom_eq_rules spelling mol marks (mol.bonds.filter spelling.runsAlong)
    (spelling.parents mol) (mol.atoms.zip (spelling.parents mol)) 0 [] []
    ⟨List.nodup_nil, by simp, rfl⟩ (by rw [h1, h2]; rfl)
  have h0 : openOn [] ((mol.atoms.zip (spelling.parents mol)).map (·.2)) = [] := rfl
  rw [h0] at h
  exact h.symm

end VeriMol
