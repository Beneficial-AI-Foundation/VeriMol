import VeriMol.Proofs.Read

/-!
# What the program answers: theorems about `VeriMol.run`

This file proves theorems 1, 3, 4, 5 and 40 of CLAIMS.md, the first
statement of theorem 2, three of the six statements of theorem 39, and two
of the six statements of theorem 49. All of them are about `VeriMol.run`,
the function that is the whole program (`VeriMol/Core/Run.lean`). Together,
theorems 2, 4 and 5 and the statement `run_filter` of theorem 49 say what
`run` answers for every list of arguments, in terms of the reader, of the
three writers and of the filter.

1. Whatever the arguments, `run` succeeds or reports an error in one fixed
   form (`run_succeeds_or_reports_error`, theorem 1).
2. A text that the reader does not read gets the reader's problem as the
   error: behind each of the three command words (`run_word_of_read_error`,
   theorem 5), and alone, unless it is one of those words itself
   (`run_of_read_error`, theorem 4).
3. A text that the reader reads gets, behind a command word, what the writer
   of that command gives for its `Mol` (`run_rewrite`, `run_plain` and
   `run_canonical`, theorem 5).
4. Every other list of arguments gets the error about the arguments
   (`run_usage`, theorem 4), apart from those of the command `filter`: behind
   the words `filter` and `perfluoro` and a number from 1 on, a text gets the
   answer of the filter (`run_filter`, theorem 49). Which texts are such a
   number is said by `groupSize?_eq_some_iff`, also of theorem 49.
5. Given one text alone, `run` prints the printed layout of the `Mol` that
   the reader returns (`run_read`, theorem 2), and it ends with exit code 0
   only for a text that the reader reads (`read_of_run`, theorem 3).
6. Single examples: what `run` prints for `CC(=O)O`, alone and behind
   `rewrite` and `plain` (theorem 39; its other three statements stand in
   `VeriMol/Proofs/Read.lean` and `VeriMol/Proofs/Write.lean`), and for two
   texts that are refused (theorem 40).

What the texts are that `rewrite`, `plain` and `canonical` print is said in
`VeriMol/Proofs/Write.lean`, `VeriMol/Proofs/Refusal.lean`,
`VeriMol/Proofs/RingNumbers.lean` and `VeriMol/Proofs/Chosen.lean`, and that
the printed layout shows the whole `Mol` in `VeriMol/Proofs/Printed.lean`.
-/

namespace VeriMol

/-- Theorem 1 of CLAIMS.md: what rule 4 of the project says about bad input, as
a theorem about `VeriMol.run`. Whatever its arguments are, the function that is
the whole program gives one of two kinds of answer:

* it succeeds: exit code 0 and nothing on standard error; or
* it rejects the input: exit code 1, nothing on standard output, and on
  standard error the text "error: <message>" followed by a line break. -/
theorem run_succeeds_or_reports_error (args : List (List Char)) :
    ((run args).exitCode = 0 ∧ (run args).stderr = []) ∨
    ((run args).exitCode = 1 ∧ (run args).stdout = [] ∧
      ∃ message, (run args).stderr = "error: ".toList ++ message ++ ['\n']) := by
  have ok : ∀ text, (Output.ok text).exitCode = 0 ∧ (Output.ok text).stderr = [] :=
    fun _ => ⟨rfl, rfl⟩
  have error : ∀ message, (Output.error message).exitCode = 1 ∧
      (Output.error message).stdout = [] ∧
      ∃ m, (Output.error message).stderr = "error: ".toList ++ m ++ ['\n'] :=
    fun message => ⟨rfl, rfl, message, rfl⟩
  unfold run rewritten filtered
  repeat' split
  all_goals first | exact .inl (ok _) | exact .inr (error _)

/-- Theorem 5 of CLAIMS.md. A text that is not read gets the same answer behind
each of the three command words: nothing on standard output, the problem that
the reader found as the error on standard error, and exit code 1.

So what a command word does with a text that is not read is one fact for
every text, and the tests need not try it text by text. -/
theorem run_word_of_read_error (word text : List Char) (problem : Problem)
    (hword : word = "rewrite".toList ∨ word = "plain".toList ∨ word = "canonical".toList)
    (h : read text = .error problem) :
    run [word, text]
      = { stdout := [], stderr := "error: ".toList ++ problem.text ++ ['\n'], exitCode := 1 } := by
  rcases hword with rfl | rfl | rfl <;> simp [run, rewritten, h, Output.error]

/-- Theorem 5 of CLAIMS.md, for a text that is read. Behind `rewrite` it gets
what the writer gives for its `Mol` in the spelling with round brackets
(`write`): that text and a line break, or the writer's message as the error
of the program. -/
theorem run_rewrite (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    run ["rewrite".toList, text] =
      match write mol with
      | .ok written => { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }
      | .error message =>
        { stdout := [], stderr := "error: ".toList ++ message ++ ['\n'], exitCode := 1 } := by
  simp only [run, ↓reduceIte, rewritten, h]
  cases write mol <;> rfl

/-- Theorem 5 of CLAIMS.md, for a text that is read. Behind `plain` it gets
what the writer gives for its `Mol` in the plain spelling (`writePlain`). -/
theorem run_plain (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    run ["plain".toList, text] =
      match writePlain mol with
      | .ok written => { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }
      | .error message =>
        { stdout := [], stderr := "error: ".toList ++ message ++ ['\n'], exitCode := 1 } := by
  simp [run, rewritten, h]
  cases writePlain mol <;> rfl

/-- Theorem 5 of CLAIMS.md, for a text that is read. Behind `canonical` it
gets what the writer of the chosen form gives for its `Mol` (`writeChosen`).
Theorem 29 says what that is where a text comes. -/
theorem run_canonical (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    run ["canonical".toList, text] =
      match writeChosen mol with
      | .ok written => { stdout := written ++ ['\n'], stderr := [], exitCode := 0 }
      | .error message =>
        { stdout := [], stderr := "error: ".toList ++ message ++ ['\n'], exitCode := 1 } := by
  simp [run, rewritten, h]
  cases writeChosen mol <;> rfl

/-! ## One text alone that is not read, and the error about the arguments -/

/-- Theorem 4 of CLAIMS.md. A text that the reader does not read, and that is
none of the three command words, gets the reader's problem as the error of the
program when it is given alone: nothing on standard output, and exit code 1.
(One of the three words alone gets the error about the arguments, SPEC.md,
section 8: the program takes it for a command without a text.) -/
theorem run_of_read_error (text : List Char) (problem : Problem)
    (hword : ¬ (text = "rewrite".toList ∨ text = "plain".toList ∨ text = "canonical".toList))
    (h : read text = .error problem) :
    run [text]
      = { stdout := [], stderr := "error: ".toList ++ problem.text ++ ['\n'], exitCode := 1 } := by
  simp only [run, hword, ↓reduceIte, h]
  rfl

/-- Theorem 4 of CLAIMS.md, its second statement. Every other list of
arguments gets the error about the arguments (SPEC.md, section 8): a list that
is neither one text that is no command word, nor a command word and a text,
nor the words `filter` and `perfluoro` with a number from 1 on and a text
(`groupSize?_eq_some_iff` says what such a number is). So no argument, three
arguments, more than four, another word in front of a text, one of the three
words alone, and four arguments that are not the two words, such a number and
a text all get this answer. -/
theorem run_usage (args : List (List Char))
    (hone : ∀ text, args = [text] →
      text = "rewrite".toList ∨ text = "plain".toList ∨ text = "canonical".toList)
    (htwo : ∀ word text, args = [word, text] →
      ¬ (word = "rewrite".toList ∨ word = "plain".toList ∨ word = "canonical".toList))
    (hfour : ∀ size text, args = ["filter".toList, "perfluoro".toList, size, text] →
      groupSize? size = none) :
    run args =
      { stdout := [],
        stderr := ("error: expected a SMILES text, or one of the words rewrite, plain and "
          ++ "canonical followed by a SMILES text, or the words filter perfluoro followed by "
          ++ "a number from 1 on and a SMILES text\n").toList,
        exitCode := 1 } := by
  -- the error about the arguments, as the program prints it. Lean's kernel compares the
  -- two texts character by character.
  have text : "error: ".toList ++ Message.usage ++ ['\n']
      = ("error: expected a SMILES text, or one of the words rewrite, plain and "
          ++ "canonical followed by a SMILES text, or the words filter perfluoro followed by "
          ++ "a number from 1 on and a SMILES text\n").toList := by
    decide +kernel
  rw [← text]
  match args with
  | [] => rfl
  | [text] =>
    have := hone text rfl
    simp only [run, this, ↓reduceIte]
    rfl
  | [word, text] =>
    have := htwo word text rfl
    simp only [not_or] at this
    simp only [run, this, ↓reduceIte]
    rfl
  | [_, _, _] => rfl
  | [word, rule, size, text] =>
    by_cases hwords : word = "filter".toList ∧ rule = "perfluoro".toList
    · obtain ⟨rfl, rfl⟩ := hwords
      have := hfour size text rfl
      simp only [run, and_self, ↓reduceIte, this]
      rfl
    · simp only [run, hwords, ↓reduceIte]
      rfl
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

/-! ## The command `filter` -/

/-- Theorem 49 of CLAIMS.md, for the number. Which texts are a number behind
the words `filter perfluoro`: those made of one or more of the digits `0` to
`9` and nothing else, whose number is not 0. -/
theorem groupSize?_eq_some_iff (text : List Char) (n : Nat) :
    groupSize? text = some n ↔
      text ≠ [] ∧ (∀ c ∈ text, c.isDigit = true) ∧ Nat.ofDigitChars 10 text 0 = n ∧ n ≠ 0 := by
  unfold groupSize?
  split
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨nonempty, digits, rfl, positive⟩
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', beq_iff_eq] at h
    rcases h with (h | h) | h
    · exact nonempty h
    · rw [List.all_eq_true.2 digits] at h
      cases h
    · exact positive h
  · rename_i h
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true', beq_iff_eq, not_or] at h
    obtain ⟨⟨nonempty, digits⟩, positive⟩ := h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨nonempty, List.all_eq_true.1 (by simpa using digits), rfl, positive⟩
    · rintro ⟨_, _, same, _⟩
      exact same

/-- Theorem 49 of CLAIMS.md, for what the program answers. Behind the words
`filter` and `perfluoro` and a number `n` from 1 on, a text gets the answer of
the filter (`filterPerfluoro`, in `VeriMol/Core/Filter.lean`): the printed
layout of the `Mol` that the filter hands on, with exit code 0, or the reason
of the refusal as the error of the program. `VeriMol/Proofs/Filter.lean` says
when the filter hands a `Mol` on. -/
theorem run_filter (size text : List Char) (n : Nat) (hsize : groupSize? size = some n) :
    run ["filter".toList, "perfluoro".toList, size, text] =
      match filterPerfluoro n text with
      | .ok mol => { stdout := mol.printed, stderr := [], exitCode := 0 }
      | .error reason =>
        { stdout := [], stderr := "error: ".toList ++ reason ++ ['\n'], exitCode := 1 } := by
  simp only [run, and_self, ↓reduceIte, hsize, filtered]
  cases filterPerfluoro n text <;> rfl

/-! ## One text alone that is read -/

/-- None of the three command words is read as a `Mol`. -/
theorem words_not_read :
    (∃ p, read "rewrite".toList = .error p) ∧ (∃ p, read "plain".toList = .error p) ∧
    (∃ p, read "canonical".toList = .error p) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Theorem 2 of CLAIMS.md. For every text that the reader reads: the program,
given the text alone, prints the printed layout of the `Mol` that the reader
returns (SPEC.md, section 7) and nothing else, and ends with exit code 0. -/
theorem run_read (text : List Char) (mol : Mol) (h : read text = .ok mol) :
    run [text] = { stdout := mol.printed, stderr := [], exitCode := 0 } := by
  have hword : ¬ (text = "rewrite".toList ∨ text = "plain".toList ∨ text = "canonical".toList) := by
    obtain ⟨⟨p₁, h₁⟩, ⟨p₂, h₂⟩, ⟨p₃, h₃⟩⟩ := words_not_read
    rintro (rfl | rfl | rfl)
    · rw [h₁] at h; cases h
    · rw [h₂] at h; cases h
    · rw [h₃] at h; cases h
  simp only [run, hword, ↓reduceIte, h]
  rfl

/-- Theorem 3 of CLAIMS.md. The other way round: if the program, given one text
alone, ends with exit code 0, then the reader reads that text, and what the
program printed is the printed layout of the `Mol`. -/
theorem read_of_run (text : List Char) (h : (run [text]).exitCode = 0) :
    ∃ mol, read text = .ok mol ∧
      run [text] = { stdout := mol.printed, stderr := [], exitCode := 0 } := by
  by_cases hword : text = "rewrite".toList ∨ text = "plain".toList ∨ text = "canonical".toList
  · rw [show run [text] = Output.error Message.usage by simp only [run, hword, ↓reduceIte]] at h
    simp [Output.error] at h
  · cases hr : read text with
    | ok mol => exact ⟨mol, rfl, run_read text mol hr⟩
    | error problem =>
      rw [show run [text] = Output.error problem.text by
        simp only [run, hword, ↓reduceIte, hr]] at h
      simp [Output.error] at h

/-! ## Single examples of what the program prints

As the single examples of `VeriMol/Proofs/Read.lean`, these say as theorems
what a test says for one text: they name, character for character, what the
program prints. -/

/-- Theorem 39 of CLAIMS.md, for what the program prints. For acetic acid,
`CC(=O)O`, it prints the eleven lines that SPEC.md, section 7, and README.md
show. -/
theorem run_aceticAcid :
    run ["CC(=O)O".toList] =
      { stdout :=
          "{ atoms := [\n".toList
          ++ "    { element := .C, isotope := none, charge := 0, hydrogens := 3 },\n".toList
          ++ "    { element := .C, isotope := none, charge := 0, hydrogens := 0 },\n".toList
          ++ "    { element := .O, isotope := none, charge := 0, hydrogens := 0 },\n".toList
          ++ "    { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],\n".toList
          ++ "  bonds := [\n".toList
          ++ "    { a := 0, b := 1, order := .single },\n".toList
          ++ "    { a := 1, b := 2, order := .double },\n".toList
          ++ "    { a := 1, b := 3, order := .single } ],\n".toList
          ++ "  orientations := [],\n".toList
          ++ "  geometries := [] }\n".toList,
        stderr := [], exitCode := 0 } := by
  -- the text is read as this `Mol` (`read_aceticAcid` in
  -- `VeriMol/Proofs/Read.lean`)
  rw [run_read _ _ read_aceticAcid]
  -- and this is its printed layout, line by line. Here `decide +kernel` stands in
  -- the place of `rfl`: Lean's kernel compares the two texts character by character.
  have hprinted : Mol.printed
      { atoms := [
          { element := .C, isotope := none, charge := 0, hydrogens := 3 },
          { element := .C, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 0 },
          { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],
        bonds := [
          { a := 0, b := 1, order := .single },
          { a := 1, b := 2, order := .double },
          { a := 1, b := 3, order := .single } ] }
      = "{ atoms := [\n".toList
          ++ "    { element := .C, isotope := none, charge := 0, hydrogens := 3 },\n".toList
          ++ "    { element := .C, isotope := none, charge := 0, hydrogens := 0 },\n".toList
          ++ "    { element := .O, isotope := none, charge := 0, hydrogens := 0 },\n".toList
          ++ "    { element := .O, isotope := none, charge := 0, hydrogens := 1 } ],\n".toList
          ++ "  bonds := [\n".toList
          ++ "    { a := 0, b := 1, order := .single },\n".toList
          ++ "    { a := 1, b := 2, order := .double },\n".toList
          ++ "    { a := 1, b := 3, order := .single } ],\n".toList
          ++ "  orientations := [],\n".toList
          ++ "  geometries := [] }\n".toList := by
    decide +kernel
  rw [hprinted]

/-- Theorem 39 of CLAIMS.md, for the command `rewrite`: for `CC(=O)O` it prints
the text again. -/
theorem run_rewrite_aceticAcid :
    run ["rewrite".toList, "CC(=O)O".toList]
      = { stdout := "CC(=O)O\n".toList, stderr := [], exitCode := 0 } := by
  rfl

/-- Theorem 39 of CLAIMS.md, for the command `plain`: for `CC(=O)O` it prints
the plain spelling. -/
theorem run_plain_aceticAcid :
    run ["plain".toList, "CC(=O)O".toList]
      = { stdout := "[CH3]-[C]-1=[O].[OH]1\n".toList, stderr := [], exitCode := 0 } := by
  rfl

/-- Theorem 40 of CLAIMS.md, an example of a refusal. In `C1CC` ring number 1
is opened and never closed. -/
theorem run_refusal_ringNeverClosed :
    run ["C1CC".toList]
      = { stdout := [],
          stderr := "error: position 1: ring 1 is opened but never closed\n".toList,
          exitCode := 1 } := by
  rfl

/-- Theorem 40 of CLAIMS.md, a second example of a refusal. `CC(C))C(=O)[O-`
has two problems, and the one further left is reported (SPEC.md, section 6).
The rule itself, for every text, is tested and not proven. -/
theorem run_refusal_twoProblems :
    run ["CC(C))C(=O)[O-".toList]
      = { stdout := [], stderr := "error: position 5: ')' has no matching '('\n".toList,
          exitCode := 1 } := by
  rfl

end VeriMol
