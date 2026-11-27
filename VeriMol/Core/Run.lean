import VeriMol.Core.Chosen
import VeriMol.Core.Filter
import VeriMol.Core.Printed
import VeriMol.Core.Read
import VeriMol.Core.Write

/-!
# The program as one function (SPEC.md, section 8)
-/

namespace VeriMol

/-! ## The output of a run -/

/-- Everything the program is to do that can be seen from outside. The library
computes this value; `Main` only performs it. What happens when `Main` cannot
write the text is no part of this value (SPEC.md, section 8). -/
structure Output where
  /-- The text written to standard output, the normal channel. -/
  stdout : List Char
  /-- The text written to standard error, the channel for error messages. -/
  stderr : List Char
  /-- The exit code: 0 for success, 1 for an error. -/
  exitCode : Nat

/-- A successful run: print `text`, nothing on standard error, exit code 0. -/
def Output.ok (text : List Char) : Output :=
  { stdout := text, stderr := [], exitCode := 0 }

/-- A run that ends with an error: nothing on standard output, the line
"error: <message>" on standard error, exit code 1. Every error of the
program is built here, so they all have this shape. -/
def Output.error (message : List Char) : Output :=
  { stdout := [], stderr := "error: ".toList ++ message ++ ['\n'], exitCode := 1 }

/-! ## The five commands -/

/-- What the commands `rewrite`, `plain` and `canonical` print for a text: the
text is read, and the `Mol` is written back with `writer`, followed by a line
break. If the text cannot be read, or the `Mol` cannot be written, the error
is printed instead. -/
def rewritten (writer : Mol → Except (List Char) (List Char)) (text : List Char) : Output :=
  match read text with
  | .error problem => .error problem.text
  | .ok mol =>
    match writer mol with
    | .ok written => .ok (written ++ ['\n'])
    | .error message => .error message

/-- What the command `filter` prints for the answer of a filter: the `Mol` that
is handed on, in the printed layout, or the reason of the refusal as the
error. -/
def filtered (answer : Except (List Char) Mol) : Output :=
  match answer with
  | .ok mol => .ok mol.printed
  | .error reason => .error reason

/-- The number behind the words `filter perfluoro`: the size from which a
perfluorinated group is refused. It is written with one or more of the digits
`0` to `9` and nothing else, and it is not 0. Any other text is no such
number. -/
def groupSize? (text : List Char) : Option Nat :=
  if text.isEmpty || !text.all Char.isDigit || Nat.ofDigitChars 10 text 0 == 0 then none
  else some (Nat.ofDigitChars 10 text 0)

/-- The whole program as one pure function: from its command-line arguments
(each one already converted to a `List Char` by `Main`) to everything it
outputs (SPEC.md, section 8).

* One argument is a SMILES text: it is read, and the `Mol` is printed.
* `rewrite` and a text: the text is read and written back in the usual
  spelling, with round brackets.
* `plain` and a text: the same in the plain spelling.
* `canonical` and a text: the text is read, and the chosen form of its `Mol`
  is written in the usual spelling. Two texts that are the same molecule with
  its atoms in another order get the same answer.
* `filter`, `perfluoro`, a number `n` from 1 on and a text: the filter of
  SPEC.md, section 16. The text is read, and the `Mol` is printed if it is
  sound and has no perfluorinated group of `n` or more carbon atoms.
  Otherwise the reason is the error.

Anything else gets the same error every time: no argument, three arguments,
more than four, another word in front of a text, one of the three words
alone, or four arguments that are not the two words, such a number and a
text. -/
def run (args : List (List Char)) : Output :=
  match args with
  | [text] =>
    if text = "rewrite".toList ∨ text = "plain".toList ∨ text = "canonical".toList then
      .error Message.usage
    else
      match read text with
      | .ok mol => .ok mol.printed
      | .error problem => .error problem.text
  | [word, text] =>
    if word = "rewrite".toList then rewritten write text
    else if word = "plain".toList then rewritten writePlain text
    else if word = "canonical".toList then rewritten writeChosen text
    else .error Message.usage
  | [word, rule, size, text] =>
    if word = "filter".toList ∧ rule = "perfluoro".toList then
      match groupSize? size with
      | some n => filtered (filterPerfluoro n text)
      | none => .error Message.usage
    else .error Message.usage
  | _ => .error Message.usage

end VeriMol
