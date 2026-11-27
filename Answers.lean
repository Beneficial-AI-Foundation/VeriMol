import VeriMol.Core

/-!
# The second program: many answers in one start

`answers` is a tool of the checks. It is not the program, and no user needs
it. It gives what `VeriMol.run` gives for many lists of command-line arguments,
in one start.

Why it exists: `reference/check_app.py` compares the answers of the Lean
program with those of the model for more than a million lists of arguments.
Starting `app` once for each of them takes hours, and most of that time goes
into the starts. This program is started once for up to a thousand lists.

Its own arguments hold the argument lists one after the other. Each list is
given as the number of its arguments, followed by the arguments themselves:

    answers 1 'CCO' 2 rewrite 'OCC' 0

asks for the answers to `app 'CCO'`, to `app rewrite 'OCC'` and to `app`
without an argument. So a text comes into this program as it comes into
`app`: as a command-line argument.

Arguments that are not such lists it refuses. It prints no answer, ends with
exit code 1, and writes one line on standard error:

    error: expected lists of arguments, each as the number of its arguments followed by the arguments

For each list it prints one line with three numbers: the exit code, and how
many bytes the text for standard output and the text for standard error
take. Behind that line it prints these two texts, with nothing between them.
The numbers of bytes are needed because an answer can hold any character,
line breaks included.

It asks `VeriMol.run` for every answer, as `Main.lean` does, and it decides
nothing about a SMILES text. Lake compiles every file of Core once and links
the result into both programs, `app` and `answers`. What `app` does and this
program does not is what `Main.lean` does with an answer: it prints the one
text on standard output and the other on standard error, and it ends with
the exit code. So the checks start `app` itself as well: `lake test` for
every program test, and `check_app.py` for a sample.

The audit does not look at this file: it is no part of Core, Proofs or Main.
A person has to read it, as with `Tests.lean`.
-/

/-- The argument lists that the arguments of this program hold. Each list
stands there as the number of its arguments, followed by the arguments. A
number is written with the digits `0` to `9` and nothing else. `none` if
something else stands where a number must stand, or if fewer arguments follow
a number than it says. -/
def argumentLists : List String → Option (List (List String))
  | [] => some []
  | count :: rest =>
    match (if count.all Char.isDigit then count.toNat? else none) with
    | none => none
    | some n =>
      if n ≤ rest.length then
        (argumentLists (rest.drop n)).map (rest.take n :: ·)
      else none
termination_by arguments => arguments.length
decreasing_by simp [List.length_drop]; omega

/-- The answer of `VeriMol.run` to one list of arguments, as this program prints
it: a line with the exit code and with the numbers of bytes of the two texts,
then the text for standard output, then the text for standard error. -/
def answer (arguments : List String) : String :=
  let output := VeriMol.run (arguments.map String.toList)
  let stdout := String.ofList output.stdout
  let stderr := String.ofList output.stderr
  s!"{output.exitCode} {stdout.utf8ByteSize} {stderr.utf8ByteSize}\n{stdout}{stderr}"

/-- The executable `answers`. Before it ends it writes out what is still
waiting for standard output, as `Main.lean` does: if the answers cannot be
written, Lean reports that, and this program ends with exit code 1. -/
def main (arguments : List String) : IO UInt32 := do
  match argumentLists arguments with
  | none =>
    IO.eprintln ("error: expected lists of arguments, each as the number of its arguments "
      ++ "followed by the arguments")
    return 1
  | some lists =>
    let out ← IO.getStdout
    for list in lists do
      out.putStr (answer list)
    out.flush
    return 0
