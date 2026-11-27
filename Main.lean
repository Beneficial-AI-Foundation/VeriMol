import VeriMol.Core

/-- The executable `app`. It contains no `if` and no `match`: it converts the
command-line arguments to lists of characters, asks `VeriMol.run` for the
complete output, and performs it.

Before it ends it writes out what is still waiting for standard output: the
line with `flush`. A short text waits there until the program ends. Without
that line, a text that cannot be written then (a full disk, an output that is
closed) would be lost without a word, and the exit code would still be 0.
With it Lean reports the failure, and the program ends with exit code 1
(SPEC.md, section 8). -/
def main (args : List String) : IO UInt32 := do
  let output := VeriMol.run (args.map String.toList)
  IO.print (String.ofList output.stdout)
  IO.eprint (String.ofList output.stderr)
  (← IO.getStdout).flush
  return output.exitCode.toUInt32
