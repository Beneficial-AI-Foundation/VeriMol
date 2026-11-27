import Lean
import VeriMol
import Main
import Audit.Ledger

/-!
# Audit: the rules of the project that a machine can check

Lean runs this file as part of `lake build` and of `lake test`. If one of the
rules that it checks is broken, the build fails and lists what is wrong.
Otherwise it prints a report that says, for each theorem of the ledger,
whether it is proven or open, and on which definitions its meaning rests.
Lake runs the file again whenever it or a file that it imports has changed;
otherwise it shows the report of the last run. The comments below cite the
nine rules of the project by their numbers: `CLAIMS.md` lists them.

What is checked, by rule:

* rule 2: the files of Core import only files of Core;
* rule 3: no declaration of Core is `partial`, `unsafe`, an axiom, or tied to
  other code; none contains `sorry`, does input or output, leaves a debug
  trace, can panic, or is a loop that need not end. Of Lean's own library
  Core mentions only the names of the list `allowedInCore`, and through them
  it reaches no function whose code is hidden. Core and Proofs hold no macro
  and no notation;
* rule 4: `Main.lean` imports only Core and declares `main` and nothing else;
  `main` is the copy that the author approved (`approvedMain`), is tied to no
  other code, and mentions only the names of two lists;
* rule 5: Core declares no instance that could change what `==` or Lean's own
  types do in the tests, and makes no declaration of Lean's library an
  instance;
* rule 9: the files of Proofs import only files of Core and Proofs; Proofs
  holds no axiom, no `native_decide` and no code that runs when a file is
  loaded; every theorem of the ledger exists, with its recorded fingerprint
  and status; and `sorry` stands only in a theorem that the ledger lists as
  open.

The two libraries are called Core and Proofs here, as in the rules. Core is
the file `VeriMol/Core.lean` with the files under `VeriMol/Core/`, Proofs is
`VeriMol/Proofs.lean` with the files under `VeriMol/Proofs/`, and
`VeriMol.lean` imports both.

The checks see the files that this file imports, directly or indirectly:
`VeriMol.lean` and `Main.lean`, and everything that they import. A file that
is not imported there is not checked, and a theorem in it does not count as
proven. The three root files `VeriMol.lean`, `VeriMol/Core.lean` and
`VeriMol/Proofs.lean` themselves may hold import lines only: a declaration in
one of them is reported. A file under `VeriMol/` that belongs to neither
library is reported as well.

The checker also tests itself on every build: the section "Self-test" holds
one small specimen of each violation, and the build fails if the checker stops
detecting one of them. That is why words such as `unsafe`, `sorry` and
`native_decide` appear in this file.

`import Lean` gives this file access to Lean's own records about every
declaration. It is part of the Lean installation, not a dependency, and no
other file of the project imports it.
-/

open Lean Elab Command

namespace Audit

/-! ## Settings

The lists `ofCoreInMain`, `allowedInMain` and `allowedInCore` hold exactly what
is mentioned: the build stops for a name that is not on its list, and for a
name on a list that nothing mentions. An entry is added to a list of this
section, and `approvedMain` is changed, only with the author's approval. -/

/-- Rule 9: the only axioms a proven theorem may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Rule 4: everything of Core that `Main` may mention: the function that is
the whole program, and what it returns, with its three parts. So `Main` can
ask Core for nothing but `VeriMol.run`, and it can take nothing but the two
texts and the exit code from the answer. The check `reference/check_app.py`
rests on that: it asks `VeriMol.run` about every text, through a second program,
and starts the built program itself for a sample only. A new entry lets
`Main` ask Core for something else. -/
def ofCoreInMain : List Name := [
  ``VeriMol.run, ``VeriMol.Output, ``VeriMol.Output.stdout, ``VeriMol.Output.stderr,
  ``VeriMol.Output.exitCode
]

/-- Rule 4: everything outside Core that `Main` may mention. With these names
`Main` can convert text, call Core, print, and write out what is waiting for
standard output, and nothing else: there is no `if`, no `match`, no
comparison and no file access on the list. A text or a number that is
written out in `Main.lean` itself is no name, so this list cannot refuse it:
that `Main` prints nothing of its own is held in place by the approved copy
of `main` (`approvedMain`, below). A new entry gives `Main` a new ability. -/
def allowedInMain : List Name := [
  -- types
  ``IO, ``IO.Error, ``Unit, ``UInt32, ``String, ``Char, ``List,
  -- output
  ``IO.print, ``IO.eprint,
  -- writing out what waits for standard output, so that a failure to write
  -- the answer is not lost: standard output as a stream (`IO.FS.Stream` is
  -- Lean's name for the type of one; no name here opens a file), and the one
  -- thing that is done with it
  ``IO.getStdout, ``IO.FS.Stream, ``IO.FS.Stream.flush,
  -- conversion between Main's text and Core's text, and of the exit code
  ``String.toList, ``String.ofList, ``List.map, ``Nat.toUInt32,
  -- what `do` notation and printing a String turn into
  ``Bind.bind, ``Pure.pure, ``Monad.toBind, ``Monad.toApplicative,
  ``Applicative.toPure, ``instMonadEIO, ``instToStringString,
  -- what Lean puts around `IO.getStdout`, an action that cannot fail, so
  -- that it can stand among actions that can
  ``BaseIO, ``EIO, ``liftM, ``instMonadLiftT, ``instMonadLiftTOfMonadLift,
  ``instMonadLiftBaseIOEIO
]

/-- Rule 4: `main` as the author has read and approved it, written here a
second time. The build stops unless `Main.lean` declares this function, under
the name `main`, and nothing else (`mainProblems` says what is compared).

Nothing is proven about `Main.lean`, and the two lists above do not say what
`main` does with the names that it may use. Three things a person has to see
in these lines: that `VeriMol.run` is asked about the arguments as they are;
that the two texts of the answer are printed, each where it belongs and once,
and nothing else is; and that the program ends with the exit code of the
answer. This copy holds in place what that person saw. The whole body is
compared and not a fingerprint of it, because two different bodies can have
the same fingerprint.

A change to `Main.lean` has to be made here as well, where it shows in
`git diff Audit.lean`. This function is never run. -/
def approvedMain (args : List String) : IO UInt32 := do
  let output := VeriMol.run (args.map String.toList)
  IO.print (String.ofList output.stdout)
  IO.eprint (String.ofList output.stderr)
  (← IO.getStdout).flush
  return output.exitCode.toUInt32

/-- Rule 3: everything of Lean's own library that a declaration of Core may
mention. A declaration of Core may mention Core and these names, and nothing
else. They are the types that Core names and their parts, the functions and
lemmas of the library that Core calls, and what Lean itself writes for a type
of Core, for a `deriving` line and for a `match`.

The other checks of rule 3 stop what is known to be wrong. This list turns
that round for what Core mentions: only what stands here is let through. So
Core cannot give an instance to a class of Lean's library that is not here,
and no function of that library comes into Core unseen.

A new entry lets Core use one more thing of Lean's library. The names are in
the order in which Lean sorts text, capital letters first; the self-test asks
for that order, so no name stands here twice. -/
def allowedInCore : List Name := [
  ``And, ``And.intro, ``BEq.beq, ``Bool, ``Bool._sizeOf_inst,
  ``Bool.and, ``Bool.false, ``Bool.not, ``Bool.or, ``Bool.true, ``Char,
  ``Char._sizeOf_inst, ``Char.isDigit, ``Char.ofNat, ``Char.toNat, ``Decidable,
  ``Decidable.decide, ``Decidable.isFalse,
  ``Decidable.isTrue, ``DecidableEq, ``Eq, ``Eq.mp, ``Eq.ndrec,
  ``Eq.ndrec_symm, ``Eq.propIntro, ``Eq.refl, ``Eq.symm, ``Except,
  ``Except.casesOn, ``Except.error, ``Except.ok, ``Exists, ``False,
  ``False.elim, ``GE.ge, ``GetElem?.getElem?, ``HAdd.hAdd, ``HAppend.hAppend,
  ``HMod.hMod, ``HMul.hMul, ``HSub.hSub, ``Iff, ``Int, ``Int._sizeOf_inst, ``Int.decLt,
  ``Int.instDecidableEq, ``Int.instLTInt, ``Int.instLinearOrderPackage,
  ``Int.instNegInt, ``Int.instRepr, ``Int.natAbs, ``LE.le, ``LT.lt,
  ``Lean.injEq_helper, ``List, ``List.Pairwise, ``List.Perm, ``List._sizeOf_inst,
  ``List.all, ``List.any, ``List.below, ``List.brecOn, ``List.casesOn,
  ``List.cons, ``List.contains, ``List.ctorIdx, ``List.decidableBAll,
  ``List.decidableLE, ``List.decidablePerm, ``List.drop, ``List.dropWhile, ``List.filter,
  ``List.filterMap, ``List.find?, ``List.findSome?, ``List.flatMap,
  ``List.foldl, ``List.head?, ``List.idxOf, ``List.instAppend, ``List.instBEq,
  ``List.instDecidableMemOfLawfulBEq, ``List.instDecidablePairwise,
  ``List.instGetElem?NatLtLength, ``List.instLE, ``List.instMembership,
  ``List.intercalate, ``List.isEmpty, ``List.length, ``List.map, ``List.nil,
  ``List.range, ``List.range', ``List.rec, ``List.reverse, ``List.sum,
  ``List.take, ``List.takeWhile, ``List.zip, ``Max.max, ``Membership.mem,
  ``Min.min, ``Nat, ``Nat.below, ``Nat.ble, ``Nat.brecOn, ``Nat.casesOn,
  ``Nat.cast, ``Nat.decEq, ``Nat.decLe, ``Nat.decLt, ``Nat.hasNotBit,
  ``Nat.instMax, ``Nat.instMod, ``Nat.land, ``Nat.ne_of_beq_eq_false, ``Nat.ofDigitChars,
  ``Nat.shiftRight, ``Nat.succ, ``Nat.toDigits, ``Neg.neg, ``Not,
  ``OfNat.ofNat, ``Option, ``Option._sizeOf_inst, ``Option.casesOn,
  ``Option.ctorIdx, ``Option.decidableEqNone, ``Option.getD,
  ``Option.instDecidableEq, ``Option.isNone, ``Option.isSome, ``Option.map,
  ``Option.none, ``Option.or, ``Option.rec, ``Option.some, ``Or, ``PProd,
  ``PULift, ``PULift.down, ``PULift.up, ``Prod, ``Prod._sizeOf_inst,
  ``Prod.casesOn, ``Prod.fst, ``Prod.mk, ``Prod.snd, ``Repr,
  ``Repr.addAppParen, ``Repr.mk, ``SizeOf, ``SizeOf.mk, ``SizeOf.sizeOf,
  ``Std.Format, ``Std.Format.FlattenBehavior.allOrNone, ``Std.Format.bracket,
  ``Std.Format.group, ``Std.Format.instAppend, ``Std.Format.line,
  ``Std.Format.nest, ``Std.Format.nil, ``Std.Format.text,
  ``Std.LinearOrderPackage.toLinearPreorderPackage,
  ``Std.LinearPreorderPackage.toPreorderPackage, ``Std.PreorderPackage.toBEq,
  ``String.toList, ``Unit, ``Unit.unit, ``Zero.ofOfNat0, ``absurd, ``bne,
  ``cond, ``congrArg, ``dite, ``getObjTagNat, ``id, ``inferInstance,
  ``instAddNat, ``instBEqOfDecidableEq, ``instBEqOption, ``instDecidableAnd,
  ``instDecidableEqBool, ``instDecidableEqChar, ``instDecidableEqList,
  ``instDecidableEqNat, ``instDecidableNot, ``instDecidableOr,
  ``instHAdd, ``instHAppendOfAppend, ``instHMod, ``instHMul,
  ``instHSub, ``instLENat, ``instLTNat, ``instLawfulBEq, ``instMinNat,
  ``instMulNat, ``instNatCastInt, ``instOfNat, ``instOfNatNat,
  ``instReprAtomChar, ``instReprBool, ``instReprChar, ``instReprList,
  ``instReprListOfReprAtom, ``instReprNat, ``instReprOption, ``instSizeOfNat,
  ``instSubNat, ``ite, ``noConfusionEnum, ``noConfusionTypeEnum,
  ``noConfusion_of_Nat, ``repr, ``reprArg, ``rfl
]

/-- Rule 3: the declarations of Lean's library that Core may reach although
Lean runs other code in their place. Each entry stands here with its reason:

* `Nat.repr` writes a number as text, and Lean runs a faster function in its
  place. `deriving Repr` reaches it, and the tests need `Repr` to print a
  `Mol` when a test fails.

A new entry lets Core run code of Lean's library that the audit does not look
into, so one is added only with the author's approval. -/
def trustedInLibrary : List Name := [``Nat.repr]

/-! ## The checks -/

/-! ### The files and their imports -/

/-- The library Core, by the name of its root file: `VeriMol/Core.lean`, with
the files under `VeriMol/Core/`. -/
def core : Name := `VeriMol.Core

/-- The library Proofs: `VeriMol/Proofs.lean`, with the files under
`VeriMol/Proofs/`. -/
def proofs : Name := `VeriMol.Proofs

/-- The file that stands for both libraries, `VeriMol.lean`: it imports the
two root files and holds nothing else. -/
def both : Name := `VeriMol

/-- Does a file belong to a library? A library is its root file and the files
under the folder of the same name: `VeriMol.Core` and `VeriMol.Core.Mol`
belong to Core, and `VeriMol` and `VeriMol.Proofs.Read` do not. (Lean names a
file by its place, with dots: `VeriMol/Core/Mol.lean` is `VeriMol.Core.Mol`.)
-/
def belongsTo (library file : Name) : Bool :=
  library.isPrefixOf file

/-- The file with the given name, as its place in the repository. -/
def placeOf (file : Name) : String :=
  "/".intercalate (file.components.map toString) ++ ".lean"

/-- The files of one library, each with Lean's record of what it contains. -/
def filesOf (env : Environment) (library : Name) : Array (Name × ModuleData) :=
  (env.header.moduleNames.zip env.header.moduleData).filter (belongsTo library ·.1)

/-- All declarations in the files of one library. Helper declarations
generated by Lean are included. -/
def declarationsOf (env : Environment) (library : Name) : Array Name :=
  (filesOf env library).flatMap (·.2.constNames)

/-- Is `c` declared in a file of the given library? -/
def declaredIn (env : Environment) (library : Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some index =>
    ((env.header.moduleNames[index.toNat]?).map (belongsTo library)).getD false
  | none => false

/-- Rules 2, 4 and 9: the imports of one file that are not from an allowed
library. (`Init` is Lean's built-in base library, which every Lean file
gets.) -/
def importProblems (file : Name) (imports : Array Name) (allowed : List Name) :
    Array String :=
  (imports.filter fun imported => !allowed.any (belongsTo · imported)).map
    (s!"the file of {file} imports {·}")

/-- Rules 3 and 9: a root file holds import lines only. So the file that
carries the name of its library must declare nothing, and neither must
`VeriMol.lean`. (Lean's second checker, `leanchecker`, is not run for the
root files, so a declaration in one of them would miss that second check.) -/
def rootFileProblems (file library : Name) (declarations : Array Name) : Array String :=
  if file == library && !declarations.isEmpty then
    #[s!"{placeOf library} holds declarations, but only import lines belong there: "
      ++ s!"{declarations.toList.take 5}"]
  else #[]

/-- Rules 3 and 9: a file under `VeriMol/` that belongs to neither library.
It would look like a part of the library, and none of the checks for Core or
for Proofs would read it. -/
def strayFileProblems (file : Name) : Array String :=
  if file == both || belongsTo core file || belongsTo proofs file then #[]
  else #[s!"{placeOf file} stands under VeriMol/ and belongs neither to Core nor to Proofs"]

/-! ### Helpers that Lean generates for a type

For a type `T`, Lean itself generates the helper `T.ctorIdx`, and for most
types a second one, `T.ctorIdx._impl`, which is `unsafe` and which Lean runs
in the place of the first (`@[implemented_by]`). Nobody wrote them, so they
are exempt from the checks for `unsafe` and for `@[implemented_by]`
(`codeProblems`), and the search into Lean's library does not take them for
hidden code (`runsHiddenCode`). The exemption is for Lean's own pair as Lean
makes it, and for nothing else:

* A name is not enough. Somebody can write a declaration of that name in
  front of the type, and Lean then generates none of its own.
* "It has no place in a file" is not enough either. An attribute can tie
  Lean's own helper to other code:
  `attribute [implemented_by other] T.ctorIdx`. The compiled program then
  runs `other`, and no proof knows of it.

So the helper `_impl` must do what Lean's does and nothing else, and the other
code of `T.ctorIdx` must be that `_impl`. -/

/-- Is `c` a declaration that somebody wrote in a file, as opposed to a helper
that Lean generated? Only written declarations have a place in a file. The
name is not asked: a written declaration may have any name, also one that
looks like the name of a helper. -/
def isWritten (c : Name) : CoreM Bool := do
  return (← findDeclarationRangesCore? c).isSome

/-- The body of a function, under its `fun`s. -/
def underLambdas : Expr → Expr
  | .lam _ _ body _ => underLambdas body
  | e => e

/-- Is `c` Lean's own `T.ctorIdx._impl`? It has no place in a file, is tied to
no other code, and its body is `fun x => getObjTagNat x`, with more arguments
in front if the type has parameters. Only the body under the `fun`s is looked
at: the types of the arguments may name anything, as the parameters of the
type do. -/
def isGeneratedImpl (c : Name) : CoreM Bool := do
  let env ← getEnv
  let .str (.str type "ctorIdx") "_impl" := c | return false
  unless (env.find? type) matches some (.inductInfo _) do
    return false
  if ← isWritten c then
    return false
  if (Compiler.getImplementedBy? env c).isSome || isExtern env c then
    return false
  let some (.defnInfo v) := env.find? c | return false
  let body := underLambdas v.value
  return body.getAppFn.isConstOf ``getObjTagNat
    && body.getUsedConstants.all fun n => n == ``getObjTagNat || n == type

/-- Is `c` Lean's own `T.ctorIdx`? It has no place in a file. For a type with
one case it is an ordinary function. For other types Lean runs
`T.ctorIdx._impl` in its place; so if other code runs in the place of `c`,
that code must be exactly Lean's own `T.ctorIdx._impl`. -/
def isGeneratedCtorIdx (c : Name) : CoreM Bool := do
  let env ← getEnv
  let .str type "ctorIdx" := c | return false
  unless (env.find? type) matches some (.inductInfo _) do
    return false
  if ← isWritten c then
    return false
  match Compiler.getImplementedBy? env c with
  | some other => return other == .str c "_impl" && (← isGeneratedImpl other)
  | none => return true

/-- Is `c` one of Lean's own two helpers? -/
def isGeneratedByLean (c : Name) : CoreM Bool := do
  return (← isGeneratedCtorIdx c) || (← isGeneratedImpl c)

/-! ### What a declaration may not be or mention -/

/-- Rule 3: why Core must not mention the declaration `n`, if it must not. -/
def forbiddenReference (n : Name) : Option String :=
  if n.getRoot == `IO || n == ``BaseIO || n == ``EIO then
    some "does input or output"
  else if [``dbgTrace, ``dbgTraceVal, ``dbgTraceIfShared, ``dbgStackTrace, ``dbgSleep].contains n then
    some "has a hidden side effect"
  else if [``panic, ``panicCore, ``panicWithPos, ``panicWithPosWithDecl].contains n then
    some "can panic"
  else if (`Lean.Loop).isPrefixOf n || n == ``Lean.instForInLoopUnitOfMonad then
    some "is a `while` or `repeat` loop, which need not end"
  else if n == ``Std.Stream.forIn || n == ``Std.instForInOfMonadOfStream then
    some "is a `for` loop over a stream, which need not end"
  else if (`Lean.Order).isPrefixOf n then
    some "belongs to `partial_fixpoint`, which defines a function that need not end"
  else
    match n with
    | .str _ last => if last.endsWith "!" then some "can panic" else none
    | _ => none

/-- Is the declaration `c` tied to code that runs when the program starts, or
when a file that imports it is read? `@[init f]` on a declaration makes the
program take its value from the action `f` at the start, whatever the
declaration says; and a declaration can be marked to run at the start itself.
Returns what is reported for it. -/
def initProblem (env : Environment) (c : Name) : Option String :=
  if (getInitFnNameFor? env c).isSome || isIOUnitInitFn env c
      || (getBuiltinInitFnNameFor? env c).isSome || isIOUnitBuiltinInitFn env c then
    some "is tied to code that runs when the program starts (@[init])"
  else none

/-- Rules 3 and 4: the five ways in which a declaration can make the compiled
program run other code than the declaration says. -/
def codeProblems (c : Name) : CoreM (Array String) := do
  let env ← getEnv
  let some info := env.find? c | return #[]
  let mut problems := #[]
  if let some problem := initProblem env c then
    problems := problems.push problem
  if info matches .opaqueInfo _ then
    problems := problems.push "is opaque (this is what `partial` produces)"
  unless ← isGeneratedByLean c do
    if info.isUnsafe then
      problems := problems.push "is unsafe"
    if (Compiler.getImplementedBy? env c).isSome then
      problems := problems.push "uses @[implemented_by]"
  if isExtern env c then
    problems := problems.push "uses @[extern]"
  return problems

/-! ### Macros and notation -/

/-- The four types of a declaration that changes how Lean reads a file: a
macro, the two kinds of parser, and an unexpander, which changes how Lean
prints. Lean takes a declaration for one of these only if it has exactly this
type. Notation is made of them. -/
def notationTypes : List Name :=
  [``Lean.Macro, ``Lean.ParserDescr, ``Lean.TrailingParserDescr, ``Lean.PrettyPrinter.Unexpander]

/-- Rules 3 and 9: does this declaration define a macro, or notation, which
is made of macros? Core and Proofs may hold none. A macro can write a
declaration that has no place in the file, and it can set an option of Lean
without the word for it, which the tests look for. (`Main` may hold none
either: the names are not on its list.) A piece of syntax that Lean stores
for a default argument is no macro (`isStoredSyntax`). -/
def definesNotation (info : ConstantInfo) : Bool :=
  info.type.getUsedConstants.any notationTypes.contains

/-- What is reported for a declaration that defines a macro or notation. -/
def notationProblem : String :=
  "defines a macro or notation, which Core and Proofs may not hold"

/-! ### Hidden code in Lean's library -/

/-- Rule 3: is the code of `n` hidden, so that `n` need not end? That is so
for

* an opaque declaration that is no C function (no `@[extern]`): this is what
  `partial` produces, in Lean's library as everywhere;
* a declaration with `@[implemented_by]`: Lean runs other code in its place.

Lean's own functions that need not end are made in these two ways: `repeatM`,
which `while` and `repeat` run; the search that a `for` loop over a stream
runs; `WellFounded.extrinsicFix`, a recursion that asks for no proof that it
ends. Not every function with hidden code fails to end: many of Lean's
functions on arrays are of this kind and do end. The audit cannot look inside,
so it refuses them all, apart from the helpers that Lean generates for a type
and from the list `trustedInLibrary`. -/
def runsHiddenCode (n : Name) : CoreM Bool := do
  let env ← getEnv
  let some info := env.find? n | return false
  if trustedInLibrary.contains n || (← isGeneratedByLean n) then
    return false
  return ((info matches .opaqueInfo _) && !isExtern env n)
    || (Compiler.getImplementedBy? env n).isSome

/-- Is `c` a piece of syntax that Lean itself stored? For a default argument
that a tactic finds, such as `(h : i < n := by decide)`, Lean stores the
tactic in a declaration of the type `Lean.Syntax`, without a place in a file.
It is data for Lean while it reads a file. The compiled program builds that
piece of data when it starts, which ends, and does nothing else with it.

Lean stores the default value of a structure field of the type `Lean.Syntax`
in the same way, although somebody wrote that value. With Lean 4.36.0 this is
no way past the search: Lean does not compile the stored value, and it copies
the value into the body of every function that uses the default, where the
search finds it. A definition of the type `Lean.Syntax` that has a place in a
file is a definition like any other. -/
def isStoredSyntax (c : Name) : CoreM Bool := do
  let some info := (← getEnv).find? c | return false
  return info.type.isConstOf ``Lean.Syntax && !(← isWritten c)

/-- Rule 3: what the declarations `starts` reach outside `library` whose code
is hidden (`runsHiddenCode`). The search goes through the bodies of
definitions: a function runs what its body mentions. A theorem has no body
here, since a proof does not run; a C function (`@[extern]`) is not looked
into; and neither is a piece of syntax that Lean stored (`isStoredSyntax`).
Declarations of `library` itself are not followed: each of them is checked on
its own.

One thing the search does not follow. Lean's compiler puts a faster function
in the place of some functions of its library, each with a proof that the two
are equal (`@[csimp]`): `List.map`, `List.append` and `String.toList` are of
these. The faster function is not in the body of the slower one, so the search
does not see it, and some of them have hidden code. They are trusted with
Lean, as its C functions are.

Returns how many declarations were looked at, and one chain for each
declaration with hidden code that was reached: the chain begins with one of
`starts` and ends with that declaration. The search goes level by level, so a
chain is as short as can be. -/
def hiddenCodeReached (library : Name) (starts : Array Name) :
    CoreM (Nat × Array (List Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut chains : Array (List Name) := #[]
  -- Each entry is a chain in reverse: the declaration that was reached last
  -- comes first.
  let mut level : Array (List Name) := starts.map ([·])
  while !level.isEmpty do
    let mut next : Array (List Name) := #[]
    for chain in level do
      let some n := chain.head? | continue
      if seen.contains n || declaredIn env library n then continue
      seen := seen.insert n
      if ← isStoredSyntax n then continue
      if ← runsHiddenCode n then
        chains := chains.push chain.reverse
        continue
      if isExtern env n then continue
      if let some (.defnInfo v) := env.find? n then
        for m in v.value.getUsedConstants do
          unless seen.contains m do
            next := next.push (m :: chain)
    level := next
  return (seen.size, chains)

/-- Rule 3: where the search into Lean's library starts. These are the
declarations outside `library` that the declarations `sources` mention, each
with one source that mentions it. Every source counts, a theorem as well: what
a theorem names is refused too, although no proof runs. That is on purpose: a
lemma can tell Lean's compiler to put one function in the place of another,
and it names that function. Only a piece of syntax that Lean stored is no
source. -/
def startsOf (library : Name) (sources : Array Name) : CoreM (NameMap Name) := do
  let env ← getEnv
  let mut starts : NameMap Name := {}
  for c in sources do
    let some info := env.find? c | continue
    if ← isStoredSyntax c then continue
    for n in info.getUsedConstantsAsSet do
      unless declaredIn env library n || starts.contains n do
        starts := starts.insert n c
  return starts

/-! ### Instances -/

/-- The names in the type of an instance that count when Lean looks for an
instance: those behind the arguments of the instance, with every abbreviation
written out and with everything worked out that Lean works out while it
looks, and without the output places of the class. (A class can have places
that Lean does not look at but works out from the others: in
`HAppend α β γ`, which stands behind `++`, that is `γ`.) So a name that
stands only among the arguments is not among them, nor a name that goes away
when an abbreviation is written out, nor a name that stands in an output
place only.

One kind of place still counts, although Lean can fill it from an instance as
well: a place that Lean marks as half an output (`semiOutParam`), such as the
first place of `Coe` or the state of `MonadStateOf`. An instance for Lean's
own types that names Core in such a place only passes this rule (for example
`instance : MonadStateOf VeriMol.Mol (StateT Bool Id)`). The list
`allowedInCore` stops it: no class of Lean's library with such a place is on
that list. -/
def namesBehindArguments (type : Expr) : MetaM (Array Name) :=
  Meta.forallTelescopeReducing type fun _ target => do
    let target ← Meta.withReducible
      (Meta.reduce target (explicitOnly := false) (skipTypes := false) (skipProofs := false))
    let env ← getEnv
    let outputs := match target.getAppFn.constName? with
      | some cls => (getOutParamPositions? env cls).getD #[]
      | none => #[]
    let places := target.getAppArgs
    let mut names := target.getAppFn.getUsedConstants
    for place in [0:places.size] do
      unless outputs.contains place do
        names := names ++ places[place]!.getUsedConstants
    return names

/-- What is reported for an instance of `BEq` in Core. -/
def beqInstanceProblem : String :=
  "is an instance of BEq, which Core may not declare: the tests compare with it"

/-- What is reported for an instance of Core that is an instance for Lean's
own types. -/
def foreignInstanceProblem : String :=
  "is an instance that names nothing of Core behind its arguments, "
    ++ "so it would change what Lean's own types do"

/-- Rule 5, seen from Core. The tests import Core, so an instance that Core
declares is found by the tests' own code. Two kinds are refused, each judged
as Lean looks for an instance (`namesBehindArguments`), and not by the type
of the instance as it is written.

* An instance of `BEq`. The tests compare with `==`, which is `BEq`. With an
  instance of its own, Core could make `==` say "equal" of any two values, and
  a wrong answer would pass its test. The class is asked of Lean itself
  (`Meta.isClass?`), which sees through abbreviations. Core's own comparisons
  need no such instance: `=`, which Lean decides with a proof
  (`deriving DecidableEq`), and `==` as Lean's library gives it, which for a
  type of Core is made from `=`.
* An instance that names nothing of `library` behind its arguments, in the
  places that count. It would change what Lean's own types do, in Core and in
  everything that imports Core. (So a class of Core cannot say
  `extends Ord α`: see the specimen `TakesOrdIn`.) -/
def instanceProblems (library : Name) (c : Name) (info : ConstantInfo) :
    CoreM (Array String) := do
  let env ← getEnv
  unless Meta.isInstanceCore env c do
    return #[]
  let mut problems := #[]
  if (← (Meta.isClass? info.type).run') == some ``BEq then
    problems := problems.push beqInstanceProblem
  unless (← (namesBehindArguments info.type).run').any (declaredIn env library ·) do
    problems := problems.push foreignInstanceProblem
  return problems

/-- Rule 5: the instances that Lean recorded for the files of `library`, each
with its file. Lean keeps, for every file, the instances that the file
registered, whether with the word `instance` or with an attribute. -/
def registeredInstances (env : Environment) (library : Name) : Array (Name × Name) := Id.run do
  let mut found := #[]
  for (file, idx) in env.header.moduleNames.toList.zipIdx do
    unless belongsTo library file do continue
    for entry in Meta.instanceExtension.ext.getModuleEntries env idx do
      let name? := match entry with
        | .global e => e.globalName?
        | .scoped _ e => e.globalName?
      if let some name := name? then
        found := found.push (file, name)
  return found

/-- Rule 5: of the instances that the files of a library registered, those
that are no declarations of that library. One line in a file of Core can make
a declaration of Lean's own library an instance:
`attribute [instance] Nat.decEq`. No declaration of Core mentions anything
then, so neither the list `allowedInCore` nor the rule about instances sees
it, and every file that imports Core finds the new instance. -/
def foreignInstances (declared : Name → Bool) (registered : Array (Name × Name)) : Array (Name × Name) :=
  registered.filter fun (_, name) => !declared name

/-! ### The list of what Core may mention -/

/-- Rule 3: of the declarations of Lean's library that Core mentions, those
that are not on the list `allowedInCore`. -/
def notAllowedInCore (mentioned : List Name) : List Name :=
  mentioned.filter fun n => !allowedInCore.contains n

/-- Rule 3: the names of the list `allowedInCore` that Core does not
mention. The list is to hold what Core names and nothing more. -/
def notNeededInCore (mentioned : List Name) : List Name :=
  allowedInCore.filter fun n => !mentioned.contains n

/-- What the audit says of a declaration of Lean's library that `source`, a
declaration of Core, mentions and that is not on the list. -/
def notOnTheList (source n : Name) : String :=
  s!"Core: {source} mentions {n}, which is not on the list Audit.allowedInCore (rule 3). If Core is "
    ++ "to use this declaration of Lean's library, it has to be added to that list in Audit.lean first"

/-- What the audit says of a name of the list that Core does not mention. -/
def notMentioned (n : Name) : String :=
  s!"Core: the list Audit.allowedInCore holds {n}, which no declaration of Core mentions (rule 3). "
    ++ "Take it off the list in Audit.lean"

/-- Rule 3: everything that is wrong between the list `allowedInCore` and what
Core mentions of Lean's library. `mentioned` holds each such declaration with
one declaration of Core that mentions it (`startsOf` gives them). The lines
are sorted by the name of the declaration of Core; the names of the list that
Core does not mention come last. -/
def listProblems (mentioned : List (Name × Name)) : Array String :=
  let outside := (mentioned.filter fun (n, _) => !(notAllowedInCore [n]).isEmpty).toArray.qsort
    fun a b => s!"{a.2} {a.1}" < s!"{b.2} {b.1}"
  outside.map (fun (n, source) => notOnTheList source n)
    ++ (notNeededInCore (mentioned.map (·.1))).toArray.map notMentioned

/-- Rules 3 and 5: everything that is wrong with one declaration of Core.
(What the declarations of Core mention and reach in Lean's library is asked
once for all of them, in `run`.) -/
def coreProblems (c : Name) : CoreM (Array String) := do
  let env ← getEnv
  let some info := env.find? c | return #[]
  let mut problems := #[]
  if info matches .axiomInfo _ then
    problems := problems.push "is an axiom"
  if definesNotation info then
    problems := problems.push notationProblem
  problems := problems ++ (← instanceProblems core c info)
  problems := problems ++ (← codeProblems c)
  for a in ← collectAxioms c do
    if a == ``sorryAx then
      problems := problems.push "contains sorry"
    else unless standardAxioms.contains a || a == c do
      problems := problems.push s!"depends on the axiom {a}"
  for n in info.getUsedConstantsAsSet do
    if let some why := forbiddenReference n then
      problems := problems.push s!"mentions {n}, which {why}"
  return problems

/-- Rule 9: everything that is wrong with one declaration of Proofs, given the
axioms it depends on. `sorry` is allowed here: it marks a theorem that is
stated but not yet proven, and the ledger deals with it. `native_decide` is
found through the axiom that it brings in. -/
def proofsProblems (info : ConstantInfo) (axioms : Array Name) : Array String :=
  if info matches .axiomInfo _ then #["is an axiom"]
  else (axioms.filter fun a => !(standardAxioms.contains a || a == ``sorryAx)).map
    fun a => s!"depends on the axiom {a}"

/-! ### Main -/

/-- Rule 4: the names that a declaration of `Main` mentions but may not.
Allowed are the names of the two lists `ofCoreInMain` and `allowedInMain`,
and Main's own declarations. Every other declaration of Core is refused, as
everything else is. -/
def notAllowedInMain (mentioned : List Name) (ownDeclarations : Array Name) : List Name :=
  mentioned.filter fun n =>
    !(ofCoreInMain.contains n || allowedInMain.contains n || ownDeclarations.contains n)

/-- Rule 4: the names of the two lists `ofCoreInMain` and `allowedInMain`
that `Main` does not mention. The lists are to hold what `Main` names and
nothing more. -/
def notNeededInMain (mentioned : List Name) : List Name :=
  (ofCoreInMain ++ allowedInMain).filter fun n => !mentioned.contains n

/-- Rule 4: what is wrong with what `Main.lean` declares. `declarations` are
the declarations of that file, `entry` is the one that it may hold, which is
`main`, and `approved` is the copy of it that the author has approved.

* The file declares `entry` and nothing else. A helper that Lean generates
  counts as well: `Main.lean` has none, and a `main` that needs one, for a
  `match` for example, is refused until this check is changed.
* `entry` and `approved` are definitions with the same type and the same
  body, expression for expression: what is compared is what Lean makes of
  the text, so a comment or another layout does not count. (Lean compares
  two expressions part by part. It leaves out two things, neither of which
  changes what a function does: the names of bound variables, and whether
  they are written as explicit or as implicit.)
* `entry` has no other name in the C code. Lean turns `main` into C code
  under a fixed name, through which the program is started. `@[export]`
  would give it another one, and the body does not show that. -/
def mainProblems (env : Environment) (entry approved : Name) (declarations : Array Name) :
    Array String := Id.run do
  let mut problems := #[]
  for c in declarations do
    unless c == entry do
      problems := problems.push
        (s!"Main: Main.lean declares {c}. It may declare {entry} and nothing else, also no helper "
          ++ "that Lean generates (rule 4)")
  match env.find? entry, env.find? approved with
  | some (.defnInfo v), some (.defnInfo w) =>
    unless declarations.contains entry do
      problems := problems.push s!"Main: {entry} is not declared in Main.lean (rule 4)"
    unless v.levelParams == w.levelParams && v.type == w.type && v.value == w.value do
      problems := problems.push
        (s!"Main: {entry} is not the function that the author has approved: its type or its body is not "
          ++ s!"that of {approved} (rule 4). If the change to Main.lean is meant, the same change is "
          ++ s!"made to {approved} in Audit.lean, with the author's approval")
    if let some other := getExportNameFor? env entry then
      problems := problems.push
        s!"Main: {entry} is given another name in the C code, {other} (@[export]) (rule 4)"
  | _, _ =>
    problems := problems.push
      s!"Main: {entry} or {approved} is missing, or is no definition (rule 4)"
  return problems

/-! ## Fingerprints (rule 9)

The fingerprint of a theorem covers its statement and the definitions that
give the statement its meaning. Without the second part, a theorem such as
"every graph the reader returns is well formed" could be emptied by redefining
"well formed", and its fingerprint would stay the same. -/

/-- A constructor, a recursor or a field accessor (such as `Output.stdout`) is
part of its type. -/
def owner (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.getMajorInduct
  | _ =>
    match (env.getProjectionFnInfo? c).bind (env.find? ·.ctorName) with
    | some (.ctorInfo v) => v.induct
    | _ => c

/-- Does the content of this declaration decide what a statement means, even
when the statement only mentions it?

* A type does: a statement about molecules means something else if a molecule
  holds something else.
* A definition that produces a statement or a type does, for example "is well
  formed". So do instances and abbreviations. Whether a definition produces a
  statement is read from its type as it is written: the type must end in
  `Prop` or in `Type`. A definition whose type stands behind a name of its
  own (`def IsSmall : Pred`, where `Pred` is a name for `Nat → Prop`) does
  not count; the report lists it among what the theorem is about.
* The helper that Lean generates for a `match` does. A statement with a `match`
  in it mentions that helper, and which case of the `match` is which stands in
  the helper and not in the statement.
* An ordinary function does not. A theorem that mentions the reader is a claim
  about the reader, so the reader must stay free to change.
* The proof of a theorem does not. -/
def givesMeaning (env : Environment) (info : ConstantInfo) : Bool :=
  match info with
  | .defnInfo v =>
    v.type.getForallBody.isSort || Meta.isInstanceCore env v.name ||
      getReducibilityStatusCore env v.name == .reducible || Meta.isMatcherCore env v.name
  | .thmInfo _ => false
  | _ => true

/-- The declarations that the content of a declaration mentions: for a type,
what its constructors hold; for a definition, its body. -/
def contentMentions (env : Environment) (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v =>
    v.ctors.toArray.flatMap fun ctor =>
      ((env.find? ctor).map (·.type.getUsedConstants)).getD #[]
  | .defnInfo v => v.value.getUsedConstants
  | _ => #[]

/-- A number computed from the content of a declaration. -/
def contentFingerprint (env : Environment) (info : ConstantInfo) : UInt64 :=
  match info with
  | .inductInfo v =>
    v.ctors.foldl (init := mixHash info.type.hash (hash v.numParams)) fun h ctor =>
      mixHash h (mixHash (hash ctor) (((env.find? ctor).map (·.type.hash)).getD 0))
  | .defnInfo v => mixHash v.type.hash v.value.hash
  | _ => info.type.hash

/-- Every declaration `inScope` on whose content the meaning of `statement`
rests, sorted by name.

Starting from the statement, this follows the type of everything it meets and
the content of everything that gives meaning. Whatever is reached through the
content of such a declaration gives meaning as well: if "is well formed" is
defined with a helper function, the helper is part of what it means. -/
def meaningOf (env : Environment) (inScope : Name → Bool) (statement : Expr) :
    Array Name := Id.run do
  -- For every declaration met so far: does its content count?
  let mut met : NameMap Bool := {}
  let mut todo : Array (Name × Bool) := statement.getUsedConstants.map (·, false)
  while !todo.isEmpty do
    let some (mentioned, throughContent) := todo.back? | break
    todo := todo.pop
    let c := owner env mentioned
    unless inScope c do continue
    let some info := env.find? c | continue
    let counts := throughContent || givesMeaning env info
    if let some before := met.find? c then
      if before || !counts then continue
    met := met.insert c counts
    todo := todo ++ info.type.getUsedConstants.map (·, false)
    if counts then
      todo := todo ++ (contentMentions env info).map (·, true)
  return ((met.toList.filter (·.2)).map (·.1)).toArray.qsort
    (fun a b => a.toString < b.toString)

/-- The fingerprint of a theorem: a number computed from its statement and
from the content of every declaration in `restsOn`. -/
def fingerprint (env : Environment) (statement : Expr) (restsOn : Array Name) : UInt64 :=
  restsOn.foldl (init := statement.hash) fun h c =>
    mixHash h (mixHash (hash c) (((env.find? c).map (contentFingerprint env)).getD 0))

/-- What the audit finds out about one theorem under `VeriMol/Proofs/`. -/
structure Found where
  name : Name
  fingerprint : UInt64
  /-- The declarations that the fingerprint covers besides the statement,
  as far as somebody wrote them (Lean's generated helpers are left out). -/
  restsOn : Array Name
  /-- The declarations of Core and Proofs that the statement names and that
  the fingerprint does not cover: what the theorem is about. -/
  isAbout : Array Name := #[]
  hasSorry : Bool
  axioms : Array Name

/-- Is `c` a theorem that somebody wrote in a file? -/
def isWrittenTheorem (c : Name) (info : ConstantInfo) : CoreM Bool := do
  if !(info matches .thmInfo _) then
    return false
  isWritten c

/-- Rule 9: is `c` a declaration that somebody wrote in a file and that is no
theorem? With `sorry` in it, such a declaration of Proofs is reported: `sorry`
is allowed only in a theorem. -/
def isWrittenNonTheorem (c : Name) (info : ConstantInfo) : CoreM Bool := do
  if info matches .thmInfo _ then
    return false
  isWritten c

/-- The declarations in scope that a statement names and that its fingerprint
does not cover, sorted by name. A constructor or a field counts as its type. -/
def isAboutOf (env : Environment) (inScope : Name → Bool) (statement : Expr)
    (covered : Array Name) : Array Name :=
  let named := (statement.getUsedConstants.map (owner env)).filter fun c =>
    inScope c && !covered.contains c
  (named.foldl (fun (seen : Array Name) c => if seen.contains c then seen else seen.push c) #[]).qsort
    (fun a b => a.toString < b.toString)

/-- Everything `inScope` that the declarations `starts` mention, directly or
through what they mention; the declarations `starts` are among it. -/
def mentionedBy (env : Environment) (inScope : Name → Bool) (starts : Array Name) : NameSet :=
  Id.run do
    let mut seen : NameSet := {}
    let mut todo := starts
    while !todo.isEmpty do
      let some c := todo.back? | break
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      let some info := env.find? c | continue
      for n in info.getUsedConstantsAsSet do
        if inScope n && !seen.contains n then
          todo := todo.push n
    return seen

/-- Rule 9: `sorry` is allowed under `VeriMol/Proofs/` only in a theorem that
is stated and not yet proven, and the ledger lists such a theorem as open. So
a declaration with `sorry` must be a theorem that is written in a file, or
something that such a theorem with `sorry` uses, for example a helper that
Lean generated for its proof. These are the others, among `withSorry`. -/
def straySorries (env : Environment) (inScope : Name → Bool)
    (withSorry openTheorems : Array Name) : Array Name :=
  let used := mentionedBy env inScope openTheorems
  withSorry.filter (!used.contains ·)

/-- Rule 9: every way in which the ledger disagrees with the theorems that
were found under `VeriMol/Proofs/`. -/
def ledgerProblems (ledger : List Entry) (found : Array Found) : Array String := Id.run do
  let mut problems := #[]
  for entry in ledger do
    match found.find? (·.name == entry.name) with
    | none =>
      problems := problems.push
        (s!"{entry.name} is in the ledger, but no theorem of that name is under VeriMol/Proofs/ "
          ++ "(deleted or renamed?)")
    | some thm =>
      if thm.fingerprint != entry.fingerprint then
        problems := problems.push
          (s!"the fingerprint of {entry.name} is not the one recorded in the ledger "
            ++ s!"(recorded {entry.fingerprint}, now {thm.fingerprint}). Either its statement "
            ++ s!"has changed, or one of the definitions it rests on: {thm.restsOn.toList}")
      if thm.hasSorry && entry.status == .proven then
        problems := problems.push
          s!"{entry.name} is recorded as proven, but it contains sorry"
      if !thm.hasSorry && entry.status == .stillOpen then
        problems := problems.push
          s!"{entry.name} is recorded as open, but it is proven: change its line to .proven"
    -- A name of the ledger must belong to one theorem only. (A `private`
    -- theorem in another file can have the name of a theorem of the ledger.)
    if (found.filter (·.name == entry.name)).size > 1 then
      problems := problems.push
        (s!"{entry.name} is the name of more than one theorem under VeriMol/Proofs/ (one of them "
          ++ "`private`?): a theorem of the ledger must have its name to itself")
  for thm in found do
    if thm.hasSorry && !ledger.any (·.name == thm.name) then
      problems := problems.push
        (s!"{thm.name} contains sorry but is not in the ledger; its line would be "
          ++ s!"⟨`{thm.name}, {thm.fingerprint}, .stillOpen⟩")
  return problems

/-! ## Self-test

Specimens for the checks above: one of each violation that they look for
(rules 3, 4, 5 and 9), declarations that are fine and must not be reported,
and specimens for the fingerprints. `selfTestFailures` holds each of them
against its check, and tries the other checks, such as those of the imports
and of the ledger, on made-up input. Nothing here is used by the program. -/

namespace SelfTest

def clean (n : Nat) : Nat := n + 1

/-- The same type and the same body as `clean`, under another name. -/
def cleanAgain (n : Nat) : Nat := n + 1

/-- A declaration with another name in the C code, which `main` may not
have, and its twin without one. -/
@[export audit_specimen_exported] def exported (n : Nat) : Nat := n + 2

def exportedTwin (n : Nat) : Nat := n + 2

/-- Another name for `Nat`. The two declarations below have one body and
these two types: only the type tells them apart. -/
abbrev OtherNat := Nat

def zeroAsNat : Nat := Nat.zero

def zeroAsOtherNat : OtherNat := Nat.zero

partial def isPartial (n : Nat) : Nat := isPartial (n + 1)

unsafe def isUnsafe (n : Nat) : Nat := n

@[implemented_by isUnsafe] def usesImplementedBy (n : Nat) : Nat := n

@[extern "no_such_c_function"] def usesExtern (n : Nat) : Nat := n

axiom isAxiom : True

theorem usesAxiom : True := isAxiom

/-- `native_decide` leaves the decision to the compiled program, which Lean's
kernel does not check. Lean 4.36.0 records each use as a new axiom of its own,
named after the theorem. -/
theorem usesNativeDecide : 2 + 2 = 4 := by native_decide

set_option warn.sorry false in
def usesSorry : Nat := sorry

def canPanic (xs : List Nat) : Nat := xs.head!

def canPanicToo (xs : List Nat) : Nat := xs[0]!

/-- `panic!` itself: the function behind it has no `!` in its name. -/
def panics : Nat := panic! "x"

def doesOutput : IO Unit := IO.println "x"

def hasSideEffect (n : Nat) : Nat := dbgTrace "x" fun _ => n

/-- A loop that never ends for `n > 0`, written without the word `partial`. -/
def loopsWhile (n : Nat) : Nat := Id.run do
  let mut k := n
  while k > 0 do
    k := k + 1
  return k

/-- The same with `repeat`. -/
def loopsRepeat (n : Nat) : Nat := Id.run do
  let mut k := n
  repeat
    if k == 0 then break
    k := k + 1
  return k

/-- A function that never ends for `n > 0`, written with `partial_fixpoint`. -/
def usesPartialFixpoint (n : Nat) : Option Nat :=
  if n = 0 then some 0 else usesPartialFixpoint (n + 1)
partial_fixpoint

/-- The function of Lean's library that `while` and `repeat` run, called by
its name. It never ends for `n > 0`. -/
def callsRepeatM (n : Nat) : Nat :=
  repeatM (m := Id) (fun k => if k == 0 then pure (.inr k) else pure (.inl (k + 1))) n

/-- A recursion of Lean's library that asks for no proof that it ends. It
never ends for `n > 0`. -/
def usesExtrinsicFix (n : Nat) : Nat :=
  WellFounded.extrinsicFix (C := fun _ => Nat) (fun _ _ => True)
    (fun k recur => if k == 0 then 0 else recur (k + 1) trivial) n

/-- A stream that never ends. -/
structure Counter where
  next : Nat

instance : Std.Stream Counter Nat where
  next? c := some (c.next, ⟨c.next + 1⟩)

/-- A `for` loop over that stream. It never ends for `n > 0`. -/
def loopsOverAStream (n : Nat) : Nat := Id.run do
  for k in (⟨n⟩ : Counter) do
    if k == 0 then return k
  return 0

/-- A number as text. Lean's library runs a faster function in the place of
`Nat.repr`, which is on the list `trustedInLibrary`. -/
def writesANumber (n : Nat) : String := toString n

/-- A function that reaches C functions of Lean's library, which are opaque as
well. Their code is not hidden in the sense of `runsHiddenCode`. -/
def usesCFunctions (text : Std.Format) : Std.Format := text.bracket "(" ")"

/-- A default argument that Lean finds by a tactic. Lean stores the tactic as
a piece of syntax, in a declaration of its own. That is no macro, and the
search into Lean's library does not look into it. -/
def picksOne (xs : List Nat) (i : Nat) (h : i < xs.length := by decide) : Nat := xs[i]

/-- Sorting a list reaches no hidden code. (The sorting function of Lean's
library has such default arguments.) -/
def sortsAList (xs : List Nat) : List Nat := xs.mergeSort

/-- A macro. Core and Proofs may hold none. -/
macro "audit_specimen_zero" : term => `(0)

/-- Notation: a parser, a macro and an unexpander. -/
notation:65 lhs " audit_specimen_plus " rhs => Nat.add lhs rhs

/-- A type with two cases: Lean generates `Two.ctorIdx` for it, which is
exempt. -/
inductive Two where
  | first | second

/-- The names of Lean's two helpers, written by hand in front of a type with
one case. Lean then generates none of its own. These two have a place in this
file, so they are not exempt. -/
unsafe def Single.ctorIdx._impl (n : Nat) : Nat := n

@[implemented_by Single.ctorIdx._impl] def Single.ctorIdx (n : Nat) : Nat := n

structure Single where
  value : Nat

/-- The same two names in front of another type with one case, written by a
macro in such a way that they have no place in this file. They are not exempt
either: this `_impl` does not do what Lean's own does (`isGeneratedImpl`). -/
macro "audit_specimen_impl" : command =>
  Lean.MonadRef.withRef Lean.Syntax.missing
    `(unsafe def $(Lean.mkIdent `Lone.ctorIdx._impl) (n : Nat) : Nat := n)

macro "audit_specimen_ctorIdx" : command =>
  Lean.MonadRef.withRef Lean.Syntax.missing
    `(@[implemented_by $(Lean.mkIdent `Lone.ctorIdx._impl)]
      def $(Lean.mkIdent `Lone.ctorIdx) (n : Nat) : Nat := n)

audit_specimen_impl
audit_specimen_ctorIdx

structure Lone where
  value : Nat

/-- A type with two cases whose helper is tied to other code by an attribute.
Lean's own helper is exempt. This one is not: the program would run
`otherCode` in its place. -/
inductive Swapped where
  | first | second

def otherCode (_ : Swapped) : Nat := 7

attribute [implemented_by otherCode] Swapped.ctorIdx

/-- A type without cases. Lean generates the two helpers for it as well, and
they are exempt. -/
inductive Never : Type

/-- A type with a parameter that is a number. Lean's own helper names `Nat`
in the type of its argument, and it is exempt all the same. -/
inductive WithNumber (n : Nat) where
  | first | second

/-- A declaration whose value the program would take from other code when it
starts. -/
def otherValue : IO Nat := pure 5

@[init otherValue] def takenFromOtherCode : Nat := 0

/-- A definition of the type `Lean.Syntax` that somebody wrote, with a loop in
it. It is a definition like any other, and the search goes into it. -/
def loopsInSyntax : Lean.Syntax :=
  Lean.Syntax.atom .none (toString (usesExtrinsicFix 1))

/-- An instance of `BEq` that says "equal" of any two values. (No value of
this type exists, so the instance does no harm here.) -/
instance lyingComparison : BEq (Fin 0 × Fin 0) := ⟨fun _ _ => true⟩

/-- An instance for one of Lean's own types. (No value of this type exists
either.) -/
instance foreignInstance : Repr (Fin 0 × Fin 0 × Fin 0) := ⟨fun _ _ => "x"⟩

/-- A name for the class `BEq` of one type. Lean looks for an instance through
an abbreviation. -/
abbrev HiddenClass := BEq (Fin 0 × Fin 0 × Fin 0 × Fin 0)

/-- An instance of `BEq` whose type, as it is written, does not hold the word. -/
instance hiddenComparison : HiddenClass := ⟨fun _ _ => true⟩

/-- An instance for one of Lean's own types that names Core among its
arguments only. -/
instance foreignBehindAnArgument [Inhabited VeriMol.Mol] :
    Repr (Fin 0 × Fin 0 × Fin 0 × Fin 0 × Fin 0) := ⟨fun _ _ => "x"⟩

/-- A name for one of Lean's own types that takes something of Core and does
not use it. -/
abbrev Unused (_ : VeriMol.Mol → Nat) := Fin 0 × Fin 0 × Fin 0 × Fin 0 × Fin 0 × Fin 0

/-- An instance for one of Lean's own types: the name of Core in its type goes
away when the abbreviation is written out. -/
instance foreignBehindAnAbbreviation : Repr (Unused fun _ => 0) := ⟨fun _ _ => "x"⟩

/-- An instance for two of Lean's own types that names Core in an output
place of its class only. -/
instance foreignWithCoreAsOutput : HAppend (Fin 0) (Fin 0) (Option VeriMol.Mol) := ⟨fun _ _ => none⟩

/-- A class that takes a class of Lean's library in. Lean makes an instance of
`Ord` from it, for every type. -/
class TakesOrdIn (α : Type) extends Ord α

/-- An instance with an output place: Core stands in a place that counts, so
it is fine. (No value of the type `Fin 0` exists.) -/
instance fineWithAnOutput : HAppend VeriMol.Mol (Fin 0) Nat := ⟨fun _ _ => 0⟩

/-- An instance for a type that is made with a type of Core: it is fine. (No
value of this type exists.) -/
instance fineInstance : Repr (VeriMol.Mol × Fin 0) := ⟨fun _ _ => "x"⟩

/-- An instance with an argument, for a type that is made from the argument
with something of Core: it is fine as well. -/
instance fineInstanceWithAnArgument (mol : VeriMol.Mol) : Inhabited (Fin (mol.atoms.length + 1)) :=
  ⟨0⟩

/-- A theorem with a name that looks like the name of a generated helper. It is
a written theorem all the same. -/
theorem _looksGenerated : True := trivial

/-- A theorem that uses the `sorry` of `usesSorry`. -/
theorem restsOnSorry : usesSorry = usesSorry := rfl

/-! Specimens for the fingerprints. -/

def Small (n : Nat) : Prop := n < 5

/-- The same type as `Small`, but another content. -/
def SmallToo (n : Nat) : Prop := n < 6

def double (n : Nat) : Nat := n + n

def IsDouble (n : Nat) : Prop := ∃ k, n = double k

structure Pair where
  left : Nat
  right : Nat

theorem aboutAFunction : ∀ n, Small (double n) → True := fun _ _ => trivial

theorem aboutADefinition : ∀ n, IsDouble n → True := fun _ _ => trivial

theorem aboutAType : ∀ p : Pair, p.left = p.left := fun _ => rfl

/-- Two statements that differ only in which case of their `match` is which.
Lean puts that into a helper for each of them. -/
theorem aboutAMatch : ∀ b : Bool, (match b with | true => 0 | false => 1) ≤ 1 := by
  intro b; cases b <;> decide

theorem aboutAMatchToo : ∀ b : Bool, (match b with | false => 0 | true => 1) ≤ 1 := by
  intro b; cases b <;> decide

end SelfTest

/-- Each specimen with the problem that `coreProblems` must report for it
(`none`: it must report nothing). -/
def coreSpecimens : List (Name × Option String) := [
  (``SelfTest.clean, none),
  (``SelfTest.isPartial, some "is opaque (this is what `partial` produces)"),
  (``SelfTest.isUnsafe, some "is unsafe"),
  (``SelfTest.usesImplementedBy, some "uses @[implemented_by]"),
  (``SelfTest.usesExtern, some "uses @[extern]"),
  (``SelfTest.isAxiom, some "is an axiom"),
  (``SelfTest.usesAxiom, some "depends on the axiom Audit.SelfTest.isAxiom"),
  (``SelfTest.usesSorry, some "contains sorry"),
  (``SelfTest.canPanic, some "mentions List.head!, which can panic"),
  (``SelfTest.canPanicToo, some "mentions GetElem?.getElem!, which can panic"),
  (``SelfTest.panics, some "mentions panicWithPosWithDecl, which can panic"),
  (``SelfTest.doesOutput, some "mentions IO.println, which does input or output"),
  (``SelfTest.hasSideEffect, some "mentions dbgTrace, which has a hidden side effect"),
  (``SelfTest.loopsWhile, some "mentions Lean.Loop.mk, which is a `while` or `repeat` loop, which need not end"),
  (``SelfTest.loopsRepeat, some "mentions Lean.Loop.mk, which is a `while` or `repeat` loop, which need not end"),
  (``SelfTest.usesPartialFixpoint,
    some "mentions Lean.Order.fix, which belongs to `partial_fixpoint`, which defines a function that need not end"),
  (``SelfTest.loopsOverAStream,
    some "mentions Std.instForInOfMonadOfStream, which is a `for` loop over a stream, which need not end"),
  (``SelfTest.Two.ctorIdx, none),
  (``SelfTest.Single.ctorIdx, some "uses @[implemented_by]"),
  (``SelfTest.Single.ctorIdx._impl, some "is unsafe"),
  (`Audit.SelfTest.Lone.ctorIdx, some "uses @[implemented_by]"),
  (`Audit.SelfTest.Lone.ctorIdx._impl, some "is unsafe"),
  (``SelfTest.Swapped.ctorIdx, some "uses @[implemented_by]"),
  (``SelfTest.Never.ctorIdx, none),
  (`Audit.SelfTest.Never.ctorIdx._impl, none),
  (``SelfTest.picksOne, none),
  (`Audit.SelfTest.picksOne._auto_1, none),
  (``SelfTest.WithNumber.ctorIdx, none),
  (`Audit.SelfTest.WithNumber.ctorIdx._impl, none),
  (``SelfTest.takenFromOtherCode,
    some "is tied to code that runs when the program starts (@[init])"),
  (``SelfTest.lyingComparison,
    some beqInstanceProblem),
  (``SelfTest.foreignInstance,
    some foreignInstanceProblem),
  (``SelfTest.hiddenComparison,
    some beqInstanceProblem),
  (``SelfTest.foreignBehindAnArgument,
    some foreignInstanceProblem),
  (``SelfTest.foreignBehindAnAbbreviation,
    some foreignInstanceProblem),
  (``SelfTest.foreignWithCoreAsOutput,
    some foreignInstanceProblem),
  (``SelfTest.TakesOrdIn.toOrd,
    some foreignInstanceProblem),
  (``SelfTest.fineWithAnOutput, none),
  (``SelfTest.fineInstance, none),
  (``SelfTest.fineInstanceWithAnArgument, none)
]

/-- Each specimen with the end of the name of the declaration of Lean's
library that `hiddenCodeReached` must find from it (`none`: it must find
nothing). -/
def reachSpecimens : List (Name × Option String) := [
  (``SelfTest.clean, none),
  (``SelfTest.writesANumber, none),
  (``SelfTest.usesCFunctions, none),
  (``SelfTest.picksOne, none),
  (`Audit.SelfTest.picksOne._auto_1, none),
  (``SelfTest.sortsAList, none),
  (``SelfTest.loopsInSyntax, some "WellFounded.extrinsicFix"),
  (``SelfTest.loopsWhile, some "repeatM"),
  (``SelfTest.loopsRepeat, some "repeatM"),
  (``SelfTest.callsRepeatM, some "repeatM"),
  (``SelfTest.usesExtrinsicFix, some "WellFounded.extrinsicFix"),
  (``SelfTest.loopsOverAStream, some "Std.Stream.forIn.visit")
]

/-- Each specimen with the problem that `codeProblems` must report for it, as
it is asked for the declarations of `Main` (`none`: it must report nothing). -/
def codeSpecimens : List (Name × Option String) := [
  (``SelfTest.clean, none),
  (``SelfTest.doesOutput, none),
  (``SelfTest.isPartial, some "is opaque (this is what `partial` produces)"),
  (``SelfTest.isUnsafe, some "is unsafe"),
  (``SelfTest.usesImplementedBy, some "uses @[implemented_by]"),
  (``SelfTest.usesExtern, some "uses @[extern]"),
  (``SelfTest.takenFromOtherCode,
    some "is tied to code that runs when the program starts (@[init])")
]

/-- Each specimen with the problem that `proofsProblems` must report for it
(`none`: it must report nothing). -/
def proofsSpecimens : List (Name × Option String) := [
  (``SelfTest.clean, none),
  (``SelfTest.usesSorry, none),
  (``SelfTest.isAxiom, some "is an axiom"),
  (``SelfTest.usesAxiom, some "depends on the axiom Audit.SelfTest.isAxiom"),
  (``SelfTest.usesNativeDecide,
    some "depends on the axiom Audit.SelfTest.usesNativeDecide._native.native_decide.ax_1_1")
]

/-- Runs the self-test. Returns where the checker went wrong: a violation
that it failed to detect, or something harmless that it reported. -/
def selfTestFailures : CoreM (Array String) := do
  let mut failures := #[]
  let fail (failures : Array String) (what : String) :=
    failures.push s!"the checker's self-test failed: {what}"
  -- Rules 3 and 5.
  for (specimen, expected) in coreSpecimens do
    let reported ← coreProblems specimen
    match expected with
    | none =>
      unless reported.isEmpty do
        failures := fail failures s!"{specimen} is fine, but it was reported: {reported}"
    | some problem =>
      unless reported.contains problem do
        failures := fail failures s!"{specimen} was not reported as \"{problem}\""
  -- Rule 4: the five checks that `Main` shares with Core.
  for (specimen, expected) in codeSpecimens do
    let reported ← codeProblems specimen
    match expected with
    | none =>
      unless reported.isEmpty do
        failures := fail failures s!"{specimen} is fine in Main, but it was reported: {reported}"
    | some problem =>
      unless reported.contains problem do
        failures := fail failures s!"{specimen} was not reported in Main as \"{problem}\""
  -- Rules 3 and 9: the three files that may hold import lines only, and a
  -- file under `VeriMol/` that belongs to neither library.
  unless (rootFileProblems core core #[]).isEmpty
      && (rootFileProblems `VeriMol.Core.Mol core #[`VeriMol.Mol]).isEmpty do
    failures := fail failures "a root file without declarations, or an ordinary file, was reported"
  unless (rootFileProblems proofs proofs #[`VeriMol.anything]).size == 1
      && (rootFileProblems both both #[`VeriMol.anything]).size == 1 do
    failures := fail failures "a declaration in a root file was not reported"
  unless [both, core, `VeriMol.Core.Mol, proofs, `VeriMol.Proofs.Read].all
      (fun file => (strayFileProblems file).isEmpty) do
    failures := fail failures "a root file or a file of a library was reported as belonging to neither"
  unless [`VeriMol.Extra, `VeriMol.CoreExtra, `VeriMol.Extra.Core].all
      (fun file => (strayFileProblems file).size == 1) do
    failures := fail failures "a file under VeriMol/ that belongs to neither library was not reported"
  let env ← getEnv
  -- Rule 3: what a declaration reaches in Lean's library.
  for (specimen, expected) in reachSpecimens do
    let starts := ((← startsOf core #[specimen]).toList.map (·.1)).toArray
    let ends := ((← hiddenCodeReached core starts).2.filterMap (·.getLast?)).toList
    match expected with
    | none =>
      unless ends.isEmpty do
        failures := fail failures
          s!"{specimen} reaches no function with hidden code, but this was reported: {ends}"
    | some name =>
      unless ends.any (·.toString.endsWith name) do
        failures := fail failures
          s!"{specimen} reaches {name}, whose code is hidden, but that was not reported: {ends}"
  -- Rules 3 and 9: a macro, and the notation that comes with it. The
  -- specimens hold a declaration of each of the four kinds, and `coreProblems`
  -- must report each. The four types are written out here once more, so that
  -- the list `notationTypes` cannot lose one unnoticed.
  let specimens := env.constants.map₂.toList.filter fun (c, _) => (`Audit.SelfTest).isPrefixOf c
  for kind in [``Lean.Macro, ``Lean.ParserDescr, ``Lean.TrailingParserDescr,
      ``Lean.PrettyPrinter.Unexpander] do
    match specimens.find? fun (_, info) => info.type.isConstOf kind with
    | none =>
      failures := fail failures s!"the specimens hold no declaration of the type {kind}"
    | some (c, _) =>
      unless (← coreProblems c).contains notationProblem do
        failures := fail failures
          s!"{c}, of the type {kind}, was not reported as \"{notationProblem}\""
  if ((env.find? ``SelfTest.clean).map definesNotation).getD true then
    failures := fail failures "an ordinary function was taken for a macro"
  -- Rule 9: `sorry` outside the theorems.
  let inSpecimens (c : Name) : Bool := (`Audit.SelfTest).isPrefixOf c
  unless straySorries env inSpecimens #[``SelfTest.usesSorry] #[] == #[``SelfTest.usesSorry] do
    failures := fail failures "a declaration with sorry that no theorem uses was not found"
  unless (straySorries env inSpecimens #[``SelfTest.usesSorry] #[``SelfTest.restsOnSorry]).isEmpty do
    failures := fail failures "a declaration with sorry that a theorem with sorry uses was reported"
  -- Rule 9: `sorry` in a declaration that is written and is no theorem.
  for (specimen, expected) in [(``SelfTest.usesSorry, true), (``SelfTest.restsOnSorry, false)] do
    match env.find? specimen with
    | some info =>
      unless (← isWrittenNonTheorem specimen info) == expected do
        failures := fail failures
          s!"{specimen} was judged wrongly: is it written and no theorem? Expected {expected}"
    | none => failures := fail failures s!"the specimen {specimen} is missing"
  -- Rule 9: a written theorem counts whatever its name looks like, and a
  -- generated helper does not.
  match env.find? ``SelfTest._looksGenerated with
  | some info =>
    unless ← isWrittenTheorem ``SelfTest._looksGenerated info do
      failures := fail failures "a written theorem whose name begins with an underscore was taken for a generated one"
  | none => failures := fail failures "the specimen _looksGenerated is missing"
  match env.find? `Audit.SelfTest.aboutAMatch.match_1 with
  | some info =>
    if ← isWritten info.name then
      failures := fail failures "the generated helper of a `match` was taken for a written declaration"
  | none => failures := fail failures "the helper of the `match` of the specimen aboutAMatch is missing"
  -- Rule 9: axioms in Proofs.
  for (specimen, expected) in proofsSpecimens do
    let reported ← match (← getEnv).find? specimen with
      | some info => pure (proofsProblems info (← collectAxioms specimen))
      | none => pure #[]
    match expected with
    | none =>
      unless reported.isEmpty do
        failures := fail failures s!"{specimen} is fine in Proofs, but it was reported: {reported}"
    | some problem =>
      unless reported.contains problem do
        failures := fail failures s!"{specimen} was not reported in Proofs as \"{problem}\""
  -- Rule 2. A file of Core may import Lean's base library and files of
  -- Core: not a file of Proofs, not the file that stands for both libraries,
  -- and not a file whose name only begins like Core's.
  unless (importProblems `VeriMol.Core.X #[`Init, `Init.Data.List, core, `VeriMol.Core.Y] [`Init, core]).isEmpty do
    failures := fail failures "allowed imports were reported"
  unless (importProblems `VeriMol.Core.X #[`Init, `Std, `VeriMol.Proofs.Y, both, `VeriMol.CoreExtra]
      [`Init, core]).size == 4 do
    failures := fail failures "a forbidden import was not reported"
  -- Rule 3: the list of what Core may mention.
  unless (notAllowedInCore allowedInCore).isEmpty do
    failures := fail failures "names on the list of Core were reported"
  unless notAllowedInCore [``List.map, ``IO.println, ``Coe.mk, ``MonadStateOf]
      == [``IO.println, ``Coe.mk, ``MonadStateOf] do
    failures := fail failures "names that are not on the list of Core were not reported"
  unless (notNeededInCore allowedInCore).isEmpty
      && notNeededInCore (allowedInCore.drop 1) == allowedInCore.take 1 do
    failures := fail failures "a name of the list of Core that Core does not mention was not reported"
  unless (allowedInCore.zip (allowedInCore.drop 1)).all fun (a, b) => a.toString < b.toString do
    failures := fail failures "the list of what Core may mention is not in order, or holds a name twice"
  for n in allowedInCore do
    if let some why := forbiddenReference n then
      failures := fail failures s!"the list of what Core may mention holds {n}, which {why}"
  -- The check as `run` makes it, on a specimen that mentions a name outside
  -- the list, and on a list with one name too many.
  let ofTheSpecimen := (← startsOf core #[``SelfTest.doesOutput]).toList
  unless (listProblems ofTheSpecimen).contains (notOnTheList ``SelfTest.doesOutput ``IO.println) do
    failures := fail failures "a declaration that mentions a name outside the list of Core was not reported"
  unless listProblems ((allowedInCore.drop 1).map fun n => (n, ``SelfTest.clean))
      == (allowedInCore.take 1).toArray.map notMentioned do
    failures := fail failures "a list of Core with one name too many was not reported as that"
  -- Rule 5: the instances that Lean recorded for the files of Core are read.
  -- Core has instances of its own, so if none were found, the check would be
  -- blind. And an instance that is no declaration of Core is told apart.
  if (registeredInstances (← getEnv) core).isEmpty then
    failures := fail failures "no instance was found in Lean's record for the files of Core"
  unless foreignInstances (fun n => n == `VeriMol.own)
      #[(`VeriMol.Core.File, `VeriMol.own), (`VeriMol.Core.File, ``Nat.decEq)]
      == #[(`VeriMol.Core.File, ``Nat.decEq)] do
    failures := fail failures "an instance that is no declaration of Core was not told apart"
  -- Rule 4.
  unless (notAllowedInMain
      [``IO.print, ``VeriMol.run, ``VeriMol.Output, ``VeriMol.Output.stdout, ``VeriMol.Output.stderr,
        ``VeriMol.Output.exitCode, `main.helper] #[`main.helper]).isEmpty do
    failures := fail failures "allowed names in Main were reported"
  unless notAllowedInMain
        [``ite, ``IO.FS.readFile, ``List.head?, ``IO.getStdin, ``IO.FS.Stream.getLine,
          ``IO.FS.Stream.putStr, ``IO.FS.Stream.mk] #[] ==
      [``ite, ``IO.FS.readFile, ``List.head?, ``IO.getStdin, ``IO.FS.Stream.getLine,
        ``IO.FS.Stream.putStr, ``IO.FS.Stream.mk] do
    failures := fail failures "forbidden names in Main were not reported"
  -- Of Core, `Main` may mention `VeriMol.run` and its answer, and nothing
  -- else: not the reader, not the way an answer is made, not a name that
  -- Core might get one day.
  unless notAllowedInMain
        [``VeriMol.read, ``VeriMol.write, ``VeriMol.Output.ok, ``VeriMol.Output.error, ``VeriMol.Output.mk,
          `VeriMol.somethingNew] #[] ==
      [``VeriMol.read, ``VeriMol.write, ``VeriMol.Output.ok, ``VeriMol.Output.error, ``VeriMol.Output.mk,
        `VeriMol.somethingNew] do
    failures := fail failures "a declaration of Core other than VeriMol.run and its answer was not reported in Main"
  -- Rule 4: the two lists hold nothing that `Main` does not mention. And no
  -- name stands on them twice: that is asked of the lists themselves.
  let bothLists := ofCoreInMain ++ allowedInMain
  unless (notNeededInMain bothLists).isEmpty do
    failures := fail failures "a name of the lists for Main was reported although Main mentions it"
  unless notNeededInMain (bothLists.filter (· != ``IO.eprint)) == [``IO.eprint]
      && notNeededInMain (bothLists.filter (· != ``VeriMol.Output.stderr)) == [``VeriMol.Output.stderr] do
    failures := fail failures "a name of the lists for Main that Main does not mention was not reported"
  unless bothLists.eraseDups.length == bothLists.length do
    failures := fail failures "a name stands twice on the lists Audit.ofCoreInMain and Audit.allowedInMain"
  -- Rule 4: `Main.lean` declares one declaration, and it is the approved one.
  -- Tried on specimens in the place of `main` and of its approved copy.
  let entry := ``SelfTest.clean
  let approved := ``SelfTest.cleanAgain
  unless (mainProblems env entry approved #[entry]).isEmpty do
    failures := fail failures "a file with one declaration, which is the approved one, was reported as Main"
  unless (mainProblems env entry approved #[entry, ``SelfTest.double]).size == 1 do
    failures := fail failures "a second declaration in Main.lean was not reported"
  unless (mainProblems env entry ``SelfTest.double #[entry]).size == 1
      && (mainProblems env entry ``SelfTest.exportedTwin #[entry]).size == 1 do
    failures := fail failures "a main with another body than the approved one was not reported"
  -- The same body with another type: only the type tells the two specimens
  -- apart, and the first line makes sure of that.
  match env.find? ``SelfTest.zeroAsNat, env.find? ``SelfTest.zeroAsOtherNat with
  | some (.defnInfo a), some (.defnInfo b) =>
    unless a.value == b.value && !(a.type == b.type) do
      failures := fail failures "the two specimens for the type of main do not have one body and two types"
  | _, _ => failures := fail failures "a specimen for the type of main is missing"
  unless (mainProblems env ``SelfTest.zeroAsNat ``SelfTest.zeroAsOtherNat #[``SelfTest.zeroAsNat]).size == 1 do
    failures := fail failures "a main with another type than the approved one was not reported"
  unless (mainProblems env entry approved #[]).size == 1 do
    failures := fail failures "a main that is not declared in Main.lean was not reported"
  unless (mainProblems env `Audit.SelfTest.noSuchDeclaration approved #[]).size == 1
      && (mainProblems env ``SelfTest.aboutAFunction approved #[``SelfTest.aboutAFunction]).size == 1
      && (mainProblems env entry `Audit.SelfTest.noSuchDeclaration #[entry]).size == 1 do
    failures := fail failures "a main or an approved copy that is missing, or no definition, was not reported"
  unless (mainProblems env ``SelfTest.exported ``SelfTest.exportedTwin #[``SelfTest.exported]).size == 1 do
    failures := fail failures "a main with another name in the C code (@[export]) was not reported"
  -- The approved copy mentions exactly the names of the two lists.
  match env.find? ``approvedMain with
  | some info =>
    unless (notNeededInMain info.getUsedConstantsAsSet.toList).isEmpty
        && (notAllowedInMain info.getUsedConstantsAsSet.toList #[]).isEmpty do
      failures := fail failures "the approved copy of main mentions other names than the two lists hold"
  | none => failures := fail failures "there is no approved copy of main"
  -- Rule 9: what a fingerprint covers besides the statement.
  let coverCases : List (String × Name × List Name) := [
    ("a definition that produces a statement is covered, a function that is merely mentioned is not",
      ``SelfTest.aboutAFunction, [``SelfTest.Small]),
    ("a function inside a covered definition is covered",
      ``SelfTest.aboutADefinition, [``SelfTest.IsDouble, ``SelfTest.double]),
    ("a type is covered",
      ``SelfTest.aboutAType, [``SelfTest.Pair]),
    ("the helper of a `match` in a statement is covered",
      ``SelfTest.aboutAMatch, [`Audit.SelfTest.aboutAMatch.match_1])
  ]
  for (what, specimen, expected) in coverCases do
    let covered := match env.find? specimen with
      | some info => (meaningOf env inSpecimens info.type).toList
      | none => []
    unless covered == expected do
      failures := fail failures s!"{what}: the fingerprint of {specimen} covers {covered}"
  let contentOf (c : Name) : Option UInt64 := (env.find? c).map (contentFingerprint env)
  if contentOf ``SelfTest.Small == contentOf ``SelfTest.SmallToo then
    failures := fail failures "two definitions with different content have the same fingerprint"
  if let some info := env.find? ``SelfTest.aboutAFunction then
    if fingerprint env info.type #[``SelfTest.Small] == fingerprint env info.type #[``SelfTest.SmallToo] then
      failures := fail failures "the fingerprint of a theorem ignores the definition it rests on"
    unless isAboutOf env inSpecimens info.type #[``SelfTest.Small] == #[``SelfTest.double] do
      failures := fail failures "the function that a statement is about was not found"
  if contentOf `Audit.SelfTest.aboutAMatch.match_1 == contentOf `Audit.SelfTest.aboutAMatchToo.match_1 then
    failures := fail failures
      "two helpers of a `match` whose cases stand in another order have the same fingerprint"
  -- Rule 9: one made-up ledger line against one made-up finding.
  let thm (fingerprint : UInt64) (hasSorry : Bool) : Array Found :=
    #[{ name := `T, fingerprint := fingerprint, restsOn := #[], hasSorry := hasSorry, axioms := #[] }]
  let ledgerCases : List (String × List Entry × Array Found × Nat) := [
    ("a ledger that agrees was reported", [⟨`T, 1, .proven⟩], thm 1 false, 0),
    ("an agreeing open theorem was reported", [⟨`T, 1, .stillOpen⟩], thm 1 true, 0),
    ("a proven helper lemma outside the ledger was reported", [], thm 1 false, 0),
    ("a deleted theorem was not reported", [⟨`T, 1, .proven⟩], #[], 1),
    ("a changed fingerprint was not reported", [⟨`T, 1, .proven⟩], thm 2 false, 1),
    ("sorry in a theorem recorded as proven was not reported", [⟨`T, 1, .proven⟩], thm 1 true, 1),
    ("a proven theorem recorded as open was not reported", [⟨`T, 1, .stillOpen⟩], thm 1 false, 1),
    ("sorry outside the ledger was not reported", [], thm 1 true, 1),
    ("two theorems with one name of the ledger were not reported",
      [⟨`T, 1, .proven⟩], thm 1 false ++ thm 1 false, 1)
  ]
  for (what, ledger, found, expected) in ledgerCases do
    unless (ledgerProblems ledger found).size == expected do
      failures := fail failures what
  return failures

/-! ## Running everything -/

/-- Runs the self-test and every check. Fails with the list of problems, or
prints the report. -/
def run : CommandElabM Unit := do
  let env ← getEnv
  let mut problems ← liftCoreM selfTestFailures

  -- The file that stands for both libraries holds import lines only, and no
  -- file under `VeriMol/` stands outside the two libraries (rules 3 and 9).
  for (file, record) in filesOf env both do
    if file == both then
      for problem in importProblems file (record.imports.map (·.module)) [`Init, core, proofs] do
        problems := problems.push problem
    for problem in rootFileProblems file both record.constNames ++ strayFileProblems file do
      problems := problems.push problem

  -- Core: rules 2, 3 and 5.
  for (file, record) in filesOf env core do
    for problem in importProblems file (record.imports.map (·.module)) [`Init, core] do
      problems := problems.push s!"Core: {problem}"
    for problem in rootFileProblems file core record.constNames do
      problems := problems.push s!"Core: {problem}"
  let coreDeclarations := declarationsOf env core
  for c in coreDeclarations do
    for problem in ← liftCoreM (coreProblems c) do
      problems := problems.push s!"Core: {c} {problem}"
  -- Core, rule 3: what its declarations mention of Lean's library, each with
  -- one declaration of Core that mentions it (`startsOf`), is exactly the
  -- list `allowedInCore`.
  let mentionedByCore ← liftCoreM (startsOf core coreDeclarations)
  for problem in listProblems mentionedByCore.toList do
    problems := problems.push problem
  -- Core, rule 5: no file of Core makes a declaration of Lean's library an
  -- instance.
  for (file, name) in foreignInstances (declaredIn env core) (registeredInstances env core) do
    problems := problems.push
      (s!"Core: the file {file} makes {name} an instance, and {name} is no declaration of Core. A file "
        ++ "of Core may not change which instances Lean finds for its own types (rule 5)")
  -- Core, rule 3: what its declarations reach in Lean's library, starting
  -- from what they mention.
  let (reachedByCore, hidden) ←
    liftCoreM (hiddenCodeReached core (mentionedByCore.toList.map (·.1)).toArray)
  for chain in hidden do
    let some first := chain.head? | continue
    let some last := chain.getLast? | continue
    problems := problems.push
      (s!"Core: {(mentionedByCore.find? first).getD first} reaches {last}, whose code is hidden, so "
        ++ s!"it need not end (through {chain}). If this function of Lean's library is known to "
        ++ "end, it can be added to Audit.trustedInLibrary")

  -- Main: rule 4.
  let mainDeclarations := declarationsOf env `Main
  for (file, record) in filesOf env `Main do
    for problem in importProblems file (record.imports.map (·.module)) [`Init, core] do
      problems := problems.push s!"Main: {problem}"
  for c in mainDeclarations do
    for problem in ← liftCoreM (codeProblems c) do
      problems := problems.push s!"Main: {c} {problem} (rule 4)"
    let some info := env.find? c | continue
    for n in notAllowedInMain info.getUsedConstantsAsSet.toList mainDeclarations do
      problems := problems.push
        (s!"Main: {c} mentions {n}, which is on neither of the lists Audit.ofCoreInMain and "
          ++ "Audit.allowedInMain (rule 4)")
  -- Main, rule 4: the file declares `main` and nothing else, and `main` is
  -- the function that the author has approved.
  for problem in mainProblems env `main ``approvedMain mainDeclarations do
    problems := problems.push problem
  -- Main, rule 4: the two lists hold what `Main` mentions and nothing else.
  let mentionedByMain := mainDeclarations.toList.flatMap fun c =>
    ((env.find? c).map (·.getUsedConstantsAsSet.toList)).getD []
  for n in notNeededInMain mentionedByMain do
    problems := problems.push
      (s!"Main: the lists Audit.ofCoreInMain and Audit.allowedInMain hold {n}, which Main does not "
        ++ "mention (rule 4). Take it off its list in Audit.lean")

  -- Proofs: rule 9. No file may import anything that could change Lean's
  -- records behind the checker's back.
  for (file, record) in filesOf env proofs do
    for problem in importProblems file (record.imports.map (·.module)) [`Init, core, proofs] do
      problems := problems.push s!"Proofs: {problem}"
    for problem in rootFileProblems file proofs record.constNames do
      problems := problems.push s!"Proofs: {problem}"
  let mut found : Array Found := #[]
  -- The declarations with `sorry`: the written theorems, and the others
  -- that are not reported at once.
  let mut openTheorems : Array Name := #[]
  let mut otherSorries : Array Name := #[]
  for c in declarationsOf env proofs do
    let some info := env.find? c | continue
    let axioms ← liftCoreM (collectAxioms c)
    for problem in proofsProblems info axioms do
      problems := problems.push s!"Proofs: {c} {problem}"
    if definesNotation info then
      problems := problems.push s!"Proofs: {c} {notationProblem}"
    if let some problem := initProblem env c then
      problems := problems.push s!"Proofs: {c} {problem}"
    if info matches .axiomInfo _ then continue
    -- A `private` theorem is stored under a longer internal name; use the
    -- name it has in the file.
    let name := privateToUserName c
    let hasSorry := axioms.contains ``sorryAx
    if ← liftCoreM (isWrittenTheorem c info) then
      let inScope := fun d => declaredIn env core d || declaredIn env proofs d
      let covered := meaningOf env inScope info.type
      let written ← liftCoreM <| covered.filterM isWritten
      found := found.push
        { name, fingerprint := fingerprint env info.type covered, restsOn := written,
          isAbout := isAboutOf env inScope info.type covered, hasSorry, axioms }
      if hasSorry then
        openTheorems := openTheorems.push c
    else if hasSorry then
      if ← liftCoreM (isWrittenNonTheorem c info) then
        problems := problems.push s!"Proofs: {name} contains sorry but is not a theorem"
      else
        otherSorries := otherSorries.push c
  for c in straySorries env (declaredIn env proofs) otherSorries openTheorems do
    problems := problems.push
      (s!"Proofs: {privateToUserName c} contains sorry, but it is no theorem that is written in a "
        ++ "file, and no such theorem with sorry uses it")
  for problem in ledgerProblems ledger found do
    problems := problems.push s!"Ledger: {problem}"

  unless problems.isEmpty do
    throwError "Audit failed:\n{"\n".intercalate (problems.toList.map ("  - " ++ ·))}"

  let inLedger := found.filter fun thm => ledger.any (·.name == thm.name)
  let stillOpen := inLedger.filter (·.hasSorry)
  let mut report := "Audit passed, and so did the checker's self-test.\n\n"
  report := report ++ s!"Core (rules 2, 3 and 5): {coreDeclarations.size} declarations checked, no problems.\n"
  report := report ++ s!"  They mention {mentionedByCore.size} declarations of Lean's library, which are "
    ++ s!"exactly the {allowedInCore.length} names of the list Audit.allowedInCore, and reach "
    ++ s!"{reachedByCore} through the bodies of its functions. None of these has hidden code, which is how "
    ++ "a function that need not end is made, apart from the helpers that Lean generates for a type "
    ++ s!"and from the list Audit.trustedInLibrary: {trustedInLibrary}. (Not followed: the faster "
    ++ "functions that Lean's compiler puts in the place of some functions of its library.)\n"
  report := report ++ "Main (rule 4): it declares main and nothing else, and the type and the body of main "
    ++ "are those of Audit.approvedMain, the copy that the author has approved, expression for "
    ++ "expression. Of Core it mentions only VeriMol.run and its answer, and beyond Core only the names on "
    ++ s!"its allowed list; the two lists hold exactly the {ofCoreInMain.length + allowedInMain.length} "
    ++ "names that it mentions. Nothing in it is opaque, unsafe, @[implemented_by], @[extern], @[init] "
    ++ "or @[export].\n\n"
  report := report ++ s!"Ledger (rule 9): {inLedger.size} statements, "
    ++ s!"{inLedger.size - stillOpen.size} proven, {stillOpen.size} open."
  for thm in inLedger.qsort (fun a b => a.name.toString < b.name.toString) do
    if thm.hasSorry then
      report := report ++ s!"\n  open    {thm.name}  (contains sorry)"
    else
      let axiomText :=
        if thm.axioms.isEmpty then "no axioms" else s!"axioms: {thm.axioms.toList}"
      report := report ++ s!"\n  proven  {thm.name}  ({axiomText})"
    unless thm.restsOn.isEmpty do
      report := report ++ "\n            its meaning rests on: "
        ++ ", ".intercalate (thm.restsOn.toList.map toString)
    unless thm.isAbout.isEmpty do
      report := report ++ "\n            it is about, and the fingerprint does not cover: "
        ++ ", ".intercalate (thm.isAbout.toList.map fun d =>
          if declaredIn env proofs d then s!"{d} (declared under VeriMol/Proofs/)" else toString d)
  report := report ++ s!"\nHelper lemmas outside the ledger: {found.size - inLedger.size}, all proven."
  logInfo report

end Audit

run_cmd Audit.run
