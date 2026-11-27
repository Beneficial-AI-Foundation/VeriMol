import VeriMol.Core.Text
import VeriMol.Core.Token

/-!
# Spelling tokens as text (SPEC.md, section 9)

The opposite direction of `cut`. Not every token can be spelled: the grammar
that this program reads (SPEC.md, section 4) has no way to write an atom with
ten hydrogens of its own, for example. The functions here return `none` for
such a token.
-/

namespace VeriMol

/-- The symbol of a kind of bond. -/
def BondOrder.symbol : BondOrder → Char
  | .single    => '-'
  | .double    => '='
  | .triple    => '#'
  | .quadruple => '$'
  | .aromatic  => ':'

/-- The character of a bond symbol or direction mark. -/
def BondSymbol.character : BondSymbol → Char
  | .order kind => kind.symbol
  | .up => '/'
  | .down => '\\'

/-- The stereo mark of an atom as text: `@` or `@@`. -/
def Orientation.spell : Orientation → List Char
  | .anticlockwise => ['@']
  | .clockwise => ['@', '@']

/-- The isotope in digits, nothing if there is none. -/
def spellIsotope : Option Nat → List Char
  | none => []
  | some isotope => natText isotope

/-- The stereo mark, nothing if there is none. -/
def spellMark : Option Orientation → List Char
  | none => []
  | some mark => mark.spell

/-- `H` for one hydrogen, `H` with the number for more, nothing for none. -/
def spellHydrogens (hydrogens : Nat) : List Char :=
  if hydrogens = 0 then []
  else if hydrogens = 1 then ['H']
  else 'H' :: natText hydrogens

/-- `+` or `-` for a charge of +1 or -1, the sign with the number for any
other charge, nothing for 0. -/
def spellCharge (charge : Int) : List Char :=
  if charge = 0 then []
  else (if charge < 0 then '-' else '+') ::
    (if charge.natAbs = 1 then [] else natText charge.natAbs)

/-- How an atom is written without square brackets, for the ten elements that
may stand without them (`Element.bare`). Six of them have a lowercase symbol
as well. -/
def bareSymbol? (element : Element) (aromatic : Bool) : Option (List Char) :=
  if element ∈ Element.bare then
    if aromatic then element.lowercaseSymbol? else some element.symbol
  else none

/-- An atom as text. An atom whose hydrogens are not given is written without
square brackets, and every other atom in square brackets: isotope, symbol,
stereo mark, hydrogens, charge.

`none` if the atom cannot be written:
* without square brackets, anything but a plain atom of the few elements that
  may stand without them;
* in square brackets, more than 9 hydrogens, a charge beyond +99 or -99, a
  hydrogen atom with hydrogens of its own, or an aromatic atom of an element
  that has no lowercase symbol. -/
def WrittenAtom.spell (atom : WrittenAtom) : Option (List Char) :=
  match atom.hydrogens with
  | none =>
    if atom.isotope = none ∧ atom.charge = 0 ∧ atom.mark = none then
      bareSymbol? atom.element atom.aromatic
    else none
  | some hydrogens =>
    if 9 < hydrogens ∨ 99 < atom.charge.natAbs ∨ (atom.element = .H ∧ 0 < hydrogens) then none
    else
      (if atom.aromatic then atom.element.lowercaseSymbol? else some atom.element.symbol).map
        fun symbol =>
          '[' :: (spellIsotope atom.isotope ++ symbol ++ spellMark atom.mark
            ++ spellHydrogens hydrogens ++ spellCharge atom.charge ++ [']'])

/-- A token as text. Ring numbers 0 to 9 are one digit, 10 to 99 are `%` and
two digits, and a larger one cannot be written. -/
def Token.spell : Token → Option (List Char)
  | .atom written => written.spell
  | .bond symbol => some [symbol.character]
  | .ring number =>
    if number < 10 then some (natText number)
    else if number < 100 then some ('%' :: natText number)
    else none
  | .branchOpen => some ['(']
  | .branchClose => some [')']
  | .dot => some ['.']

/-- The tokens as one text, one after the other. `none` if one of them cannot
be spelled. -/
def spell : List Token → Option (List Char)
  | [] => some []
  | token :: rest =>
    match token.spell, spell rest with
    | some first, some behind => some (first ++ behind)
    | _, _ => none

end VeriMol
