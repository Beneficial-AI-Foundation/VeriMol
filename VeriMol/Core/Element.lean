/-!
# The elements and their symbols (SPEC.md, section 15)
-/

namespace VeriMol

/-- The 118 chemical elements, in the order of their atomic numbers (SPEC.md,
section 15). Each case is named like the symbol of its element. -/
inductive Element where
  | H  | He | Li | Be | B  | C  | N  | O  | F  | Ne | Na | Mg | Al | Si | P  | S  | Cl | Ar
  | K  | Ca | Sc | Ti | V  | Cr | Mn | Fe | Co | Ni | Cu | Zn | Ga | Ge | As | Se | Br | Kr
  | Rb | Sr | Y  | Zr | Nb | Mo | Tc | Ru | Rh | Pd | Ag | Cd | In | Sn | Sb | Te | I  | Xe
  | Cs | Ba | La | Ce | Pr | Nd | Pm | Sm | Eu | Gd | Tb | Dy | Ho | Er | Tm | Yb | Lu | Hf
  | Ta | W  | Re | Os | Ir | Pt | Au | Hg | Tl | Pb | Bi | Po | At | Rn | Fr | Ra | Ac | Th
  | Pa | U  | Np | Pu | Am | Cm | Bk | Cf | Es | Fm | Md | No | Lr | Rf | Db | Sg | Bh | Hs
  | Mt | Ds | Rg | Cn | Nh | Fl | Mc | Lv | Ts | Og
  deriving DecidableEq, Repr

/-- The symbol of an element as a text: `['C', 'l']` for chlorine. -/
def Element.symbol : Element → List Char
  | .H  => ['H']       | .He => ['H', 'e']  | .Li => ['L', 'i']  | .Be => ['B', 'e']  | .B  => ['B']
  | .C  => ['C']       | .N  => ['N']       | .O  => ['O']       | .F  => ['F']       | .Ne => ['N', 'e']
  | .Na => ['N', 'a']  | .Mg => ['M', 'g']  | .Al => ['A', 'l']  | .Si => ['S', 'i']  | .P  => ['P']
  | .S  => ['S']       | .Cl => ['C', 'l']  | .Ar => ['A', 'r']  | .K  => ['K']       | .Ca => ['C', 'a']
  | .Sc => ['S', 'c']  | .Ti => ['T', 'i']  | .V  => ['V']       | .Cr => ['C', 'r']  | .Mn => ['M', 'n']
  | .Fe => ['F', 'e']  | .Co => ['C', 'o']  | .Ni => ['N', 'i']  | .Cu => ['C', 'u']  | .Zn => ['Z', 'n']
  | .Ga => ['G', 'a']  | .Ge => ['G', 'e']  | .As => ['A', 's']  | .Se => ['S', 'e']  | .Br => ['B', 'r']
  | .Kr => ['K', 'r']  | .Rb => ['R', 'b']  | .Sr => ['S', 'r']  | .Y  => ['Y']       | .Zr => ['Z', 'r']
  | .Nb => ['N', 'b']  | .Mo => ['M', 'o']  | .Tc => ['T', 'c']  | .Ru => ['R', 'u']  | .Rh => ['R', 'h']
  | .Pd => ['P', 'd']  | .Ag => ['A', 'g']  | .Cd => ['C', 'd']  | .In => ['I', 'n']  | .Sn => ['S', 'n']
  | .Sb => ['S', 'b']  | .Te => ['T', 'e']  | .I  => ['I']       | .Xe => ['X', 'e']  | .Cs => ['C', 's']
  | .Ba => ['B', 'a']  | .La => ['L', 'a']  | .Ce => ['C', 'e']  | .Pr => ['P', 'r']  | .Nd => ['N', 'd']
  | .Pm => ['P', 'm']  | .Sm => ['S', 'm']  | .Eu => ['E', 'u']  | .Gd => ['G', 'd']  | .Tb => ['T', 'b']
  | .Dy => ['D', 'y']  | .Ho => ['H', 'o']  | .Er => ['E', 'r']  | .Tm => ['T', 'm']  | .Yb => ['Y', 'b']
  | .Lu => ['L', 'u']  | .Hf => ['H', 'f']  | .Ta => ['T', 'a']  | .W  => ['W']       | .Re => ['R', 'e']
  | .Os => ['O', 's']  | .Ir => ['I', 'r']  | .Pt => ['P', 't']  | .Au => ['A', 'u']  | .Hg => ['H', 'g']
  | .Tl => ['T', 'l']  | .Pb => ['P', 'b']  | .Bi => ['B', 'i']  | .Po => ['P', 'o']  | .At => ['A', 't']
  | .Rn => ['R', 'n']  | .Fr => ['F', 'r']  | .Ra => ['R', 'a']  | .Ac => ['A', 'c']  | .Th => ['T', 'h']
  | .Pa => ['P', 'a']  | .U  => ['U']       | .Np => ['N', 'p']  | .Pu => ['P', 'u']  | .Am => ['A', 'm']
  | .Cm => ['C', 'm']  | .Bk => ['B', 'k']  | .Cf => ['C', 'f']  | .Es => ['E', 's']  | .Fm => ['F', 'm']
  | .Md => ['M', 'd']  | .No => ['N', 'o']  | .Lr => ['L', 'r']  | .Rf => ['R', 'f']  | .Db => ['D', 'b']
  | .Sg => ['S', 'g']  | .Bh => ['B', 'h']  | .Hs => ['H', 's']  | .Mt => ['M', 't']  | .Ds => ['D', 's']
  | .Rg => ['R', 'g']  | .Cn => ['C', 'n']  | .Nh => ['N', 'h']  | .Fl => ['F', 'l']  | .Mc => ['M', 'c']
  | .Lv => ['L', 'v']  | .Ts => ['T', 's']  | .Og => ['O', 'g']

/-- Every element once, in the order of the atomic numbers. -/
def Element.all : List Element := [
  .H, .He, .Li, .Be, .B, .C, .N, .O, .F, .Ne, .Na, .Mg, .Al, .Si, .P, .S, .Cl, .Ar,
  .K, .Ca, .Sc, .Ti, .V, .Cr, .Mn, .Fe, .Co, .Ni, .Cu, .Zn, .Ga, .Ge, .As, .Se, .Br, .Kr,
  .Rb, .Sr, .Y, .Zr, .Nb, .Mo, .Tc, .Ru, .Rh, .Pd, .Ag, .Cd, .In, .Sn, .Sb, .Te, .I, .Xe,
  .Cs, .Ba, .La, .Ce, .Pr, .Nd, .Pm, .Sm, .Eu, .Gd, .Tb, .Dy, .Ho, .Er, .Tm, .Yb, .Lu, .Hf,
  .Ta, .W, .Re, .Os, .Ir, .Pt, .Au, .Hg, .Tl, .Pb, .Bi, .Po, .At, .Rn, .Fr, .Ra, .Ac, .Th,
  .Pa, .U, .Np, .Pu, .Am, .Cm, .Bk, .Cf, .Es, .Fm, .Md, .No, .Lr, .Rf, .Db, .Sg, .Bh, .Hs,
  .Mt, .Ds, .Rg, .Cn, .Nh, .Fl, .Mc, .Lv, .Ts, .Og
]

/-- The ten elements whose atoms may stand without square brackets (SPEC.md,
section 4). -/
def Element.bare : List Element :=
  [.B, .C, .N, .O, .P, .S, .F, .Cl, .Br, .I]

/-- The element that has exactly this symbol, or `none` if no element has it.
`['C', 'o']` gives cobalt. `['C', 'O']` and `['c']` give `none`: the symbol must
fit letter by letter, with its capital letter. -/
def Element.ofSymbol? (symbol : List Char) : Option Element :=
  Element.all.find? (fun e => e.symbol == symbol)

/-- The lowercase symbol of this element, with which SMILES writes an atom of
an aromatic ring. Eight elements have one, as in OpenSMILES. -/
def Element.lowercaseSymbol? : Element → Option (List Char)
  | .B  => some ['b']  | .C  => some ['c']  | .N  => some ['n']  | .O  => some ['o']
  | .P  => some ['p']  | .S  => some ['s']  | .Se => some ['s', 'e']  | .As => some ['a', 's']
  | _   => none

/-- The element that has exactly this lowercase symbol, or `none` if no element
has it. -/
def Element.ofLowercaseSymbol? (symbol : List Char) : Option Element :=
  Element.all.find? (fun e => e.lowercaseSymbol? == some symbol)

end VeriMol
