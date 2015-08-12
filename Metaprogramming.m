(* Wolfram Language package *)

BeginPackage["OptimizationToolkit`Metaprogramming`", {"OptimizationToolkit`"}];

Unprotect["`*"];
ClearAll["`*"];

GetSymbols  ::usage = "";
Localize    ::usage = "";
Construct   ::usage = "";
Inline      ::usage = "";
HoldFlatten ::usage = "";

Begin["`Private`"]; (* Begin Private Context *)

(******************************************************************************)

SetAttributes[holdToString, {Listable}];
holdToString[h_Hold] :=
  StringTake[ToString[h], {6, -2}];

symbolPositions[exp_] :=
  Position[exp, Except[_[___]], Heads -> False];

extractHeldUnique[e_, p_] :=
  DeleteDuplicates[Extract[e, p, Hold]];

SetAttributes[iLocalReplacementRules, {HoldFirst}];
iLocalReplacementRules[exp_] :=
  Module[ {e, p, h, s, v},
    e = Hold[exp];
    p = symbolPositions[e];
    h = extractHeldUnique[e, p];
    s = holdToString[h];
    v = Unique[s];
    {h, v}
  ];

SetAttributes[localReplacementRules, {HoldFirst}];
localReplacementRules[exp_] :=
  Module[ {h, v, r1, r2},
    {h, v} = iLocalReplacementRules[exp];
    r1 = Thread[h -> v] /. Hold -> HoldPattern;
    r2 = Thread[v -> h];
    {r1, r2}
  ];
localReplacementRules[exp_, "In"] :=
  Thread[#1 -> #2] & @@ iLocalReplacementRules[exp] /. Hold -> HoldPattern;
localReplacementRules[exp_, "Out"] :=
  Thread[#2 -> #1] & @@ iLocalReplacementRules[exp];

(******************************************************************************)

End[]; (* End Private Context *)

SetAttributes[HoldFlatten, {HoldAll}];
HoldFlatten[exp_] :=
  Module[ {h = HoldComplete[exp]},
    Delete[h, Position[h, Hold]] /. HoldComplete -> Hold
  ];

EndPackage[]