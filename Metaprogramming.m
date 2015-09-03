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

ClearAll[holdToString];
SetAttributes[holdToString, {Listable}];
holdToString[h_Hold] :=
  StringTake[ToString[h], {6, -2}];

ClearAll[symbolPositions];
symbolPositions[exp_] :=
  Position[exp, _, Infinity, Heads -> True];

ClearAll[extractHeldUnique];
extractHeldUnique[exp_] :=
  exp // RightComposition[
     DeleteDuplicates[Extract[#, symbolPositions[#], Hold]] &,
     DeleteCases[#, h_Hold /; Depth[h] > 2] &,
     Cases[#, h : Hold[s_Symbol] /; Context[s] =!= "System`"] &
     ];

ClearAll[iLocalReplacementRules];
SetAttributes[iLocalReplacementRules, {HoldFirst}];
iLocalReplacementRules[exp_] :=
  Module[ {e, h, s, v},
    e = Hold[exp];
    h = extractHeldUnique[e];
    s = holdToString[h];
    v = Unique[s];
    {h, v}
  ];

ClearAll[localReplacementRules];
SetAttributes[localReplacementRules, {HoldFirst}];
localReplacementRules[exp_] :=
  Module[ {h, v, r1, r2},
    {h, v} = iLocalReplacementRules[exp];
    r1 = Thread[h -> v] /. Hold -> HoldPattern;
    r2 = Thread[v -> h];
    {r1, r2}
  ];
localReplacementRules[exp_, "In"] :=
  Thread[#1 -> #2] & @@ iLocalReplacementRules[exp] /. 
   Hold -> HoldPattern;
localReplacementRules[exp_, "Out"] :=
  Thread[#2 -> #1] & @@ iLocalReplacementRules[exp];

ClearAll[expandOnce];
SetAttributes[expandOnce, {HoldAll}];
expandOnce[e_] :=
  Module[ {v, r},
    v = extractHeldUnique[e];
    r = Flatten[v /. Hold[s_] :> DownValues[s]];
    e //. r
  ];

ClearAll[expandAll];
SetAttributes[expandAll, {HoldAll}];
expandAll[e_] :=
  FixedPoint[expandOnce, e];

(******************************************************************************)

Inline // ClearAll;
Inline ~ SetAttributes ~ {HoldAllComplete};
Inline // Options = {Definitions -> {UpValues, OwnValues, DownValues}};

Inline[f_, exp_, wrapper_ : Identity, opts : OptionsPattern[]] :=
  Module[{defTypes, rules},
    defTypes = OptionValue[Definitions];
    rules = Flatten[#[f] & /@ defTypes];
    wrapper[exp] //. rules
  ];

Inline[fList : {___}, exp_, wrapper_ : Identity, opts : OptionsPattern[]] :=
  Module[{fold},
    fold = Fold[Inline[#2, #1, wrapper, opts] &, wrapper[exp], fList];
    Nest[Identity @@ # &, fold, Length[fList]]
  ];

(******************************************************************************)

SetAttributes[HoldFlatten, {HoldAll}];
HoldFlatten[exp_] :=
  Module[ {h = HoldComplete[exp]},
    Delete[h, Position[h, Hold]] /. HoldComplete -> Hold
  ];

End[]; (* End Private Context *)

EndPackage[]