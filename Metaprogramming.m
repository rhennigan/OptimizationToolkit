(* Wolfram Language package *)

BeginPackage["OptimizationToolkit`Metaprogramming`", {"OptimizationToolkit`"}];

GetSymbols  ::usage = "";
Localize    ::usage = "";
Construct   ::usage = "";
Inline      ::usage = "";
Definitions ::usage = "";
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

$heldHeads = { Hold, HoldComplete, HoldForm };

heldExpressionQ // ClearAll;
heldExpressionQ // Attributes = { HoldAllComplete };
heldExpressionQ // Options = {};

heldExpressionQ[ head_ @ ___ ] := $heldHeads ~ MemberQ ~ head;

validFormQ // ClearAll;
validFormQ // Attributes = {};
validFormQ // Options = {};

validFormQ[ formatType_ ] :=
  validFormQ @ formatType =
    Module[
        { checked },
        checked = Quiet @ Check[ Null ~ ToString ~ formatType, $Failed ];
        checked =!= $Failed
    ];

HeldToString // ClearAll;
HeldToString // Attributes = { HoldFirst };
HeldToString // Options = Options @ ToString;
HeldToString::fmtval = "`1` is not a valid format type.";

HeldToString[
    expression_? heldExpressionQ,
    form_? validFormQ ~ Optional ~ OutputForm,
    options : OptionsPattern[]
] :=
  Module[
      { headString, trimSpec, expressionString },
      headString = ToString @ Head @ expression;
      trimSpec = { StringLength @ headString + 2, -2 };
      expressionString = ToString[ expression, form, options ];
      expressionString ~ StringTake ~ trimSpec
  ];

HeldToString[
    expression_,
    form_? validFormQ ~ Optional ~ OutputForm,
    options : OptionsPattern[]
] :=
  With[
      { held = HoldComplete @ expression },
      HeldToString[ held, form, options ]
  ];

HeldToString[ _, form_, OptionsPattern[] ] :=
  Module[
      { validForm },
      validForm = validFormQ @ form;
      If[ !validForm, HeldToString::fmtval ~ Message ~ form ];
      Null /; validForm
  ];

(******************************************************************************)

Inline // ClearAll;
Inline // Attributes = { HoldAllComplete };
Inline // Options = {
    Definitions -> { UpValues, OwnValues, DownValues },
    MaxIterations -> $IterationLimit
};

Inline[
    function_,
    expression_,
    wrapper_ : Identity,
    options : OptionsPattern[]
] :=
  Module[
      { held, definitionTypes, getDefinitionList, replacementRules, replaced },
      held = HoldComplete @ expression;
      definitionTypes = OptionValue @ Definitions;
      getDefinitionList = # @ function &;
      replacementRules = getDefinitionList /@ definitionTypes // Flatten;
      Off @ ReplaceRepeated::rrlim;
      replaced = ReplaceRepeated[ held, replacementRules,
          MaxIterations -> OptionValue @ MaxIterations
      ];
      On @ ReplaceRepeated::rrlim;
      wrapper @@ replaced
  ];


iInline // ClearAll;
iInline // Attributes = { HoldAllComplete };
iInline // Options = Options @ Inline;

iInline[ expression_, function_ ] :=
  With[ { currentOptions = Options @ iInline },
      Inline[ function, expression, HoldComplete, currentOptions ]
  ];


listToHold // ClearAll;
listToHold // Attributes = { HoldAllComplete };
listToHold // Options = {};

listToHold[ { a$___ } ] := Hold @ a$;
listToHold[ list_List, All ] := Identity @@ (Hold @ list /. List -> Hold);


dropHead // ClearAll;
dropHead // Attributes = {};
dropHead // Options = {};

dropHead = Identity @@ # &;


Inline[
    functionList : { ___ },
    expression_,
    wrapper_ : Identity,
    options : OptionsPattern[]
] :=
  Module[
      { heldExpression, heldFunctions, functionCount, folded, stacked },
      heldExpression = HoldComplete @ expression;
      heldFunctions = listToHold @ functionList;
      functionCount = Length @ heldFunctions;
      iInline ~ SetOptions ~ options;
      folded = Fold[ iInline, heldExpression, heldFunctions ];
      iInline // Options = Options @ Inline;
      stacked = Nest[ dropHead, folded, functionCount ];
      wrapper @@ stacked
  ];

Inline[ f_ ][ a$___ ] := Inline[ f, a$ ];

(******************************************************************************)

SetAttributes[HoldFlatten, {HoldAll}];
HoldFlatten[exp_] :=
  Module[{h = HoldComplete[exp]},
      Delete[h, Position[h, Hold]] /. HoldComplete -> Hold
  ];

End[]; (* End Private Context *)

EndPackage[]