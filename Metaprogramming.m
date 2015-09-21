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

HeldWith // ClearAll;
HeldWith // Attributes = { HoldAllComplete };
HeldWith // Options = {};

CompoundWith // ClearAll;
CompoundWith // Attributes = { HoldAllComplete };
CompoundWith // Options = {};

CompoundWith[ bindings : _Set...; expression_, wrapper_ : Identity ] :=
  Module[
      {
          heldBindings, numBindings, folded,
          swapped, holdLocation, holdRemoved
      },
      heldBindings = Reverse @ HoldComplete @ bindings;
      numBindings = Length @ heldBindings;
      folded = Fold[ HeldWith, HoldComplete @ expression, heldBindings ];
      swapped = folded //. HeldWith[ e_, b_Set ] :> HeldWith[ { b }, e ];
      holdLocation = { 2 ~ ConstantArray ~ numBindings ~ Append ~ 0 };
      holdRemoved = swapped ~ Delete ~ holdLocation;
      With[ { h = holdRemoved }, wrapper @ h ] /. HeldWith -> With
  ];

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
    Module[ { checked },
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
  Module[ { headString, trimSpec, expressionString },
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
  With[ { held = HoldComplete @ expression },
      HeldToString[ held, form, options ]
  ];

HeldToString[ _, form_, OptionsPattern[] ] :=
  Module[ { validForm },
      validForm = validFormQ @ form;
      If[ !validForm, HeldToString::fmtval ~ Message ~ form ];
      Null /; validForm
  ];



(******************************************************************************)

fullInactivate // ClearAll;
fullInactivate // Attributes = {};
fullInactivate // Options = {};

fullInactivate[ h : HoldComplete[ _ ] ] :=
  Block[ { Developer`$InactivateExclusions = { { List, "Symbol" } } },
      With[ { i = Inactivate @ h }, HoldComplete @@ i ]
  ];

fullInactivate[ expression_ ] :=
  Block[ { Developer`$InactivateExclusions = { { List, "Symbol" } } },
      Inactivate[ expression ]
  ];



(******************************************************************************)

$ = Sequence[];

SequenceIdentity // ClearAll;
SequenceIdentity // Attributes = {};
SequenceIdentity // Options = {};
SequenceIdentity[ args___ ] := args;

toNull // ClearAll;
toNull // Attributes = {};
toNull // Options = {};
toNull[ ___ ] := $;



(******************************************************************************)

Inline // ClearAll;
Inline // Attributes = { HoldAllComplete };
Inline // Options    =
  {
      Definitions     -> { OwnValues, DownValues, UpValues },
      MaxIterations   -> $IterationLimit,
      "ForceSymbolic" -> False
  };

Inline[
    function_,
    expression_,
    wrapper_ : Automatic,
    options : OptionsPattern[]
] :=
  Module[

      {
          held, definitionTypes, getDefinitions, replacementRules,
          makeSymbolic, symbolicRules, replaced, wrapperFunction
      },

      held = HoldComplete @ expression;
      definitionTypes = OptionValue @ Definitions;

      getDefinitions =
        If[ Head @ function === Inactive
            ,
            With[ { f = Identity @@ function },
                With[ { def = # @ f }, Inactivate @ def ] &
            ]
            ,
            # @ function &
        ];

      replacementRules = getDefinitions /@ definitionTypes // Flatten;
      makeSymbolic = # /. Verbatim[ Blank ][ ___ ] -> Blank[] &;

      symbolicRules = If[ OptionValue @ "ForceSymbolic",
          MapAt[ makeSymbolic, replacementRules, { All, 1 } ],
          replacementRules
      ];

      Off @ ReplaceRepeated::rrlim;

      replaced = ReplaceRepeated[ held, symbolicRules,
          MaxIterations -> OptionValue @ MaxIterations
      ];

      On @ ReplaceRepeated::rrlim;
      wrapperFunction = wrapper /. Automatic -> Identity;

      wrapperFunction @@ replaced
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
    wrapper_ : Automatic,
    options : OptionsPattern[]
] :=
  Module[

      {
          heldExpression, heldFunctions, functionCount,
          folded, unstacked, wrapperFunction
      },

      heldExpression = HoldComplete @ expression;
      heldFunctions = listToHold @ functionList;
      functionCount = Length @ heldFunctions;
      iInline ~ SetOptions ~ options;
      folded = Fold[ iInline, heldExpression, heldFunctions ];
      iInline // Options = Options @ Inline;
      unstacked = Nest[ dropHead, folded, functionCount ];
      wrapperFunction = wrapper /. Automatic -> Identity;

      wrapperFunction @@ unstacked
  ];

Inline[ f_ ][ a$___ ] := Inline[ f, a$ ];

Inline /: (patt_ := Inline[ f_, exp_, a___ ]) := Inline[ f, patt := exp, a ];



(******************************************************************************)

$blanks = (Blank | BlankSequence | BlankNullSequence);

getBlankArgPattern // ClearAll;
getBlankArgPattern // Attributes = {};
getBlankArgPattern // Options = {};

getBlankArgPattern[ f_, HoldPattern[ pattern_HoldPattern :> ___ ] ] :=
  Module[ { heldPattern },

      heldPattern = pattern //. {
          f -> List,
          (b : $blanks)[ ___ ] :> b[],
          Verbatim[ Pattern ][ _, b___ ] :> b
      };

      Identity @@ heldPattern
  ];

rescopeDefinition // ClearAll;
rescopeDefinition // Attributes = {};
rescopeDefinition // Options = {};

rescopeDefinition[ definition : HoldPattern[ pattern_HoldPattern :> ___ ] ] :=
  Module[ { symbolPositions, symbolPatterns, symbolStrings, newSymbols, rules },
      symbolPositions = # ~ Append ~ 1 & /@ Position[ pattern, _Pattern ];

      symbolPatterns = DeleteDuplicates @
        Extract[ pattern, symbolPositions, HoldPattern ];

      symbolStrings = StringTake[ ToString @ #, { 13, -2 } ]& /@ symbolPatterns;
      newSymbols = Unique[ # <> "$" ] & /@ symbolStrings;
      newSymbols ~ SetAttributes ~ { Temporary };
      rules = RuleDelayed @@@ Transpose[ { symbolPatterns, newSymbols } ];
      definition /. rules
  ];

extractPatterns // ClearAll;
extractPatterns // Attributes = {};
extractPatterns // Options = {};

extractPatterns[ definitions : { HoldPattern[ _HoldPattern :> ___ ]... } ] :=
  First /@ definitions;


Deconstruct // ClearAll;
Deconstruct // Attributes = { HoldAllComplete };
Deconstruct // Options = {};

Deconstruct[ pattern_, args__ : None ] :=
  Module[
      {
          f, namePositions, heldNames, length, stringNames, assocList,
          heldAssoc, heldRules, constructedDefinition
      },

      f // Attributes =
        If[ HoldComplete @ args === HoldComplete @ None,
            { HoldAllComplete },
            { Temporary, HoldAllComplete }
        ];

      namePositions = # ~ Append ~ 1 & /@
        Position[ pattern, Verbatim[ Pattern ][ _, ___ ], Heads -> True ];

      heldNames = Extract[ pattern, namePositions, Hold ];
      length = Length @ heldNames;
      stringNames = StringTake[ ToString @ #, { 6, -2 } ] & /@ heldNames;
      assocList = Thread[ stringNames -> heldNames ];
      heldAssoc = With[ { a = assocList }, HoldComplete @@ a ];

      heldRules = ReplacePart[ heldAssoc,
          ({ #, 2, 0 } & /@ Range[ length ]) -> List
      ];

      constructedDefinition =
        ReplacePart[
            With[ { args$ = pattern, exp = heldRules },
                HoldComplete[ f[ args$ ] := exp ]
            ],
            { { 1, 2, 0 } -> Association }
        ];

      ReleaseHold @ constructedDefinition;
      If[ args =!= None, f[ args ], f ]
  ];



(******************************************************************************)

HoldFlatten // ClearAll;
HoldFlatten // Attributes = { HoldAllComplete };
HoldFlatten // Options = {};

HoldFlatten[ expression_ ] :=
  Module[ { heldExpression, holdPositions, removedHolds },
      heldExpression = HoldComplete @ expression;
      holdPositions = heldExpression ~ Position ~ Hold;
      removedHolds = heldExpression ~ Delete ~ holdPositions;
      removedHolds /. HoldComplete -> Hold
  ];


(******************************************************************************)

End[]; (* End Private Context *)

EndPackage[]