(* Wolfram Language Package *)

BeginPackage["OptimizationToolkit`"];

Unprotect["`*"];
ClearAll["`*"];

Needs["OptimizationToolkit`Types`"];
Needs["OptimizationToolkit`Profiling`"];
Needs["OptimizationToolkit`Metaprogramming`"];

$DefaultExcludedForms =
    {
      _Random, _RandomChoice, _RandomColor, _RandomComplex, _RandomFunction, 
      _RandomGraph, _RandomImage, _RandomInteger, _RandomPermutation, 
      _RandomPrime, _RandomReal, _RandomSample, _RandomSeed, _RandomVariate, 
      _RandomWalkProcess, Times[-1, _]
    };

(* Exported symbols added here with SymbolName::usage *)

FactorExpression   ::usage = "Use this to make magic happen (maybe).";
OptimizeDownValues ::usage = "";
Memoize            ::usage = "";
CompoundSimplify   ::usage = "";
CompoundActivate   ::usage = "";
ToHoldForm         ::usage = "";
SExp               ::usage = "A container for S-Expressions";


Begin["`Private`"]; (* Begin Private Context *)

(******************************************************************************)
(* Auxillary definitions *)
(******************************************************************************)

extractPatternFromDownValue[
  downValue : (Verbatim[HoldPattern][_[___]] :> exp_)
  ] :=
  downValue[[1]];

extractHeldExpressionFromDownValue[
  downValue : (Verbatim[HoldPattern][_[___]] :> exp_)
  ] :=
  Hold[exp];

heldExpressionToString[expression_Hold] :=
  StringTake[ToString[InputForm[expression]], {6, -2}];

heldExpressionHead[expression : Hold[_]] :=
  expression /. Hold[s_Symbol[___]] :> s;

extractFunctionsFromExpression[exp_] :=
  Union[Cases[exp, (f_)[___] :> f, Infinity]];

heldExpressionSymbols[heldExpression : Hold[_]] :=
  Union[Cases[heldExpression, s_Symbol :> Hold[s], Infinity]];

heldExpressionSymbols[downValue : (Verbatim[HoldPattern][_[___]] :> exp_)] :=
  heldExpressionSymbols[extractHeldExpressionFromDownValue[downValue]];

getTemporaryEvaluationRules[expressionSymbols : {Hold[_]...}] :=
  Module[ {replacementSymbolsIn, replacementSymbolsOut},
    replacementSymbolsIn = expressionSymbols /. 
    Hold[s_] :> 
    With[ {v = Unique[]},
      Hold[s] :> v
    ];
    replacementSymbolsOut = replacementSymbolsIn /. 
    HoldPattern[h_Hold :> v_] :> v :> h;
    {replacementSymbolsIn, replacementSymbolsOut}
  ];

expandOnce[replacedVarsExpression_Hold] :=
  Module[ {nonSystemFunctions, symbolicRules},
    nonSystemFunctions = Select[
        extractFunctionsFromExpression[replacedVarsExpression], 
        Context[#] =!= "System`"&
        ];
    symbolicRules = Flatten[
        DownValues /@ nonSystemFunctions /. 
        Verbatim[Blank][_] :> 
        Blank[]
        ];
    replacedVarsExpression /. symbolicRules
  ];

$CompilerFunctionList = Compile`CompilerFunctions[] ~ Join ~ {Det, Rational};
CompilableFunctionQ[_] :=
  False;
Scan[(CompilableFunctionQ[#] = True) &, $CompilerFunctionList];

(******************************************************************************)

iCompoundSimplify[expression_] :=
  Module[ {expressionCounts, mostRedundant},
    expressionCounts = Select[
      Tally @ Cases[
        expression,
        Except[Inactive[_]], 
        Infinity, 
        Heads -> True
        ],
      #[[2]] > 1 && Depth[#[[1]]] > 1 &
    ];
    mostRedundant = MaximalBy[expressionCounts, Last];
    If[ mostRedundant =!= {},
      Module[ {mr = mostRedundant[[1, 1]], nv = Unique[]},
        Sow[nv, "variables"];
        Sow[Inactive[Set][nv, mr], "assignments"];
        expression /. mr -> nv
      ],
      expression
    ]
  ];

SExp = With[ {args = {##2}, f = #1},
         f @@ args
       ] &;

toSExpressions[inactivatedExp_] :=
  Module[ {replacement},
    replacement = Cases[
      inactivatedExp,
      Inactive[f_][a___] :> (HoldPattern[Inactive[f][a]] -> Inactive[SExp][f, a]),
      Infinity, Heads -> True
    ];
    inactivatedExp //. replacement
  ];

toMExpressions[inactivatedExp_] :=
  Module[ {replacement},
    replacement = Cases[
      inactivatedExp,
      Inactive[SExp][f_, a___] :> (HoldPattern[Inactive[SExp][f, a]] :> Inactive[f][a]),
      Infinity, Heads -> True
    ];
    inactivatedExp //. replacement
  ];

SetAttributes[CompoundSimplify, {HoldAll}];
CompoundSimplify[expression_] :=
  Module[ {exp, out, variables, assignments, inactivatedExp},
      (*exp = With[{e = expression}, Inactivate[e]];*)
    exp = Inactivate @ expression;
    {out, {variables, assignments}} = Reap @ FixedPoint[iCompoundSimplify, exp];
    Scan[SetAttributes[#1, {Temporary}] & , variables];
    inactivatedExp =
        Inactive[Block][
          variables,
          Inactive[CompoundExpression] @@ Append[assignments, With[ {o = out},
                                                                Inactivate @ o
                                                              ]]
        ];
        (*toSExpressions @ *)
    inactivatedExp
  ];

CompoundActivate[inactivatedExp_] :=
  Activate[toSExpressions @ inactivatedExp];

ToHoldForm[exp_] :=
  Module[ {held = With[ {e = exp},
                    HoldForm @ e
                  ]},
    held /. Inactive[s_] :> Hold @ s /. Hold[s_] :> s
  ];

(******************************************************************************)

findRedundantExpressions[exp_, varCount_Integer, minDepth_Integer, excludedForms_List] :=
  Module[ {
      expressionCounts,
      mostRedundantExpressions
    },
    expressionCounts =
        Tally[Cases[exp,
          Except[Alternatives @@ excludedForms, _[___]],
          Infinity]];
    mostRedundantExpressions =
        MaximalBy[Cases[expressionCounts,
          {subExp_ /; Depth[subExp] >= minDepth, x_Integer /; x > 1}
        ], Last];
    If[ mostRedundantExpressions =!= {},
      Module[ {
          v = Unique[],
          newVal = mostRedundantExpressions[[1, 1]]
        },
        Sow[HeldSet[v, newVal]];
        findRedundantExpressions[exp /. newVal -> v, varCount + 1, minDepth, excludedForms]
      ],
      Sow[exp];
      varCount - 1
    ]
  ];

(******************************************************************************)

memoize[dv : RuleDelayed[_, _Set]] :=
  dv;

memoize[dv : (_ :> _)] :=
  With[ {
      insert = dv[[1]] /. Verbatim[Pattern][sym_, _] :> sym
    },
    dv /. {
      (hp_ :> def_) :> hp :> (insert = def)
    }
  ] /. {
    HoldPattern[Verbatim[HoldPattern][h_] = def_] :> (h = def)
  };

memoize[f_Symbol] :=
  (
    DownValues[Evaluate[f]] = memoize /@ DownValues[f]
  );

memoize[other_] :=
  other;

(******************************************************************************)
(* Exported functions *)
(******************************************************************************)

FactorExpression::depth = "The depth specification `1` is not a positive integer.";

FactorExpression[exp_, opts : OptionsPattern[]] :=
  Module[ {
      output, minDepth, excludedForms,
      varCount, assignments, localVariables,
      cexp, mexp, fexp, out
    },
    output = OptionValue["Output"];
    minDepth = OptionValue["MinDepth"];
    excludedForms = OptionValue["ExcludedForms"];
    If[ !(IntegerQ[minDepth] && minDepth >= 1),
      Message[FactorExpression::depth, minDepth]
    ];
    {varCount, assignments} = Reap[findRedundantExpressions[exp, 1, minDepth, excludedForms]];
    localVariables = Cases[assignments, HeldSet[v_, _] :> v, 2];
    cexp = First[Apply[HeldCompoundExpression, assignments, {1}]];
    mexp = With[ {
        localVariablesT = localVariables,
        cexpT = cexp
      },
             Hold[Block[ localVariablesT,
                    cexpT
                  ]]
           ];
    fexp = Evaluate[mexp] /. {
      HeldSet -> Set,
      HeldCompoundExpression -> CompoundExpression
    } /. HoldPattern[Block[ {},
                       CompoundExpression[e_]
                     ]] :> e;
    out = Switch[output,
      CompiledFunction,
      Module[ {
          parameters = Union[Cases[exp, _Symbol, Infinity]]
        },
        HeldCompile[({#1, _Real} & ) /@ parameters, fexp] /. {
          Hold[Block[ vars_,
                 modexp_
               ]] :> Block[ vars,
                       modexp
                     ],
          HeldCompile -> Compile
        }
      ],
      _, fexp
    ];
    out
  ];

Options[FactorExpression] =
    {
      "Output" -> Automatic,
      "MinDepth" -> 1,
      "ExcludedForms" -> $DefaultExcludedForms
    };

SyntaxInformation[FactorExpression] =
    {
      "ArgumentsPattern" -> {_, OptionsPattern[]}
    };

(******************************************************************************)

canCompileQ[downValue : (HoldPattern[_] :> _)] :=
  AllTrue[
    List @@ GetTypeSignature[downValue],
    MatchQ[#1, _TensorType | Real | Integer] &
  ];

compileFromDownValues[downValue : (HoldPattern[_] :> _)] :=
  Module[ {
      type, argSymbols, compileArgumentPattern,
      localExpressionSymbols, localVars, localAssignments,
      heldExpression, expressionSymbols, replacementSymbolsIn,
      replacementSymbolsOut, toFactor, factoredBlock,
      heldBlock, heldCompile, compiledFunction
    },
    type = GetTypeSignature[downValue];
    argSymbols = Table[Unique[], {Length[type]}];
    compileArgumentPattern = Apply[
      Prepend,
      Transpose[{
        Cases[List @@ type, s_ :> {s}] /.
            {TensorType[t_, i_]} :> {_t, i} /.
            {s_} :> {_s},
        argSymbols
      }], {1}];
    localExpressionSymbols = downValue /.
        (Verbatim[HoldPattern][_[args___]] :> _) :> {args} /.
        Verbatim[Pattern][sym_, _] :> Hold[sym];
    localVars = Flatten[localExpressionSymbols];
    localAssignments = Apply[HeldSet, Transpose[{localExpressionSymbols, argSymbols}], {1}];
    heldExpression = downValue /. (Verbatim[HoldPattern][_[___]] :> exp_) :> Hold[exp];
    expressionSymbols = Union[Cases[heldExpression, s_Symbol :> Hold[s], Infinity]];
    replacementSymbolsIn = expressionSymbols /. Hold[s_] :> With[ {v = Evaluate[Unique[]]},
                                                              Hold[s] :> v
                                                            ];
    replacementSymbolsOut = replacementSymbolsIn /. HoldPattern[h_Hold :> v_] :> v :> h;
    toFactor = ReleaseHold[heldExpression /.
        s_Symbol :> Hold[s] /.
        replacementSymbolsIn /.
        Hold[s_Symbol] :> s
    ];
    factoredBlock = FactorExpression[toFactor] /. HoldForm -> Hold;
    heldBlock = HeldBlock[
      localVars,
      HeldCompoundExpression @@ Append[localAssignments, factoredBlock]
    ] /. replacementSymbolsIn;
    heldCompile = HeldCompile[compileArgumentPattern, heldBlock];
    compiledFunction = heldCompile /. {
      HeldSet -> Set,
      HeldCompoundExpression -> CompoundExpression,
      Hold[Block[ v_,
             e_
           ]] :> Block[ v,
                   e
                 ],
      HeldBlock -> Block,
      HeldCompile -> Compile
    }
  ];

compiledDownValue[downValue : (HoldPattern[_] :> _)] :=
  Module[ {args, cf, patt, cArgs, cfPlaced},
    cf = compileFromDownValues[downValue];
    patt = First[downValue];
    cArgs = patt /.
        Verbatim[HoldPattern][_[args___]] :> {args} /.
        Verbatim[Pattern][s_, _] :> Hold[s];
    cfPlaced =
        With[ {c = cf},
          HoldComplete[c[args]] /.
              args -> cArgs /.
              Hold[e_] :> e
        ];
    patt :> Evaluate[cfPlaced] /. HoldComplete[e_] :> e /. c_CompiledFunction[{a___}] :> c[a]
  ];

(******************************************************************************)

OptimizeDownValues[f_Symbol, opts : OptionsPattern[]] :=
  Module[ {
      dv = DownValues[f],
      filt, fopts, newDV
    },
    filt = Alternatives @@ Options[FactorExpression][[All, 1]];
    fopts = Sequence @@ Cases[{opts}, (o : filt -> s_) :> o -> s];
      (*newDV = Table[Quiet[Check[*)
      (*compiledDownValue[downValue],*)
      (*downValue /. (h_HoldPattern :> exp_) :> h :> Evaluate[FactorExpression[exp, fopts]] /. Hold[b_] :> b*)
      (*]], {downValue, dv}];*)
    newDV = dv /. (h_HoldPattern :> exp_) :> h :> Evaluate[FactorExpression[exp, fopts]] /. Hold[b_] :> b;
    If[ OptionValue["Rewrite"],
      DownValues[Evaluate[f]] = newDV
    ];
    If[ OptionValue["Memoize"],
      memoize[f],
      newDV
    ]
  ];

Options[OptimizeDownValues] =
    {
      "Rewrite" -> False,
      "Memoize" -> False,
      "Compile" -> False
    } ~ Join ~ Options[FactorExpression];

(******************************************************************************)

Memoize[f_Symbol] :=
  memoize[f];

(******************************************************************************)

End[]; (* End Private Context *)

EndPackage[];