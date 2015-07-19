(* Mathematica Package                                                            *)
(* Created by IntelliJ IDEA                                                       *)

(* :Title: FactorExpression                                                       *)
(* :Context: FactorExpression`                                                    *)
(* :Author: Richard Hennigan                                                      *)
(* :Date: 7/18/2015                                                               *)

(* :Package Version: 0.1                                                          *)
(* :Mathematica Version: 10.1.0  for Microsoft Windows (64-bit) (March 24, 2015)  *)
(* :Copyright: (c) 2015 Richard Hennigan                                          *)
(* :Keywords:                                                                     *)
(* :Discussion:                                                                   *)

BeginPackage["FactorExpression`"];

$DefaultExcludedForms =
    {
      _Random, _RandomChoice, _RandomColor, _RandomComplex, _RandomFunction, _RandomGraph, _RandomImage, _RandomInteger,
      _RandomPermutation, _RandomPrime, _RandomReal, _RandomSample, _RandomSeed, _RandomVariate, _RandomWalkProcess,
      Times[-1, _]
    };

(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = "Use this to make magic happen (maybe).";

Begin["`Private`"]; (* Begin Private Context *)

FactorExpression::depth = "The depth specification `1` is not a positive integer.";

findRedundantExpressions[exp_, varCount_Integer, minDepth_Integer, excludedForms_List] := Module[
  {expressionCounts, mostRedundantExpressions},
  expressionCounts =
      Tally[Cases[exp,
        Except[Alternatives @@ Prepend[excludedForms, V[_Integer]], _[___]],
        Infinity]];
  mostRedundantExpressions =
      MaximalBy[Cases[expressionCounts,
        {subExp_ /; Depth[subExp] >= minDepth, x_Integer /; x > 1}
      ], Last];
  If[mostRedundantExpressions =!= {},
    Module[{newVar, newVal},
      {newVar, newVal} = {V[varCount], mostRedundantExpressions[[1, 1]]};
      Sow[HeldSet[newVar, newVal]];
      findRedundantExpressions[exp /. newVal -> newVar, varCount + 1, minDepth, excludedForms]
    ],
    Sow[exp];
    varCount - 1
  ]
];

FactorExpression[exp_, opts : OptionsPattern[]] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[
    {
      output, minDepth, excludedForms,
      varCount, assignments, localVariables,
      cexp, mexp, fexp
    },

    output = OptionValue["Output"];
    minDepth = OptionValue["MinDepth"];
    excludedForms = OptionValue["ExcludedForms"];

    If[Not[IntegerQ[minDepth] && minDepth >= 1], Message[FactorExpression::depth, minDepth]];

    {varCount, assignments} = Reap[findRedundantExpressions[exp, 1, minDepth, excludedForms]];
    localVariables = Symbol["V" <> ToString[#]]& /@ Range[varCount];
    cexp = First[HeldCompoundExpression @@@ assignments /. V[x_Integer] :> Symbol["V" <> ToString[x]]];
    mexp = With[{localVariablesT = localVariables, cexpT = cexp}, Hold@Block[localVariablesT, cexpT]];
    fexp = Evaluate[mexp] /. {HeldSet -> Set, HeldCompoundExpression -> CompoundExpression, Hold -> HoldForm};

    Switch[output,
      CompiledFunction, Module[
      {parameters = Union[Cases[exp, _Symbol, Infinity]]},
      HeldCompile[{#, _Real}& /@ parameters, fexp (*),
        Parallelization -> True,
        RuntimeAttributes -> {Listable} *)
      ] /. {
        HoldForm[Block[vars_, modexp_]] :> Block[vars, modexp],
        HeldCompile -> Compile
      }
    ],
      _, fexp
    ]
  ]
];

Options[FactorExpression] = {
  "Output" -> Automatic,
  "MinDepth" -> 1,
  "ExcludedForms" -> $DefaultExcludedForms
};

End[]; (* End Private Context *)

EndPackage[]