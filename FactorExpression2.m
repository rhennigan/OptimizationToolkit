(* Mathematica Package         *)
(* Created by IntelliJ IDEA    *)

(* :Title: FactorExpression2     *)
(* :Context: FactorExpression2`  *)
(* :Author: rhennigan            *)
(* :Date: 7/16/2015              *)

(* :Package Version: 1.0       *)
(* :Mathematica Version:       *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                  *)
(* :Discussion:                *)

BeginPackage["FactorExpression2`"];
(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = "Use this to make magic happen (maybe).";

Begin["`Private`"]; (* Begin Private Context *)

findRedundantExpressions[exp_, varCount_Integer] := Module[
  {expressionCounts, mostRedundantExpressions},
  expressionCounts = Tally[Cases[exp, Except[V[_Integer], _[___]], Infinity]];
  mostRedundantExpressions = Cases[MaximalBy[expressionCounts, Last], {_, x_Integer /; x > 1}];
  If[mostRedundantExpressions =!= {},
    Module[{newVar, newVal},
      {newVar, newVal} = {V[varCount], mostRedundantExpressions[[1, 1]]};
      Sow[HeldSet[newVar, newVal]];
      findRedundantExpressions[exp /. newVal -> newVar, varCount + 1]
    ],
    Sow[exp];
    varCount - 1
  ]
];

FactorExpression[exp_, opts : OptionsPattern[]] := Block[
  {$RecursionLimit = Infinity, $IterationLimit = Infinity},
  Module[
    {output, varCount, assignments, localVariables, cexp, mexp, fexp},
    output = OptionValue["Output"];
    {varCount, assignments} = Reap[findRedundantExpressions[exp, 1]];
    localVariables = Symbol["V" <> ToString[#]]& /@ Range[varCount];
    cexp = First[HeldCompoundExpression @@@ assignments /. V[x_Integer] :> Symbol["V" <> ToString[x]]];
    mexp = With[{localVariablesT = localVariables, cexpT = cexp}, Hold@Module[localVariablesT, cexpT]];
    fexp = Evaluate[mexp] /. {HeldSet -> Set, HeldCompoundExpression -> CompoundExpression};
    Switch[output,
      CompiledFunction, Module[
      {parameters = Union[Cases[exp, _Symbol, Infinity]]},
      HeldCompile[{#, _Real}& /@ parameters, fexp] /. {
        Hold[Module[vars_, modexp_]] :> Module[vars, modexp],
        HeldCompile -> Compile
      }
    ],
      _, fexp
    ]
  ]
];

Options[FactorExpression] = {
  "Output" -> CompiledFunction
};

End[]; (* End Private Context *)

EndPackage[]