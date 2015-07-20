(* Mathematica Package                                                            *)
(* Created by IntelliJ IDEA                                                       *)

(* :Title: FactorExpression                                                       *)
(* :Context: FactorExpression`                                                    *)
(* :Author: Richard Hennigan                                                      *)
(* :Date: 7/20/2015                                                               *)

(* :Package Version: 0.2                                                          *)
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
OptimizeDownValues::usage = "";


Begin["`Private`"]; (* Begin Private Context *)

(**********************************************************************************************************************)
(* Auxillary definitions *)
(**********************************************************************************************************************)

FactorExpression::depth = "The depth specification `1` is not a positive integer.";


Module[
  {
    varCounter = 0
  },
  newVar := Symbol["FactorExpression`$" <> ToString[varCounter++]]
];


findRedundantExpressions[exp_, varCount_Integer, minDepth_Integer, excludedForms_List] :=
    Module[
      {
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

      If[mostRedundantExpressions =!= {},

        Module[
          {
            v = newVar,
            newVal = mostRedundantExpressions[[1, 1]]
          },

          Sow[HeldSet[v, newVal]];
          findRedundantExpressions[exp /. newVal -> v, varCount + 1, minDepth, excludedForms]
        ],

        Sow[exp];
        varCount - 1
      ]
    ];

(**********************************************************************************************************************)
(* Exported functions *)
(**********************************************************************************************************************)

FactorExpression[exp_, opts : OptionsPattern[]] :=
    Module[
      {
        output, minDepth, excludedForms,
        varCount, assignments, localVariables,
        cexp, mexp, fexp, out
      },

      output = OptionValue["Output"];
      minDepth = OptionValue["MinDepth"];
      excludedForms = OptionValue["ExcludedForms"];

      If[Not[IntegerQ[minDepth] && minDepth >= 1], Message[FactorExpression::depth, minDepth]];

      {varCount, assignments} = Reap[findRedundantExpressions[exp, 1, minDepth, excludedForms]];
      localVariables = Cases[assignments, HeldSet[v_, _] :> v, 2];
      cexp = First[HeldCompoundExpression @@@ assignments];

      mexp =
          With[
            {
              localVariablesT = localVariables,
              cexpT = cexp
            },
            Hold @ Block[localVariablesT, cexpT]
          ];

      fexp =
          Evaluate[mexp] /. {
            HeldSet -> Set,
            HeldCompoundExpression -> CompoundExpression,
            Hold -> HoldForm
          };

      out =
          Switch[output,
            CompiledFunction,
            Module[
              {
                parameters = Union[Cases[exp, _Symbol, Infinity]]
              },
              HeldCompile[ {#, _Real}& /@ parameters, fexp] /. {
                HoldForm[Block[vars_, modexp_]] :> Block[vars, modexp],
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
      "ExcludedForms" -> $DefaultExcludedForms,
      "Rewrite" -> Automatic
    };

SyntaxInformation[FactorExpression] =
    {
      "ArgumentsPattern" -> {_, OptionsPattern[]}
    };

(**********************************************************************************************************************)

OptimizeDownValues[f_Symbol, opts : OptionsPattern[]] := Module[
  {dv = DownValues[f], newDV},
  newDV = dv /. (h_HoldPattern :> exp_) :> h :> Evaluate[FactorExpression[exp, opts]] /. HoldForm[b_Block] :> b;
  If[OptionValue["Rewrite"],
    DownValues[Evaluate[f]] = newDV,
    newDV
  ]];

Options[OptimizeDownValues] = {
  "Rewrite" -> False
};

(**********************************************************************************************************************)

End[]; (* End Private Context *)

EndPackage[]