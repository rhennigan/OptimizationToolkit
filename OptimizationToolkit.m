(* Mathematica Package                                                            *)
(* Created by IntelliJ IDEA                                                       *)

(* :Title: OptimizationToolkit                                                    *)
(* :Context: OptimizationToolkit`                                                 *)
(* :Author: Richard Hennigan                                                      *)
(* :Date: 7/20/2015                                                               *)

(* :Package Version: 0.2                                                          *)
(* :Mathematica Version: 10.1.0  for Microsoft Windows (64-bit) (March 24, 2015)  *)
(* :Copyright: (c) 2015 Richard Hennigan                                          *)
(* :Keywords:                                                                     *)
(* :Discussion:                                                                   *)

BeginPackage["OptimizationToolkit`"];

$DefaultExcludedForms =
    {
      _Random, _RandomChoice, _RandomColor, _RandomComplex, _RandomFunction, _RandomGraph, _RandomImage, _RandomInteger,
      _RandomPermutation, _RandomPrime, _RandomReal, _RandomSample, _RandomSeed, _RandomVariate, _RandomWalkProcess,
      Times[-1, _]
    };

(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = "Use this to make magic happen (maybe).";
OptimizeDownValues::usage = "";
Memoize::usage = "";


Begin["`Private`"]; (* Begin Private Context *)

(**********************************************************************************************************************)
(* Auxillary definitions *)
(**********************************************************************************************************************)

FactorExpression::depth = "The depth specification `1` is not a positive integer.";


Module[
  {
    varCounter = 0
  },
  newVar := Symbol["OptimizationToolkit`$" <> ToString[varCounter++]]
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

memoize[dv : RuleDelayed[_, _Set]] :=
    dv;

memoize[dv : RuleDelayed[_, _]] :=
    With[
      {
        insert = dv[[1]] /. Verbatim[Pattern][sym_, _] :> sym
      },
      dv /. {
        RuleDelayed[hp_, def_] :> RuleDelayed[hp, Set[insert, def]]
      }
    ] /. {
      HoldPattern[Set[Verbatim[HoldPattern][h_], def_]] :> Set[h, def]
    };

memoize[f_Symbol] :=
    (
      DownValues[Evaluate[f]] = memoize /@ DownValues[f]
    );

memoize[other_] :=
    other;

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
      "ExcludedForms" -> $DefaultExcludedForms
    };

SyntaxInformation[FactorExpression] =
    {
      "ArgumentsPattern" -> {_, OptionsPattern[]}
    };

(**********************************************************************************************************************)

OptimizeDownValues[f_Symbol, opts : OptionsPattern[]] :=
    Module[
      {
        dv = DownValues[f],
        filt, fopts, newDV
      },
      filt = Alternatives @@ Options[FactorExpression][[All, 1]];
      fopts = Sequence @@ Cases[List@opts, Rule[o : filt, s_] :> Rule[o, s]];
      newDV = dv /. (h_HoldPattern :> exp_) :> h :> Evaluate[FactorExpression[exp, fopts]] /. HoldForm[b_Block] :> b;

      If[OptionValue["Rewrite"], DownValues[Evaluate[f]] = newDV];
      If[OptionValue["Memoize"], memoize[f], newDV]

    ];

Options[OptimizeDownValues] =
    {
      "Rewrite" -> False,
      "Memoize" -> False
    } ~ Join ~ Options[FactorExpression];

(**********************************************************************************************************************)

Memoize[f_Symbol] :=
    memoize[f];

(**********************************************************************************************************************)

End[]; (* End Private Context *)

EndPackage[];
