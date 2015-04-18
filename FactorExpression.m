(* Mathematica Package            *)
(* Created by IntelliJ IDEA       *)

(* :Title: FactorExpression       *)
(* :Context: FactorExpression`    *)
(* :Author: rhennigan             *)
(* :Date: 4/18/2015               *)

(* :Package Version: 1.0          *)
(* :Mathematica Version:          *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                     *)
(* :Discussion:                   *)

BeginPackage["FactorExpression`"]
(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = ""

Begin["`Private`"] (* Begin Private Context *)

inReals[exp_] := Module[
  {allSymbols, symbols, membership},
  allSymbols = Cases[exp, _Symbol, Infinity];
  symbols = Union[allSymbols];
  membership = Element[symbols, Reals];
  Return[membership];
]

simplify[exp_] := Module[
  {assumption, simplified},
  assumption = inReals[exp];
  simplified = Simplify[exp, assumption];
  Return[simplified];
]

commutativeSubsets[exp_] := Module[
  {productQ},
  productQ = Head[exp] === Times && Length[exp] > 2;
  If[productQ,
    Module[{subproductSets, subproducts},
      subproductSets = Subsets[List @@ exp, {2, Infinity}];
      subproducts = Times @@@ subproducts;
      Sow /@ subproducts
    ],
    Sow[exp]
  ];
  Return[exp];
]

mostRedundantFactor[exp_] := Module[
  {subexpressions, subexpressionCounts, factor, count},
  subexpressions = First @ Last @ Reap[
    commutativeSubsets[exp];
    Map[commutativeSubsets, exp, Infinity]
  ];
  subexpressionCounts = Select[Tally[subexpressions], Depth[ #[[1]] ] > 1 &];
  {factor, count} = First[MaximalBy[subexpressionCounts, Last]];
  Return[{factor, count}];
]

factorExpression[exp_, varCount_Integer, opts:OptionsPattern[]] := Module[
  {factor, count},
  {factor, count} = mostRedundantFactor[exp];
  If[count > 1,
    Module[{prefix, newVar, newExp},
      prefix = OptionValue["Prefix"];
      newVar = If[prefix === None,
        Module[{v}, v],
        Symbol[prefix <> ToString[varCount + 1]]
      ];
      Sow[{newVar, factor}];
      newExp = exp /. factor -> newVar;
      factorExpression[newExp, varCount + 1, opts]
    ],
    exp
  ]
]

Options[factorExpression] = {"Language" -> None, "Prefix" -> None};

Unprotect[FactorExpression];

FactorExpression[exp_, opts:OptionsPattern[]] /; Depth[exp] == 1 := {exp, {}}
FactorExpression[exp_, opts:OptionsPattern[]] := {#1[[1]], #1[[2, 1]]} & @ Reap[factorExpression[exp, 0, opts]]

Options[FactorExpression] = {"Language" -> None, "Prefix" -> None};
SyntaxInformation[FactorExpression] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
Attributes[FactorExpression] = {Protected};

End[] (* End Private Context *)

EndPackage[]