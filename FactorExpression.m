(* Mathematica Package            *)
(* Created by IntelliJ IDEA       *)

(* :Title: FactorExpression       *)
(* :Context: FactorExpression`    *)
(* :Author: rhennigan             *)
(* :Date: 4/18/2015               *)

(* :Package Version: 0.1          *)
(* :Mathematica Version: 10       *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                     *)
(* :Discussion:                   *)

BeginPackage["FactorExpression`"]
(* Exported symbols added here with SymbolName::usage *)

FactorExpression::usage = ""
FactorExpressionFunction::usage = ""

Begin["`Private`"] (* Begin Private Context *)

FactorExpression::lang = "The language specification `1` is not recognized.";
FactorExpression::comm = "The comments specification `1` is not recognized.";

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

factorExpression[exp_, varCount_Integer, opts : OptionsPattern[]] := Module[
  {factor, count},
  {factor, count} = mostRedundantFactor[exp];
  If[count > 1,
    Module[{prefix, newVar, newExp},
      prefix = OptionValue["Prefix"];
      newVar = If[prefix === None,
        Module[{Global`v}, Global`v],
        Symbol[ToString[prefix] <> ToString[varCount + 1]]
      ];
      Sow[{newVar, factor, count}];
      newExp = exp /. factor -> newVar;
      factorExpression[newExp, varCount + 1, opts]
    ],
    exp
  ]
]

formatAssignment[{v_, e_, c_}, {"C", type_String, comments : (True | False)}] := Module[
  {end},
  end = If[comments, StringJoin[";  /* ", ToString[c], " */\n"], ";\n"];
  StringJoin[
    type, " ", ToString[CForm[v]], " = ", ToString[CForm[e]], end
  ]
]

Options[factorExpression] = {
  "Language" -> None,
  "Prefix" -> None,
  "Comments" -> True
};

Unprotect[FactorExpression];

FactorExpression[exp_, opts : OptionsPattern[]] /; Depth[exp] == 1 := {exp, {}}
FactorExpression[exp_, opts : OptionsPattern[]] := Module[
  {lang, comments, simple, assignments},
  lang = OptionValue["Language"];
  comments = OptionValue["Comments"];
  If[Not[BooleanQ[comments]],
    Message[FactorExpression::comm, OptionValue["Comments"]],
    {simple, assignments} = { #[[1]] , #[[2, 1]] } & @ Reap[factorExpression[exp, 0, opts]];
    Switch[lang,
      None, {simple, assignments},
      "C", StringJoin[
      formatAssignment[#, {"C", "double", comments}] & /@ assignments,
      "return ", ToString[CForm[simple]], ";"
    ],
      _, Message[FactorExpression::lang, lang];
    ]
  ]
]

Options[FactorExpression] = {
  "Language" -> None,
  "Prefix" -> None,
  "Comments" -> True
};

SyntaxInformation[FactorExpression] = {"ArgumentsPattern" -> {_, OptionsPattern[]}};
Attributes[FactorExpression] = {Protected};

FactorExpressionFunction[exp_, opts : OptionsPattern[]] := Module[
  {lang, comments, simple, assignments, allSymbols, newSymbols, listHold, assignment},
  lang = OptionValue["Language"];
  comments = OptionValue["Comments"];
  If[Not[BooleanQ[comments]],
    Message[FactorExpression::comm, OptionValue["Comments"]],
    {simple, assignments} = FactorExpression[exp, opts];
    allSymbols = Union[Cases[{simple, assignments}, _Symbol, Infinity]];
    newSymbols = assignments[[All, 1]];
    With[
      {
        args = Complement[allSymbols, newSymbols],
        locals = newSymbols,
        compoundExpression = listHold @@ Append[Table[assignment[assignments[[i, 1]], assignments[[i, 2]]], {i, Length[assignments]}], simple]
      },
      Function[Evaluate[args],
        Module[locals, compoundExpression]
      ] /. {
        listHold -> CompoundExpression,
        assignment -> Set
      }
    ]
  ]
]

Options[FactorExpressionFunction] = {
  "Language" -> None,
  "Prefix" -> None,
  "Comments" -> True
};

End[] (* End Private Context *)

EndPackage[]

(*args=Complement[Union[Cases[{simple,assignments},_Symbol,Infinity]],\
assignments\[LeftDoubleBracket]All,1\[RightDoubleBracket]];
NotebookPut[Notebook[{Cell[BoxData[RowBox[{RowBox[{"factoredFunction",\
"[",RowBox[Riffle[ToString[#]<>"_"&/@args,","]],"]"}],":=",RowBox[{\
"Module","[","
",RowBox[{
RowBox[{"{",RowBox[Riffle[ToString/@assignments\[LeftDoubleBracket]\
All,1\[RightDoubleBracket],","]],"}"}],",","
",
RowBox[Append[Flatten[{RowBox[{ToString[#\[LeftDoubleBracket]1\
\[RightDoubleBracket]],"=",ToBoxes[#\[LeftDoubleBracket]2\
\[RightDoubleBracket]]}],";","
"}&/@assignments],ToBoxes[simple]]]
}],"
","]"}]}]],"Input"]}]]*)