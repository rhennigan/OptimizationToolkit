(* Mathematica Package         *)
(* Created by IntelliJ IDEA    *)

(* :Title: OptimizationToolkit Profiling     *)
(* :Context: OptimizationToolkit`Profiling`  *)
(* :Author: Richard Hennigan            *)
(* :Date: 7/24/2015              *)

(* :Package Version: 0.2       *)
(* :Mathematica Version:       *)
(* :Copyright: (c) 2015 Richard Hennigan *)
(* :Keywords:                  *)
(* :Discussion:                *)

BeginPackage["OptimizationToolkit`Profiling`", {"OptimizationToolkit`"}];
(* Exported symbols added here with SymbolName::usage *)

Profile               ::usage = "";
ProfilingPieChart     ::usage = "";
ProfilingTimelinePlot ::usage = "";

Begin["`Private`"]; (* Begin Private Context *)

$KernelStartTime = DatePlus[Now, {-SessionTime[], "Second"}];
$TimingLog = <||>;

SetAttributes[OrderedTable, {HoldFirst}];
OrderedTable[expression_, iterators__] := Table[expression, iterators];

SetAttributes[OrderedModule, {HoldAll}];
OrderedModule[locals_, expression__] := With[{l = locals}, Module[l, expression]];

$FunctionReplacements =
    {
      Table -> OrderedTable,
      Module -> OrderedModule
    };

ClearAll[NewTimingID];
Module[{varCounter = 0}, NewTimingID[] := varCounter++];

(**********************************************************************************************************************)
(* Insert timing for single expression *)
(**********************************************************************************************************************)

ClearAll[insertTiming];

insertTiming[expression_Hold] := With[
  {
    exp = insertSubexpressionTiming[expression],
    head = heldExpressionHead[expression],
    expStr = heldExpressionToString[expression],
    res = newVar
  },
  Hold[With[{id = NewTimingID[]}, TaggedBlock[{res},
    $TimingLog[id] = <|
        "head" -> head,
        "expStr" -> expStr,
        "started" -> SessionTime[]
        |>;
    res = TaggedHold[exp];
    $TimingLog[id]["ended"] = SessionTime[];
    If[Head[$TimingLog[id]["total"]] === Missing,
      $TimingLog[id][
        "total"] = $TimingLog[id]["ended"] - $TimingLog[id][
        "started"],
      $TimingLog[id][
        "total"] += $TimingLog[id]["ended"] - $TimingLog[id][
        "started"]
    ];
    res
  ]]] /. {TaggedBlock -> Block, TaggedHold[e_] :> e}];

(**********************************************************************************************************************)
(* Insert timing for subexpressions *)
(**********************************************************************************************************************)

ClearAll[insertSubexpressionTiming];

insertSubexpressionTiming[expression_Hold] := Module[
  {functions, atomics},
  functions =
      Complement[Union[Cases[expression, (f_)[___] :> f, {2}]], {Hold}];
  atomics =
      Complement[
        Union[Cases[expression, (s_ /; Depth[s] == 1) :> s, {2}]], {Hold}];

  If[functions === {},
    With[{expanded = expandOnce[expression]},
      If[expanded =!= expression, insertSubexpressionTiming[expanded],
        expanded]
    ],
    Module[
      {patt, pos, replacements, exp},
      patt = Alternatives @@ (Blank[#] & /@ functions)~Join~atomics;
      pos = Position[expression, patt, 2];
      replacements =
          Extract[expression, pos, Hold] /.
              Hold[exp_] :> (HoldPattern[exp] :>
                  With[{eval = insertTiming[Hold[exp]]}, eval /; True]);
      expression /. replacements
    ]
  ]
];

(**********************************************************************************************************************)
(* Profiling Reports *)
(**********************************************************************************************************************)

Attributes[ProfilingReportData] = {HoldAllComplete};

Profile[expression_Hold] :=
    Module[
      {ready, results, report},
      $KernelStartTime = DatePlus[Now, {-SessionTime[], "Second"}];
      $TimingLog = <||>;

      ready = With[
        {timing = insertTiming[expression]},
        HoldComplete[timing]] //. Hold[exp_] :> exp /. $FunctionReplacements;

      results = ReleaseHold[ready];
      report = With[{v = Values[$TimingLog]}, ProfilingReportData[v]];
      {report, results}
    ];

With[{kst = DatePlus[Now, {-SessionTime[], "Second"}]},
  convertKernelTime[time_Real] := DatePlus[kst, {time, "Second"}]];
valueToInterval[v_Association] := {v["total"],
  Labeled[Interval[convertKernelTime /@ {v["started"], v["ended"]}],
    v["expStr"], Above]};

ClearAll[ProfilingPieChart];

ProfilingPieChart[report_ProfilingReportData, opts : OptionsPattern[]] :=
    Module[
      {timeSpent},
      timeSpent = SortBy[
        {#[[1]]["head"], Total[#["total"] & /@ #]} & /@
            GatherBy[report[[1]], #["head"] &],
        -Last[#] &
      ];
      PieChart[timeSpent[[All, 2]], ChartLabels -> timeSpent[[All, 1]], opts]
    ];

ClearAll[ProfilingTimelinePlot];

ProfilingTimelinePlot[report_ProfilingReportData, count_Integer : 100, opts : OptionsPattern[]] /; count > 0 :=
    Module[
      {plotInvervals},
      plotInvervals = SortBy[
        valueToInterval /@ report[[1]],
        -First[#] &
      ][[;; Min[Length[report[[1]]], count], 2]];
      TimelinePlot[plotInvervals, opts]
    ];


End[]; (* End Private Context *)

EndPackage[]