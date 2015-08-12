(* Wolfram Language package *)

BeginPackage["OptimizationToolkit`Profiling`", {"OptimizationToolkit`"}];
(* Exported symbols added here with SymbolName::usage *)

Profile               ::usage = "";
ProfilingPieChart     ::usage = "";
ProfilingTimelinePlot ::usage = "";

Begin["`Private`"]; (* Begin Private Context *)

$KernelStartTime = DatePlus[Now, {-SessionTime[], "Second"}];
$TimingLog = <||>;

SetAttributes[OrderedTable, {HoldFirst}];
OrderedTable[expression_, iterators__] :=
  Table[expression, iterators];


SetAttributes[OrderedModule, {HoldAll}];
OrderedModule[locals_, expression__] :=
  With[ {l = locals},
    Module[ l,
      expression
    ]
  ];

test[x_]:= With[{local = x}, local];

$FunctionReplacements =
    {
      Table -> OrderedTable,
      Module -> OrderedModule
    };

ClearAll[NewTimingID];
Module[ {varCounter = 0},
  NewTimingID[] :=
    varCounter++
];

(**********************************************************************************************************************)
(* Insert timing for single expression *)
(**********************************************************************************************************************)

ClearAll[insertTiming];

insertTiming[expression_Hold] :=
  With[ {
  exp = insertSubexpressionTiming[expression],
  head = heldExpressionHead[expression],
  expStr = heldExpressionToString[expression],
  res = newVar
  },
    Hold[With[ {id = NewTimingID[]},
           TaggedBlock[{res},
           $TimingLog[id] = <|
           "head" -> head,
           "expStr" -> expStr,
           "started" -> SessionTime[]
           |>;
           res = TaggedHold[exp];
           $TimingLog[id]["ended"] = SessionTime[];
           If[ Head[$TimingLog[id]["total"]] === Missing,
             $TimingLog[id][
               "total"] = $TimingLog[id]["ended"] - $TimingLog[id][
               "started"],
             $TimingLog[id][
               "total"] += $TimingLog[id]["ended"] - $TimingLog[id][
               "started"]
           ];
           res
           ]
         ]] /. {TaggedBlock -> Block, TaggedHold[e_] :> e}
  ];

(**********************************************************************************************************************)
(* Insert timing for subexpressions *)
(**********************************************************************************************************************)

ClearAll[insertSubexpressionTiming];

insertSubexpressionTiming[expression_Hold] :=
  Module[ {functions, atomics},
    functions =
        Complement[Union[Cases[expression, (f_)[___] :> f, {2}]], {Hold}];
    atomics =
        Complement[
          Union[Cases[expression, (s_ /; Depth[s] == 1) :> s, {2}]], {Hold}];
    If[ functions === {},
      With[ {expanded = expandOnce[expression]},
        If[ expanded =!= expression,
          insertSubexpressionTiming[expanded],
          expanded
        ]
      ],
      Module[ {patt, pos, replacements},
        patt = Alternatives @@ (Blank[#] & /@ functions) ~ Join ~ atomics;
        pos = Position[expression, patt, 2];
        replacements =
            Extract[expression, pos, Hold] /.
                Hold[exp_] :> (HoldPattern[exp] :>
                    With[ {eval = insertTiming[Hold[exp]]},
                      eval /; True
                    ]);
        expression /. replacements
      ]
    ]
  ];

(**********************************************************************************************************************)
(* Profiling Reports *)
(**********************************************************************************************************************)

Attributes[ProfilingReportData] = {HoldAllComplete};

Profile[expression_Hold] :=
  Module[ {ready, results, report},
    $KernelStartTime = DatePlus[Now, {-SessionTime[], "Second"}];
    $TimingLog = <||>;
    ready = With[ {timing = insertTiming[expression]},
              HoldComplete[timing]
            ] //. Hold[exp_] :> exp /. $FunctionReplacements;
    results = ReleaseHold[ready];
    report = With[ {v = Values[$TimingLog]},
               ProfilingReportData[v]
             ];
    {report, results}
  ];

With[ {kst = DatePlus[Now, {-SessionTime[], "Second"}]},
  convertKernelTime[time_Real] :=
    DatePlus[kst, {time, "Second"}]
];
valueToInterval[v_Association] :=
  {v["total"],
  Labeled[Interval[convertKernelTime /@ {v["started"], v["ended"]}],
  v["expStr"], Above]};

ClearAll[ProfilingPieChart];

ProfilingPieChart[report_ProfilingReportData, opts : OptionsPattern[]] :=
  Module[ {timeSpent},
    timeSpent = SortBy[
      {#[[1]]["head"], Total[#["total"] & /@ #]} & /@
          GatherBy[report[[1]], #["head"] &],
      -Last[#] &
    ];
    PieChart[timeSpent[[All, 2]], ChartLabels -> timeSpent[[All, 1]], opts]
  ];

ClearAll[ProfilingTimelinePlot];

ProfilingTimelinePlot[report_ProfilingReportData, count_Integer : 100, opts : OptionsPattern[]] /; count > 0 :=
  Module[ {plotInvervals},
    plotInvervals = SortBy[
      valueToInterval /@ report[[1]],
      -First[#] &
    ][[;; Min[Length[report[[1]]], count], 2]];
    TimelinePlot[plotInvervals, opts]
  ];


ClearAll[$rec, $timing, Profile];
SetAttributes[$rec, {HoldAll}];
$rec[Hold[$timing_], exp_] :=
  Module[ {held, cleaned, s, t, res},
    held = With[ {e = Inactivate[exp]},
             HoldComplete[e]
           ];
    cleaned = held //. Inactive[$rec][e : __] :> e //. Inactive[f_] :> f //. Sequence[Hold[$timing], a___] :> a;
    s = StringTake[ToString[InputForm[cleaned]], {14, -2}];
    {t, res} = AbsoluteTiming[Activate[exp]];
    $timing[s] = If[ Head[$timing[s]] === Missing,
                   {t},
                   Append[$timing[s], t]
                 ];
    res
  ];

SetAttributes[Profile, {HoldAll}];
Profile2[exp_] :=
  Module[ {$timing, hexp, replaced, ready, result},
    $timing = <||>;
    hexp = Inactivate[exp];
    replaced = FixedPoint[# //. Flatten[Cases[#, Inactive[f_] :> With[ {d = DownValues[f]},
                                                                   Inactivate[d]
                                                                 ], Infinity, Heads -> True]] &, hexp];
    ready = Map[# /. e : Inactive[f_][a___] :> With[ {t = Hold[$timing]},
                                                 (Inactive[$rec][t, e])
                                               ] &, replaced, {0, Infinity}];
    result = Activate[ready];
    {$timing, result}
  ];

End[]; (* End Private Context *)

EndPackage[]