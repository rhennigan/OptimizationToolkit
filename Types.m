(* Mathematica Package         *)
(* Created by IntelliJ IDEA    *)

(* :Title: Types     *)
(* :Context: Types`  *)
(* :Author: rhennigan            *)
(* :Date: 7/21/2015              *)

(* :Package Version: 1.0       *)
(* :Mathematica Version:       *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                  *)
(* :Discussion:                *)

BeginPackage["OptimizationToolkit`Types`", {"OptimizationToolkit`"}];
(* Exported symbols added here with SymbolName::usage *)

GetTypeSignature::usage = "";
TensorType::usage = "";
UnknownType::usage = "";

Begin["`Private`"]; (* Begin Private Context *)

(**********************************************************************************************************************)

GetTypeSignature::utype = "Unable to determine type from pattern.";

iGetTypeSignature[downValue : (HoldPattern[_] :> _)] :=
    Module[
      {
        extractedArgs = Cases[downValue, Verbatim[HoldPattern][_[args___]] :> args]
      },
      extractedArgs /.
          Verbatim[Blank][] :> (Message[GetTypeSignature::utype]; _UnknownType) //.
          {
            Verbatim[Pattern][_, l_] :> l,
            Verbatim[Blank][t___] :> t
          } /.
          {patt_} /; ArrayQ[patt] && Length[Union[Flatten[patt]]] == 1 :>
              TensorType[Flatten[patt][[1]], Depth[patt] - 1]
    ];

GetTypeSignature[f_Symbol] := iGetTypeSignature /@ DownValues[f];

(**********************************************************************************************************************)

End[]; (* End Private Context *)

EndPackage[]