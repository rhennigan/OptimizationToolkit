(* Wolfram Language package *)

BeginPackage["OptimizationToolkit`Types`", {"OptimizationToolkit`"}];

Unprotect["`*"];
ClearAll["`*"];

GetTypeSignature ::usage = "";
TypeSignature    ::usage = "";
TensorType       ::usage = "";
UnknownType      ::usage = "";

Begin["`Private`"]; (* Begin Private Context *)

(**********************************************************************************************************************)

GetTypeSignature::utype = "Unable to determine type from pattern.";

homogenousArrayQ[patt_] :=
  ArrayQ[patt] && Length[Union[Flatten[patt]]] == 1;

toTensorType[patt_] :=
  TensorType[Flatten[patt][[1]], Depth[patt] - 1];

iGetTypeSignature[downValue : (HoldPattern[_] :> _)] :=
  Module[ {extractedArgs, noBlanks, noPatterns},
    extractedArgs = TypeSignature @@ Cases[downValue, Verbatim[HoldPattern][_[args___]] :> args];
    noBlanks = extractedArgs /. 
    Verbatim[Blank][] :> 
    (Message[GetTypeSignature::utype];
     _UnknownType);
    noPatterns = noBlanks //. {
      Verbatim[Pattern][_, l_] :> l,
      Verbatim[Blank][t___] :> t
    };
    noPatterns /. (patt_)?homogenousArrayQ :> toTensorType[patt]
  ];

GetTypeSignature[downValue : (HoldPattern[_] :> _)] :=
  iGetTypeSignature[downValue];
  
GetTypeSignature[function_Symbol] :=
  GetTypeSignature /@ DownValues[function];

(* TODO: generate CompiledFunction expressions from type signatures *)

(**********************************************************************************************************************)

End[]; (* End Private Context *)

EndPackage[]