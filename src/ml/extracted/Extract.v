Require Vir.TopLevel.
Require Vir.Transformations.Transform.
Require Vir.ParserHelper.

Require ExtrOcamlBasic.
Require ExtrOcamlString.
Require ExtrOcamlIntConv.

Extraction Language Ocaml.
Extraction Blacklist String List Char Core Z Format.
Extract Inlined Constant Flocq.Core.Defs.F2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.FF2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.B2R => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.IEEE754.Binary.round_mode => "(fun _ -> assert false)".
Extract Inlined Constant Flocq.Calc.Bracket.inbetween_loc => "(fun _ -> assert false)".

Extract Inlined Constant Archi.ppc64 => "false".

Set Extraction AccessOpaque.
Cd "ml/extracted".

Extraction Library ExtrOcamlIntConv.
Recursive Extraction Library TopLevel.
Extraction Library Transform.
Extraction Library ParserHelper.
