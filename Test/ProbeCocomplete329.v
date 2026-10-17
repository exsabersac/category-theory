Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Chain.

Generalizable All Variables.

(** * Probe: strength boundaries of Sets cocompleteness *)

(*
   本文件为测试：ProbeCocomplete329。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DualityNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Check (Sets_Complete (Opposite D) (Opposite_Functor F)).

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Sets_Complete D F).

Check (Sets_Colimit F).

(*
   本节说明 ProbeCocomplete329 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Opposite_Functor F).

(*
   本节说明 ProbeCocomplete329 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Opposite D).

End DualityNegative.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ApexNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Definition probe_apex_is_sum :
  Sets_colim_obj F = Sets_colim_sum F := eq_refl.

End ApexNegative.

(* Positive controls naming Cocomplete.v's own constants: the carriers DO
   agree by eq_refl, and the apex equivalence IS the generated relation. *)
Check Sets_colim_carrier_is_coproduct.
Check Sets_colim_equiv_is_rel.
Check Sets_colim_obj.
Check Sets_colim_sum.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TriangleNegative.

Context (D : Category) (F : D ⟶ Sets) (N : Cocone F) (d : obj[D]).

Fail Definition probe_triangle_whole_morphism :
  Sets_colim_med F N ∘ Sets_colim_inj F d = vertex_map[N] := eq_refl.

End TriangleNegative.

(*
   本节说明 ProbeCocomplete329 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Sets_colim_med.
Check Sets_colim_inj.
Check @vertex_map.

(*
   本节说明 ProbeCocomplete329 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The quotient does not collapse: at the two-object discrete shape the
   two fibres stay apart. *)
Check two_fibres_not_collapsed.

Check two_fibres_not_equal_in_colimit.

Check two_disc_objects_distinct.

Check two_disc_hom_is_eq.

Check colim_rel_separates.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check omega_stages_merged.

Check omega_stages_apart_in_coproduct.

(* The degenerate control, labelled as one in its own file. *)
Check empty_shape_colim_empty.

(** ** The headline artifacts *)

Check Sets_Cocomplete.

Check Sets_Omega_Colimit.

Check Sets_Chain_Colimit.

Check Sets_colim_triangle.
