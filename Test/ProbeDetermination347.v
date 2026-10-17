(*
   本文件为测试：ProbeDetermination347。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Determination.

Generalizable All Variables.

(*
   本节说明伴随、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Probe.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
   本节说明 ProbeDetermination347 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example probe_ctl_obj (c : C) :
  coarrow_obj (adj_counit_couniversal A c) = U c := eq_refl.

Example probe_ctl_arrow (c : C) :
  coarrow (adj_counit_couniversal A c) = @counit C D F U A c := eq_refl.

Check @adj_counit_couniversal.
Check @adj_counit_couniversal_med.
Check @ump_couniversal_arrows.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_ctl_med (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    ≈ to adj[A] f := adj_counit_couniversal_med A c d f.

(*
   本节说明 ProbeDetermination347 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_med_strict (c : C) (d : D) (f : F d ~{C}~> c) :
  unique_obj (ump_couniversal_arrows (adj_counit_couniversal A c) f)
    = to adj[A] f := eq_refl.

End Probe.

(*
   本节说明 ProbeDetermination347 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_347_instrument : (true = false) := eq_refl.
