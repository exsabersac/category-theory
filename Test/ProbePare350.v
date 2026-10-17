(*
   本文件为测试：ProbePare350。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Construction.Karoubi.Universal.
Require Import Category.Adjunction.Pare.

Generalizable All Variables.

Section ProbeAssoc.

Context {A X : Category}.
Context (G : A ⟶ X).
Context (K : X ⟶ A).

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(*
   本节说明 ProbePare350 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ctl_assoc_fobj :
  @fobj A X ((G ◯ K) ◯ G) = @fobj A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_assoc_fmap :
  @fmap A X ((G ◯ K) ◯ G) = @fmap A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_unitor_fobj :
  @fobj A X (Id[X] ◯ G) = @fobj A X G := eq_refl.

Example ctl_unitor_fmap :
  @fmap A X (Id[X] ◯ G) = @fmap A X G := eq_refl.

(* NEGATIVE 1 (CONVERSION): whole 函子 records do NOT agree, even
 though both actions above do. [Compose] not associative the
 nose. （已译） *)
Fail Definition neg_assoc_record :
  ((G ◯ K) ◯ G) = (G ◯ (K ◯ G)) := eq_refl.

(* NEGATIVE 2 (CONVERSION): nor is [Id] a strict unit for it. *)
Fail Definition neg_unitor_record : (Id[X] ◯ G) = G := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition neg_unitor_right : (G ◯ Id[A]) = G := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_law_respects :
  @fmap_respects A X ((G ◯ K) ◯ G) = @fmap_respects A X (G ◯ (K ◯ G))
  := eq_refl.

Fail Definition neg_law_id :
  @fmap_id A X ((G ◯ K) ◯ G) = @fmap_id A X (G ◯ (K ◯ G)) := eq_refl.

Fail Definition neg_law_comp :
  @fmap_comp A X ((G ◯ K) ◯ G) = @fmap_comp A X (G ◯ (K ◯ G)) := eq_refl.

End ProbeAssoc.

Section ProbeTyping.

Context {A X : Category}.
Context (P : PareData A X).

(* 相关说明。 （已译） *)
Check (pare_Geps P).
Check (pare_rhoG P).
Check (pare_epsK P).
Check (pare_Krho P).

(* 相关说明。 （已译） *)
Check (pare_idem P : pare_K P ⟹ pare_K P).

(*
   本节说明 ProbePare350 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check ((pare_epsK P) ∙ (pare_Krho P)).

End ProbeTyping.

Section ProbeRoundTrip.

Context {A X : Category}.
Context (P : PareData A X).
Context (F : X ⟶ A).
Context (r : pare_K P ⟹ F) (s : F ⟹ pare_K P).
Context (Hsr : ∀ x, transform[s] x ∘ transform[r] x
                      ≈ transform[pare_idem P] x).
Context (Hrs : ∀ x, transform[r] x ∘ transform[s] x ≈ id).

(* CONTROL: 伴随 built splitting exists. （已译） *)
Check (pare_Adjunction P F r s Hsr Hrs).

(* 相关说明。 （已译） *)
Check (pare_r P F (pare_Adjunction P F r s Hsr Hrs)).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_round_trip :
  pare_r P F (pare_Adjunction P F r s Hsr Hrs) = r := eq_refl.

End ProbeRoundTrip.

(* Names negatives depend must named OUTSIDE [Fail],
 rename would leave file 编译 guard green. （已译） *)
Check @pare_idem.
Check @pare_idem_Idempotent.
Check @pare_unit.
Check @pare_counit.
Check @pare_Adjunction.
Check @pare_SplitIdempotent.
Check @pare_left_adjoint_iff_splits.
Check @PareSplits.
Check @PareLeftAdjoint.
Check @pare_epsK.
Check @pare_Krho.
Check @PareData.
Check @nat_compose.
Check @pare_r.
Check @fmap_respects.
Check @fmap_id.
Check @fmap_comp.
