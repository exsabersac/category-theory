Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Reflective.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(** * Boundary probe for Construction/Reflective/Limit.v (issue #373) *)

(*
   本文件为测试：ProbeReflectiveLimit373。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* If this command ever succeeds, the [Fail] wrapper is not doing its job
   and every negative below is worthless. *)

Fail Check probe373_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** Controls *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (reflector R).
Check (reflective_adj R).
Check (reflective_CreatesLimit R K : CreatesLimit K (Incl C S)).
Check (reflective_Incl_PreservesLimitCone R K
         : PreservesLimitCone K (Incl C S)).
Check (fun L : Limit (Incl C S ◯ K) =>
         creation_preserves_limit (reflective_CreatesLimit R K) L).
Check (fun x : Sub C S => to (reflective_counit_iso R x)).
Check (fun x : Sub C S =>
         @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x).
Check (fun (N : Cone K) (H : IsLimitCone N) => unique_obj (H N)).
Check (fun (N : Cone K) (x : J) => cone_leg N x).
Check (fun (N : Cone K) => FCone (Incl C S) N).
Check (@StrictlyCreatesLimit J (Sub C S) C K (Incl C S)).
Check (fun (L : Limit (Incl C S ◯ K)) (M : Cone K) (HM : IsLimitCone M)
           (P : Cone (Incl C S ◯ K)) =>
         reflective_two_routes_agree R K L M HM P).
Check (reflective_inherits_limits R K).
Check (reflective_lift R K).
Check (reflective_CreatesAllLimits R).
Check (reflective_Complete R).

(** ** CONVERSION 1: the two preservation routes are different terms *)

Fail Example probe_two_routes (L : Limit (Incl C S ◯ K)) :
  creation_preserves_limit (reflective_CreatesLimit R K) L
    = reflective_Incl_PreservesLimitCone R K := eq_refl.

(** ** CONVERSION 2: ... and their mediators do not agree on the nose *)

Fail Example probe_two_routes_med (L : Limit (Incl C S ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (Incl C S ◯ K)) :
  unique_obj
    (creation_preserves_limit (reflective_CreatesLimit R K) L M HM P)
    = unique_obj (reflective_Incl_PreservesLimitCone R K M HM P) := eq_refl.

(** ** CONVERSION 3: the counit isomorphism does not reduce *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_counit_iso_leg (x : Sub C S) :
  to (reflective_counit_iso R x)
    = @counit _ _ (reflector R) (Incl C S) (reflective_adj R) x := eq_refl.

(** ** TYPING 4: creation is not preservation *)

Fail Check (reflective_CreatesLimit R K
              : PreservesLimitCone K (Incl C S)).

(** ** TYPING 5: creation is not STRICT creation *)

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (reflective_CreatesLimit R K
              : StrictlyCreatesLimit K (Incl C S)).

End Boundaries.

(** ** FORMABILITY 6: [Subcategory] identifies hom with proof *)

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@homset Cu xu yu).

Fail Check (Subcategory Cu).

End UniverseProbe.

(** ** FORMABILITY 7 and 8: the cone vocabulary identifies J with C *)

(*
   本节说明函子、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ShapeUniverseProbe.

Universes jo jh jp vo vh vp.
Constraint jh < vh.

Context (Ju : Category@{jo jh jp}).
Context (Vu : Category@{vo vh vp}).

Check (obj[Ju]).
Check (obj[Vu]).
Check (Ju ⟶ Vu).

Context (Fu : Ju ⟶ Vu).

Check (@Cone Ju Vu Fu).
Check (@ACone Ju Vu).

Fail Check (@cone_leg Ju Vu Fu).
Fail Check (@IsLimitCone Ju Vu Fu).

End ShapeUniverseProbe.

(** ** Non-vacuity: the torsion-free abelian groups *)

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_KAb : 0 ⟶ Sub Ab TorsionFree_Sub :=
  From_0 (Sub Ab TorsionFree_Sub).

Definition probe_ab_cone : Cone (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| vertex_obj := @terminal_obj Ab Ab_Terminal |}.
  unshelve econstructor; intro x; inversion x.
Defined.

Definition probe_ab_limit : Limit (Incl Ab TorsionFree_Sub ◯ probe_KAb).
Proof.
  unshelve refine {| limit_cone := probe_ab_cone |}.
  intro N.
  unshelve econstructor.
  - exact (@one Ab Ab_Terminal _).
  - intro x; inversion x.
  - intros v Hv; apply (@one_unique Ab Ab_Terminal).
Defined.

Example probe_ab_limit_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_limit]
    = @terminal_obj Ab Ab_Terminal := eq_refl.

Definition probe_ab_created : Limit probe_KAb :=
  reflective_inherits_limits TorsionFree_Reflective probe_KAb probe_ab_limit.

(* The created cone IS the lift of the cone downstairs ... *)

Example probe_ab_created_cone :
  @limit_cone _ _ _ probe_ab_created
    = reflective_lift TorsionFree_Reflective probe_KAb probe_ab_cone
  := eq_refl.

(* ... its apex IS the reflector applied to the terminal object ... *)

Example probe_ab_created_apex :
  vertex_obj[@limit_cone _ _ _ probe_ab_created]
    = fobj[reflector TorsionFree_Reflective] (@terminal_obj Ab Ab_Terminal)
  := eq_refl.

(*
   本节说明同构、（余）强度、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example probe_ab_created_carrier :
  `1 (vertex_obj[@limit_cone _ _ _ probe_ab_created])
    = AbModTorsion (@terminal_obj Ab Ab_Terminal) := eq_refl.

(* The subcategory is complete as soon as [Ab] is; no completeness
   witness for [Ab] is claimed here, so this is a conditional. *)

Check (reflective_Complete TorsionFree_Reflective).
