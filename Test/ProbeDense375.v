Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.Dense.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Skeleton.Separation.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeDense375。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* 相关说明。 （已译） *)

Fail Check probe375_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context (S : Subcategory C).
Context (F : Subcategory.Full C S).
Context (D : IsoDense S).

(** ** Controls *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (Incl_Faithful C S).
Check (Full_Implies_Full_Functor C S F).
Check (IsoDense S).
Check (iso_dense_ESO S D).
Check (ESO_iso_dense S (iso_dense_ESO S D)).
Check (dense_incl_equivalence S F D).
Check (dense_incl_adjoint_equivalence S F D).
Check (dense_reflector S F D).
Check (dense_adj S F D).
Check (dense_full_subcategory_reflective S F D : Reflective S).
Check (fun a : Sub C S => dense_counit_iso S F D a).
Check (fun a : Sub C S => dense_counit_Isomorphism S F D a).
Check (fun a : Sub C S =>
         @counit _ _ (dense_reflector S F D) (Incl C S)
           (dense_adj S F D) a).
Check (fun a : Sub C S => @id (Sub C S) a).
Check (reflector (dense_full_subcategory_reflective S F D)).
Check (reflective_adj (dense_full_subcategory_reflective S F D)).
Check (reflective_full (dense_full_subcategory_reflective S F D)).
Check (fun a : Sub C S => reflective_counit_iso
         (dense_full_subcategory_reflective S F D) a).

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeDense375 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_iso_dense_round :
  ESO_iso_dense S (iso_dense_ESO S D) = D := eq_refl.

(* 相关说明。 （已译） *)

Example probe_iso_dense_round_obj (c : C) :
  `1 (ESO_iso_dense S (iso_dense_ESO S D) c) = `1 (D c) := eq_refl.

Example probe_ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO S (ESO_iso_dense S E) = E := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_counit_is_chosen_iso (a : Sub C S) :
  fmap[Incl C S]
    (@counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a)
    = to (`2 (D (Incl C S a))) := eq_refl.

Check (fun a : Sub C S =>
         (fmap[Incl C S]
            (@counit _ _ (dense_reflector S F D) (Incl C S)
               (dense_adj S F D) a),
          to (`2 (D (Incl C S a))))).

(* * ** TYPING 3: counit not 恒等, cannot be （已译） *)

(*
   本节说明（余）端、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example probe_counit_id (a : Sub C S) :
  @counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a
    = @id (Sub C S) a := eq_refl.

(* * ** TYPING 4: 伴随 not Reflective record （已译） *)

Fail Check (dense_adj S F D : Reflective S).

End Boundaries.

(* * ** FORMABILITY 5: [Subcategory] identifies hom 证明 （已译） *)

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

(* * ** Witness (i): skeleton indiscrete 范畴 bool （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_skel_refl :
  Reflective (skel_sub Indiscrete_bool_Skeleton) :=
  skeleton_reflective Indiscrete_bool_Skeleton.

Example probe_skel_true :
  fobj[reflector probe_skel_refl] true
    = skel_rep Indiscrete_bool_Skeleton true := eq_refl.

Example probe_skel_false :
  fobj[reflector probe_skel_refl] false
    = skel_rep Indiscrete_bool_Skeleton false := eq_refl.

(* 相关说明。 （已译） *)

Example probe_skel_carrier_false :
  `1 (fobj[reflector probe_skel_refl] false) = true := eq_refl.

(* ... so at [false] reflection moves 对象: it not inert. （已译） *)

Example probe_skel_not_inert :
  `1 (fobj[reflector probe_skel_refl] false) = false → False.
Proof. discriminate. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition BothPoints : Subcategory (Indiscrete bool) :=
  @Build_Subcategory (Indiscrete bool)
    (fun _ => True)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition BothPoints_Full :
  Construction.Subcategory.Full (Indiscrete bool) BothPoints :=
  fun _ _ _ _ _ => I.

Definition swap_dense : IsoDense BothPoints :=
  fun c => ((negb c; I); Indiscrete_iso (negb c) c).

Definition swap_reflective : Reflective BothPoints :=
  dense_full_subcategory_reflective BothPoints BothPoints_Full swap_dense.

(* The reflector negates. *)

Example swap_reflector_true :
  `1 (fobj[reflector swap_reflective] true) = false := eq_refl.

Example swap_reflector_false :
  `1 (fobj[reflector swap_reflective] false) = true := eq_refl.

(* The two endpoints counit at 对象 [a] DIFFERENT 对象
 [Sub], what makes 恒等 form ill-typed rather than
 merely unproved. （已译） *)

Lemma swap_objects_differ (a : Sub (Indiscrete bool) BothPoints) :
  fobj[reflector swap_reflective] (Incl (Indiscrete bool) BothPoints a) = a
    → False.
Proof.
  destruct a as [b p]; destruct b; simpl; intro H;
  inversion H.
Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma swap_not_self_dense :
  (∀ a : Sub (Indiscrete bool) BothPoints,
      `1 (swap_dense (Incl (Indiscrete bool) BothPoints a)) = a) → False.
Proof.
  intro H; exact (swap_objects_differ ((true; I)) (H (true; I))).
Qed.

(* The counit at such 对象 nevertheless 同构, is
 form 命题's third clause takes here. （已译） *)

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_iso BothPoints BothPoints_Full swap_dense a).

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_Isomorphism BothPoints BothPoints_Full swap_dense a).
