Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Variety.

Generalizable All Variables.

(* * * Comparing group variety 范畴 groups （已译） *)

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma nullary_bundle {A : Type} (k : UA.nullary → A) :
  k = (fun i => match i return A with end).
Proof. extensionality i; destruct i. Qed.

Lemma binary_bundle {A : Type} (k : UA.binary → A) :
  k = (fun i => match i return A with
                | UA.Fst => k UA.Fst
                | UA.Snd => k UA.Snd
                end).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma unary_bundle {A : Type} (k : UA.unary → A) : k = (fun _ => k UA.Only).
Proof. extensionality i; destruct i; reflexivity. Qed.

Lemma alg_hom_one {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B) :
  UA.map f (UA.one' (G:=A)) = UA.one' (G:=B).
Proof.
  unfold UA.one'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i.
Qed.

Lemma alg_hom_mul {A B : UA.OpAlgebra UA.GroupOp} (f : UA.AlgHom A B)
  (a b : UA.carrier A) :
  UA.map f (UA.mul' a b) = UA.mul' (UA.map f a) (UA.map f b).
Proof.
  unfold UA.mul'.
  rewrite UA.op_commute.
  f_equal.
  extensionality i; destruct i; reflexivity.
Qed.

(** ** The comparison functor *)

Section ToGrp.

(* 相关说明。 （已译） *)

Program Definition GroupVariety_obj_to_Grp (x : GroupVariety) : GrpObject := {|
  grp_setoid := {| carrier   := UA.carrier (`1 x)
                 ; is_setoid := eq_Setoid (UA.carrier (`1 x)) |};
  grp_unit := UA.one' (G:=`1 x);
  grp_mul  := fun a b => UA.mul' a b;
  grp_inv  := fun a => UA.inv' a;
  (* The carrier setoid is [eq_Setoid], so `≈` is already a [Prop]. *)
  grp_prop := eq_PropEquiv (UA.carrier (`1 x))
|}.
(*
   本节说明 GroupComparison 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  symmetry.
  exact (X UA.assoc (fun i => match i with
                              | UA.One => a | UA.Two => b | UA.Three => c
                              end)).
Qed.
Next Obligation.
  exact (X UA.unit_left (fun _ => a)).
Qed.
Next Obligation.
  exact (X UA.inv_left (fun _ => a)).
Qed.

Program Definition GroupVariety_hom_to_Grp {x y : GroupVariety} (f : x ~> y) :
  GrpHom (GroupVariety_obj_to_Grp x) (GroupVariety_obj_to_Grp y) := {|
  grp_map := {| morphism := UA.map (`1 f) |}
|}.
(* 相关说明。 （已译） *)
Next Obligation.
  exact (alg_hom_one f).
Qed.
Next Obligation.
  exact (alg_hom_mul f a b).
Qed.

Program Definition GroupVariety_to_Grp : GroupVariety ⟶ Grp := {|
  fobj := GroupVariety_obj_to_Grp;
  fmap := fun _ _ f => GroupVariety_hom_to_Grp f
|}.

End ToGrp.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma GroupVariety_to_Grp_Faithful : Faithful GroupVariety_to_Grp.
Proof. construct; simpl in *; auto. Qed.

Program Definition GroupVariety_hom_from_Grp {x y : GroupVariety}
  (g : GroupVariety_obj_to_Grp x ~{Grp}~> GroupVariety_obj_to_Grp y) : x ~> y :=
  ({| UA.map := grp_map g |}; I).
Next Obligation.
  destruct o; simpl.
  - (* 相关说明。 （已译） *)
    rewrite (nullary_bundle (fun i => grp_map g (args i))).
    rewrite (nullary_bundle args).
    exact (grp_map_unit g).
  - (* mul: binary *)
    rewrite (binary_bundle (fun i => grp_map g (args i))).
    rewrite (binary_bundle args).
    exact (grp_map_mul g (args UA.Fst) (args UA.Snd)).
  - (* inv: unary, where [inv'] uses a constant bundle *)
    rewrite (unary_bundle (fun i => grp_map g (args i))).
    rewrite (unary_bundle args).
    exact (grp_map_inv g (args UA.Only)).
Qed.

Program Definition GroupVariety_to_Grp_Full : Functor.Full GroupVariety_to_Grp := {|
  prefmap := fun _ _ g => GroupVariety_hom_from_Grp g
|}.

(*
   本节说明函子、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GroupVariety_to_Grp_reflects_iso :
  ∀ x y : GroupVariety,
    GroupVariety_to_Grp x ≅ GroupVariety_to_Grp y → x ≅ y :=
  @FullyFaithful _ _ GroupVariety_to_Grp
    GroupVariety_to_Grp_Full GroupVariety_to_Grp_Faithful.
