Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/representable+functor

   本文件给出自然变换相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ClassifierNatural.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.
Context `{HS : @SubobjectClassifier C HT}.

(* ------------------------------------------------------------------------ *)
(** ** The substitution law *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition char_sub {x : C} (s : SubObj x) : x ~> Ω :=
  char (sub_mono s) (sub_is_monic s).

Example char_sub_is_classifier_to {x : C} (s : SubObj x) :
  char_sub s = to (classifier_classifies x) s := eq_refl.

(* 相关说明。 （已译） *)
Lemma char_sub_respects {x : C} (s s' : SubObj x) :
  s ≈ s' → char_sub s ≈ char_sub s'.
Proof. destruct s, s'; apply char_respects. Qed.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma char_reindex {x y : C} (f : y ~> x) (s : SubObj x) :
  char_sub (sub_reindex f s) ≈ char_sub s ∘ f.
Proof.
  transitivity (char_sub (sub_reindex (char_sub s ∘ f) truth_subobject)).
  - apply char_sub_respects.
    symmetry.
    transitivity (sub_reindex f (sub_reindex (char_sub s) truth_subobject)).
    + apply sub_reindex_comp.
    + apply sub_reindex_respects, classifier_pullback_roundtrip.
  - apply classifier_char_roundtrip.
Qed.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma reindex_char {x y : C} (f : y ~> x) (h : x ~> Ω) :
  sub_reindex f (sub_reindex h truth_subobject)
    ≈ sub_reindex (h ∘ f) truth_subobject.
Proof. symmetry; apply sub_reindex_comp. Qed.

(*
   本节说明等价、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma sub_reindex_id_sym {x : C} (s : SubObj x) : s ≈ sub_reindex id s.
Proof. symmetry; apply sub_reindex_id. Qed.

Lemma classifier_pullback_roundtrip_id {x : C} (s : SubObj x) :
  sub_reindex (char_sub s) truth_subobject ≈ sub_reindex id s.
Proof.
  transitivity s.
  - apply classifier_pullback_roundtrip.
  - apply sub_reindex_id_sym.
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* Both components taken verbatim [classifier_classifies], so what
 two definitions add precisely 自然性 field. （已译） *)

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition classifier_char_transform :
  @Transform (C^op) Sets (@Sub C HP) (@Curried_CoHom C Ω) := {|
  transform := fun x : C => to (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; symmetry; apply (@char_reindex x y f). Qed.
Next Obligation. simpl; intros; apply (@char_reindex x y f). Qed.

Program Definition classifier_pullback_transform :
  @Transform (C^op) Sets (@Curried_CoHom C Ω) (@Sub C HP) := {|
  transform := fun x : C => from (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; apply (@reindex_char x y f). Qed.
(* 相关说明。 （已译） *)
Next Obligation.
  simpl; intros; rename x0 into h.
  exact (sub_reindex_comp h f truth_subobject).
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Program Definition Sub_classifier_natural :
  @Isomorphism ([(C^op), Sets]) (@Sub C HP) (@Curried_CoHom C Ω) := {|
  to   := classifier_char_transform ;
  from := classifier_pullback_transform
|}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply classifier_char_roundtrip.
  - symmetry; apply id_right.
Qed.
Next Obligation. simpl; intros; apply classifier_pullback_roundtrip_id. Qed.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example classifier_natural_component_to (x : C) :
  transform (to Sub_classifier_natural) x = to (classifier_classifies x)
  := eq_refl.

Example classifier_natural_component_from (x : C) :
  transform (from Sub_classifier_natural) x = from (classifier_classifies x)
  := eq_refl.

Example classifier_natural_to_computes (x : C) (s : SubObj x) :
  transform (to Sub_classifier_natural) x s = char_sub s := eq_refl.

Example classifier_natural_from_computes (x : C) (h : x ~> Ω) :
  transform (from Sub_classifier_natural) x h
    = sub_reindex h truth_subobject := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The Yoneda reading *)

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example CoHom_is_Hom_op : @Curried_CoHom C Ω = @Curried_Hom (C^op) Ω := eq_refl.

Definition Sub_Representable : Representable (@Sub C HP) :=
  @Build_Representable (C^op) (@Sub C HP) (@Ω C HT HS)
    (iso_sym Sub_classifier_natural).

Example Sub_repr_obj :
  @repr_obj (C^op) (@Sub C HP) Sub_Representable = @Ω C HT HS := eq_refl.

End ClassifierNatural.
