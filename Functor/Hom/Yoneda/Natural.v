Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/Yoneda+lemma

   本文件给出自然变换相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The two bifunctors *)

Section YonedaBifunctors.

Context (C : Category).

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition yo_eval_obj (p : [C, Sets] ∏ C) : Sets := fst p (snd p).

Definition yo_eval_map {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_eval_obj x ~{Sets}~> yo_eval_obj y :=
  transform[fst tf] (snd y) ∘ fmap[fst x] (snd tf).

Lemma yo_eval_map_respects (x y : [C, Sets] ∏ C) :
  Proper (equiv ==> equiv) (@yo_eval_map x y).
Proof.
  destruct x as [F a], y as [G b].
  intros [tau f] [tau' f'] [Ht Hf] z; simpl in *.
  rewrite (@fmap_respects _ _ F _ _ _ _ Hf z).
  apply Ht.
Qed.

Lemma yo_eval_map_id (x : [C, Sets] ∏ C) : @yo_eval_map x x id ≈ id.
Proof.
  destruct x as [F a]; intro z; simpl.
  srewrite (@fmap_id _ _ F a).
  now srewrite (@fmap_id _ _ F a).
Qed.

Lemma yo_eval_map_comp (x y z : [C, Sets] ∏ C) (g : y ~> z) (f : x ~> y) :
  yo_eval_map (g ∘ f) ≈ yo_eval_map g ∘ yo_eval_map f.
Proof.
  destruct x as [F a], y as [G b], z as [H c].
  destruct g as [sigma g], f as [tau f]; intro w; simpl in *.
  srewrite (@naturality _ _ _ _ tau b c g).
  now srewrite (@fmap_comp _ _ F a b c g f).
Qed.

Definition YoEval : ([C, Sets] ∏ C) ⟶ Sets := {|
  fobj          := yo_eval_obj;
  fmap          := @yo_eval_map;
  fmap_respects := yo_eval_map_respects;
  fmap_id       := fun x => yo_eval_map_id x;
  fmap_comp     := fun x y z g f => yo_eval_map_comp x y z g f
|}.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma yo_eval_map_alt {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_eval_map tf ≈ fmap[fst y] (snd tf) ∘ transform[fst tf] (snd x).
Proof.
  destruct x as [F a], y as [G b], tf as [tau f]; intro z; simpl in *.
  now srewrite (@naturality _ _ _ _ tau a b f).
Qed.

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Yoneda_op : C ⟶ ([C, Sets])^op := Opposite_Functor (Curried_Hom C).

Definition YoNat : ([C, Sets] ∏ C) ⟶ Sets :=
  Hom ([C, Sets]) ◯ (Yoneda_op ∏⟶ Id) ◯ Swap.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition yo_nat_obj (p : [C, Sets] ∏ C) : Sets :=
  {| carrier   := @hom ([C, Sets]) [Hom (snd p),─] (fst p)
   ; is_setoid := @homset ([C, Sets]) [Hom (snd p),─] (fst p) |}.

Definition yo_nat_obj_agrees (p : [C, Sets] ∏ C) :
  fobj[YoNat] p = yo_nat_obj p := eq_refl.

(* 相关说明。 （已译） *)
Program Definition yo_nat_map {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_nat_obj x ~{Sets}~> yo_nat_obj y :=
  {| morphism := fun a =>
       fst tf ∘[[C, Sets]] a ∘[[C, Sets]]
         (@fmap _ _ (Curried_Hom C) (snd y) (snd x) (snd tf)) |}.
Next Obligation.
  repeat intro; simpl.
  now rewrite X.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition yo_nat_map_agrees {x y : [C, Sets] ∏ C} (tf : x ~> y)
  (a : fobj[YoNat] x) : fmap[YoNat] tf a = yo_nat_map tf a := eq_refl.

End YonedaBifunctors.

Arguments yo_eval_obj {C} p.
Arguments yo_eval_map {C x y} tf.
Arguments yo_nat_obj {C} p.
Arguments yo_nat_map {C x y} tf.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition yoneda_natural (C : Category) :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoNat C) (YoEval C) := {|
  to   := {| transform :=
               fun p => to   (Covariant_Yoneda_Lemma C (fst p) (snd p)) |};
  from := {| transform :=
               fun p => from (Covariant_Yoneda_Lemma C (fst p) (snd p)) |}
|}.
Next Obligation.
  srewrite (@naturality _ _ _ _ x0 o0 o h).
  apply proper_morphism, proper_morphism.
  unfold op; cat.
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ x0 o0 o h).
  apply proper_morphism, proper_morphism.
  unfold op; cat.
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ t o x1 x2).
  apply proper_morphism.
  unfold op; now srewrite (@fmap_comp _ _ f0 o0 o x1 x2 h).
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ t o x1 x2).
  apply proper_morphism.
  unfold op; now srewrite (@fmap_comp _ _ f0 o0 o x1 x2 h).
Qed.
Next Obligation.
  srewrite (@fmap_id _ _ f o).
  now srewrite (@fmap_id _ _ f o).
Qed.
Next Obligation.
  srewrite (@fmap_id _ _ f x1).
  srewrite (@naturality _ _ _ _ x0 o x1 x2).
  apply proper_morphism.
  unfold op; cat.
Qed.

(* The components ARE existing pointwise Yoneda 同构, both
 legs. Leibniz [eq_refl] — convertibility exception. （已译） *)
Definition yoneda_natural_to_component
  (C : Category) (F : C ⟶ Sets) (A : C) :
  transform[to (yoneda_natural C)] (F, A) = to (Covariant_Yoneda_Lemma C F A)
  := eq_refl.

Definition yoneda_natural_from_component
  (C : Category) (F : C ⟶ Sets) (A : C) :
  transform[from (yoneda_natural C)] (F, A)
    = from (Covariant_Yoneda_Lemma C F A)
  := eq_refl.

(* The naturality square, written out at a pair of arrows. *)
Lemma yoneda_natural_square (C : Category) (F G : C ⟶ Sets) (A B : C)
      (tau : F ⟹ G) (f : A ~{C}~> B) (al : fobj[YoNat C] (F, A)) :
  transform[to (yoneda_natural C)] (G, B)
      (@fmap _ _ (YoNat C) (F, A) (G, B) (tau, f) al)
    ≈ @fmap _ _ (YoEval C) (F, A) (G, B) (tau, f)
        (transform[to (yoneda_natural C)] (F, A) al).
Proof.
  exact (@naturality_sym _ _ _ _ (to (yoneda_natural C))
           (F, A) (G, B) (tau, f) al).
Qed.

(* ...and same square elementary terms: Mac Lane's two readings of
 复合, one going through representable one through F. （已译） *)
Corollary yoneda_eval_at_identity (C : Category) (F G : C ⟶ Sets) (A B : C)
      (tau : F ⟹ G) (f : A ~{C}~> B) (al : [Hom A,─] ⟹ F) :
  transform[tau] B (transform[al] B (id ∘ f))
    ≈ transform[tau] B (fmap[F] f (transform[al] A id)).
Proof. exact (yoneda_natural_square C F G A B tau f al). Qed.

(* 相关说明。 （已译） *)

Section EvaluationAt.

Context (C : Category).
Context (c : C).

(* ev_c : [C, Sets] ⟶ Sets, F ↦ F c. *)
Program Definition YoEvalAt : [C, Sets] ⟶ Sets := {|
  fobj := fun F => F c;
  fmap := fun F G tau => transform[tau] c
|}.
Next Obligation. srewrite (@fmap_id _ _ x c). reflexivity. Qed.

(* It is partial application evaluation bifunctor: 对象
 definitionally (Leibniz [eq_refl]), arrows only up ≈, because the
 bifunctor's action at ⟨τ, id⟩ still transports along [fmap[F] id].（已译） *)
Definition yo_eval_at_obj (F : C ⟶ Sets) :
  fobj[YoEvalAt] F = fobj[YoEval C] (F, c) := eq_refl.

Lemma yo_eval_at_map (F G : C ⟶ Sets) (tau : F ⟹ G) :
  fmap[YoEvalAt] tau ≈ @fmap _ _ (YoEval C) (F, c) (G, c) (tau, id[c]).
Proof. intro z; simpl; symmetry; now srewrite (@fmap_id _ _ F c). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition yo_repr_naturality_strict (F G : C ⟶ Sets) (tau : F ⟹ G)
  (al : [Hom c,─] ⟹ F) :
  transform[tau] c (transform[al] c id)
    = transform[nat_compose tau al] c id
  := eq_refl.

#[export] Program Instance YoEvalAt_Representable : Representable YoEvalAt := {|
  repr_obj := [Hom c,─];
  represented :=
    {| to   := {| transform := fun F => to   (Covariant_Yoneda_Lemma C F c) |}
     ; from := {| transform := fun F => from (Covariant_Yoneda_Lemma C F c) |} |}
|}.
Next Obligation. now srewrite (@naturality _ _ _ _ f c x1 x2). Qed.
Next Obligation. now srewrite (@naturality _ _ _ _ f c x1 x2). Qed.
Next Obligation.
  srewrite (@fmap_id _ _ x x1).
  srewrite (@naturality _ _ _ _ x0 c x1 x2).
  apply proper_morphism; cat.
Qed.

(* The 表示 对象 representable copresheaf nose. （已译） *)
Definition yo_repr_obj : @repr_obj _ _ YoEvalAt_Representable = [Hom c,─]
  := eq_refl.

End EvaluationAt.

Arguments YoEvalAt {C} c.

(*
   本节说明函子、层/筛、Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition YoEvalPre@{u u0 u1} (C : Category@{u u0 u0}) :
  ((@Presheaves C Sets@{u0 u1}) ∏ (C^op)) ⟶ Sets@{u0 u1} := YoEval (C^op).

Definition YoNatPre@{u u0 u1} (C : Category@{u u0 u0}) :
  ((@Presheaves C Sets@{u0 u1}) ∏ (C^op)) ⟶ Sets@{u0 u1} := YoNat (C^op).

Definition yoneda_natural_pre (C : Category) :
  @Isomorphism ([((@Presheaves C Sets) ∏ (C^op)), Sets])
               (YoNatPre C) (YoEvalPre C)
  := yoneda_natural (C^op).

(* The presheaf-side object actions, read in C's own vocabulary. *)
Definition yo_nat_pre_obj@{u u0 u1} (C : Category@{u u0 u0})
  (F : C^op ⟶ Sets@{u0 u1}) (A : C) :
  fobj[YoNatPre C] (F, A) = Presheaves [Hom ─,A] F := eq_refl.

Definition yo_eval_pre_obj@{u u0 u1} (C : Category@{u u0 u0})
  (F : C^op ⟶ Sets@{u0 u1}) (A : C) :
  fobj[YoEvalPre C] (F, A) = F A := eq_refl.

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Yoneda_Lemma_derived (C : Category) (F : C^op ⟶ Sets) (A : C) :
  Presheaves [Hom ─,A] F ≅ F A := Covariant_Yoneda_Lemma (C^op) F A.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition yoneda_lemma_derived_to (C : Category) (F : C^op ⟶ Sets) (A : C)
  (x : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) x = to (Yoneda_Lemma C F A) x := eq_refl.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition yoneda_lemma_derived_from_at
  (C : Category) (F : C^op ⟶ Sets) (A : C) (y : F A) (x : C)
  (phi : x ~{C}~> A) :
  transform[from (Yoneda_Lemma_derived C F A) y] x phi
    = transform[from (Yoneda_Lemma C F A) y] x phi := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma yoneda_lemma_derived_agrees (C : Category) (F : C^op ⟶ Sets) (A : C) :
  to (Yoneda_Lemma_derived C F A) ≈ to (Yoneda_Lemma C F A)
    ∧ from (Yoneda_Lemma_derived C F A) ≈ from (Yoneda_Lemma C F A).
Proof. split; simpl; intros; reflexivity. Qed.

(* The components presheaf-side natural 同构 in-tree
 [Yoneda_Lemma]'s maps, pointwise nose. （已译） *)
Definition yoneda_natural_pre_to_component
  (C : Category) (F : C^op ⟶ Sets) (A : C) (x : Presheaves [Hom ─,A] F) :
  transform[to (yoneda_natural_pre C)] (F, A) x = to (Yoneda_Lemma C F A) x
  := eq_refl.

Definition yoneda_natural_pre_from_component
  (C : Category) (F : C^op ⟶ Sets) (A : C) (y : F A) (x : C)
  (phi : x ~{C}~> A) :
  transform[transform[from (yoneda_natural_pre C)] (F, A) y] x phi
    = transform[from (Yoneda_Lemma C F A) y] x phi
  := eq_refl.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Witness.

Notation NatCat := (Deloop Nat_Plus).
Notation NatRep := (fobj[Curried_Hom NatCat] ttt).

(* Two endomorphisms representable: precomposition 5 with
 2. Each [fmap] Yoneda 函子 at arrow. （已译） *)
Definition yo_wit_alpha (n : nat) : NatRep ⟹ NatRep :=
  @fmap _ _ (Curried_Hom NatCat) ttt ttt n.

(* Evaluation at 恒等 reads arrow back off transformation:
 forward leg Yoneda 同构 sends [yo_wit_alpha n] n. （已译） *)
Example yo_wit_to_alpha_5 :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt) (yo_wit_alpha 5%nat) = 5%nat
  := eq_refl.

Example yo_wit_to_alpha_2 :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt) (yo_wit_alpha 2%nat) = 2%nat
  := eq_refl.

(* ...so forward leg not 常值, transformations are
 distinct: 同构 separates them. （已译） *)
Lemma yo_wit_alpha_distinct :
  yo_wit_alpha 5%nat ≈ yo_wit_alpha 2%nat → False.
Proof.
  intro H.
  pose proof (H ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

(* Both components pair square probed at non-恒等, so
 instance below not disguised unit law. （已译） *)
Lemma yo_wit_alpha_not_id :
  yo_wit_alpha 2%nat ≈ @id ([NatCat, Sets]) NatRep → False.
Proof.
  intro H.
  pose proof (H ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma yo_wit_arrow_not_id :
  (3%nat : ttt ~{NatCat}~> ttt) ≈ @id NatCat ttt → False.
Proof. intro H; simpl in H; discriminate. Qed.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example yo_wit_square_left :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt)
    (@fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
       (yo_wit_alpha 2%nat, 3%nat) (yo_wit_alpha 5%nat)) = 10%nat
  := eq_refl.

Example yo_wit_square_right :
  @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat)
    (transform[to (yoneda_natural NatCat)] (NatRep, ttt)
       (yo_wit_alpha 5%nat))
    = 10%nat
  := eq_refl.

(* The square itself, at pair — instance 定理, not of
 [eq_refl]. （已译） *)
Lemma yo_wit_square :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt)
    (@fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
       (yo_wit_alpha 2%nat, 3%nat) (yo_wit_alpha 5%nat))
    ≈ @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
        (yo_wit_alpha 2%nat, 3%nat)
        (transform[to (yoneda_natural NatCat)] (NatRep, ttt)
           (yo_wit_alpha 5%nat)).
Proof.
  exact (yoneda_natural_square NatCat NatRep NatRep ttt ttt
           (yo_wit_alpha 2%nat) 3%nat (yo_wit_alpha 5%nat)).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma yo_wit_eval_map_not_id :
  @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat) ≈ id → False.
Proof.
  intro H.
  pose proof (H 5%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma yo_wit_nat_map_not_id :
  @fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat) ≈ id → False.
Proof.
  intro H.
  pose proof (H (yo_wit_alpha 5%nat) ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

(* ...and 对象 E at pair genuinely has more than one element,
 so 同构 not between singletons. （已译） *)
Lemma yo_wit_eval_obj_nontrivial :
  ∃ u v : fobj[YoEval NatCat] (NatRep, ttt), u ≈ v → False.
Proof. exists 0%nat, 1%nat; intro H; discriminate. Qed.

(* Riehl's Remark 2.2.7 at witness: evaluation at single 对象 is
 已表示的 representable copresheaf. （已译） *)
Example yo_wit_repr_obj :
  @repr_obj _ _ (YoEvalAt_Representable NatCat ttt)
    = fobj[Curried_Hom NatCat] ttt := eq_refl.

Example yo_wit_repr_to :
  transform[to (@represented _ _ (YoEvalAt_Representable NatCat ttt))]
    NatRep (yo_wit_alpha 5%nat) = 5%nat := eq_refl.

End Witness.
