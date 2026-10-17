Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(* * * The 范畴 伴随 between two fixed 范畴 （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* An 对象 范畴: 左伴随, 右伴随, an
 伴随 between them. `∃` here [sigT], so 伴随 data
 no choice principle involved. （已译） *)
Definition AdjObj (C D : Category) : Type :=
  ∃ (F : D ⟶ C) (U : C ⟶ D), F ⊣ U.

Definition adjobj_left {C D : Category} (x : AdjObj C D) : D ⟶ C := `1 x.
Definition adjobj_right {C D : Category} (x : AdjObj C D) : C ⟶ D := `1 `2 x.
Definition adjobj_adj {C D : Category} (x : AdjObj C D) :
  adjobj_left x ⊣ adjobj_right x := `2 `2 x.

(* 相关说明。 （已译） *)
Record ConjPair {C D : Category} {x y : AdjObj C D} : Type := {
  conj_left  : adjobj_left x ⟹ adjobj_left y;
  conj_right : adjobj_right y ⟹ adjobj_right x;
  conj_pair_law :
    Conjugate (adjobj_adj y) (adjobj_adj x) conj_left conj_right
}.

(* Two conjugate pairs agree both components agree; by
 [conj_pair_right_unique] [conj_pair_left_unique] below, comparing
 either component alone would give same 关系. （已译） *)
#[export]
Program Instance ConjPair_Setoid {C D : Category} {x y : AdjObj C D} :
  Setoid (@ConjPair C D x y) := {|
  equiv := fun f g => (conj_left f ≈ conj_left g)
                    ∧ (conj_right f ≈ conj_right g)
|}.
Next Obligation.
  constructor.
  - intros f; split; reflexivity.
  - intros f g [Hl Hr]; split; symmetry; assumption.
  - intros f g h [Hl Hr] [Hl' Hr']; split; etransitivity; eassumption.
Qed.

Program Definition Adj (C D : Category) : Category := {|
  obj     := AdjObj C D;
  hom     := fun x y => @ConjPair C D x y;
  homset  := fun x y => @ConjPair_Setoid C D x y;
  id      := fun x => {| conj_left := nat_id; conj_right := nat_id |};
  compose := fun x y z f g =>
    {| conj_left  := conj_left f ∙ conj_left g
     ; conj_right := conj_right g ∙ conj_right f |}
|}.
(* The identity pair is conjugate: Conjugate.v's [conjugate_id]. *)
Next Obligation. exact (conjugate_id (adjobj_adj x)). Qed.
(* The 复合 pair conjugate: Conjugate.v's [conjugate_compose],
 whose conclusion already composes second component backward. （已译） *)
Next Obligation.
  exact (conjugate_compose (adjobj_adj z) (adjobj_adj y) (adjobj_adj x)
           _ _ _ _ (conj_pair_law f) (conj_pair_law g)).
Qed.
Next Obligation. proper; simpl in *; simplify; rewrites; reflexivity. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.
Next Obligation. split; simpl; intros; cat. Qed.

(* 相关说明。 （已译） *)
Section Determined.
Context {C D : Category} {x y : AdjObj C D}.

Lemma conj_pair_right_unique (f g : @ConjPair C D x y) :
  conj_left f ≈ conj_left g → conj_right f ≈ conj_right g.
Proof.
  intro H.
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_respects.
Qed.

Lemma conj_pair_left_unique (f g : @ConjPair C D x y) :
  conj_right f ≈ conj_right g → conj_left f ≈ conj_left g.
Proof.
  intro H.
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law f)).
  rewrite (conj_mate_inv_uniq _ _ _ _ (conj_pair_law g)).
  now apply conj_mate_inv_respects.
Qed.

End Determined.

(*
   本节说明自然变换、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example adj_id_sigma (C D : Category) (x : Adj C D) :
  conj_left (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_id_tau (C D : Category) (x : Adj C D) :
  conj_right (@id (Adj C D) x) = nat_id := eq_refl.

Example adj_compose_sigma (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_left (f ∘ g) = conj_left f ∙ conj_left g := eq_refl.

Example adj_compose_tau (C D : Category) (x y z : Adj C D)
        (f : y ~> z) (g : x ~> y) :
  conj_right (f ∘ g) = conj_right g ∙ conj_right f := eq_refl.
