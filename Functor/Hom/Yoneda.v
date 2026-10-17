Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The Yoneda lemma and the Yoneda embedding. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   本文件给出 Yoneda 相关结果。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the lemma的来源与用途

   https://mta.ca/~cat-dist/catlist/1999/yoneda

   本节说明Yoneda、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C^op }~> x =>
                     @fmap (C^op) Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric). *)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Lemma `(C : Category) `(F : C ⟶ Sets) :
  ∀ A : C, Copresheaves [Hom A,─] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C }~> x =>
                     @fmap C Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric). *)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Presheaves [Hom ─,A] [Hom ─,B] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X ∘ X0).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Copresheaves [Hom B,─] [Hom A,─] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X0 ∘ X).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.
