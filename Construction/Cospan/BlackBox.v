Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

(*
    Reference: Baez–Fong, "A compositional framework for passive linear

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Section: forgetful black-box on decorated cospans *)

Section ForgetDecoration.

Context {C : Category}.
Context (HP : HasPushouts C).
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context (F : C ⟶ D).
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context `{H_Coc : @Cocartesian C}.

(** The action on objects: identity. *)
Definition forget_decoration_obj : C -> C := fun X => X.

(** The action on morphisms: project the cospan out of the decorated cospan. *)
Definition forget_decoration_morphism
  {X Y : C} (f : DecoratedCospanArrow X Y)
  : CospanArrow X Y := dc_cospan f.

(** [forget_decoration] respects the decorated-cospan equivalence,
    descending to a well-defined function on the equivalence classes
    of [DecoratedCospanCat]. *)
Lemma forget_decoration_morphism_respects
  {X Y : C} (f g : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g ->
  cospan_equiv (forget_decoration_morphism f) (forget_decoration_morphism g).
Proof.
  intros [E _].
  exact E.
Qed.

Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(** [forget_decoration] preserves identity: the underlying cospan of the
    identity-decorated cospan on [X] is the identity cospan on [X]. *)
Lemma forget_decoration_id (X : C) :
  forget_decoration_morphism
    (dec_cospan_id id_decoration X)
  = cospan_id X.
Proof. reflexivity. Qed.

(** [forget_decoration] preserves composition: the underlying cospan of a
    composed decorated cospan is the composed cospan. *)
Lemma forget_decoration_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  forget_decoration_morphism
    (dec_cospan_compose HP LM cospan_merge g f)
  = cospan_compose HP (forget_decoration_morphism g) (forget_decoration_morphism f).
Proof. reflexivity. Qed.

(** Cospan-equivalence variants (for downstream use via [≈] rewriting). *)
Lemma forget_decoration_correct_id {X : C} :
  cospan_equiv
    (forget_decoration_morphism (dec_cospan_id id_decoration X))
    (cospan_id X).
Proof. apply cospan_equiv_refl. Qed.

Lemma forget_decoration_correct_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  cospan_equiv
    (forget_decoration_morphism
       (dec_cospan_compose HP LM cospan_merge g f))
    (cospan_compose HP
       (forget_decoration_morphism g)
       (forget_decoration_morphism f)).
Proof.
  rewrite forget_decoration_compose.
  apply cospan_equiv_refl.
Qed.

End ForgetDecoration.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ForgetDecorationFunctor.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.

Program Definition forget_decoration
  : (DecoratedCospanCat HP LM id_decoration cospan_merge) ⟶ (CospanCat C HP) := {|
  fobj := fun X => X;
  fmap := fun X Y f => @forget_decoration_morphism C D MD F X Y f
|}.
Next Obligation.
  proper.
  apply (@forget_decoration_morphism_respects C D MD F);
    assumption.
Defined.
Next Obligation.
  apply (@forget_decoration_correct_id C D MD F id_decoration).
Defined.
Next Obligation.
  apply (@forget_decoration_correct_compose C HP MC D MD F LM
                                            H_Coc cospan_merge).
Defined.

End ForgetDecorationFunctor.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
