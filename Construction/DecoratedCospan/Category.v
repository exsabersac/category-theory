Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.DecoratedCospan.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/decorated+cospan
    Wikipedia: none-exists (the Wikipedia "Cospan" article does not
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872

   本文件给出范畴变体或层范畴等。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospanCategory.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(*
   本节说明 Category 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Coherent : Type := {
  (*
   本节说明拉回/推出、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dc_compose_respects_dec :
    forall {X Y Z : C}
           (g g' : DecoratedCospanArrow Y Z)
           (f f' : DecoratedCospanArrow X Y)
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_compose_respects_aux HP
                              (dc_cospan g) (dc_cospan g')
                              (dc_cospan f) (dc_cospan f')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_compose_decoration HP LM cospan_merge g f
      ≈ dec_compose_decoration HP LM cospan_merge g' f';

  (** Identity-decoration left coherence: the composite-decoration of
      [(id_decoration Y) ∘ f] equals [dc_decoration f] after transport
      along the cospan-level identity-left apex iso. *)
  dc_id_left_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_left HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            (dec_cospan_id id_decoration Y) f
      ≈ dc_decoration f;

  (** Identity-decoration right coherence: symmetric, for f ∘ id. *)
  dc_id_right_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_right HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            f (dec_cospan_id id_decoration X)
      ≈ dc_decoration f;

  (** Associativity of the decoration: the composite-decoration of
      [(h ∘ g) ∘ f] equals that of [h ∘ (g ∘ f)] after transport along
      the cospan-level associativity apex iso. *)
  dc_compose_assoc_dec :
    forall {X Y Z W : C}
           (h : DecoratedCospanArrow Z W)
           (g : DecoratedCospanArrow Y Z)
           (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_compose_assoc HP
                              (dc_cospan h)
                              (dc_cospan g)
                              (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            h (dec_cospan_compose HP LM cospan_merge g f)
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_compose HP LM cospan_merge h g) f
}.

(*
   本节说明 Category 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context `{DCC : DecCospan_Coherent}.

Set Default Proof Using "All".

(** Proper instance for composition.  The cospan part comes from
    [cospan_compose_respects_aux]; the decoration part from
    [dc_compose_respects_dec]. *)
Lemma dec_cospan_compose_respects_aux
      {X Y Z : C}
      (g g' : DecoratedCospanArrow Y Z) (f f' : DecoratedCospanArrow X Y)
      (Hf : dec_cospan_equiv f f') (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge g f)
    (dec_cospan_compose HP LM cospan_merge g' f').
Proof.
  unshelve econstructor.
  - exact (cospan_compose_respects_aux HP
             (dc_cospan g) (dc_cospan g')
             (dc_cospan f) (dc_cospan f')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl.
    exact (dc_compose_respects_dec g g' f f' Hf Hg).
Qed.

#[export] Program Instance dec_cospan_compose_respects {X Y Z : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_compose C HP MC D MD F LM H_Coc cospan_merge X Y Z).
Next Obligation.
  proper.
  now apply dec_cospan_compose_respects_aux.
Qed.

(** Identity laws and associativity, each pairing the cospan-level
    lemma with the matching coherence field. *)

Lemma dec_cospan_id_left {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge (dec_cospan_id id_decoration Y) f)
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_left HP (dc_cospan f)).
  - simpl. exact (dc_id_left_dec f).
Qed.

Lemma dec_cospan_id_right {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge f (dec_cospan_id id_decoration X))
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_right HP (dc_cospan f)).
  - simpl. exact (dc_id_right_dec f).
Qed.

Lemma dec_cospan_compose_assoc {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f).
Proof.
  unshelve econstructor.
  - exact (cospan_compose_assoc HP (dc_cospan h) (dc_cospan g) (dc_cospan f)).
  - simpl. exact (dc_compose_assoc_dec h g f).
Qed.

Lemma dec_cospan_compose_assoc_sym {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f)
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f)).
Proof.
  apply dec_cospan_equiv_sym, dec_cospan_compose_assoc.
Qed.

(** ** [DecoratedCospanCat] as a [Category] record *)

Program Definition DecoratedCospanCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => DecoratedCospanArrow X Y;
  homset   := fun X Y => DecoratedCospanArrow_Setoid;
  id       := fun X => dec_cospan_id id_decoration X;
  compose  := fun X Y Z g f => dec_cospan_compose HP LM cospan_merge g f;
  compose_respects := fun X Y Z => @dec_cospan_compose_respects X Y Z;
  id_left  := fun X Y f => dec_cospan_id_left f;
  id_right := fun X Y f => dec_cospan_id_right f;
  comp_assoc := fun X Y Z W f g h => dec_cospan_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => dec_cospan_compose_assoc_sym f g h
|}.

End DecoratedCospanCategory.

Arguments DecoratedCospanCat
  {C} HP {H_Coc} {MC} {D} {MD} {F} LM id_decoration cospan_merge {DCC}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
