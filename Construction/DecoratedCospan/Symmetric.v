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
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

Generalizable All Variables.

(*
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    nLab: https://ncatlab.org/nlab/show/decorated+cospan
    Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospanSymmetric.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.

(*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dec_tensor_decoration
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : @I D _ ~{D}~> F (cospan_apex (cospan_tensor (dc_cospan f) (dc_cospan g))) :=
  let Nf := cospan_apex (dc_cospan f) in
  let Ng := cospan_apex (dc_cospan g) in
  fmap[F] (cospan_merge Nf Ng)
    ∘ lax_ap[F]
    ∘ bimap (dc_decoration f) (dc_decoration g)
    ∘ from (@unit_left D _ (@I D _)).

Definition dec_cospan_tensor
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : DecoratedCospanArrow (X + Y) (X' + Y') := {|
  dc_cospan := cospan_tensor (dc_cospan f) (dc_cospan g);
  dc_decoration := dec_tensor_decoration f g
|}.

(*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Bifunctor_Coherent : Type := {
  (*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dec_tensor_id_dec :
    forall (X Y : C),
      fmap[F] (to (projT1 (cospan_tensor_id X Y)))
        ∘ dec_tensor_decoration
            (dec_cospan_id id_decoration X)
            (dec_cospan_id id_decoration Y)
      ≈ id_decoration (X + Y)%object;

  (** Decoration coherence for [tensor_respects]: pairwise equivalent
      decorated cospans yield equivalent tensors, with the decoration
      transporting along the per-component apex isos. *)
  dec_tensor_respects_dec :
    forall {X Y X' Y' : C}
           (f f' : DecoratedCospanArrow X Y)
           (g g' : DecoratedCospanArrow X' Y')
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_tensor_respects
                              (dc_cospan f) (dc_cospan f')
                              (dc_cospan g) (dc_cospan g')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_tensor_decoration f g
      ≈ dec_tensor_decoration f' g';

  (** Decoration interchange: the tensor of two composites equals the
      composite of two tensors, with decorations matching after the
      cospan-level apex-iso transport. *)
  dec_tensor_compose_compat_dec :
    forall {X Y Z X' Y' Z' : C}
           (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
           (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y'),
      fmap[F] (to (projT1 (cospan_tensor_compose_compat HP
                              (dc_cospan g) (dc_cospan f)
                              (dc_cospan g') (dc_cospan f'))))
        ∘ dec_tensor_decoration
            (dec_cospan_compose HP LM cospan_merge g f)
            (dec_cospan_compose HP LM cospan_merge g' f')
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_tensor g g')
          (dec_cospan_tensor f f')
}.

Context `{DCBC : DecCospan_Bifunctor_Coherent}.

Set Default Proof Using "All".

(** ** Bifunctor-level lemmas, pairing cospan + decoration coherences *)

Lemma dec_cospan_tensor_id (X Y : C) :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_id id_decoration X)
       (dec_cospan_id id_decoration Y))
    (dec_cospan_id id_decoration (X + Y)%object).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_id X Y).
  - simpl. exact (dec_tensor_id_dec X Y).
Qed.

Lemma dec_cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : DecoratedCospanArrow X Y)
      (g g' : DecoratedCospanArrow X' Y')
      (Hf : dec_cospan_equiv f f')
      (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_tensor f g)
    (dec_cospan_tensor f' g').
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_respects
             (dc_cospan f) (dc_cospan f')
             (dc_cospan g) (dc_cospan g')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl. exact (dec_tensor_respects_dec f f' g g' Hf Hg).
Qed.

Lemma dec_cospan_tensor_compose_compat
      {X Y Z X' Y' Z' : C}
      (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
      (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y') :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_compose HP LM cospan_merge g f)
       (dec_cospan_compose HP LM cospan_merge g' f'))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_tensor g g')
       (dec_cospan_tensor f f')).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_compose_compat HP
             (dc_cospan g) (dc_cospan f)
             (dc_cospan g') (dc_cospan f')).
  - simpl. exact (dec_tensor_compose_compat_dec g f g' f').
Qed.

(** ** [DecoratedCospan_Bifunctor]: the Bifunctor on [DecoratedCospanCat] *)

#[export] Program Instance dec_cospan_tensor_respects_proper
  {X Y X' Y' : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_tensor X X' Y Y').
Next Obligation.
  proper.
  now apply dec_cospan_tensor_respects.
Qed.

Program Definition DecoratedCospan_Bifunctor
  : ((DecoratedCospanCat HP LM id_decoration cospan_merge)
       ∏ (DecoratedCospanCat HP LM id_decoration cospan_merge))
    ⟶ (DecoratedCospanCat HP LM id_decoration cospan_merge) := {|
  fobj := fun xy => @Cospan_tensor_obj C H_Coc (fst xy) (snd xy);
  fmap := fun xy uv fg => dec_cospan_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply dec_cospan_tensor_respects; assumption.
Qed.
Next Obligation.
  apply dec_cospan_tensor_id.
Qed.
Next Obligation.
  apply dec_cospan_tensor_compose_compat.
Qed.

(*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dec_mor_as_cospan {X Y : C} (f : X ~> Y)
  : DecoratedCospanArrow X Y :=
  {| dc_cospan := mor_as_cospan f;
     dc_decoration := id_decoration Y |}.

End DecoratedCospanSymmetric.

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
