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
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.

Generalizable All Variables.

(** * Braided and Symmetric Monoidal structure on [DecoratedCospanCat] *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,

   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospanBraided.

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
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation Dtensor f g := (dec_cospan_tensor LM cospan_merge f g).
Notation Dcompose g f := (dec_cospan_compose HP LM cospan_merge g f).
Notation Did X := (dec_cospan_id id_decoration X).
Notation Dlift f := (dec_mor_as_cospan id_decoration f).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Braided_Coherent : Type := {

  (** Naturality of [braid] : as a decorated-cospan equation.
      Goal shape (matching [@braid_natural]):
        [bimap h f ∘ braid_{x,z} ≈ braid_{y,w} ∘ bimap f h]
      where the bimap is [dec_cospan_tensor] and braid is
      [Dlift paws]. *)
  dec_braid_natural_eq :
    forall {x y z w : C}
           (f : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w),
      dec_cospan_equiv
        (Dcompose (Dtensor h f) (Dlift (@paws C H_Coc x z)))
        (Dcompose (Dlift (@paws C H_Coc y w)) (Dtensor f h));

  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dec_hexagon_identity_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (to (@coprod_assoc C H_Coc y z x)))
           (Dcompose
              (Dlift (@paws C H_Coc x (y + z)%object))
              (Dlift (to (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Did y) (Dlift (@paws C H_Coc x z)))
           (Dcompose
              (Dlift (to (@coprod_assoc C H_Coc y x z)))
              (Dtensor (Dlift (@paws C H_Coc x y)) (Did z))));

  (** Hexagon identity (from form), RIGHT-associated. *)
  dec_hexagon_identity_sym_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (from (@coprod_assoc C H_Coc z x y)))
           (Dcompose
              (Dlift (@paws C H_Coc (x + y)%object z))
              (Dlift (from (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Dlift (@paws C H_Coc x z)) (Did y))
           (Dcompose
              (Dlift (from (@coprod_assoc C H_Coc x z y)))
              (Dtensor (Did x) (Dlift (@paws C H_Coc y z)))))
}.

Context `{DCBrC : DecCospan_Braided_Coherent}.

Set Default Proof Using "All".

(** ** [DecoratedCospan_BraidedMonoidal] : the BraidedMonoidal instance *)

Program Definition DecoratedCospan_BraidedMonoidal
  : @BraidedMonoidal DC := {|
  braided_is_monoidal := DecoratedCospan_Monoidal HP LM id_decoration cospan_merge;
  braid := fun X Y => Dlift (@paws C H_Coc X Y)
|}.
Next Obligation.
  (*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
                h (Did _) (Did _) g). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge). }
  apply dec_cospan_equiv_sym.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
               (Did _) g h (Did _)).
    - apply dec_cospan_equiv_refl. }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl. }
  apply dec_cospan_equiv_sym.
  apply dec_braid_natural_eq.
Qed.
Next Obligation.
  (*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.
Next Obligation.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_sym_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.

(*
   本节说明 Braided 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Symmetric_Coherent : Type := {
  dec_braid_invol_eq :
    forall {x y : C},
      dec_cospan_equiv
        (Dcompose (Dlift (@paws C H_Coc x y))
                  (Dlift (@paws C H_Coc y x)))
        (Did (y + x)%object)
}.

Context `{DCSC : DecCospan_Symmetric_Coherent}.

(** ** [DecoratedCospan_SymmetricMonoidal] : the SymmetricMonoidal instance *)

Program Definition DecoratedCospan_SymmetricMonoidal
  : @SymmetricMonoidal DC := {|
  symmetric_is_braided := DecoratedCospan_BraidedMonoidal
|}.
Next Obligation.
  apply dec_braid_invol_eq.
Qed.

End DecoratedCospanBraided.

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
