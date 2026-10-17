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

Generalizable All Variables.

(*
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872
    nLab:      https://ncatlab.org/nlab/show/decorated+cospan

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospan.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).

(** ** Decorated cospan arrows

    A decorated cospan from [X] to [Y] is a cospan together with a
    decoration of its apex. *)
Record DecoratedCospanArrow (X Y : C) : Type := {
  dc_cospan : CospanArrow X Y;
  dc_decoration : @I D _ ~{D}~> F (cospan_apex dc_cospan)
}.

Arguments dc_cospan {X Y} _.
Arguments dc_decoration {X Y} _.
Arguments Build_DecoratedCospanArrow {X Y} _ _.

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record dec_cospan_equiv {X Y : C} (f g : DecoratedCospanArrow X Y) : Type := {
  dce_cospan_eq : cospan_equiv (dc_cospan f) (dc_cospan g);
  dce_dec_eq    :
    fmap[F] (to (projT1 dce_cospan_eq)) ∘ dc_decoration f
      ≈ dc_decoration g
}.

Arguments dce_cospan_eq {X Y f g} _.
Arguments dce_dec_eq    {X Y f g} _.

Lemma dec_cospan_equiv_refl {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f f.
Proof.
  unshelve econstructor.
  - apply cospan_equiv_refl.
  - simpl. rewrite fmap_id, id_left. reflexivity.
Defined.

Lemma dec_cospan_equiv_sym {X Y : C} (f g : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g -> dec_cospan_equiv g f.
Proof.
  intros [E He].
  unshelve econstructor.
  - apply cospan_equiv_sym; exact E.
  - destruct E as [phi [E1 E2]]; simpl in *.
    (* Need: fmap[F] (from phi) ∘ dc_decoration g ≈ dc_decoration f.
       Have: fmap[F] (to phi) ∘ dc_decoration f ≈ dc_decoration g.
       Apply fmap[F] (from phi) ∘ - to both sides. *)
    rewrite <- He.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite iso_from_to, fmap_id, id_left.
    reflexivity.
Defined.

Lemma dec_cospan_equiv_trans {X Y : C} (f g h : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g -> dec_cospan_equiv g h -> dec_cospan_equiv f h.
Proof.
  intros [E He] [E' He'].
  unshelve econstructor.
  - eapply cospan_equiv_trans; eassumption.
  - destruct E as [phi [E1 E2]].
    destruct E' as [psi [F1 F2]].
    simpl in *.
    (* The transitive cospan-equiv has apex iso (psi ∘ phi);
       fmap[F] (to (psi ∘ phi)) = fmap[F] (to psi ∘ to phi)
                                 = fmap[F] (to psi) ∘ fmap[F] (to phi). *)
    rewrite fmap_comp.
    rewrite <- comp_assoc.
    rewrite He.
    exact He'.
Defined.

#[export] Program Instance DecoratedCospanArrow_Setoid {X Y : C} :
  Setoid (DecoratedCospanArrow X Y) := {|
  equiv := fun f g => dec_cospan_equiv f g
|}.
Next Obligation.
  constructor.
  - intros f; apply dec_cospan_equiv_refl.
  - intros f g; apply dec_cospan_equiv_sym.
  - intros f g h; apply dec_cospan_equiv_trans.
Defined.

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).

Definition dec_cospan_id (X : C) : DecoratedCospanArrow X X := {|
  dc_cospan := cospan_id X;
  dc_decoration := id_decoration X
|}.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context `{H_Coc : @Cocartesian C}.

(*
   本节说明幺半结构、拉回/推出、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

Definition dec_compose_decoration
  {X Y Z : C} (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
  : @I D _ ~{D}~> F (cospan_apex (cospan_compose HP (dc_cospan g) (dc_cospan f))) :=
  let N := cospan_apex (dc_cospan f) in
  let M := cospan_apex (dc_cospan g) in
  let P := pushout (cospan_in2 (dc_cospan f)) (cospan_in1 (dc_cospan g)) in
  fmap[F] (pushout_in1 P ▽ pushout_in2 P)
    ∘ fmap[F] (cospan_merge N M)
    ∘ lax_ap[F]
    ∘ bimap (dc_decoration f) (dc_decoration g)
    ∘ from (@unit_left D _ (@I D _)).

Definition dec_cospan_compose
  {X Y Z : C} (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
  : DecoratedCospanArrow X Z := {|
  dc_cospan := cospan_compose HP (dc_cospan g) (dc_cospan f);
  dc_decoration := dec_compose_decoration g f
|}.

(*
   本节说明 DecoratedCospan 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End DecoratedCospan.

(** Argument metadata for the section-closed definitions. *)

Arguments dc_cospan {C D MD F X Y} _.
Arguments dc_decoration {C D MD F X Y} _.
Arguments dce_cospan_eq {C D MD F X Y f g} _.
Arguments dce_dec_eq    {C D MD F X Y f g} _.

(*
   本节说明幺半结构、自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
