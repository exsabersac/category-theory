Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Traversable.
Require Import Category.Functor.Applicative.

Generalizable All Variables.

(** The pointwise product of traversable functors is traversable *)

(*
   Reference: Jaskelioff and Rypacek, "An Investigation of the Laws of
   Wikipedia: none-exists - there is no Wikipedia page for "traversable

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProductTraversable.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Existing Instance CC_Monoidal.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ProductFunctor_Traversable_ap_functor_nat :
  Traversable F → Traversable G
    → ∀ H : C ⟶ C, @Applicative _ _ H
    → (F :*: G) ◯ H ⟹ H ◯ (F :*: G).
Proof.
  intros O P ??.

  transform.
  - simpl.
    intro x.
    exact (lax_ap[H0] ∘ bimap (transform[@sequence _ _ _ O _ X] x)
                              (transform[@sequence _ _ _ P _ X] x)).
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X] _ _ f) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X] _ _ f) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X] _ _ f) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X] _ _ f) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
Defined.

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* Program Definition ProductFunctor_Traversable :
 Traversable F → Traversable G
 → Traversable (F :*: G) := fun O P => {|
 sequence := ProductFunctor_Traversable_ap_functor_nat _ _;
 sequence_自然性 := _;
 sequence_Id := _;
 sequence_Compose := _
|}.
Next Obligation.
 pose 证明 (@sequence_自然性 _ _ _ _ _ O G0 _ H3 _ _ f X) X0.
 pose 证明 (@sequence_自然性 _ _ _ _ _ P G0 _ H3 _ _ f X) X1.
 repeat (unfold ap; simpl).
(*
 pose 证明 (自然性[@slm_transform _ _ _ _ _ _ _ _ f]).
 rewrite <- comp_assoc.
 rewrite <- bimap_comp.
 rewrites.
 rewrite bimap_comp.
 rewrite !comp_assoc.
 apply compose_respects; [|reflexivity].
 (* This must proven based how slm_transform interacts ap. *)
*)
Next Obligation.
 repeat (unfold ap; simpl).
 rewrite id_left.
 rewrite (@sequence_Id _ _ _ _ _ O), (@sequence_Id _ _ _ _ _ P).
 cat.
Qed.
(*
Next Obligation.
 repeat (unfold lax_ap; simpl).
 rewrite (@sequence_Compose _ _ _ _ _ O G0 H2 H3 H4 X),
 (@sequence_Compose _ _ _ _ _ P G0 H2 H3 H4 X).
 pose 证明 (自然性[@ap_函子_nat _ _ _ _ G0
 (@is_lax_monoidal _ _ _ _ _ H2)]
 (F (H3 X), G (H3 X))
 (H3 (F X), H3 (G X))
 (transform sequence X, transform sequence X)) X3;
 simpl *.
 rewrite <- !comp_assoc.
 rewrite (comp_assoc _ (bimap _ _)).
 rewrites.
 rewrite !comp_assoc.
 rewrite <- fmap_comp.
 reflexivity.
Qed.
*)
Next Obligation. （已译） *)

End ProductTraversable.
