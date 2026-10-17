Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * The free abelian group functor is not continuous *)

(*
 nLab: https://ncatlab.org/nlab/show/continuous+functor
 Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The point of Sets, and the zero endomorphism of an abelian group *)

Definition SetsPoint : Sets := @terminal_obj Sets Sets_Terminal.

(* Built directly rather than as [Ab_zero_hom A ∘ Ab_one A]: the composite
   would route through [Ab_trivial], whose monomorphic [Set] universes would
   then pin this constant (see the header's UNIVERSES). *)
Definition ab_zero_endo (A : Ab) : A ~{Ab}~> A.
Proof.
  unshelve refine {| cmon_map := {| morphism := fun _ => cmon_zero A |} |}.
  - intros x y _; reflexivity.
  - reflexivity.
  - intros a b; simpl; symmetry; apply cmon_plus_zero_l.
Defined.

Lemma ab_zero_endo_value (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (ab_zero_endo A) a ≈ cmon_zero A.
Proof. simpl; reflexivity. Qed.

(** ** The one separation everything below is spent on *)

(*
   本节说明 FreeNotContinuous 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_ab_one_id_not_zero :
  @id Ab (FreeAb SetsPoint) ≈ ab_zero_endo (FreeAb SetsPoint) → False.
Proof.
  intro H.
  pose proof (H (fa_gen (X:=SetsPoint) ttt)) as Hg; simpl in Hg.
  exact (free_ab_gen_not_zero (X:=SetsPoint) ab_int 1%Z ab_int_one_not_zero
           ttt Hg).
Qed.

(** ** Witness 1: the empty limit — the free group on a point is not
       terminal in Ab *)

Program Definition empty_cone_at {C : Category} (K : _0 ⟶ C) (c : C)
  : Cone K := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun x => match x return _ with end |}
|}.
Next Obligation. destruct x. Qed.

Definition SetsEmptyDiagram : _0 ⟶ Sets := From_0 Sets.

Lemma SetsPoint_empty_IsLimitCone :
  IsLimitCone (empty_cone_at SetsEmptyDiagram SetsPoint).
Proof.
  intro M.
  unshelve eexists.
  - exact (@one Sets Sets_Terminal _).
  - intro x; destruct x.
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Qed.

Definition SetsPoint_empty_Limit : Limit SetsEmptyDiagram :=
  limitcone_limit _ SetsPoint_empty_IsLimitCone.

Theorem FreeAb_not_PreservesLimitCone_empty :
  PreservesLimitCone SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ SetsPoint_empty_IsLimitCone) as H.
  destruct (H (empty_cone_at _ (FreeAb SetsPoint))) as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

(* The apex-only form, which the product witnesses below CANNOT reach. *)
Theorem FreeAb_not_PreservesLimit_empty :
  PreservesLimit SetsEmptyDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (@preserves_limit _ _ _ _ _ P SetsPoint_empty_Limit) as H.
  destruct (@ump_limit _ _ _ _ H (empty_cone_at _ (FreeAb SetsPoint)))
    as [u _ Hu].
  apply free_ab_one_id_not_zero.
  transitivity u.
  - symmetry; apply Hu; intro x; destruct x.
  - apply Hu; intro x; destruct x.
Qed.

Definition FreeAb_not_PreservesAllLimits : PreservesAllLimits FreeAb → False :=
  fun H => FreeAb_not_PreservesLimit_empty (H _ SetsEmptyDiagram).

(** ** Witness 2: a countable product in Mac Lane's shape *)

Definition NatOnes : nat → Sets := fun _ => SetsPoint.
Definition NatOneDiagram : DiscreteCat nat ⟶ Sets := DiscreteCat_Functor' NatOnes.

Definition NatOneProduct :
  IsIndexedProduct NatOnes SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).
Proof.
  constructor; intros c pi.
  exists (@one Sets Sets_Terminal c).
  - intro a; apply (@one_unique Sets Sets_Terminal).
  - intros v _; apply (@one_unique Sets Sets_Terminal).
Defined.

Definition NatOneCone : Cone NatOneDiagram :=
  discrete_cone NatOneDiagram SetsPoint (fun _ => @one Sets Sets_Terminal SetsPoint).

Definition NatOneCone_IsLimitCone : IsLimitCone NatOneCone :=
  discrete_IsLimitCone_of_IsIndexedProduct NatOneDiagram NatOneCone NatOneProduct.

Definition nat_legs (n : nat) : FreeAb SetsPoint ~{Ab}~> FreeAb SetsPoint :=
  match n with
  | O   => id
  | S _ => ab_zero_endo (FreeAb SetsPoint)
  end.

Definition NatCompeting : Cone (FreeAb ◯ NatOneDiagram) :=
  discrete_cone (FreeAb ◯ NatOneDiagram) (FreeAb SetsPoint) nat_legs.

Lemma fmap_one_point :
  fmap[FreeAb] (@one Sets Sets_Terminal SetsPoint) ≈ @id Ab (FreeAb SetsPoint).
Proof.
  rewrite (@one_unique Sets Sets_Terminal SetsPoint _ (@id Sets SetsPoint)).
  exact (@fmap_id Sets Ab FreeAb SetsPoint).
Qed.

Theorem FreeAb_not_PreservesLimitCone_countable_product :
  PreservesLimitCone NatOneDiagram FreeAb → False.
Proof.
  intro P.
  pose proof (P _ NatOneCone_IsLimitCone) as H.
  destruct (H NatCompeting) as [u Hu _].
  apply free_ab_one_id_not_zero.
  assert (Hone : ∀ n : nat, u ≈ nat_legs n).
  { intro n.
    rewrite <- (Hu n).
    change (cone_leg (FCone FreeAb NatOneCone) n)
      with (fmap[FreeAb] (cone_leg NatOneCone n)).
    rewrite fmap_one_point.
    now rewrite id_left. }
  rewrite <- (Hone 0%nat).
  exact (Hone 1%nat).
Qed.

(** ** Witness 3: the binary product, through the comparison map *)

Definition BinOnes : bool → Sets := binary_fam SetsPoint SetsPoint.
Definition BinDiagram : DiscreteCat bool ⟶ Sets := DiscreteCat_Functor' BinOnes.

Definition FreeAb_binary_cmp :
  FreeAb (BinOnes true × BinOnes false)
    ~{Ab}~> FreeAb (BinOnes true) × FreeAb (BinOnes false) :=
  binary_comparison FreeAb BinOnes.

Theorem FreeAb_binary_comparison_not_iso :
  IsIsomorphism FreeAb_binary_cmp → False.
Proof.
  intro Hiso.
  apply free_ab_one_id_not_zero.
  assert (Hsets : @exl Sets _ SetsPoint SetsPoint ≈ @exr Sets _ SetsPoint SetsPoint).
  { transitivity (@one Sets Sets_Terminal (SetsPoint × SetsPoint));
      [ | symmetry ]; apply (@one_unique Sets Sets_Terminal). }
  assert (Hcmp : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp
                 ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint) ∘ FreeAb_binary_cmp).
  { unfold FreeAb_binary_cmp.
    rewrite (binary_comparison_exl FreeAb BinOnes).
    rewrite (binary_comparison_exr FreeAb BinOnes).
    now rewrite Hsets. }
  assert (Hlr : @exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)
                ≈ @exr Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint)).
  { destruct Hiso as [g Hgf Hfg].
    rewrite <- (id_right (@exl Ab _ (FreeAb SetsPoint) (FreeAb SetsPoint))).
    rewrite <- Hgf, comp_assoc, Hcmp, <- comp_assoc, Hgf.
    now rewrite id_right. }
  rewrite <- (@exl_fork Ab _ _ _ _
                (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
  rewrite Hlr.
  apply (@exr_fork Ab _ _ _ _
           (@id Ab (FreeAb SetsPoint)) (ab_zero_endo (FreeAb SetsPoint))).
Qed.

Theorem FreeAb_not_PreservesLimitCone_binary_product :
  PreservesLimitCone BinDiagram FreeAb → False.
Proof.
  intro P.
  apply FreeAb_binary_comparison_not_iso.
  exact (comparison_iso_of_PreservesLimitCone FreeAb P
           (binary_image_cone_IsLimitCone FreeAb BinOnes)
           (binary_cone BinOnes)
           (binary_cone_IsLimitCone BinOnes)).
Qed.

Theorem FreeAb_not_CartesianFunctor :
  @CartesianFunctor Sets Ab FreeAb _ _ → False.
Proof.
  intro HF.
  apply FreeAb_binary_comparison_not_iso.
  exact (fst (cartesian_functor_iff_comparison_iso FreeAb) HF SetsPoint SetsPoint).
Qed.

(** ** The conclusion of the exercise *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeAb_not_continuous : ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_countable_product (H _ NatOneDiagram).

Definition FreeAb_not_continuous_via_empty :
  ContinuousFunctor FreeAb → False :=
  fun H => FreeAb_not_PreservesLimitCone_empty (H _ SetsEmptyDiagram).

(** ** The positive side of the same adjunction *)

Definition Ab_Forget_Continuous : ContinuousFunctor Ab_Forget :=
  right_adjoint_Continuous free_ab_adjunction.

Definition FreeAb_Cocontinuous : CocontinuousFunctor FreeAb :=
  left_adjoint_Cocontinuous free_ab_adjunction.

(** ** Readbacks *)

Example freeab_is_left_adjoint : FreeAb ⊣ Ab_Forget := free_ab_adjunction.

Example free_ab_one_carrier :
  carrier (Ab_Forget (FreeAb SetsPoint)) = FATerm SetsPoint := eq_refl.

Example bin_diagram_objects : BinOnes true = SetsPoint := eq_refl.
