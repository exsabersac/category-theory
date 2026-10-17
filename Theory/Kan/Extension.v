Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Kan extensions *)

(*
 nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   本文件给出 Kan 扩张：沿函子 F 的左/右 Kan 扩张分别为预复合诱导函子的左/右伴随（当存在时）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于 Kan 扩张的来源与用途

   nLab:  https://ncatlab.org/nlab/show/codensity+monad
   nLab:  https://ncatlab.org/nlab/show/nerve+and+realization
   Paper: Kan, "Adjoint functors", Transactions of the American
   Paper: Leinster, "Codensity and the ultrafilter monad", Theory and
   Paper: Hinze, "Kan Extensions for Program Optimisation — Or: Art and

   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

(*
   nLab: https://ncatlab.org/nlab/show/Kan+extension

   本节说明Kan 扩张、伴随、自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.
Next Obligation. apply naturality. Qed.
Next Obligation. apply naturality_sym. Qed.

(*
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class RightKan := {
  (* jww (2017-06-09): Rename ran_函子, RightKan Ran, then a
 coercion Ran 函子? （已译） *)
  Ran : [A, C] ⟶ [B, C];           (* the right Kan extension functor       *)

  ran_adjoint : Induced ⊣ Ran      (* universal property: Induced ⊣ Ran     *)
}.

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;                       (* the extending functor R : B ⟶ C *)

  ran_transform : LocalRan ◯ F ⟹ X;       (* counit ε : R ◯ F ⟹ X            *)

  (* terminality / 普遍性质: μ factors uniquely through counit
 μ ≈ ran_transform ∙ (δ ⊲ F), δ unique mediating arrow （已译） *)
  ump_ran (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
    (∃! δ, μ ≈ ran_transform ∙ δ ⊲ F);
}.

(*
   Wikipedia: "There is also a local definition of 'the Kan extension of a

   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance RightKan_to_LocalRightKan {R : RightKan} (X : A ⟶ C) :
  LocalRightKan X := {|
  LocalRan := Ran X;
  ran_transform := from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_id
|}.
Next Obligation.
  exists (to (@adj _ _ _ _ (@ran_adjoint R) M X) μ).
  - intros.
    spose (@from_adj_nat_l _ _ _ _ ran_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_from_to _ _ _ (@adj _ _ _ _ ran_adjoint M X) μ x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@from _ _ _ (@adj _ _ _ _ ran_adjoint M X))).
    simpl; intros; cat.
  - intros.
    assert (μ ≈ (adj[ran_adjoint])⁻¹ v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint).
      destruct (adj[ran_adjoint]); simpl in *.
      destruct from; simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_left.
    }
    clear -X1.
    destruct (adj[ran_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_to_from v).
    destruct to; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

(*
   nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LeftKan := {
  Lan : [A, C] ⟶ [B, C];           (* the left Kan extension functor        *)

  lan_adjoint : Lan ⊣ Induced      (* universal property: Lan ⊣ Induced     *)
}.

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;                       (* the extending functor L : B ⟶ C *)

  lan_transform : X ⟹ LocalLan ◯ F;       (* unit η : X ⟹ L ◯ F              *)

  (* initiality / 普遍性质: ε factors uniquely through unit as
 ε ≈ (δ ⊲ F) ∙ lan_transform, δ unique mediating arrow （已译） *)
  ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
    ∃! δ, ε ≈ δ ⊲ F ∙ lan_transform;
}.

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance LeftKan_to_LocalLeftKan {R : LeftKan} (X : A ⟶ C) :
  LocalLeftKan X := {|
  LocalLan := Lan X;
  lan_transform := to (@adj _ _ _ _ lan_adjoint X (Lan X)) nat_id
|}.
Next Obligation.
  exists (from (@adj _ _ _ _ (@lan_adjoint R) X M) ε).
  - intros.
    spose (@to_adj_nat_r _ _ _ _ lan_adjoint) as X0.
    rewrite <- X0; clear X0.
    spose (@iso_to_from _ _ _ (@adj _ _ _ _ lan_adjoint X M) ε x) as X0.
    unfold nat_compose; simpl in *.
    rewrites.
    sapply (proper_morphism (@to _ _ _ (@adj _ _ _ _ lan_adjoint X M))).
    simpl; intros; cat.
  - intros.
    assert (ε ≈ (to adj[lan_adjoint]) v). {
      intro.
      specialize (X0 x).
      rewrite X0; clear X0.
      srewrite_r (@to_adj_nat_r _ _ _ _ lan_adjoint).
      destruct (to adj[lan_adjoint]); simpl in *.
      apply proper_morphism; simpl.
      now apply nat_id_right.
    }
    clear -X1.
    destruct (adj[lan_adjoint]); simpl in *.
    intros.
    rewrite <- (iso_from_to v).
    destruct from; simpl in *.
    apply proper_morphism.
    simpl.
    now apply X1.
Qed.

End KanExtension.

Arguments RightKan {_ _} F _.
Arguments Ran {_ _} F {_ _}.

Arguments LocalRightKan {_ _} F {_} _.
Arguments LocalRan {_ _} F {_} _ {_}.

Arguments LeftKan {_ _} F _.
Arguments Lan {_ _} F {_ _}.

Arguments LocalLeftKan {_ _} F {_} _.
Arguments LocalLan {_ _} F {_} _ {_}.

(* From "All Concepts Kan Extensions", Marina Christina Lehner:

 "A 函子 preserves Kan extension composing then extending is
 equivalent extending then composing." （已译） *)

(* A 函子 L preserves left Kan extensions when applying L after extending
 agrees extending after applying L, i.e. L ◯ Lan K G ≈ Lan K (L ◯ G).
 The two LeftKan hypotheses supply extensions each side.（已译） *)

Definition preserves_left_Kan `(L : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!LeftKan K E) `(!LeftKan K F), L ◯ Lan K G ≈ Lan K (L ◯ G).

(* Dual: R preserves right Kan extensions when R ◯ Ran K G ≈ Ran K (R ◯ G). *)

Definition preserves_right_Kan `(R : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!RightKan K E) `(!RightKan K F), R ◯ Ran K G ≈ Ran K (R ◯ G).

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明Kan 扩张、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem left_adjoint_impl `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R ->
  ∀ {E} (G : E ⟶ C) (H : E ⟶ D),
    [[[E,D]]](L ◯ G, H) ≊ [[[E,C]]](G, R ◯ H).
Proof.
  intros.
  simpl.
  isomorphism; simpl.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- to_adj_nat_l.
        rewrite <- to_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply to_adj_respects.
      now apply X0.
  - construct.
    + transform.
      * intros.
        apply X; simpl.
        now apply X0.
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
      * simpl.
        rewrite <- from_adj_nat_l.
        rewrite <- from_adj_nat_r.
        now srewrite (@naturality _ _ _ _ X0 _ _ f).
    + simpl.
      proper.
      apply from_adj_respects.
      now apply X0.
  - simpl.
    now apply from_adj_comp_law.
  - simpl.
    now apply to_adj_comp_law.
Qed.

(*
   本节说明Kan 扩张、伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem left_adjoints_preserve `(L : C ⟶ D) :
  ∀ R : D ⟶ C, L ⊣ R → preserves_left_Kan L.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply X; simpl.
      rewrite <- fobj_Compose.
      apply LeftKan0; simpl.
      spose (left_adjoint_impl _ _ X G (Lan K (L ◯ G) ◯ K)) as X0.
      transitivity (R ◯ (Lan K (L ◯ G) ◯ K)).
      * apply (to X0); simpl.
        apply LeftKan1; simpl.
        exact nat_id.
      * now apply fun_comp_assoc.
    + rewrite <- fobj_Compose.
      apply LeftKan1; simpl.
      spose (left_adjoint_impl _ _ X G (L ◯ Lan K G ◯ K)) as X0.
      apply X0; simpl; clear X0.
      transitivity (R ◯ L ◯ fobj[Lan _] G ◯ K). {
        apply LeftKan0; simpl.
        transform.
        - intros.
          apply unit.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
        - simpl.
          unfold unit.
          rewrite <- to_adj_nat_l.
          rewrite <- to_adj_nat_r.
          rewrite id_left, id_right.
          reflexivity.
      }
      pose proof (@fun_comp_assoc_sym _ _ _ _ R L (Lan K G ◯ K)).
      pose proof (@fun_comp_assoc_sym _ _ _ _ R (L ◯ Lan K G) K).
      pose proof (@fun_comp_assoc_sym _ _ _ _ (R ◯ L) (Lan K G) K).
      transitivity ((R ◯ L) ◯ ((fobj[Lan _] G) ◯ K)); auto.
      transitivity (R ◯ (L ◯ ((fobj[Lan _] G) ◯ K))); auto.
      transitivity (R ◯ ((L ◯ (fobj[Lan _] G)) ◯ K)).
      * apply whisker_left.
        apply fun_comp_assoc.
      * exact nat_id.
    + simpl.
      admit.
    + simpl.
      admit.
  - simpl.
    admit.
Abort.
