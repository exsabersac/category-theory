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
   Where Kan 扩张 来源, and 用途

   本节：nLab: https://ncatlab.org/nlab/show/codensity+单子 nLab: https://ncatlab.org/nlab/show/nerve+and+realization Paper: Kan, "伴随 函子", Transactions American Mathematical Society 87, 1958 Paper: Leinster, "Codensity ultrafilter 单子", Theory Applications

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

(*
   The restriction (预复合) 函子 Induced := (− ◯ F) : [B,C] ⟶ [A,C],

   本节：written F* p* 文献. On 对象 it sends G : B ⟶ C G ◯ F; 自然变换 f : G ⟹ H it 贴须 F, giving component (Induced f)_z = f_(F z). The Kan 扩张 along F are adjoints this 函子.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ◯ F;
  fmap := fun _ _ f => {| transform := fun z => transform[f] (F z) |}
|}.
Next Obligation. apply naturality. Qed.
Next Obligation. apply naturality_sym. Qed.

(*
   Global 右 Kan 扩张 along F: the 右伴随 Ran of the restriction

   本节：函子 Induced = (− ◯ F). The 伴随 Induced ⊣ Ran corresponds hom-set 同构 [A,C](M ◯ F, X) ≅ [B,C](M, Ran X), 自然 M.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class RightKan := {
  (* jww (2017-06-09): Rename this to ran_functor, RightKan to Ran, and then a
     coercion from Ran to functor? *)
  Ran : [A, C] ⟶ [B, C];           (* the right Kan extension functor       *)

  ran_adjoint : Induced ⊣ Ran      (* universal property: Induced ⊣ Ran     *)
}.

(*
   Local (pointwise-free) 右 Kan 扩张 of a single 函子 X : A ⟶ C

   本节说明相关定义、性质与动机。 along F. This is 终对象 among pairs (函子, counit), can exist even when global 伴随 Ran above does not.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;                       (* the extending functor R : B ⟶ C *)

  ran_transform : LocalRan ◯ F ⟹ X;       (* counit ε : R ◯ F ⟹ X            *)

  (* terminality / universal property: μ factors uniquely through the counit
     as μ ≈ ran_transform ∙ (δ ⊲ F), with δ the unique mediating arrow *)
  ump_ran (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
    (∃! δ, μ ≈ ran_transform ∙ δ ⊲ F);
}.

(*
   given 函子 F along p' which can exist even if the entire 函子 defined

   Wikipedia: "There is also a local definition of 'the Kan extension of a

   本节说明相关定义、性质与动机。 above [global Kan 扩张] does not. This is generalization fact that particular diagram shape C can have 极限 even if not every such diagram does.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   A global 右 Kan 扩张 restricts to a local one at each X: take the

   本节说明相关定义、性质与动机。 extending 函子 be Ran X counit be image identity under 伴随 iso (the counit Induced ⊣ Ran at X).

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
   Global 左 Kan 扩张 along F: the 左伴随 Lan of the restriction

   本节：函子 Induced = (− ◯ F). The 伴随 Lan ⊣ Induced corresponds hom-set 同构 [A,C](X, M ◯ F) ≅ [B,C](Lan X, M), 自然 M.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LeftKan := {
  Lan : [A, C] ⟶ [B, C];           (* the left Kan extension functor        *)

  lan_adjoint : Lan ⊣ Induced      (* universal property: Lan ⊣ Induced     *)
}.

(*
   Local 左 Kan 扩张 of a single 函子 X : A ⟶ C along F.  This is the

   本节说明相关定义、性质与动机。 始对象 among pairs (函子, unit), can exist even when global 伴随 Lan above does not.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;                       (* the extending functor L : B ⟶ C *)

  lan_transform : X ⟹ LocalLan ◯ F;       (* unit η : X ⟹ L ◯ F              *)

  (* initiality / universal property: ε factors uniquely through the unit as
     ε ≈ (δ ⊲ F) ∙ lan_transform, with δ the unique mediating arrow *)
  ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
    ∃! δ, ε ≈ δ ⊲ F ∙ lan_transform;
}.

(*
   A global 左 Kan 扩张 restricts to a local one at each X: take the

   本节说明相关定义、性质与动机。 extending 函子 be Lan X unit be image identity under 伴随 iso (the unit Lan ⊣ Induced at X).

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

(* From "All Concepts are Kan Extensions", by Marina Christina Lehner:

   "A functor preserves a Kan extension when composing then extending is
   equivalent to extending then composing." *)

(* A functor L preserves left Kan extensions when applying L after extending
   agrees with extending after applying L, i.e. L ◯ Lan K G ≈ Lan K (L ◯ G).
   The two LeftKan hypotheses supply the extensions on each side. *)

Definition preserves_left_Kan `(L : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!LeftKan K E) `(!LeftKan K F), L ◯ Lan K G ≈ Lan K (L ◯ G).

(* Dual: R preserves right Kan extensions when R ◯ Ran K G ≈ Ran K (R ◯ G). *)

Definition preserves_right_Kan `(R : E ⟶ F) :=
  ∀ C D (G : C ⟶ E) (K : C ⟶ D)
    `(!RightKan K E) `(!RightKan K F), R ◯ Ran K G ≈ Ran K (R ◯ G).

(*
   "We show that left adjoints preserve left Kan 扩张, while right

   本节说明相关定义、性质与动机。 adjoints will preserve right adjoints [sic]. These connections adjoints run deeper.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   If L ⊣ R then 预复合 by L is hom-isomorphic to 后复合 by R:

   本节说明相关定义、性质与动机。 [E,D](L ◯ G, H) ≊ [E,C](G, R ◯ H), 函子-范畴 lift defining hom-set 伴随.

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
   Work in progress: left adjoints preserve left Kan 扩张 (Lehner, "All

   本节说明相关定义、性质与动机。 Concepts are Kan Extensions"). The proof is incomplete — three obligations are left open proof script is abandoned before `Qed`, so theorem is NOT added environment introduces no axioms. Retained proof sketch.

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
