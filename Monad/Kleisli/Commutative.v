Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/commutative+monad
    nLab: https://ncatlab.org/nlab/show/premonoidal+category

   本文件给出 Kleisli 范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KleisliCommutative.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(*
   本节说明Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_pure_eqv {a b : C} {u v : a ~{C}~> b} (E : u ≈ v) :
  (kpure u : a ~{Kleisli}~> b) ≈ kpure v.
Proof. now apply kpure_proper. Qed.

(* ------------------------------------------------------------------ *)
(** ** The braid conjugation identity for the double strengths.        *)
(* ------------------------------------------------------------------ *)

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dstr_braid {x y : C} :
  (dstr' : M x ⨂ M y ~> M (x ⨂ y))
    ≈ fmap[M] braid ∘ (dstr : M y ⨂ M x ~> M (y ⨂ x)) ∘ braid.
Proof.
  unfold dstr, dstr', rstr.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite braid_invol.
  rewrite id_right.
  rewrite !comp_assoc.
  rewrite join_fmap_fmap.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Commutativity versus centrality: both directions.               *)
(* ------------------------------------------------------------------ *)

(*
   本节说明Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem kleisli_all_central (comm : commutative_sm (M:=M))
        {x y : C} (f : x ~{Kleisli}~> y) :
  @central Kleisli Kleisli_Binoidal x y f.
Proof.
  apply kleisli_central_iff; intros c d g.
  split.
  - now rewrite (comm y d).
  - now rewrite (comm d y).
Qed.

(*
   本节说明Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem kleisli_all_central_commutative
        (allc : ∀ (x y : C) (f : x ~{Kleisli}~> y),
                  @central Kleisli Kleisli_Binoidal x y f) :
  commutative_sm (M:=M).
Proof.
  intros x y.
  destruct (kleisli_central_iff (a:=M x) (b:=x) (@id C (M x))) as [fwd _].
  destruct (fwd (allc (M x) x (@id C (M x))) (M y) y (@id C (M y)))
    as [sq _].
  rewrite bimap_id_id in sq.
  rewrite !id_right in sq.
  exact sq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The comm-gated structures.                                      *)
(* ------------------------------------------------------------------ *)

Section WithComm.

Hypothesis comm : commutative_sm (M:=M).

(*
   本节说明幺半结构、幺半群、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Kleisli_Monoidal : @Monoidal Kleisli :=
  @Premonoidal_Monoidal Kleisli Kleisli_Binoidal Kleisli_Premonoidal
    (fun (x y : Kleisli) (f : x ~{Kleisli}~> y) =>
       kleisli_all_central comm f).

(* The induced tensor computes the double strength on morphism pairs:
   [bimap] over [Kleisli_Monoidal] is definitionally the interleaved
   composite [composite_ff'], whose right-then-left normal form is
   [kl_square_rl]. *)
Lemma kleisli_bimap_dstr {a b c d : C}
      (f : a ~{Kleisli}~> b) (g : c ~{Kleisli}~> d) :
  (f ⨂[Kleisli_Monoidal] g)
    ≈ dstr ∘ ((f : a ~{C}~> M b) ⨂ (g : c ~{C}~> M d)).
Proof. exact (kl_square_rl f g). Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_bimap_inj_left {a b : C} (w : C) (f : a ~{Kleisli}~> b) :
  (f ⨂[Kleisli_Monoidal] (@id Kleisli w))
    ≈ fmap[@inj_left Kleisli Kleisli_Binoidal w] f.
Proof. exact (@composite_id_right Kleisli Kleisli_Binoidal a b w f). Qed.

Lemma kl_bimap_inj_right (w : C) {a b : C} (f : a ~{Kleisli}~> b) :
  ((@id Kleisli w) ⨂[Kleisli_Monoidal] f)
    ≈ fmap[@inj_right Kleisli Kleisli_Binoidal w] f.
Proof. exact (@composite_id_left Kleisli Kleisli_Binoidal a b w f). Qed.

(*
   本节说明Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_pure_tensor {a b c d : C} (u : a ~{C}~> b) (v : c ~{C}~> d) :
  ((kpure u) ⨂[Kleisli_Monoidal] (kpure v)) ≈ kpure (u ⨂ v).
Proof.
  rewrite kleisli_bimap_dstr.
  assert (E : ((kpure u : a ~{C}~> M b) ⨂ (kpure v : c ~{C}~> M d))
                ≈ (ret[M] ⨂ ret[M]) ∘ (u ⨂ v)).
  { unfold kpure.
    now rewrite <- bimap_comp. }
  rewrite E; clear E.
  rewrite comp_assoc.
  rewrite dstr_ret_ret.
  unfold kpure.
  reflexivity.
Qed.

(* One-sided pure padding, the workhorse of every transfer proof below:
   a pure morphism tensored with the Kleisli identity is the pure image
   of the identity-padded base tensor. *)
Lemma kl_bimap_pure_l {a b : C} (u : a ~{C}~> b) (w : C) :
  ((kpure u) ⨂[Kleisli_Monoidal] (@id Kleisli w))
    ≈ kpure (u ⨂ id[w]).
Proof.
  rewrite kl_bimap_inj_left.
  apply pure_inj_left.
Qed.

Lemma kl_bimap_pure_r (w : C) {a b : C} (u : a ~{C}~> b) :
  ((@id Kleisli w) ⨂[Kleisli_Monoidal] (kpure u))
    ≈ kpure (id[w] ⨂ u).
Proof.
  rewrite kl_bimap_inj_right.
  apply pure_inj_right.
Qed.

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kl_pure_unit_left (x : C) :
  to (@unit_left Kleisli Kleisli_Monoidal x)
    ≈ kpure (to (@unit_left C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_left_from (x : C) :
  from (@unit_left Kleisli Kleisli_Monoidal x)
    ≈ kpure (from (@unit_left C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_right (x : C) :
  to (@unit_right Kleisli Kleisli_Monoidal x)
    ≈ kpure (to (@unit_right C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_unit_right_from (x : C) :
  from (@unit_right Kleisli Kleisli_Monoidal x)
    ≈ kpure (from (@unit_right C _ x)).
Proof. reflexivity. Qed.

Lemma kl_pure_assoc (x y z : C) :
  to (@tensor_assoc Kleisli Kleisli_Monoidal x y z)
    ≈ kpure (to (@tensor_assoc C _ x y z)).
Proof. reflexivity. Qed.

Lemma kl_pure_assoc_from (x y z : C) :
  from (@tensor_assoc Kleisli Kleisli_Monoidal x y z)
    ≈ kpure (from (@tensor_assoc C _ x y z)).
Proof. reflexivity. Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kl_braid_natural {x y z w : C}
      (g : x ~{Kleisli}~> y) (h : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       ((h ⨂[Kleisli_Monoidal] (@id Kleisli y)))
       (((@id Kleisli z) ⨂[Kleisli_Monoidal] g)))
    (kpure braid)
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (kpure braid)
         (((@id Kleisli y) ⨂[Kleisli_Monoidal] h)))
      ((g ⨂[Kleisli_Monoidal] (@id Kleisli z))).
Proof.
  rewrite !kl_bimap_inj_left, !kl_bimap_inj_right.
  rewrite <- (comp_assoc (kpure (@braid C _ y w))).
  rewrite (kl_square_lr h g).
  rewrite (kl_square_rl g h).
  rewrite kl_pure_pre.
  rewrite kl_pure_post.
  (* C-level: dstr' ∘ (h ⨂ g) ∘ β ≈ M(β) ∘ (dstr ∘ (g ⨂ h)) *)
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite dstr_braid.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc braid braid).
  rewrite braid_invol.
  rewrite id_left.
  reflexivity.
Qed.

(* The two hexagons transfer from the base along the pure functor: after
   converting the padded bimaps to pure images, both sides collapse to
   the pure image of the corresponding base hexagon. *)
Lemma kl_hexagon {x y z : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (kpure (to (@tensor_assoc C _ y z x)))
       (kpure (@braid C _ x ((y ⨂ z)%object))))
    (kpure (to (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (((@id Kleisli y) ⨂[Kleisli_Monoidal] (kpure (@braid C _ x z))))
         (kpure (to (@tensor_assoc C _ y x z))))
      (((kpure (@braid C _ x y)) ⨂[Kleisli_Monoidal] (@id Kleisli z))).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  apply hexagon_identity.
Qed.

Lemma kl_hexagon_sym {x y z : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (kpure (from (@tensor_assoc C _ z x y)))
       (kpure (@braid C _ ((x ⨂ y)%object) z)))
    (kpure (from (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (((kpure (@braid C _ x z)) ⨂[Kleisli_Monoidal] (@id Kleisli y)))
         (kpure (from (@tensor_assoc C _ x z y))))
      (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure (@braid C _ y z)))).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  apply hexagon_identity_sym.
Qed.

Definition Kleisli_Braided : @BraidedMonoidal Kleisli :=
  @Build_BraidedMonoidal Kleisli
    Kleisli_Monoidal
    (fun x y : C => kpure (@braid C _ x y))
    (fun (x y : C) (g : x ~{Kleisli}~> y)
         (z w : C) (h : z ~{Kleisli}~> w) => kl_braid_natural g h)
    (fun x y z : C => @kl_hexagon x y z)
    (fun x y z : C => @kl_hexagon_sym x y z).

(* The involution law is the pure image of the base one. *)
Lemma kl_braid_invol {x y : C} :
  @compose Kleisli _ _ _ (kpure (@braid C _ y x)) (kpure (@braid C _ x y))
    ≈ @id Kleisli ((x ⨂ y)%object).
Proof.
  rewrite kl_pure_comp.
  transitivity (kpure (@id C ((x ⨂ y)%object))).
  - apply kl_pure_eqv.
    apply braid_invol.
  - apply kpure_id.
Qed.

Definition Kleisli_Symmetric : @SymmetricMonoidal Kleisli :=
  @Build_SymmetricMonoidal Kleisli
    Kleisli_Braided
    (fun x y : C => @kl_braid_invol x y).

(* The braiding of Kl(M) is the pure image of the base braiding by
   construction; recorded to complete the pure-transfer kit. *)
Lemma kl_pure_braid (x y : C) :
  @braid Kleisli (@symmetric_is_braided Kleisli Kleisli_Symmetric) x y
    ≈ kpure (@braid C _ x y).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The copy-discard descent to Kl(M).                              *)
(* ------------------------------------------------------------------ *)

Section WithCD.

Context `{CD : @CopyDiscard C _}.

(*
   本节说明函子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_pure_mid_swap_inv (X Y : C) :
  @mid_swap_inv Kleisli Kleisli_Symmetric X Y
    ≈ kpure (@mid_swap_inv C _ X Y).
Proof.
  unfold mid_swap_inv.
  rewrite !kpure_comp_functor.
  apply compose_respects.
  2: reflexivity.
  apply compose_respects.
  2: exact (kl_bimap_pure_r X (from (@tensor_assoc C _ X Y Y))).
  apply compose_respects.
  2: {
    etransitivity.
    - apply bimap_respects; [reflexivity|].
      exact (kl_bimap_pure_l (@braid C _ X Y) Y).
    - exact (kl_bimap_pure_r X ((@braid C _ X Y) ⨂ id[Y])).
  }
  apply compose_respects.
  2: exact (kl_bimap_pure_r X (to (@tensor_assoc C _ Y X Y))).
  reflexivity.
Qed.

(** *** The per-object commutative comonoid on Kl(M)

    copy := kpure copy and discard := kpure discard; every law is the
    pure image of the corresponding base law. *)

Lemma kl_delta_coassoc (x : C) :
  @compose Kleisli _ _ _
    (((kpure copy[x]) ⨂[Kleisli_Monoidal] (@id Kleisli x)))
    (kpure copy[x])
  ≈ @compose Kleisli _ _ _
      (@compose Kleisli _ _ _
         (kpure (from (@tensor_assoc C _ x x x)))
         (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure copy[x]))))
      (kpure copy[x]).
Proof.
  rewrite kl_bimap_pure_l, kl_bimap_pure_r.
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_coassoc C _ x (cd_comonoid x)).
Qed.

Lemma kl_delta_counit_left (x : C) :
  @compose Kleisli _ _ _
    (((kpure discard[x]) ⨂[Kleisli_Monoidal] (@id Kleisli x)))
    (kpure copy[x])
  ≈ kpure (from (@unit_left C _ x)).
Proof.
  rewrite kl_bimap_pure_l.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_counit_left C _ x (cd_comonoid x)).
Qed.

Lemma kl_delta_counit_right (x : C) :
  @compose Kleisli _ _ _
    (((@id Kleisli x) ⨂[Kleisli_Monoidal] (kpure discard[x])))
    (kpure copy[x])
  ≈ kpure (from (@unit_right C _ x)).
Proof.
  rewrite kl_bimap_pure_r.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_counit_right C _ x (cd_comonoid x)).
Qed.

Definition Kleisli_cd_comonoid_base (x : C) :
  @Comonoid Kleisli Kleisli_Monoidal x :=
  @Build_Comonoid Kleisli Kleisli_Monoidal x
    (kpure copy[x])
    (kpure discard[x])
    (kl_delta_coassoc x)
    (kl_delta_counit_left x)
    (kl_delta_counit_right x).

Lemma kl_delta_cocommutative (x : C) :
  @compose Kleisli _ _ _ (kpure (@braid C _ x x)) (kpure copy[x])
    ≈ kpure copy[x].
Proof.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact (@delta_cocommutative_of_ccomon C _ x (cd_comonoid x)).
Qed.

Definition Kleisli_cd_comonoid (x : C) :
  @CommutativeComonoid Kleisli Kleisli_Symmetric x :=
  @Build_CommutativeComonoid Kleisli Kleisli_Symmetric x
    (Kleisli_cd_comonoid_base x)
    (kl_delta_cocommutative x).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kl_cd_tensor_delta (X Y : C) :
  kpure copy[(X ⨂ Y)%object]
    ≈ @canonical_tensor_delta Kleisli Kleisli_Symmetric X Y
        (Kleisli_cd_comonoid_base X) (Kleisli_cd_comonoid_base Y).
Proof.
  transitivity
    (kpure (@canonical_tensor_delta C _ X Y
              (cd_comonoid X) (cd_comonoid Y))).
  { apply kl_pure_eqv.
    exact (cd_tensor_delta X Y). }
  unfold canonical_tensor_delta.
  rewrite kpure_comp_functor.
  apply compose_respects.
  - symmetry.
    exact (kl_pure_mid_swap_inv X Y).
  - symmetry.
    exact (kl_pure_tensor copy[X] copy[Y]).
Qed.

Lemma kl_cd_tensor_epsilon (X Y : C) :
  kpure discard[(X ⨂ Y)%object]
    ≈ @canonical_tensor_epsilon Kleisli Kleisli_Symmetric X Y
        (Kleisli_cd_comonoid_base X) (Kleisli_cd_comonoid_base Y).
Proof.
  transitivity
    (kpure (@canonical_tensor_epsilon C _ X Y
              (cd_comonoid X) (cd_comonoid Y))).
  { apply kl_pure_eqv.
    exact (cd_tensor_epsilon X Y). }
  unfold canonical_tensor_epsilon.
  rewrite kpure_comp_functor.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    exact (kl_pure_tensor discard[X] discard[Y]).
Qed.

Lemma kl_cd_unit_delta :
  kpure copy[@I C _] ≈ kpure (from (@unit_left C _ (@I C _))).
Proof.
  apply kl_pure_eqv.
  exact cd_unit_delta.
Qed.

Lemma kl_cd_unit_epsilon :
  kpure discard[@I C _] ≈ @id Kleisli (@I C _).
Proof.
  transitivity (kpure (@id C (@I C _))).
  - apply kl_pure_eqv.
    exact cd_unit_epsilon.
  - apply kpure_id.
Qed.

(*
   本节说明单子、Kleisli、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Kleisli_CopyDiscard : @CopyDiscard Kleisli Kleisli_Symmetric :=
  @Build_CopyDiscard Kleisli Kleisli_Symmetric
    Kleisli_cd_comonoid
    kl_cd_tensor_delta
    kl_cd_tensor_epsilon
    kl_cd_unit_delta
    kl_cd_unit_epsilon.

End WithCD.

End WithComm.

End KleisliCommutative.
