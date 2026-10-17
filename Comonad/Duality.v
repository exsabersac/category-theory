Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.CoKleisli.
Require Import Category.Comonad.Coalgebra.

Generalizable All Variables.

(* * * Duality 余单子: transfer package both resolutions （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/comonad
   nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   Theory/Monad.v 定义 [Comonad := @Monad (C^op) (W^op)]，且本库对偶使 C^op^op = C 与
   (W^op)^op = W 由 reflexivity 成立。本文件打包该选择对分解理论的后果：

   - C 上余单子与 C^op 上单子之间的转换——镜像地，C 上单子与 C^op 上余单子——是恒等，
     往返由 [reflexivity] 成立（[op_Monad_of_Comonad]、[Comonad_of_op_Monad] 等）；

   - 每个伴随 F ⊣ U（F : D ⟶ C 左伴随）在 C 上以自函子 F ◯ U 诱导余单子
     （[Adjunction_Comonad]），是 Monad/Adjunction.v 中 [Adjunction_Monad] 的形式对偶：
     用 Adjunction/Opposite.v 对偶伴随得 U^op ⊣ F^op，取其在 C^op 上诱导的单子；

   - 余单子的两种典范分解来自 Monad/Kleisli/Adjunction.v 与
     Monad/Eilenberg/Moore/Adjunction.v 的单子分解经对偶：对 co-Kleisli 范畴，遗忘
     x ↦ W x 是余自由的*左*伴随（[CoKleisli_Adjunction]），余代数的 co-Eilenberg–Moore
     同理（[CoEM_Adjunction]）——在 op 下单子世界的自由/遗忘对换边，故余单子分解为
     遗忘 ⊣ 余自由。复合 Forget ◯ Cofree 对两分解在表面上恢复 W。 *)

(*
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
   nLab: https://ncatlab.org/nlab/show/comonadic+functor

   本节说明伴随、函子、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonadComonadDuality.

Context {C : Category}.
Context {W : C ⟶ C}.

Definition op_Monad_of_Comonad (H : @Comonad C W) : @Monad (C^op) (W^op) := H.

Definition Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) : @Comonad C W := H.

Lemma Comonad_of_op_Monad_of_Comonad (H : @Comonad C W) :
  Comonad_of_op_Monad (op_Monad_of_Comonad H) = H.
Proof. reflexivity. Qed.

Lemma op_Monad_of_Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) :
  op_Monad_of_Comonad (Comonad_of_op_Monad H) = H.
Proof. reflexivity. Qed.

(** Mirrored: 单子 C same thing 余单子 C^op. Both
 typecheck because (C^op)^op = C (W^op)^op = W hold by
 reflexivity. （已译） *)

Definition op_Comonad_of_Monad (H : @Monad C W) : @Comonad (C^op) (W^op) := H.

Definition Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) : @Monad C W := H.

Lemma Monad_of_op_Comonad_of_Monad (H : @Monad C W) :
  Monad_of_op_Comonad (op_Comonad_of_Monad H) = H.
Proof. reflexivity. Qed.

Lemma op_Comonad_of_Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) :
  op_Comonad_of_Monad (Monad_of_op_Comonad H) = H.
Proof. reflexivity. Qed.

End MonadComonadDuality.

(*
   本节说明伴随、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjunctionComonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Definition Adjunction_Comonad (A : F ⊣ U) : @Comonad C (F ◯ U) :=
  let M : @Monad (C^op) (F^op ◯ U^op) :=
    Adjunction_Monad (Opposite_Adjunction F U A) in
  @Build_Monad (C^op) ((F ◯ U)^op)
    (fun x => @ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @fmap_ret (C^op) (F^op ◯ U^op) M x y f)
    (fun x => @join_fmap_join (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_fmap_ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_ret (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @join_fmap_fmap (C^op) (F^op ◯ U^op) M x y f).

End AdjunctionComonad.

(*
   本节说明伴随、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoKleisliAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoKleisli_Forget : @CoKleisli C W H ⟶ C :=
  Opposite_Functor (@Kleisli_Forget (C^op) (W^op) H).

Definition CoKleisli_Cofree : C ⟶ @CoKleisli C W H :=
  Opposite_Functor (@Kleisli_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. *)

Lemma CoKleisli_Forget_obj (x : C) : CoKleisli_Forget x = W x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Forget_fmap {x y : C} (f : W x ~{C}~> y) :
  fmap[CoKleisli_Forget] f ≈ extend f.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_obj (x : C) : CoKleisli_Cofree x = x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[CoKleisli_Cofree] f ≈ f ∘ extract.
Proof. reflexivity. Qed.

Definition CoKleisli_Adjunction : CoKleisli_Forget ⊣ CoKleisli_Cofree :=
  Opposite_Adjunction _ _ (@Kleisli_Adjunction (C^op) (W^op) H).

(** The counit 伴随 counit 余单子. （已译） *)

Lemma CoKleisli_counit_agrees {x : C} :
  @counit _ _ _ _ CoKleisli_Adjunction x ≈ @extract C W H x.
Proof. reflexivity. Qed.

(** The unit at x 恒等箭头 W x, read co-Kleisli
 态射 x ~{CoKleisli}~> CoKleisli_Cofree (W x). （已译） *)

Lemma CoKleisli_unit_agrees {x : C} :
  @unit _ _ _ _ CoKleisli_Adjunction x ≈ id[W x].
Proof. reflexivity. Qed.

(** The comultiplication 余单子 induced 伴随 (dually
 Monad/Adjunction.v it CoKleisli_Forget-image unit) is
 duplicate. （已译） *)

Lemma CoKleisli_duplicate_agrees {x : C} :
  fmap[CoKleisli_Forget] (@unit _ _ _ _ CoKleisli_Adjunction x)
    ≈ @duplicate C W H x.
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers W: 复合 Forget ◯ Cofree naturally
 isomorphic W, 恒等 components. （已译） *)

Theorem CoKleisli_Comonad_agrees : CoKleisli_Forget ◯ CoKleisli_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  exact (@fmap_extend_extract C W H x y f).
Qed.

End CoKleisliAdjunction.

(*
   本节说明伴随、单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoEilenbergMooreAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoEM_Forget : @CoEilenbergMoore C W H ⟶ C :=
  Opposite_Functor (@EM_Forget (C^op) (W^op) H).

Definition CoEM_Cofree : C ⟶ @CoEilenbergMoore C W H :=
  Opposite_Functor (@EM_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. *)

Lemma CoEM_Forget_obj (x : @CoEilenbergMoore C W H) : CoEM_Forget x = `1 x.
Proof. reflexivity. Qed.

Lemma CoEM_Forget_fmap {x y : @CoEilenbergMoore C W H}
      (f : x ~{@CoEilenbergMoore C W H}~> y) :
  fmap[CoEM_Forget] f ≈ t_alg_hom[f].
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_carrier (x : C) : `1 (CoEM_Cofree x) = W x.
Proof. reflexivity. Qed.

(** 本节：The costructure map cofree coalgebra x duplicate. （已译） *)

Lemma CoEM_Cofree_coalg (x : C) :
  t_alg[`2 (CoEM_Cofree x)] ≈ @duplicate C W H x.
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  t_alg_hom[fmap[CoEM_Cofree] f] ≈ fmap[W] f.
Proof. reflexivity. Qed.

Definition CoEM_Adjunction : CoEM_Forget ⊣ CoEM_Cofree :=
  Opposite_Adjunction _ _ (@EM_Adjunction (C^op) (W^op) H).

(** The counit 伴随 counit 余单子. （已译） *)

Lemma CoEM_counit_agrees {x : C} :
  @counit _ _ _ _ CoEM_Adjunction x ≈ @extract C W H x.
Proof.
  unfold counit; cbn.
  cat.
Qed.

(** 本节：The unit at coalgebra acts costructure map, stated the
 underlying arrow coalgebra homomorphism. （已译） *)

Lemma CoEM_unit_agrees {y : @CoEilenbergMoore C W H} :
  t_alg_hom[@unit _ _ _ _ CoEM_Adjunction y] ≈ t_alg[`2 y].
Proof.
  unfold unit; cbn.
  rewrite fmap_id.
  cat.
Qed.

(** The comultiplication 余单子 induced 伴随 is
 duplicate. （已译） *)

Lemma CoEM_duplicate_agrees {x : C} :
  fmap[CoEM_Forget] (@unit _ _ _ _ CoEM_Adjunction (CoEM_Cofree x))
    ≈ @duplicate C W H x.
Proof.
  cbn.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers W: 复合 Forget ◯ Cofree naturally
 isomorphic W, 恒等 components. （已译） *)

Theorem CoEM_Comonad_agrees : CoEM_Forget ◯ CoEM_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End CoEilenbergMooreAdjunction.
