Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/Kleisli+category
    Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KleisliAdjunction.

Context `{@Monad C M}.

#[local] Obligation Tactic := program_simpl.

(*
   本节说明函子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Kleisli_Free : C ⟶ Kleisli := {|
  fobj := fun x => x;
  fmap := fun x y f => ret ∘ f
|}.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation.
  (* ret ∘ (f ∘ g) ≈ join ∘ fmap[M] (ret ∘ f) ∘ (ret ∘ g) *)
  rewrite fmap_comp.
  rewrite (comp_assoc join).
  rewrite join_fmap_ret.
  rewrite id_left.
  rewrite (comp_assoc (fmap f)).
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(*
   本节说明函子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Kleisli_Forget : Kleisli ⟶ C := {|
  fobj := fun x => M x;
  fmap := fun x y f => join ∘ fmap[M] f
|}.
Next Obligation. proper. now rewrites. Qed.
Next Obligation. apply join_fmap_ret. Qed.
Next Obligation.
  (* join ∘ fmap[M] (join ∘ fmap[M] f ∘ g)
       ≈ (join ∘ fmap[M] f) ∘ (join ∘ fmap[M] g) *)
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  rewrite join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc join (fmap (fmap _))).
  rewrite join_fmap_fmap; cat.
Qed.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Kleisli_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier   := @hom Kleisli (Kleisli_Free x) y
     ; is_setoid := @homset Kleisli (Kleisli_Free x) y |}
    {| carrier   := @hom C x (Kleisli_Forget y)
     ; is_setoid := @homset C x (Kleisli_Forget y) |} := {|
  to   := {| morphism := fun f => f |};
  from := {| morphism := fun f => f |}
|}.
Next Obligation. proper. Qed.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Naturality transposition source 论元, stated the
 underlying arrows: precomposing Kleisli 态射 pure one is
 plain precomposition C. （已译） *)

Lemma kleisli_transpose_nat_l {x y z : C} (f : y ~{C}~> M z) (g : x ~{C}~> y) :
  join ∘ fmap[M] f ∘ (ret ∘ g) ≈ f ∘ g.
Proof.
  rewrite comp_assoc.
  rewrite <- (comp_assoc join (fmap[M] f) ret).
  rewrite <- fmap_ret.
  rewrite (comp_assoc join ret f).
  rewrite join_ret.
  cat.
Qed.

Program Definition Kleisli_Adjunction : Kleisli_Free ⊣ Kleisli_Forget :=
  @Build_Adjunction' Kleisli C Kleisli_Free Kleisli_Forget Kleisli_adj_iso _ _.
Next Obligation. apply kleisli_transpose_nat_l. Qed.
Next Obligation. reflexivity. Qed.

(** The unit 伴随 unit 单子. （已译） *)

Lemma Kleisli_unit_agrees {x : C} :
  @unit _ _ _ _ Kleisli_Adjunction x ≈ ret[M].
Proof. reflexivity. Qed.

(** The counit at x 恒等箭头 M x, read Kleisli
 态射 F_M (U_M x) ~{C_M}~> x runs computation. （已译） *)

Lemma Kleisli_counit_agrees {x : C} :
  @counit _ _ _ _ Kleisli_Adjunction x ≈ id[M x].
Proof. reflexivity. Qed.

(** The multiplication 单子 induced 伴随 (per
 Monad/Adjunction.v it U_M-image counit) join. （已译） *)

Lemma Kleisli_join_agrees {x : C} :
  fmap[Kleisli_Forget] (@counit _ _ _ _ Kleisli_Adjunction x) ≈ join[M].
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(** The resolution recovers M: 复合 U_M ◯ F_M naturally
 isomorphic M, 恒等 components. （已译） *)

Theorem Kleisli_Monad_agrees : Kleisli_Forget ◯ Kleisli_Free ≈ M.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  cat.
Qed.

End KleisliAdjunction.
