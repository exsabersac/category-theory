Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** The product of two functors. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance ProductFunctor
        {C : Category} {D : Category} {F : C ⟶ D}
        {J : Category} {K : Category} {G : J ⟶ K} :
  (C ∏ J) ⟶ (D ∏ K) := {
  fobj := fun x => (F (fst x), G (snd x));            (* (c, j) ↦ (F c, G j) *)
  fmap := fun _ _ f => (fmap[F] (fst f), fmap[G] (snd f));  (* (f, g) ↦ (F f, G g) *)
  fmap_respects := fun x y f g eqv =>
    (fmap_respects (fst x) (fst y) (fst f) (fst g) (fst eqv),
     fmap_respects (snd x) (snd y) (snd f) (snd g) (snd eqv));
  fmap_id := fun x =>
    (@fmap_id C D F (fst x), @fmap_id J K G (snd x));
  fmap_comp := fun x y z f g =>
    (@fmap_comp C D F (fst x) (fst y) (fst z) (fst f) (fst g),
     @fmap_comp J K G (snd x) (snd y) (snd z) (snd f) (snd g))
}.

(* F ∏⟶ G : C ∏ J ⟶ D ∏ K, the componentwise product of functors. *)
Notation "F ∏⟶ G" := (@ProductFunctor _ _ F _ _ G) (at level 9).

(* Conjugating bifunctor symmetry Swap (C ∏ D ⟶ D ∏ C, defined in
 Construction/Product) exchanges its two factors. Given F : C ∏ J ⟶ D ∏ K,
 this yields J ∏ C ⟶ K ∏ D as Swap ◯ F ◯ Swap, sending 对象 x to
 Swap (F (Swap x)).（已译） *)
Program Definition ProductFunctor_swap
        {C : Category} {D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : (J ∏ C) ⟶ (K ∏ D) := {|
  fobj := fun x => Swap (F (Swap x));
  fmap := fun _ _ f => _
|}.
Next Obligation.
  simpl in *.
  split; apply F; split; assumption.
Defined.
Next Obligation.
  proper; simpl; simplify; simpl in *.
  - rewrite !let_snd.
    rewrites; reflexivity.
  - rewrite !let_fst.
    rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite !let_fst, !let_snd; cat.
Qed.
Next Obligation.
  simpl in *.
  rewrite !let_fst, !let_snd; simplify;
  rewrite ?fst_comp, ?snd_comp;
  rewrite <- fmap_comp; reflexivity.
Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ProductFunctor_fst F : C ⟶ D, the slice c ↦ fst (F (c, I)). *)
Program Definition ProductFunctor_fst
        {C : Category} {D : Category}
        {J : Category} `{@Monoidal J} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : C ⟶ D := {|
  fobj := fun x => fst (F (x, I));
  fmap := fun x y f => fst (@fmap _ _ F (x, I) (y, I) (f, id));
  fmap_respects := fun x y f g eqv =>
    fst (@fmap_respects _ _ F (x, I) (y, I) (f, id) (g, id)
                        (eqv, reflexivity _));
  fmap_id := fun x => fst (@fmap_id _ _ F (x, I));
  fmap_comp := fun x y z f g =>
    _ (fst (@fmap_comp _ _ F (x, I) (y, I) (z, I) (f, id) (g, id)))
|}.
Next Obligation.
  intros.
  rewrite fst_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.

(* ProductFunctor_snd F : J ⟶ K, the slice j ↦ snd (F (I, j)). *)
Program Definition ProductFunctor_snd
        {C : Category} `{@Monoidal C} `{D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : J ⟶ K := {|
  fobj := fun x => snd (F (I, x));
  fmap := fun x y f => snd (@fmap _ _ F (I, x) (I, y) (id, f));
  fmap_respects := fun x y f g eqv =>
    snd (@fmap_respects _ _ F (I, x) (I, y) (id, f) (id, g)
                        (reflexivity _, eqv));
  fmap_id := fun x => snd (@fmap_id _ _ F (I, x));
  fmap_comp := fun x y z f g =>
    _ (snd (@fmap_comp _ _ F (I, x) (I, y) (I, z) (id, f) (id, g)))
|}.
Next Obligation.
  intros.
  rewrite snd_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.
