Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Monoid objects in a monoidal category *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   本文件给出幺半范畴中的幺半群对象：乘法 μ、单位 η，以及结合律与左右单位律（插入结合子/单位子使态射可复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/microcosm+principle
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/Day+convolution
   Paper: Eckmann, Hilton, "Group-like structures in general categories
   Paper: Bénabou, "Algèbre élémentaire dans les catégories", C. R.
   Paper: Rivas, Jaskelioff, "Notions of Computation as Monoids", 2014

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonoidObject.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;             (* unit           η : I       ~> mon *)
  mappend : mon ⨂ mon ~> mon;     (* multiplication μ : mon ⨂ mon ~> mon *)

  (* left unit law: mappend ∘ (mempty ⨂ id) ≈ λ (left unitor I ⨂ mon ≅ mon) *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  (* right unit law: mappend ∘ (id ⨂ mempty) ≈ ρ (right unitor mon ⨂ I ≅ mon) *)
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* associativity, with the associator α reassociating the triple tensor:
     (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

Context (mon : C).
Context `{@MonoidObject mon}.

(* Symmetric form of [mappend_assoc], reassociating in the opposite direction
   by composing with the inverse associator [tensor_assoc ⁻¹]. *)
Lemma mappend_assoc_sym :
  mappend ∘ bimap id mappend ≈ mappend ∘ bimap mappend id ∘ (tensor_assoc ⁻¹).
Proof.
  rewrite mappend_assoc.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  cat.
Qed.

End MonoidObject.

(* Projections to the unit and multiplication of a given monoid object [M]. *)
Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

Section Monoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(*
   nLab: "Classical monoids are of course just monoids in Set with the

   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Monoid := @MonoidObject C CC_Monoidal.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (x × y) := {|
  mempty  := @mempty _ _ _ X △ @mempty _ _ _ Y;
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  assert ((mempty[X] △ mempty[Y] ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (mempty[X] △ mempty[Y]) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y]))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  assert ((split mappend[X] mappend[Y] ∘ toggle ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !id_left.
  rewrite !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !split_comp.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite !id_right.
  rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
  rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
  rewrite <- !split_comp.
  rewrite !comp_assoc.
  rewrite HX, HY.
  rewrite !id_left.
  apply fork_respects; clear;
  now unfold split; unfork; cat.
Qed.

Context `{@Closed C _}.

(* Duplicate the [z] component across both halves of a product:
   (x × y) × z ~> (x × z) × (y × z). Used to feed the shared argument to both
   pointwise multiplications in [Hom_Monoid]. *)
Definition doppel {x y z : C} : (x × y) × z ~> (x × z) × (y × z) :=
  first exl △ first exr.

(* The pair of uncurried projections equals evaluating both function arguments
   at the shared point, after distributing that point via [doppel]. *)
Lemma uncurry_exl_fork_exr {x y : C} :
  uncurry exl △ uncurry exr ≈ split eval eval ∘ @doppel (y ^ x) (y ^ x) x.
Proof.
  unfold doppel.
  rewrite split_fork.
  now rewrite !eval_first.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ uncurry exl △ uncurry exr)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exr_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ Y) as HY.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exl_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ Y) as HY.
  rewrite uncurry_exl_fork_exr.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  rewrite split_fork.
  rewrite !eval_first.
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !uncurry_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  now rewrite uncurry_curry.
Qed.

End Monoid.
