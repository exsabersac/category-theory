Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* 拉回 (pullback)（也称纤维积）是共跨 `b → a ← c` 的极限；对偶于推出（C 中的拉回是
   C^op 中的推出）。

   nLab:      https://ncatlab.org/nlab/show/pullback
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   本库记号下的普遍性质：f 与 g 的拉回是对象 [Pull]，带投影
   [pullback_fst : Pull ~> x] 与 [pullback_snd : Pull ~> y]，满足
   f ∘ pullback_fst ≈ g ∘ pullback_snd，使得对每个满足 f ∘ q1 ≈ g ∘ q2 的 (Q, q1, q2)
   存在唯一 u : Q ~> Pull 满足 pullback_fst ∘ u ≈ q1 与 pullback_snd ∘ u ≈ q2。 *)

(*
   Wikipedia: "In fact, the pullback is the universal solution to finding a

   本节说明拉回/推出、笛卡尔、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Wikipedia: "A pullback of the morphisms f and g consists of an object P

   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/base+change
   nLab:  https://ncatlab.org/nlab/show/finite+limit
   nLab:  https://ncatlab.org/nlab/show/hyperdoctrine
   nLab:  https://ncatlab.org/nlab/show/span

   本节说明（余）极限、拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull         : C;            (* the pullback object  b ×_a c (fibered product) *)
  pullback_fst : Pull ~> x;    (* projection p1 : Pull ~> x *)
  pullback_snd : Pull ~> y;    (* projection p2 : Pull ~> y *)

  (* the projection square commutes *)
  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  (* universal property: the commuting square is terminal among such squares,
     i.e. every competing cone (Q, q1, q2) factors through a unique mediator u *)
  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

(*
   本节说明拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pullback_unique {C : Category} {x y z : C} {f : x ~> z} {g : y ~> z}
      (P Q : Pullback f g) : Pull f g P ≅ Pull f g Q.
Proof.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HQ.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HP.
  pose proof (ump_pullbacks f g P _ (pullback_fst f g P) (pullback_snd f g P)
                            (pullback_commutes f g P)) as HPP.
  pose proof (ump_pullbacks f g Q _ (pullback_fst f g Q) (pullback_snd f g Q)
                            (pullback_commutes f g Q)) as HQQ.
  destruct (unique_property HQ) as [HQfst HQsnd].
  destruct (unique_property HP) as [HPfst HPsnd].
  unshelve refine {|
    to   := unique_obj HQ;
    from := unique_obj HP
  |}.
  - (* to ∘ from ≈ id at Pull Q, by uniqueness against HQQ *)
    transitivity (unique_obj HQQ).
    + symmetry; apply (uniqueness HQQ); split.
      * rewrite comp_assoc, HQfst; exact HPfst.
      * rewrite comp_assoc, HQsnd; exact HPsnd.
    + apply (uniqueness HQQ); split; apply id_right.
  - (* from ∘ to ≈ id at Pull P, by uniqueness against HPP *)
    transitivity (unique_obj HPP).
    + symmetry; apply (uniqueness HPP); split.
      * rewrite comp_assoc, HPfst; exact HQfst.
      * rewrite comp_assoc, HPsnd; exact HQsnd.
    + apply (uniqueness HPP); split; apply id_right.
Defined.

(** A 范畴 has all binary pullbacks if every cospan has pullback.
 This dual [HasPushouts] [Structure/Pushout.v]. （已译） *)
Class HasPullbacks (C : Category) : Type := {
  pullback : forall {x y z : C} (f : x ~> z) (g : y ~> z), Pullback f g
}.

Arguments pullback {C _ x y z} f g.

(* A weak pullback differs pullback mediating 态射 is
 merely required exist; uniqueness dropped. （已译） *)
Record WeakPullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  weak_pull : C;
  weak_pullback_fst : weak_pull ~> x;
  weak_pullback_snd : weak_pull ~> y;

  weak_pullback_commutes :
    f ∘ weak_pullback_fst ≈ g ∘ weak_pullback_snd;

  weak_ump_pullbacks :
    ∀ Q (q1 : Q ~> x) (q2 : Q ~> y),
      f ∘ q1 ≈ g ∘ q2
      → ∃ u : Q ~> weak_pull,
          weak_pullback_fst ∘ u ≈ q1 ∧ weak_pullback_snd ∘ u ≈ q2
}.

(* Every pullback is a weak pullback by forgetting uniqueness. *)
Definition Pullback_to_WeakPullback {C : Category} {x y z : C}
           {f : x ~> z} {g : y ~> z} (P : Pullback f g) : WeakPullback f g.
Proof.
  refine {|
    weak_pull              := Pull f g P;
    weak_pullback_fst      := pullback_fst f g P;
    weak_pullback_snd      := pullback_snd f g P;
    weak_pullback_commutes := pullback_commutes f g P
  |}.
  intros Q q1 q2 H.
  pose proof (ump_pullbacks f g P Q q1 q2 H) as U.
  exists (unique_obj U).
  exact (unique_property U).
Defined.

(*
   本节说明拉回/推出、笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   Wikipedia: "The pullback is similar to the product, but not the same. One

   本节说明拉回/推出、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   Wikipedia: "... another way of characterizing the pullback: as the

   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
