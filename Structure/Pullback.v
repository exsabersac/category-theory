Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* 拉回 / Pullback (fibered product)

   nLab:      https://ncatlab.org/nlab/show/pullback
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   共跨 b → a ← c 的极限：对象 Pull，投影 pullback_fst/snd，方块交换，
   且对每个竞争方块有唯一中介 u。对偶是推出（Pushout）。
   Limit of a cospan; dual of pushout.
*)

(*
   关于拉回 / On pullbacks

   Haskell 直觉：依赖积 / 纤维积 —— 例如
   `{(x,y) | f x == g y}`，或数据库 join、透镜里的 pullback。
   「在 z 上对齐」的两路数据。
   Haskell intuition: fibered product `{(x,y) | f x == g y}` (join).
*)

(*
   【Record Pullback 语法与字段展开】/ Syntax & field walkthrough

   1) Record（非 Class）：对固定 f : x ~> z、g : y ~> z 打包一个拉回锥。
      Record bundles one pullback for a fixed cospan (not a class on C).

   2) 数据 / Data
      - Pull              —— 拉回对象 / pullback object
      - pullback_fst/snd  —— 投影 Pull ~> x / Pull ~> y

   3) 交换 / Commute
      - pullback_commutes : f ∘ fst ≈ g ∘ snd

   4) UMP
      - ump_pullbacks : 任意交换方块 (Q,q1,q2) 经唯一 u : Q ~> Pull 分解。
        Every commuting square factors via unique u.

   5) HasPullbacks：范畴「有全部二元拉回」的类型类。
      Class saying C has all binary pullbacks.

   阅读：先积（Cartesian）与极限（Limit），再看拉回是「带方程的积」。
   Read products & limits first; pullback = product with an equation.
*)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull         : C;            (* 拉回对象 / pullback object *)
  pullback_fst : Pull ~> x;    (* 投影 p1 / projection p1 *)
  pullback_snd : Pull ~> y;    (* 投影 p2 / projection p2 *)

  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;
    (* 方块交换 / square commutes *)

  (* UMP：竞争方块经唯一 u 分解 / competing square factors via unique u *)
  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    → ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

(* 两拉回对象唯一同构 / Unique iso between pullbacks *)
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

(** 范畴有全部二元拉回 / C has all binary pullbacks
    (dual: HasPushouts). *)
Class HasPullbacks (C : Category) : Type := {
  pullback : forall {x y z : C} (f : x ~> z) (g : y ~> z), Pullback f g
}.

Arguments pullback {C _ x y z} f g.

(* 弱拉回：只要存在中介，不要唯一性 / Weak: existence without uniqueness *)
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
