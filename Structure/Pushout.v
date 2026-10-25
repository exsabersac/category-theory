Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(** * Pushouts: ergonomic accessors / * 推出装置：符合人体工学的取件器 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

 A pushout is the colimit of a span [y <-f- x -g-> z] in [C]: an apex
 object [y +_x z] together with two injections [pushout_in1 : y ~> apex]
 and [pushout_in2 : z ~> apex] whose square commutes,

 pushout_in1 ∘ f ≈ pushout_in2 ∘ g,

 and which is universal (initial) among such cocones.  Universal property,
 in library notation: for every competing cocone [(Q, q1, q2)] with
 [q1 ∘ f ≈ q2 ∘ g] there is a unique mediator [u : apex ~> Q] with

 u ∘ pushout_in1 ≈ q1   and   u ∘ pushout_in2 ≈ q2.

 Pushout is dual to pullback: a pushout in [C] is exactly a pullback in
 [C^op].  Accordingly the underlying representation reuses [Pullback]:

 Definition Pushout {C} {x y z : C^op} (f : x ~> z) (g : y ~> z)
 := Pullback f g.

 That phrasing forces users to write their morphisms in [C^op] (i.e.
 reversed).  This file provides a thin convenience layer that takes the
 span in [C] directly, plus a [HasPushouts] predicate that quantifies the
 existence of all binary pushouts.

 The accessors [pushout_apex], [pushout_in1], [pushout_in2],
 [pushout_commutes] and [pushout_ump] are written with the morphisms
 inverted to the underlying [Pullback] representation, so downstream code
 can think entirely in terms of [C]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/pushout 
 维基百科:  https://en.wikipedia.org/wiki/Pushout_(category_theory) 

 推出（pushout）是 [C] 中一个跨度 [y <-f- x -g-> z] 的余极限：一个顶点对象 [y +_x z] 以及两个单射 [pushout_in1 : y ~> apex] 和 [pushout_in2 : z ~> apex]，使得该方形交换，

 pushout_in1 ∘ f ≈ pushout_in2 ∘ g,

 并且在所有这样的余锥中具有普遍性（初始性）。普遍性质，用库记法表示：对于每一个竞争余锥 [(Q, q1, q2)]，以及 [q1 ∘ f ≈ q2 ∘ g]，都存在唯一的中介映射 [u : apex ~> Q]，使得

 u ∘ pushout_in1 ≈ q1   且   u ∘ pushout_in2 ≈ q2。

 推出是拉回（pullback）的对偶：[C] 中的推出恰好是 [C^op] 中的拉回。因此，其底层表示重用 [Pullback]：

 定义 Pushout {C} {x y z : C^op} (f : x ~> z) (g : y ~> z)
 := Pullback f g。这种表述迫使用户以 [C^op]（即反向）的方式编写它们的态射。该文件提供了一个薄的便利层，可以直接在 [C] 中使用跨度，以及一个 [HasPushouts] 谓词，用于量化所有二元推挤的存在性。

 访问器 [pushout_apex]、[pushout_in1]、[pushout_in2]、[pushout_commutes] 和 [pushout_ump] 是以反转的态射写入底层 [Pullback] 表示的，因此下游代码可以完全以 [C] 来思考。
*)

Section Pushout.

Context {C : Category}.

(** Pushout of the span [y <-f- x -g-> z]. / 拉出跨度 [y <-f- x -g-> z] 。 *)
(*
   【IsPushout / HasPushouts 定义展开】/ Definition walkthrough

   1) 不新开「推出 Class」：IsPushout f g := Pullback (C^op) … —— 字面是 C^op 中的拉回。
      Pushout = pullback in the opposite category (definitional duality).

   2) 几何图景 / Picture
      跨度 y <-f- x -g-> z 的推出：顶点 P，内射 in1 : y ~> P、in2 : z ~> P，
      交换 in1∘f ≈ in2∘g，且对其它交换余锥唯一中介（pushout_ump）。
      Cocone over a span; UMP = unique mediator out of the apex.

   3) HasPushouts：为每个跨度选一个 IsPushout（= HasPullbacks (C^op)）。
      Choice of a pushout for every span.

   阅读：Pullback → 本文件访问器 → HasPushouts。Set 中 ≈ 粘合商。
   Read: Pullback → accessors here → HasPushouts. In Set ≈ quotient glue.
*)

Definition IsPushout {x y z : C} (f : x ~> y) (g : x ~> z) : Type :=
  @Pullback (C^op) y z x f g.

Definition pushout_apex {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : C :=
  @Pull (C^op) y z x f g P.

Definition pushout_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : y ~{C}~> pushout_apex P :=
  @pullback_fst (C^op) y z x f g P.

Definition pushout_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : z ~{C}~> pushout_apex P :=
  @pullback_snd (C^op) y z x f g P.

(** The square commutes: both legs precomposed with the span agree. / 方形是可换的：两个边在与跨格前组合时是一致的。 *)
Lemma pushout_commutes {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) :
  pushout_in1 P ∘ f ≈ pushout_in2 P ∘ g.
Proof.
  exact (@pullback_commutes (C^op) y z x f g P).
Qed.

(*
   * The universal property: given any other cocone over the same span there
   is a unique mediating morphism from the pushout apex. 

   --------
   * 泛性质：对于相同范围上的任何其他余锥，存在一个从推挤顶点出发的唯一中介态射。
*)
Lemma pushout_ump {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      (Q : C) (q1 : y ~> Q) (q2 : z ~> Q)
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : pushout_apex P ~> Q,
    u ∘ pushout_in1 P ≈ q1 ∧ u ∘ pushout_in2 P ≈ q2.
Proof.
  exact (@ump_pullbacks (C^op) y z x f g P Q q1 q2 Hcomm).
Qed.

(** Convenience: the mediating morphism out of a pushout. / 便利性：从推上的出发的中介态射。 *)
Definition pushout_med {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
           (Hcomm : q1 ∘ f ≈ q2 ∘ g)
  : pushout_apex P ~> Q :=
  unique_obj (pushout_ump P Q q1 q2 Hcomm).

Lemma pushout_med_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in1 P ≈ q1.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [H _].
  exact H.
Qed.

Lemma pushout_med_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in2 P ≈ q2.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [_ H].
  exact H.
Qed.

Lemma pushout_med_unique {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (v : pushout_apex P ~> Q) :
  v ∘ pushout_in1 P ≈ q1 -> v ∘ pushout_in2 P ≈ q2 ->
  pushout_med P Hcomm ≈ v.
Proof.
  intros H1 H2.
  unfold pushout_med.
  apply (uniqueness (pushout_ump P Q q1 q2 Hcomm)); split; assumption.
Qed.

(*
   * Equality lemma: two mediators out of a pushout that agree on both
   pushout legs are equal.  Useful for showing [u ≈ v] without
   exhibiting the intermediate [pushout_med] explicitly. 

   --------
   * 等式引理：如果两个中介者在一个推挤图的两个腿上都相等，那么它们相等。对于在不显式展示中间项 [pushout_med] 的情况下证明 [u ≈ v] 很有用。
*)
Lemma pushout_med_eq {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (u v : pushout_apex P ~> Q) :
  u ∘ pushout_in1 P ≈ q1 ->
  u ∘ pushout_in2 P ≈ q2 ->
  v ∘ pushout_in1 P ≈ q1 ->
  v ∘ pushout_in2 P ≈ q2 ->
  u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_med P Hcomm).
  - symmetry. apply pushout_med_unique; assumption.
  - apply pushout_med_unique; assumption.
Qed.

End Pushout.

(** A category has all binary pushouts if every span has a pushout. / 如果每个叉子都有推子，则一个范畴具有所有二元推子。 *)
Class HasPushouts (C : Category) : Type := {
  pushout : forall {x y z : C} (f : x ~> y) (g : x ~> z), IsPushout f g
                                        (* a chosen pushout for every span / 每个跨度的选定推出 *)
}.

Arguments pushout {C _ x y z} f g.

(*
   * [HasPushouts C] is exactly [HasPullbacks (C^op)] by definitional
   unfolding of [IsPushout].  We expose both directions of the equivalence
   as functions so the two predicates can be interchanged at will. 

   --------
   *  根据 [IsPushout] 的定义性展开，[HasPushouts C] 恰好是 [HasPullbacks (C^op)]。我们将等价关系的两个方向作为函数展示，以便两个谓词可以随意互换。
*)
Definition HasPullbacks_op_of_HasPushouts
           {C : Category} (HP : HasPushouts C) : HasPullbacks (C^op).
Proof.
  unshelve econstructor.
  intros x y z f g.
  (*
 A pullback in C^op of f : x ~{C^op}~> z, g : y ~{C^op}~> z is a pushout in
 C of f : z ~{C}~> x, g : z ~{C}~> y; the latter is supplied by [HP]. 

 --------
 在 C^op 中，f : x ~{C^op}~> z, g : y ~{C^op}~> z 的拉回是 C 中 f : z ~{C}~> x, g : z ~{C}~> y 的推出；后者由 [HP] 提供。
*)
  exact (@pushout C HP z x y f g).
Defined.

Definition HasPushouts_of_HasPullbacks_op
           {C : Category} (HP : HasPullbacks (C^op)) : HasPushouts C.
Proof.
  unshelve econstructor.
  intros x y z f g.
  exact (@pullback (C^op) HP y z x f g).
Defined.
