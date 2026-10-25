Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Cones.

Generalizable All Variables.

(** * Limit as a terminal cone / * 极限作为终端圆锥 *)

(*
 nLab:      https://ncatlab.org/nlab/show/limit
 Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

 Wikipedia: a limit "may also be characterized as terminal objects in the
 category of cones to F." nLab agrees: the limit lim F is the universal cone,
 "precisely the terminal object in the category of all cones over F", since
 every cone has a unique morphism into it.

 This file makes that characterization constructive: from a terminal object
 [T] of [Cones F] (see [Instance/Cones.v], the category whose objects are
 cones over F and whose morphisms are apex maps commuting with the legs) we
 build a [Limit F] (see [Structure/Limit.v]). The terminal cone becomes
 [limit_cone], and the universal property [ump_limits] is read off from
 terminality of [T]:

 - the mediating morphism on apexes is [`1 (one N)], the apex component of
 the unique cone map [! : N ~> T];
 - it satisfies the leg-factorization φ_x ∘ u ≈ ψ_x by [`2 (one N)], the
 commuting condition packaged into that cone morphism;
 - its uniqueness follows from [one_unique]: any apex map [v] carrying its
 own factorization proof [H] yields a cone morphism [(v; H)] into [T],
 which terminality forces to equal [one N] (hence v equals u on apexes).

 Dually, a colimit is the terminal object of [Cocones F] -- [Cones (F^op)],
 whose arrows run in C^op, so "initial in the category of cocones" reads
 as TERMINAL there -- obtained below by instantiating this at [F^op]. 

 --------
 nLab：https://ncatlab.org/nlab/show/limit
 Wikipedia：https://en.wikipedia.org/wiki/Limit_(category_theory)

 Wikipedia：极限“也可以被描述为F的锥的范畴中的终对象。”nLab同意：极限 lim F 是普遍锥，“恰好是所有F上的锥的范畴中的终对象”，因为每个锥都有唯一的态射进入它。

 该文件将这种表征构造化：从 [Cones F] 的终对象 [T]（见 [Instance/Cones.v]，F的锥为对象、顶点映射与腿交换为态射的范畴）我们构建一个 [Limit F]（见 [Structure/Limit.v]）。终锥成为 [limit_cone]，并且普遍性质 [ump_limits] 从 [T] 的终性直接得出：- 顶点上的中介态射是 [`1 (one N)]，唯一圆锥映射的顶点分量是 [! : N ~> T]；
 - 它满足腿分解 φ_x ∘ u ≈ ψ_x，通过 [`2 (one N)]，即封装在该圆锥态射中的交换条件；
 - 它的唯一性来自 [one_unique]：任何顶点映射 [v] 携带自身的分解证明 [H] 都会产生一个圆锥态射 [(v; H)] 到 [T]，而末端性强制它等于 [one N]（因此 v 在顶点上等于 u）。

 对偶地，余极限是 [Cocones F] -- [Cones (F^op)] 的终对象，其箭头在 C^op 中，所以“在共圆锥类别中的初始”在此处读作终对象——通过在 [F^op] 实例化如下获得。
*)
Program Definition Limit_Cones `(F : J ⟶ C) `{T : @Terminal (Cones F)} :
  Limit F := {|
  limit_cone := @terminal_obj _ T;
  ump_limits := fun N =>
    {| unique_obj := `1 (@one _ T N)
     ; unique_property := `2 (@one _ T N)
     ; uniqueness       := fun v H => @one_unique _ T N (@one _ T N) (v; H) |}
|}.

(* * * The converse, and the colimit readings / * * 对偶，以及余极限读数 *)

(*
 The converse of [Limit_Cones]: the limit cone is terminal in [Cones F].
 Its unique arrow from a cone [N] is the limit's mediator with its own
 factorization proof, and uniqueness is [uniqueness] twice.

 COLIMITS.  With [Cocones F := Cones (F^op)] (Instance/Cones.v), a cocone
 morphism is an arrow of C^op, so the colimit -- the initial cocone in the
 textbook's covariant reading -- is the TERMINAL object of [Cocones F].
 [Colimit F] is [Limit (F^op)] definitionally (Structure/Limit.v), so the
 two passages below are [Limit_Cones]/[Cones_Limit] at [F^op] with no
 tactic.  The covariant spelling [Initial ((Cocones F)^op)] is THE SAME
 TYPE, [(X^op)^op = X] holding by [eq_refl] here, which
 [initial_op_is_terminal] records; [Initial (Cocones F)] itself is a
 DIFFERENT type (terminality in [(Cocones F)^op]), refuted at [eq_refl]
 and pinned in Test/ProbeFinite417.v. 

 --------
 [Limit_Cones] 的逆命题：极限锥在 [Cones F] 中是终端的。它从锥 [N] 的唯一箭头是极限的中介与其自身的分解证明，并且唯一性在 [uniqueness] 中两次出现。

 余极限。使用 [Cocones F := Cones (F^op)]（Instance/Cones.v），余锥态射是 C^op 的箭头，因此余极限——在教材的协变解释中为初始余锥——是 [Cocones F] 的终端对象。[Colimit F] 在定义上等于 [Limit (F^op)]（Structure/Limit.v），所以下面的两个过程在 [F^op] 中没有策略地是 [Limit_Cones] / [Cones_Limit]。协变拼写 [Initial ((Cocones F)^op)] 是相同类型，[(X^op)^op = X] 通过 [eq_refl] 保持，这由 [initial_op_is_terminal] 记录；[Initial (Cocones F)] 本身是一个不同类型（在 [(Cocones F)^op] 中的终端性），在 [eq_refl] 中被驳斥并在 Test/ProbeFinite417.v 中固定。
*)

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Initial.

Definition Cones_Limit `(F : J ⟶ C) (L : Limit F) : @Terminal (Cones F).
Proof.
  unshelve refine (@Build_Terminal (Cones F) (@limit_cone _ _ _ L)
    (fun N => (unique_obj (@ump_limits _ _ _ L N);
               unique_property (@ump_limits _ _ _ L N))) _).
  intros N f g; simpl.
  transitivity (unique_obj (@ump_limits _ _ _ L N)).
  - symmetry.
    exact (uniqueness (@ump_limits _ _ _ L N) (`1 f) (`2 f)).
  - exact (uniqueness (@ump_limits _ _ _ L N) (`1 g) (`2 g)).
Defined.

Definition Colimit_Cocones `(F : J ⟶ C) (T : @Terminal (Cocones F)) :
  Colimit F := @Limit_Cones _ _ (Opposite_Functor F) T.

Definition Cocones_Colimit `(F : J ⟶ C) (L : Colimit F) :
  @Terminal (Cocones F) := Cones_Limit (Opposite_Functor F) L.

Definition Colimit_Cocones_initial `(F : J ⟶ C)
  (I : @Initial (Opposite (Cocones F))) : Colimit F := Colimit_Cocones F I.

Definition Cocones_Colimit_initial `(F : J ⟶ C) (L : Colimit F) :
  @Initial (Opposite (Cocones F)) := Cocones_Colimit F L.

Example initial_op_is_terminal `(F : J ⟶ C) :
  @Initial (Opposite (Cocones F)) = @Terminal (Cocones F) := eq_refl.
