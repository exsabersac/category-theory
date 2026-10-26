Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Adjoints preserve the terminal object and binary products, packaged  / * 伴随保留终端对象和二进制产品，打包*)

(*
Awodey §9.6 (awodey:9.6:remark-adjoint-existence-tests): the corollaries
   of RAPL/LAPC that make limit preservation a usable test for the
   non-existence of adjoints, stated in the vocabulary of
   Functor/Structure/Terminal.v and Functor/Structure/Cartesian.v so that
   a refutation is a short contradiction rather than a walk through the
   general cone machinery.  Built for #432 (Instance/Sets/NoAdjoint.v, the
   first consumer, Mac Lane §V.5 Exercise 1).

   Each constant is a two-line composition: Adjunction/Continuity.v's
   [right_adjoint_PreservesLimitCone] at the empty or the two-object
   discrete diagram, read through Structure/Limit/Comparison.v's bridges
   [terminal_functor_iff_preserves_terminal] and
   [cartesian_functor_iff_preserves_binary_products]; the two
   left-adjoint forms are the same two lines for [Opposite_Adjunction F U
   A], in which [F^op] is the right adjoint.  Nothing is re-proved.

   PLACEMENT.  Comparison.v already requires Continuity.v, so these cannot
   live in Continuity.v without a cycle; Comparison.v owns the bridges but
   not the adjunction vocabulary.  A satellite of Continuity.v keeps both
   donors unedited.  Closure 39 files excluding self, Comparison.v 12 at
   the margin, Structure/Cocartesian.v 1, the other seventeen [Require]s 0
   (an earlier revision dropped the 1).

   UNIVERSES.  Each of the four carries [u0 = u2], the hom levels of the
   two categories identified — [Adjunction]'s own equation ([h1 = h2] in
   [Build_Adjunction']'s block; [right_adjoint_PreservesLimitCone] carries
   it already), not this file's; no [Set]; the stdlib caps [EqdepFacts],
   [JMeq], [eq_ind], [eq_ind_r], [eq_rect_r] and [Logic_lemmas.equality]
   are [DiscreteCat_Functor']'s (Comparison.v).  Four [.glob] heads,
   all “Closed under the global context”; no [Qed], no [Defined] — [:=]
   terms.

   NOTATION TRAP.  [InitialFunctor F] and [CocartesianFunctor F] are
   NOTATIONS (Functor/Structure/Terminal.v, Functor/Structure/
   Cartesian.v) and do not parse in a definition's return type; the
   two left-adjoint forms spell them out as [@TerminalFunctor (D^op) (C^op)
   (F^op) _ _] and [@CartesianFunctor (D^op) (C^op) (F^op) _ _]; [About]
   prints the first back as [InitialFunctor F] and the second as the
   qualified [Cartesian.CartesianFunctor] (an earlier revision said both
   print under the notations). 

--------
Awodey §9.6 (awodey:9.6:remark-adjoint-existence-tests)：推论
 RAPL/LAPC 使极限保持成为可用的测试
 词汇中陈述的伴随词不存在
 Functor/Structure/Terminal.v 和 Functor/Structure/Cartesian.v 以便
 反驳是一个简短的矛盾，而不是一个完整的过程
 通用圆锥机械。 为 #432 构建（Instance/Sets/NoAdjoint.v，
 第一个消费者，Mac Lane §V.5 练习 1)。

每个常量都是两行组成：Adjunction/Continuity.v's
 [right_adjoint_PreservesLimitCone] 在空或两个对象处
 离散图，通读 Structure/Limit/Comparison.v 的桥梁
 [terminal_functor_iff_preserves_terminal] 和
 [cartesian_functor_iff_preserves_binary_products]； 两个
 左伴随形式与 [Opposite_Adjunction F U 的两行相同
 A]，其中 [F^op] 是右伴随。 没有什么可以被重新证明。

放置。 Comparison.v 已经需要 Continuity.v，所以这些不能
 存在于 Continuity.v 中，没有循环； Comparison.v 拥有桥梁，但是
 不是附加词汇。 Continuity.v 的卫星同时保留了两者
 未经编辑的捐助者。 关闭 39 个文件（不包括 self），Comparison.v 12 at
 边距，Structure/Cocartesian.v 1，其他十七个 [Require]s 0
 （较早的修订版删除了 1）。

宇宙。 四个中的每一个都带有 [u0 = u2]，即
 确定了两个类别 - [Adjunction] 自己的方程（[h1 = h2] 在
 [Build_Adjunction'] 的块； [right_adjoint_PreservesLimitCone] 携带
 已经），不是这个文件的； 没有 [Set]； stdlib 上限 [EqdepFacts]，
 [JMeq]、[eq_ind]、[eq_ind_r]、[eq_rect_r] 和 [Logic_lemmas.equality]
 是 [DiscreteCat_Functor']（Comparison.v）。 四个 [.glob] 头，
 所有“在全球范围内关闭”； 没有 [Qed]，没有 [Defined] — [:=]
 条款。

符号陷阱。 [InitialFunctor F] 和 [CocartesianFunctor F] 是
 符号（Functor/Structure/Terminal.v、Functor/Structure/
 Cartesian.v) 并且不解析定义的返回类型； 的
 两个左伴随形式将它们拼写为 [@TerminalFunctor (D^op) (C^op)
 (F^op)_ _] 和 [@CartesianFunctor (D^op) (C^op) (F^op) _ _]； 保护25X
 将第一个背面打印为 [InitialFunctor F]，第二个背面打印为
 合格的 [Cartesian.CartesianFunctor]（较早的修订版表示两者
 打印在注释下）。 
*)

Section AdjointPreservation.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
A right adjoint preserves the terminal object: RAPL at the empty
   discrete diagram, read through Structure/Limit/Comparison.v's bridge
   into Functor/Structure/Terminal.v's class. 

--------
右伴随保留终端对象：空处的 RAPL
 离散图，通读 Structure/Limit/Comparison.v 的桥
 进入 Functor/Structure/Terminal.v 的类。 
*)
Definition right_adjoint_preserves_terminal `{@Terminal C} `{@Terminal D} :
  @TerminalFunctor C D U _ _ :=
  snd (terminal_functor_iff_preserves_terminal U)
      (right_adjoint_PreservesLimitCone A (DiscreteCat_Functor' nullary_fam)).

(*
A right adjoint preserves binary products: RAPL at the two-object
   discrete diagrams, through the cartesian bridge. 

--------
右伴随保留二元乘积：双对象处的 RAPL
 通过笛卡尔桥的离散图。 
*)
Definition right_adjoint_preserves_binary_products
  `{@Cartesian C} `{@Cartesian D} : @CartesianFunctor C D U _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products U)
      (fun x y => right_adjoint_PreservesLimitCone A
                    (DiscreteCat_Functor' (binary_fam x y))).

(*
A left adjoint preserves the initial object: the same two lines for
   the opposite adjunction, in which [F^op] is the right adjoint.  The
   return type is [InitialFunctor F] spelled out, because that name is a
   notation (Functor/Structure/Terminal.v) and does not parse here. 

--------
左伴随保留初始对象：相同的两行
 相反的伴随，其中 [F^op] 是右伴随。 的
 返回类型是 [InitialFunctor F] 拼写的，因为该名称是
 符号（Functor/Structure/Terminal.v）并且不在这里解析。 
*)
Definition left_adjoint_preserves_initial `{@Initial C} `{@Initial D} :
  @TerminalFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (terminal_functor_iff_preserves_terminal (F^op))
      (right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
         (DiscreteCat_Functor' nullary_fam)).

(*
A left adjoint preserves binary coproducts: [CocartesianFunctor F],
   likewise spelled out (Functor/Structure/Cartesian.v). 

--------
左伴随保留二元余积：[CocartesianFunctor F]，
 同样拼写（Functor/Structure/Cartesian.v）。 
*)
Definition left_adjoint_preserves_binary_coproducts
  `{@Cocartesian C} `{@Cocartesian D} :
  @CartesianFunctor (D^op) (C^op) (F^op) _ _ :=
  snd (cartesian_functor_iff_preserves_binary_products (F^op))
      (fun x y => right_adjoint_PreservesLimitCone (Opposite_Adjunction F U A)
                    (DiscreteCat_Functor' (binary_fam x y))).

End AdjointPreservation.
