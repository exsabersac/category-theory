Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Adjunction.GAFT.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SpanningArrow.

Generalizable All Variables.

(**
* Probe for Adjunction/SpanningArrow.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 6 and Lemma 2, printed pp. 127-128.  Issue #448.  The
    variety remark has its own probe, Test/ProbeVarietySpanning448.v.

    The import list above is the target file's own import list,
    unabbreviated.  A short prefix is what makes a probe pass vacuously,
    so nothing is trimmed even where a require is redundant.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc.  Kinds, under THIS import list:

      CONVERSION  - "cannot unify A and B" parenthetical present.
      TYPING      - the "has type X while it is expected to have type Y"
                    opener with NO such parenthetical.
      INSTANCE    - "(no type class instance found)": the negative must
                    be a [Definition] in a section with NO instance in
                    scope, since a [Check] tolerates the open evar and a
                    section that carries the instance ACCEPTS the term.
      UNIVERSE    - "universe inconsistency".  RECORDED CORRECTION: no
                    negative of this kind remains in the file.  B7 was the
                    only one, and it turned over when
                    [DiscreteCat_Functor] was annotated (PR "algebraic
                    carriers are sets", 2026-09-17); the section that held
                    it now keeps it as a positive control.  The kind is
                    left listed because the section still guards against
                    the refusal coming back.

    One boundary is NOT a refusal and is pinned positively (B1 below):
    [Spanning] with its two [sub_le] arguments exchanged is inhabited by
    EVERY arrow, so a refutation probe on it would be vacuous.

    The instrument check comes first; every library constant a negative
    names has a positive control outside any refutation command.

--------
* 探针用于 Adjunction/SpanningArrow.v

Mac Lane，《为工作数学家准备的范畴》，第2版，第V.7节 定义6和引理2，印刷页127-128。问题#448。该多样性备注有其专用探针，Test/ProbeVarietySpanning448.v。

上面的导入列表是目标文件自身的导入列表，未缩写。短前缀是让探针形式上通过的原因，所以即使某个 require 是多余的，也不会进行裁剪。

下面声称被驳斥的每条陈述都在整个文件的副本中被去掉了其驳斥关键字，单独编译，并读取其完整错误；一个成立的驳斥在本仓库的 coqc 下不会打印任何内容。种类，在本导入列表下：

转换 - 出现“无法统一 A 和 B”的括号说明。类型检查 - 开头没有这种括号的“具有类型 X，而预期具有类型 Y”。实例 - “（未找到类型类实例）”：在没有实例在作用域中的部分中，这种负面必须是 [Definition]，因为 [Check] 容忍开放的 evar，并且一个包含实例的部分可以接受该项。宇宙 - “宇宙不一致”。记录的更正：文件中不再存在这种负面情况。B7 是唯一的一个，当 [DiscreteCat_Functor] 被标注时（PR “代数载体是集合”，2026-09-17）它翻转了；现在保存它的部分将其作为阳性对照。种类仍然保持列出，因为该部分仍在防止拒绝重新出现。

一个边界并不是拒绝，并且是以积极的方式固定的（见下文B1）：
    [Spanning]及其交换了两个[sub_le]参数的情况被每个箭头所拥有，所以对它的反驳探针将是空洞的。

仪器检查优先；每个库常量的负名称在任何反驳命令之外都有一个阳性对照。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check spanning_arrow_448_no_such_constant.

(** ** Positive controls / ** 阳性对照 *)

Check @SubFactorsThrough.
Check @Spanning.
Check @spanning_arrow.
Check @PreservesWidePullbacks.
Check @SpanningArrowsOutOf.
Check @SubObj.
Check @sub_top.
Check @sub_le.
Check @sub_top_greatest.
Check @sub_dom.
Check @sub_mono.
Check @spanning_sub.
Check @spanning_factor.
Check @spanning_solution_set.
Check @factors_through_top.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @GAFT.
Check @GAFT_from_spanning.
Check @Complete.
Check @PreservesImageLimit.
Check @HasWidePullbacks.

(** ** Readbacks that HOLD, and the vacuity of the swapped order / ** 保持的回读，以及交换顺序的空洞性 *)

Section Readbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).
Context {x : X} {a : A} (f : x ~> G a).

(*
B1: the flipped order is VACUOUS -- inhabited for every f by
   [sub_top_greatest] -- which is why [Spanning] reads [sub_le sub_top m]
   and not [sub_le m sub_top].

--------
B1：颠倒的顺序是空的——对于每个 f 都被 [sub_top_greatest] 占据——这就是为什么 [Spanning] 读取 [sub_le sub_top m] 而不是 [sub_le m sub_top]。
*)
Definition p448_b1_flipped : Type :=
  ∀ m : SubObj a, SubFactorsThrough G f m → sub_le m sub_top.
Example p448_b1_vacuous : p448_b1_flipped.
Proof. intros m _; apply sub_top_greatest. Defined.

(*
B6: the two load-bearing [Defined]s, read back at eq_refl.  With
   [factors_through_top] closed by Qed the first is refused; with
   [spanning_solution_set] closed by Qed the last three are.

--------
B6：两个承重的 [Defined]，在 eq_refl 中回读。当 [factors_through_top] 被 Qed 关闭时，第一个被拒绝；当 [spanning_solution_set] 被 Qed 关闭时，最后三个被拒绝。
*)
Example p448_t_lift : `1 (factors_through_top G f) = f := eq_refl.
Example p448_t_index :
  sol_index (spanning_solution_set G GP x) = SpanningArrowsOutOf G x
  := eq_refl.
Example p448_t_obj (i : SpanningArrowsOutOf G x) :
  sol_obj (spanning_solution_set G GP x) i = `1 i := eq_refl.
Example p448_t_arr (i : SpanningArrowsOutOf G x) :
  sol_arr (spanning_solution_set G GP x) i = `1 (`2 i) := eq_refl.

(*
B2 -- CONVERSION (the message carries the "cannot unify" parenthetical
   on the codomain, "cannot unify "fobj[G] a" and "x""): the factorization
   composite in the wrong order, "The term "fmap[G] (sub_mono m)" has
   type "fobj[G] (sub_dom m) ~{ X }~> fobj[G] a" while it is expected to
   have type "fobj[G] (sub_dom m) ~{ X }~> x"".

--------
B2 -- 转换（消息在陪体上带有“无法统一”的注释，“无法统一‘fobj[G] a’和‘x’”）：因式分解复合顺序错误，“项‘fmap[G] (sub_mono m)’的类型为‘fobj[G] (sub_dom m) ~{ X }~> fobj[G] a’，而期望的类型为‘fobj[G] (sub_dom m) ~{ X }~> x’”。
*)
Fail Definition p448_b2 (m : SubObj a) : Type :=
  { k : x ~> G (sub_dom m) & k ∘ fmap[G] (sub_mono m) ≈ f }.

(*
B3 -- TYPING, not INSTANCE: [GP] is an EXPLICIT argument of the
   discharged [spanning_solution_set], so omitting it mis-applies the
   next argument: "The term "z" has type "obj[X]" while it is expected to
   have type "PreservesWidePullbacks G"".

--------
B3 -- 类型，而不是实例：[GP] 是已释放的 [spanning_solution_set] 的显式参数，因此省略它会错误地应用下一个参数：“术语‘z’的类型为‘obj[X]’，而预期类型为‘PreservesWidePullbacks G’。”
*)
Fail Definition p448_b3 (z : X) : SolutionSet G z :=
  spanning_solution_set G z.

(*
B5 -- TYPING: the spanning factor lands in the intersection, not in
   [a]: "has type "x ~{ X }~> fobj[G] (sub_dom (spanning_sub G f))" while
   it is expected to have type "x ~{ X }~> fobj[G] a"".

--------
B5 -- 类型检查：生成因子落在交集上，而不是在 [a]："具有类型 x ~{ X }~> fobj[G] (sub_dom (spanning_sub G f))"，而期望的类型是 "x ~{ X }~> fobj[G] a"。
*)
Fail Definition p448_b5 : x ~> G a := spanning_factor G GP f.

End Readbacks.

(** ** The missing-instance boundary, in a section WITHOUT the instance / ** 缺失实例边界，在没有实例的部分 *)

Section NoWidePullbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context {x : X} {a : A} (f : x ~> G a).

(*
B4 -- INSTANCE: "Cannot infer the implicit parameter HWP of
   spanning_sub whose type is "HasWidePullbacks A" (no type class
   instance found)".  Posed in the section that has the instance, the
   same term is ACCEPTED (measured), so the probe must live here.

--------
B4 -- 实例: “无法推断 spanning_sub 的隐式参数 HWP，其类型为 'HasWidePullbacks A'（未找到类型类实例）”。 在具有该实例的部分中提出时，相同的项是被接受的（已测量），所以探针必须存在于此处。
*)
Fail Definition p448_b4 : SubObj a := spanning_sub G f.

End NoWidePullbacks.

(** ** The former Set pin on GAFT, now lifted / ** 以前在GAFT上的设置引脚，现在已取消 *)

Section UnannotatedGAFT.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

(*
Former B7, now a positive control.

   RECORDED CORRECTION.  An earlier revision read: "B7 -- UNIVERSE: over
   an UNANNOTATED section, applying [GAFT] to the spanning solution set is
   refused, 'universe inconsistency: Cannot enforce Set = <the section's
   hom universe>' -- a section Context binds rigid universes and GAFT is
   pinned at [Category@{_ Set Set}] through Theory/WeaklyInitial.v's
   [initial_from_weakly_initial].  This is why [GAFT_from_spanning] sits
   in its own section over [Category@{oA Set Set}]; the annotated form is
   the positive control, [GAFT_from_spanning] itself, checked above."

   The chain of attribution was right as far as it went, and one link
   further back was the cause: [initial_from_weakly_initial] carried the
   [Set] because it takes two [Limit (DiscreteCat_Functor …)] premises and
   [DiscreteCat_Functor] was declared with bare binders, minimizing to
   [DiscreteCat@{u Set Set}].  Annotated in place in the PR "algebraic
   carriers are sets" (2026-09-17), Instance/Discrete.v, that [Set] is
   gone from [GAFT]'s statement and this application is ACCEPTED over a
   section whose universes are rigid.  It is kept here as a positive
   control: dropping the annotation refuses it again and breaks this file.
   [GAFT_from_spanning] keeps its own section, which is now a
   presentational choice rather than a universe obligation.

   SECOND CORRECTION, same PR, later commit.  The sentence above ended
   "[GAFT_from_spanning] keeps its own section", and that section is no
   longer annotated either: [Universes oA oX.] and the two
   [Category@{o Set Set}] annotations were DELETED and its [A] and [X] are
   now declared bare, exactly as this probe's are.  So this definition and
   [GAFT_from_spanning] are now THE SAME STATEMENT over the same binders,
   and [p448_b7_via_theorem] below records that by inhabiting this
   section's goal FROM the theorem -- which is the strongest identification
   available, since [GAFT_from_spanning] is [Qed] and no [eq_refl] reaches
   inside it.
   The widening is measured in Adjunction/SpanningArrow.v's header, where
   the BEFORE and AFTER [About]s are quoted side by side; the headline is
   that the BEFORE block carried [Set = oA], demanding a category whose
   OBJECTS as well as homs live in [Set], and the AFTER block carries no
   [Set] at all.

--------
之前是B7，现在是阳性对照。

已记录的更正。之前的修订版本写道：“B7 -- 宇宙：在一个未注释的部分上，试图将 [GAFT] 应用于跨越解集被拒绝，‘宇宙不一致：无法强制 Set = <该部分的 hom 宇宙>’——一个部分上下文绑定了刚性宇宙，而 GAFT 通过 Theory/WeaklyInitial.v 的 [initial_from_weakly_initial] 被固定在 [Category@{_ Set Set}] 。这就是为什么 [GAFT_from_spanning] 位于其自身部分之上覆盖 [Category@{oA Set Set}]；带注释的形式是正控件，即 [GAFT_from_spanning] 本身，如上所检验。”

归因链在其范围内是正确的，而更早的一环才是原因：[initial_from_weakly_initial] 承载了 [Set]，因为它需要两个 [Limit (DiscreteCat_Functor …)] 前提，而 [DiscreteCat_Functor] 是用裸绑定器声明的，最小化为 [DiscreteCat@{u Set Set}]。注释在 PR “代数载体是集合”(2026-09-17)，Instance/Discrete.v 中的相应位置，[Set] 从 [GAFT] 的陈述中消失，并且此应用在其宇宙是刚性的部分上被接受。它在这里保留作为积极的对照：去掉注释会再次拒绝它并破坏此文件。[GAFT_from_spanning] 保留了自己的部分，这现在是一个展示上的选择，而不是宇宙义务。

第二次修正，相同的 PR，稍后的提交。上面那句话以“[GAFT_from_spanning] 保持其自己的部分”结束，而该部分现在也不再有注释：[Universes oA oX.] 和两个 [Category@{o Set Set}] 注释被删除，其 [A] 和 [X] 现在被声明为裸的，正如这个探针的情况一样。因此，这个定义和 [GAFT_from_spanning] 现在是相同的语句，并且作用在相同的绑定器上，而下面的 [p448_b7_via_theorem] 通过从定理中占据该部分的目标来记录这一点——这是可用的最强识别，因为 [GAFT_from_spanning] 是 [Qed]，并且没有 [eq_refl] 触及它内部。扩展在 Adjunction/SpanningArrow.v 的头部被测量，其中 BEFORE 和 AFTER 的 [About] 并排引用；标题是 BEFORE 块包含 [Set = oA]，要求一个对象及其态射都位于 [Set] 中的范畴，而 AFTER 块根本不包含 [Set]。
*)
Definition p448_b7 (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := GAFT G comp cont (spanning_solution_set G GP).

(*
The two are now interchangeable, up to the implicit/explicit shape of
   the wide-pullback argument.  If the annotations are ever put back, this
   line stops compiling.

--------
这两个现在是可以互换的，取决于宽回退参数的隐式/显式形状。如果注解被重新加回，这一行就无法编译。
*)
Definition p448_b7_via_theorem (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := @GAFT_from_spanning A X G HWP GP comp cont.

End UnannotatedGAFT.
