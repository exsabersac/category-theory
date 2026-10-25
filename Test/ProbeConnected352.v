Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Connected.Components.

Generalizable All Variables.

(**
* Probe: the boundaries Theory/Connected/Components.v measures

   That file's header records five rejections and carries no [Fail] of its
   own.  A measurement is not a guard: nothing in the build would notice if
   a donor changed and one of them started to succeed.  This file converts
   each into a pinned negative, beside a control that must SUCCEED, so that
   the boundary breaks the build loudly rather than silently moving.

   The import list is the target's own, in the target's order, with the
   target itself appended.  A probe compiled against a shorter prefix can
   fail for a missing-reference or missing-coercion reason and read as a
   genuine mathematical rejection.

   THREE KINDS, and here they really are distinguishable — the error TEXT
   separates them, not merely the label:

     CONVERSION   (negatives 1 and 2) ends in
                  `(cannot unify "X" and "Y")`
     TYPING       (negative 3) reports `has type ... while it is expected
                  to have type ...` with NO `cannot unify` clause and no
                  universe clause
     FORMABILITY  (negatives 4 and 5) ends in
                  `(universe inconsistency: Cannot enforce ...)`

   Each negative below was stripped of its [Fail] and its whole error read,
   not merely its tail; the distinguishing phrase is quoted at each.

--------
* 探针：边界 Theory/Connected/Components.v 测量

那个文件的头部记录了五次拒绝，并且自身没有任何 [Fail]。一项测量不是防护：构建中的任何内容都不会注意到如果捐赠者发生变化，其中之一开始成功。这个文件将每个转换成固定的负值，同时旁边有一个必须成功的控制，这样边界会大声地破坏构建，而不是静默地移动。

导入列表是目标自身的，按目标的顺序排列，并附加目标本身。针对较短前缀编译的探针可能因缺少引用或缺少强制而失败，并被视为真正的数学排斥。

三种，这里它们确实可以区分——错误文本将它们分开，而不仅仅是标签：

转换（否定 1 和 2）以 `(cannot unify "X" and "Y")` 结束
类型检查（否定 3）报告 `has type ... while it is expected to have type ...`，没有 `cannot unify` 条款，也没有宇宙条款
可形成性（否定 4 和 5）以 `(universe inconsistency: Cannot enforce ...)` 结束

下面的每个负面都被剥离了其 [Fail]，并且其整个错误被读取，而不仅仅是其尾部；每个区分短语都已被引用。
*)

(**
** Instrument check

   This command must ERROR at compile time ("The command has not failed!"),
   which is what confirms that a [Fail] wrapping a SUCCEEDING command is
   itself rejected.  Read its scope precisely: it does NOT detect a [Fail]
   that accepted everything, since such a [Fail] would compile here too.
   What it rules out is the commoner accident — a [Fail] silently treated
   as a no-op — and it is checked first because the whole file rests on
   it.

--------
** 仪器检查

   该命令必须在编译时出错（"命令未失败！"），这就确认了一个包裹成功命令的 [Fail] 本身会被拒绝。精确地读取其作用域：它不会检测接受所有内容的 [Fail]，因为这样的 [Fail] 在这里也能编译。它排除的是更常见的意外——一个 [Fail] 被默默地当作空操作处理——并且它会首先被检查，因为整个文件都依赖于它。
*)
Fail Fail Check Category.

(**
** Negatives 1 and 2 — CONVERSION

   [zigzag_fmap] recurses on the CHAIN.  At a variable chain it is stuck
   and rebuilds nothing, so neither functor law holds definitionally.  The
   controls are the SAME statements at [zz_nil], which DO close by
   [eq_refl]: that is what locates the failure at the recursion rather than
   at [Id] or at [◯], and it is why [zigzag_fmap_id] and
   [zigzag_fmap_compose] are proved by induction in the target.

--------
** 否定 1 和 2 —— 转换

[zigzag_fmap] 在链上递归。在变量链上它被卡住，什么也不重建，因此没有一个函子律在定义上成立。控制是在 [zz_nil] 的相同语句，这些语句通过 [eq_refl] 关闭：这就是为何失败出现在递归时，而不是在 [Id] 或 [◯]，并且这也解释了为什么 [zigzag_fmap_id] 和 [zigzag_fmap_compose] 可以通过目标中的归纳证明。
*)

Section Conversion.
Context {C D E : Category}.

(*
NEGATIVE 1.  Stripped, this reports:
     The term "eq_refl" has type "zigzag_fmap Id[C] s = zigzag_fmap Id[C] s"
     while it is expected to have type "zigzag_fmap Id[C] s = s"
     (cannot unify "zigzag_fmap Id[C] s" and "s").

--------
负面 1. 精简后，此报告如下：
     术语“eq_refl”的类型为“zigzag_fmap Id[C] s = zigzag_fmap Id[C] s”，
     而期望的类型为“zigzag_fmap Id[C] s = s”（无法统一“zigzag_fmap Id[C] s”和“s”）。
*)
Fail Definition probe_fmap_id_variable (x y : C) (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s := eq_refl.

(* CONTROL 1: at the empty chain the same statement DOES close. / 控制 1：在空链上，相同的陈述确实会关闭。 *)
Definition probe_fmap_id_nil (x : C) :
  zigzag_fmap Id[C] (zz_nil x) = zz_nil x := eq_refl.

(*
NEGATIVE 2.  Stripped, this reports:
     (cannot unify "zigzag_fmap (G ◯ F) s"
              and "zigzag_fmap G (zigzag_fmap F s)").

--------
负 2.  拆开后，报告如下：
     （无法统一 "zigzag_fmap (G ◯ F) s"
              和 "zigzag_fmap G (zigzag_fmap F s)"）。
*)
Fail Definition probe_fmap_comp_variable (F : C ⟶ D) (G : D ⟶ E)
  (x y : C) (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s) := eq_refl.

(* CONTROL 2: at the empty chain it closes. / 控制 2：在空链处它关闭。 *)
Definition probe_fmap_comp_nil (F : C ⟶ D) (G : D ⟶ E) (x : C) :
  zigzag_fmap (G ◯ F) (zz_nil x) = zigzag_fmap G (zigzag_fmap F (zz_nil x))
  := eq_refl.

(*
CONTROLS naming the constants the two negatives depend on, so that
   renaming any of them breaks a command OUTSIDE a [Fail].

--------
控制命名常量是两个负数依赖的，因此重命名其中任何一个都会破坏 [Fail] 外部的命令。
*)
Check @zigzag_fmap.
Check @zigzag_fmap_id.
Check @zigzag_fmap_compose.
Check @ZigZag.
Check @zz_nil.

End Conversion.

(**
** Negative 3 — TYPING

   [Proper (equiv ==> equiv) fobj[F]] is CONVERTIBLE with the type of
   [zigzag_fmap F], but the elaborator does not unfold [Proper] and
   [respectful] while unifying, so the certificate is rejected as a
   record-literal field assignment.

   THE CONTROL IS THE LITERAL TERM, not an eta-expansion of it: control 3a
   discharges the field with [exact (@zigzag_fmap C D F)] — character for
   character what the [Fail] rejects — and [Print] on the result returns
   the very record literal that was refused,
   [{| morphism := fobj[F]; proper_morphism := @zigzag_fmap C D F |}].
   So the same term is rejected as a definition body and accepted when
   built by script, which is what makes this a fact about unification and
   not about the term, and is why [pi0_fmap] in the target is built with
   [unshelve refine].  Control 3b keeps the eta-expanded form because that
   is what the shipped [pi0_fmap] actually stores.

--------
** 负 3 — 类型检查

   [Proper (equiv ==> equiv) fobj[F]] 可以与 [zigzag_fmap F] 的类型互相转换，但在统一时，展开器不会展开 [Proper] 和 [respectful]，因此该证书被拒绝，原因是它作为记录字面量字段赋值不合法。

   控制对象是字面项，而不是其 eta 展开的形式：控制 3a 使用 [exact (@zigzag_fmap C D F)] 解除字段 —— 精确到字符与 [Fail] 拒绝的一致 —— 并且对结果使用 [Print] 返回了原本被拒绝的记录字面量，[{| morphism := fobj[F]；proper_morphism := @zigzag_fmap C D F |}]。
   因此，同一项作为定义体会被拒绝，但由脚本生成时却被接受，这就是为什么这是关于统一的事实，而不是关于该项本身的原因，也是为什么目标中的 [pi0_fmap] 是用 [unshelve refine] 构建的。控制 3b 保留 eta 展开的形式，因为这正是发布的 [pi0_fmap] 实际存储的内容。
*)

Section Typing.
Universes o so hc hd.
Context {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F : C ⟶ D).

(*
NEGATIVE 3.  Stripped, this reports — with NO `cannot unify` clause and
   no universe clause, which is what separates it from the other four:
     The term "@zigzag_fmap C D F" has type
      "∀ x y : obj[C], ZigZag x y → ZigZag (fobj[F] x) (fobj[F] y)"
     while it is expected to have type "Proper (equiv ==> equiv) fobj[F]".

--------
负面 3。去掉冗余后，该报告——没有 `cannot unify` 条款，也没有宇宙条款，这正是它与其他四个的区别：
  术语 "@zigzag_fmap C D F" 的类型是
   "∀ x y : obj[C], ZigZag x y → ZigZag (fobj[F] x) (fobj[F] y)"
  而它期望的类型是 "Proper (equiv ==> equiv) fobj[F]"。
*)
Fail Definition probe_proper_as_field :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D :=
  {| morphism := fobj[F]; proper_morphism := @zigzag_fmap C D F |}.

(* CONTROL 3a: the LITERAL rejected term, supplied by a one-step script. / 控制 3a：由一步脚本提供的字面拒绝术语。 *)
Definition probe_proper_literal :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  exact (@zigzag_fmap C D F).
Defined.

(* CONTROL 3b: the eta-expanded form the shipped [pi0_fmap] stores. / 控制 3b：已运输的 [pi0_fmap] 存储的 eta 扩展形式。 *)
Definition probe_proper_by_script :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

End Typing.

(*
CONTROL: [proper_morphism] is named OUTSIDE a [Fail].  Without this,
   renaming that field would make negative 3 fire for a missing-reference
   reason and pass vacuously — the field is otherwise mentioned only
   inside the [Fail] itself.

--------
控制：[proper_morphism] 被命名为 [Fail] 外部。没有这个，重命名该字段会因为缺失引用的原因触发负 3，并且形式上会通过 —— 该字段在其他地方仅在 [Fail] 内部提及。
*)
Check @proper_morphism.

Check @pi0.
Check @pi0_fmap.
Check @pi0_fmap_at.

(**
** Negatives 4 and 5 — FORMABILITY

   The target spells out universe binders in three places and reports the
   annotation as LOAD-BEARING.  Each clone below has the target's body with
   the binders removed and nothing else changed, so the comparison is
   attributable to the annotation alone.

   No explicit universe instance is written inside either [Fail]: a [Fail]
   carrying one can pass for an arity reason on another Coq version, which
   would make the guard vacuous without anything noticing.

--------
** 负面示例 4 和 5 — 可形成性

目标在三个地方写出了宇宙绑定器，并将注解报告为承重。下面的每个克隆都具有目标的主体，但删除了绑定器，其他内容保持不变，因此比较仅归因于注解本身。

在 [Fail] 中没有写入任何显式的宇宙实例：携带一个的 [Fail] 由于另一版本的 Coq 的元数原因可以通过，这将使保护变得无效而无人注意。
*)

(* An unannotated clone of [zigzag_fmap]. / [zigzag_fmap] 的未标注克隆。 *)
Fixpoint probe_zigzag_fmap_unann {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) : ZigZag (F x) (F y) :=
  match s in ZigZag a b return ZigZag (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  end.

(* Unannotated clones of the [pi0_proj] chain. / [pi0_proj] 链的未标注克隆。 *)
Definition probe_ObjSetoid_unann (C : Category) : SetoidObject :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence obj[C] |} |}.

Definition probe_coarser_unann (C : Category) :
  SetoidCoarser (A:=probe_ObjSetoid_unann C) (@ZigZag C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

Definition probe_pi0_unann (C : Category) : SetoidObject :=
  SetsQuotient (probe_ObjSetoid_unann C) (@ZigZag C) (zigzag_Equivalence C).

Definition probe_pi0_proj_unann (C : Category) :
  probe_ObjSetoid_unann C ~{Sets}~> probe_pi0_unann C :=
  sets_quot_proj (probe_ObjSetoid_unann C) (@ZigZag C)
    (zigzag_Equivalence C) (probe_coarser_unann C).

Section FormabilityHom.
Universes uo uhc uhd.
Constraint uhc < uhd.
Context (Cu : Category@{uo uhc uhc}) (Du : Category@{uo uhd uhd}).
Context (Fu : Cu ⟶ Du) (a b : Cu) (s : ZigZag a b).

(*
CONTROLS: the two categories, the functor and the chain are all
   formable with the hom universes declared STRICTLY apart, so the
   negative below cannot be firing merely on the section's levels.

--------
控制：这两个类别、函子和链都可以用严格分开的同类宇宙来构造，所以下面的负面情况不能仅仅在截面的层次上触发。
*)
Check Cu.
Check Du.
Check Fu.
Check s.

(* CONTROL 5: the SHIPPED, annotated [zigzag_fmap] applies across them. / 控制 5：已运输的、带注释的 [zigzag_fmap] 适用于它们。 *)
Check (zigzag_fmap Fu s).

(*
NEGATIVE 5.  Stripped, this reports:
     The term "Fu" has type "@Functor@{uo uhc uhc uo uhd uhd} Cu Du"
     while it is expected to have type "@Functor@{...} ?C ?D"
     (universe inconsistency: Cannot enforce uhd = uhc because uhc < uhd).
   The expected type shows the two hom universes IDENTIFIED — which is the
   minimization the target's binders undo.

--------
否定 5。精简后，这报告如下：
     术语“Fu”的类型为“@Functor@{uo uhc uhc uo uhd uhd} Cu Du”，
     而预期类型为“@Functor@{...} ?C ?D”
     （宇宙不一致：无法强制 uhd = uhc，因为 uhc < uhd）。
   预期类型显示两个同构宇宙已被识别——这是目标绑定器撤消的最小化。
*)
Fail Check (probe_zigzag_fmap_unann Fu s).

End FormabilityHom.

Section FormabilityObj.
Universes vo vh.
Constraint vh < vo.
Context (Cv : Category@{vo vh vh}).

(* CONTROLS at a category whose homs sit STRICTLY BELOW its objects. / CONTROLS at a category whose homs sit STRICTLY BELOW its objects. / 控制在其上的霍姆严格位于其对象之下的范畴。 *)
Check Cv.
Check (obj[Cv]).

(*
CONTROL 4: the SHIPPED, annotated [pi0_proj] IS formable here.  This is
   the discriminating half: same body, only the binders differ.

--------
控制 4：已发货、带注释的 [pi0_proj] 可以在这里形成。这是区分性的部分：主体相同，只有绑定器不同。
*)
Check (pi0_proj Cv).

(*
NEGATIVE 4.  Stripped, this reports:
     The term "Cv" has type "Category@{vo vh vh}"
     while it is expected to have type "Category@{...}"
     (universe inconsistency: Cannot enforce vh = vo because vh < vo).
   The three elided levels are one and the same freshly generated level, so
   the expected type shows ALL THREE of C's universes identified.  (Elided
   here as in negative 5: the generated names vary per compilation and are
   not quotable.)

--------
负面 4。剥离后，这报告：
     术语“Cv”的类型是“Category@{vo vh vh}”，
     而它预期的类型是“Category@{...}”
     （宇宙不一致：无法强制 vh = vo，因为 vh < vo）。
   三个省略的层级实际上是同一个新生成的层级，因此
   预期类型显示了 C 的三个宇宙都已被识别。（这里省略，与负面 5 类似：生成的名称在每次编译中会有所不同，无法引用。）
*)
Fail Check (probe_pi0_proj_unann Cv).

End FormabilityObj.

(*
CONTROLS naming the public constants the formability negatives are
   about, outside any [Fail].

--------
控制命名公共常量时，可成形性负面作用存在于任何 [Fail] 之外。
*)
Check @pi0_proj.
Check @pi0_proj_at.
Check @ObjSetoid.
Check @pi0_coarser.
Check @zigzag_Equivalence.
Check @sets_quot_proj.
Check @SetsQuotient.
Check @SetoidCoarser.

(**
** Controls for the headline results the target claims

   These are not boundaries; they are here so that a rename or a change of
   statement in the target breaks THIS file too.

--------
** 控制目标声称的主要结果

这些不是边界；它们存在的目的是为了在目标重命名或更改声明时，这个文件也会被破坏。
*)
Check @Connected.
Check @ConnectedNonempty.
Check @Zero_Connected.
Check @Zero_not_ConnectedNonempty.
Check @connected_readings_differ.
Check @connected_iff_pi0_subsingleton.
Check @ConnectedComponent.
Check @Component_Incl.
Check @Component_Connected.
Check @Component_reindex_equiv.
Check @eso_connected.
Check @equivalence_connected.
Check @image_connected_not_connected.
Check @DiscreteCat_bool_not_connected.
Check @Parallel_Connected.
Check @Pi0.

(*
Controls for the connected-diagram section (Riehl §3.4).  These guard
   the derived notion the same way: a rename in the target breaks here.

--------
连接图部分的控件（Riehl §3.4）。它们以相同的方式保护派生概念：目标中的重命名会在这里出错。
*)
Check @ConnectedDiagram.
Check @ConnectedNonemptyDiagram.
Check @connected_diagram_of_nonempty.
Check @connected_diagram_reindex.
Check @connected_diagram_pi0.
Check @pi0_connected_diagram.
Check @Parallel_ConnectedDiagram.
Check @bool_diagram_not_connected.
