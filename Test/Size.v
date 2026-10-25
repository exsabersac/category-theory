(* ========================================================================= *)
(* Machine-checked demonstrations for the size vocabulary of Theory/Size.v. / Theory/Size.v 的尺寸词汇的机器检查演示。   *)
(*                                                                           *)
(* This file is where issue #253's NEGATIVE demonstrations live, because they / 这个文件是问题 #253 的负面示例所在，因为它们 *)
(* need the rejection vernacular, and each use of it is a hit for the / need the rejection vernacular, and each use of it is a hit for the / 需要拒绝的表达方式，每次使用它都是一次成功         *)
(* [make todo] hygiene sweep (Makefile greps case-insensitively over every / [make todo] 卫生清理（Makefile 对每个内容进行不区分大小写的搜索）  *)
(* .v file for a small set of trigger words, one of which is that vernacular's / .v 文件用于一小组触发词，其中之一是该方言的*)
(* own name).  Confining them here follows the in-tree precedent set by / own name).  Confining them here follows the in-tree precedent set by / 自己的名字）。将它们限制在这里遵循了树内先例        *)
(* Test/Issue138.v and Test/ProbeFunnyPoly.v,77, which use it the / Test/Issue138.v 和 Test/ProbeFunnyPoly.v,77，使用它的     *)
(* same way; Monad/Transformer.v does too.  This file contributes exactly / 同样的方式；Monad/Transformer.v 也如此。这个文件正好贡献了 *)
(* four such hits, and the pull request states that number rather than / four such hits, and the pull request states that number rather than / 四次这样的点击，并且拉取请求声明了那个数字，而不是         *)
(* hiding it.  Prose elsewhere in this file is deliberately worded to avoid / hiding it.  Prose elsewhere in this file is deliberately worded to avoid / 隐藏它。本文件其他地方的散文故意用词以避免    *)
(* the trigger words, so the sweep's delta is exactly the four commands. / 触发词，所以扫描的增量正好是四个命令。      *)
(*                                                                           *)
(* WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command / WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command / 方言显示与未显示的内容。它在命令成功时起作用  *)
(* it wraps raises ANY error.  It does not report WHICH error, so on its own / it wraps raises ANY error.  It does not report WHICH error, so on its own / 它会捕获任何错误。它不会报告具体哪个错误，所以单独使用时  *)
(* it cannot distinguish a universe inconsistency from an ordinary type / 它无法将宇宙不一致与普通类型区分开来        *)
(* mismatch or a typo.  Test/Issue138.v sets the precedent of saying so / 不匹配或拼写错误。Test/Issue138.v 设定了如此说的先例 *)
(* out loud, and the distinction is load-bearing here -- see BLOCK B. / 大声说，这里的区别是承重的——见 B 块。         *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(* ===== BLOCK A — the size predicates are inhabited, and strict ===== / ===== 块 A — 尺寸谓词是有定义的，并且是严格的 ===== *)

(* The vocabulary exists and can be used as a conclusion. / 词汇是存在的，并且可以用作结论。 *)
Check (One_Small : Small _1).
Check (small_locally_small _1 One_Small : LocallySmall _1).

(*
Every category is locally small at its OWN hom level.  This is the sense in
   which the library's discipline is stronger than the books' convention:
   [Class Category]'s [homset] field builds local smallness in, so the
   predicate is universally satisfiable at the ambient level.

--------
每个范畴在其自身的 Hom 层次上都是局部小的。这就是库的学科比书的惯例更强的意义所在：[Class Category] 的 [homset] 字段内建了局部小性，因此该谓词在整体层次上是普遍可满足的。
*)
Check (fun C : Category => locally_small_ambient C : LocallySmall C).

(*
THE CONTENT CHECK -- and note carefully which predicate it is about.

   [Small] is strict ([uo < o], [uh < h]) and that is where all of its content
   lies: were the constraints absent one could discharge it for EVERY category
   by handing back the category's own objects and homs.  The rejected commands
   below demonstrate that the discharge does not go through.

   [LocallySmall] is NOT strict -- it is declared [uh <= h] on purpose -- so no
   such claim holds for it, and the [locally_small_ambient] [Check] above is
   precisely the universal discharge in question.  The first rejected command
   below is therefore about [LocallySmall] AT A STRICT INSTANTIATION, not
   about the class as declared.

   Unlike BLOCK B, the rejections here are unambiguous: every term is
   well-typed apart from its universe constraints, so the only thing that can
   refuse it is the constraint solver.

--------
内容检查——并仔细注意它涉及的是哪个谓词。

[Small] 是严格的（[uo < o]，[uh < h]），这就是它所有内容所在：如果没有这些约束，就可以通过返回类别自身的对象和态射来对每个类别进行放 discharged。下面被拒绝的命令展示了这种放 discharged 并未通过。

[LocallySmall] 不是严格的——它被故意声明为 [uh <= h]——所以对它没有这样的主张，上面提到的 [locally_small_ambient] [Check] 正是所讨论的普适放 discharged。因此，下面第一个被拒绝的命令是关于 [LocallySmall] 在严格实例化时，而不是关于所声明的类。

与 BLOCK B 不同，这里的拒绝是明确的：每个项的类型都正确，除了它的宇宙约束，所以唯一可能拒绝它的是约束求解器。
*)
Fail Definition A253_trivial_locally_small@{o h p uh up
    | h <= p, uh <= up, uh < h}
  (C : Category@{o h p}) : LocallySmall@{o h p uh up} C :=
  @Build_LocallySmall@{o h p uh up} C
    (fun x y => (x ~> y)) (@homset C)
    (fun _ _ f => f) (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f) (fun x y u => reflexivity u).

Fail Definition A253_trivial_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) : Small@{o h p uo uh up} C :=
  @Build_Small@{o h p uo uh up} C
    (@Build_LocallySmall@{o h p uh up} C
       (fun x y => (x ~> y)) (@homset C)
       (fun _ _ f => f) (fun _ _ f => f)
       (fun _ _ _ _ H => H)
       (fun x y f => reflexivity f) (fun x y u => reflexivity u))
    obj[C] (fun x => x) (fun x => x)
    (fun _ => obj_refl _) (fun _ => obj_refl _).

(*
[A253_trivial_small] above is rejected inside its [Build_LocallySmall]
   sub-term -- the error is the same [Cannot enforce h <= uh because uh < h] as
   the previous command -- so elaboration never reaches [obj[C]] and that
   command alone is NO evidence about [uo < o].  This one isolates the object
   half, with no category and no hom in sight: a type cannot be resized to a
   strictly lower level.  Together the two cover both of [Small]'s strict
   constraints.

--------
上面的 [A253_trivial_small] 在其 [Build_LocallySmall] 子项中被拒绝 —— 错误与前一个命令的 [Cannot enforce h <= uh because uh < h] 相同 —— 因此展开从未到达 [obj[C]]，而单靠该命令不能说明 [uo < o]。这一个隔离了对象的一半，没有类别，也没有同类可见：类型不能被调整到严格更低的层次。两者加起来涵盖了 [Small] 的严格约束。
*)
Fail Definition A253_no_object_resize@{o uo | uo < o} (A : Type@{o})
  : Type@{uo} := A.

(* ===== BLOCK B — self-membership, and the distinction issue #253 conflates ==== / ===== B 块 — 自我成员资格，以及 #253 混淆的区分问题 ==== *)

(*
Mac Lane's remark 1 is that [Set] is not small, i.e. not an object of
   itself.  Issue #253 asks for rejected-[Check] witnesses that "[Sets] as an
   object of itself, [Cat] as an object of itself" are UNIVERSE
   INCONSISTENCIES.  Both halves of that need correction, and the first is the
   more surprising.

   (i) THE NAIVE CHECK DOES NOT DEMONSTRATE ANYTHING.  [Check (Cat : obj[Cat])]
   SUCCEEDS.  It is not a witness of self-membership at all, because [Cat] is
   universe-polymorphic: the elaborator instantiates the two occurrences at
   DIFFERENT levels, so what is actually checked is [Cat@{i..} : obj[Cat@{j..}]]
   with the second strictly above the first.  That is the Cat/Cat' tower, and
   it is a THEOREM of the design rather than a defect -- it is exactly what
   BLOCK B's positive checks below record.  Wrapping [Check (Cat : obj[Cat])]
   in the rejection vernacular would therefore not compile, because the
   command it wraps succeeds.

   The demonstration has to PIN ONE INSTANCE on both sides.  Written that way
   the self-membership really is rejected, and rejected on universes alone:
   the ascription is type-correct in shape, since [obj[Cat]] is [Category] and
   [Cat] is a [Category], so nothing but the constraint solver can refuse it.
   This is the genuine formal counterpart of Mac Lane's remark, and the reason
   Instance/Cat.v can say self-membership is "a universe inconsistency
   caught by the elaborator rather than a paradox to be excluded by axiom".

--------
Mac Lane 的评论 1 是 [Set] 并不小，也就是说，它本身不是一个对象。问题 #253 请求被拒绝的 [Check] 证据，说明“[Sets] 作为它自身的对象，[Cat] 作为它自身的对象”是宇宙不一致的。这两部分都需要修正，第一部分更令人吃惊。

(i) 这个天真的检查并没有证明任何东西。 [Check (Cat : obj[Cat])] 成功了。 它根本不是自我成员性的证据，因为 [Cat] 是宇宙多态的：详细设计器在不同层次上实例化了两个出现，因此实际检查的是 [Cat@{i..} : obj[Cat@{j..}])]，第二个严格高于第一个。 那就是 Cat/Cat' 的层级，这在设计上是一个定理而不是缺陷——这正是下面 BLOCK B 的正面检查记录下来的内容。 因此，把 [Check (Cat : obj[Cat])] 包裹在拒绝术语中将无法编译，因为它所包裹的命令是成功的。

演示必须在两边对一个实例进行固定。这样写的话，自我成员关系确实会被拒绝，并且只在宇宙上被拒绝：归属在形式上是类型正确的，因为 [obj[Cat]] 是 [Category]，而且 [Cat] 是一个 [Category]，所以除了约束求解器之外，没有其他东西可以拒绝它。这是真正对应于 Mac Lane 评论的形式版本，也是 Instance/Cat.v 可以说自我成员关系是“由 elaborator 捕捉到的宇宙不一致，而不是必须通过公理排除的悖论”的原因。
*)
Fail Definition B253_cat_self@{a b c d e}
  : obj[Cat@{a b c d e}] := Cat@{a b c d e}.

(*
(ii) FOR [Sets] IT IS NOT A UNIVERSE INCONSISTENCY AT ALL.  [obj[Sets]] is
   [SetoidObject] -- a carrier type paired with a setoid -- whereas [Sets] is a
   [Category].  A category is not a setoid, so this is an ORDINARY TYPE ERROR
   and would remain one at any universe levels whatsoever.  Pinning instances
   changes nothing.  The rejected command is kept only with that correction
   attached, since on its own it would be read as saying what the issue says.

--------
(ii) 对于 [Sets] 来说，这根本不是宇宙不一致。[obj[Sets] 是 [SetoidObject] —— 一种与集合等价类配对的载体类型 —— 而 [Sets] 是 [Category]。一个范畴不是集合等价类，所以这是一个普通类型错误，无论在哪个宇宙层次上都会保持不变。固定实例不会改变任何事情。被拒绝的命令仅在附加了该更正的情况下保留，因为单独看，它会被理解为问题所说明的内容。
*)
Fail Check (Sets : obj[Sets]).

(*
The positive half, which is what actually carries the stratification: a
   category at one level is an object of [Cat] built at the next.  Every one of
   these is accepted -- and per (i) they are the very ascriptions that make the
   naive self-membership check succeed.

--------
正半部分，实际上承载分层的部分：一个层级的类别是下一个层级构建的 [Cat] 对象。这些中的每一个都被接受——根据 (i)，它们正是使得天真的自我成员检查成功的归属。
*)
Check (_1 : obj[Cat]).
Check (Sets : obj[Cat]).
Check (Cat : obj[Cat]).

(*
[Cat] is itself a category, hence an object of a [Cat] one level up.  Coq's
   universe polymorphism supplies the whole tower silently; there is no [Cat']
   to define, which is the divergence from Mac Lane's single fixed [U].

--------
[Cat] 本身是一个类别，因此是上一级 [Cat] 的一个对象。Coq 的宇宙多态性默默地提供了整个塔；没有 [Cat'] 需要定义，这与 Mac Lane 的单一固定 [U] 不同。
*)
Check (Cat : Category).

(* ===== BLOCK C — Riehl's arrows-with-dom-and-cod packaging ===== / ===== C区 — Riehl 的有顶盖和尾盖箭头包装 ===== *)

(* The unindexed packaging exists for every category... / 每个类别都有未编入索引的包装... *)
Check (fun C : Category => ArrowQuiverOfCat C : ArrowQuiver).

(*
...and both of Riehl's retraction laws hold definitionally, by [obj_refl].
   In her unindexed presentation they are equations a candidate must satisfy;
   here the identity arrow stores its endpoints, so they are computations.

--------
...并且根据 [obj_refl]，Riehl 的两个收缩定律在定义上都成立。
   在她未编入索引的演示中，它们是候选者必须满足的方程；
   在这里，恒等箭头存储它的端点，因此它们是计算。
*)
Example C253_dom_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.

Example C253_cod_retract (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x :=
  obj_refl _.
