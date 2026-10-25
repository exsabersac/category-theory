Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(** * Probe for Instance/Sets/Classifier/OneLevel.v (issue #402) / * 探查实例/集合/分类器/单级.v（问题 #402） *)

(*
Every boundary that file's header reports is pinned here, from OUTSIDE
   the target: an in-file refutation command renames in lockstep with the
   constant it guards and so cannot detect a rename.  The Require list
   above mirrors the target's, plus
   Structure/SubobjectClassifier/Natural.v (for the two constants that are
   not statable at [Sets]) and the target itself.

   TEN refutation commands = 1 instrument check + 9 negatives of THREE
   kinds — 6 FORMABILITY, 1 TYPING, 2 CONVERSION — told apart by the
   error TEXT:

     FORMABILITY  the error carries a universe clause ("universe
                  inconsistency", "Cannot enforce ...");
     TYPING       a plain has-type mismatch, or "Illegal application",
                  with no universe clause and no "cannot unify";
     CONVERSION   "cannot unify" between two terms of ONE type.

   Each was stripped one at a time, compiled alone, and its whole error
   read.  Guard coverage was measured mechanically over the
   comment-stripped source: 49 identifiers occur inside a refutation
   command and 37 of them also occur outside one; the 12 that do not are
   exhaustively the keywords [Fail], [Example], [Type] and [eq_refl], the
   bound variables [h] and [p], the three universe binders local to the
   two [Fail Example]s, the two [Fail Example] names themselves (which
   never enter the environment), and the instrument's deliberately absent
   name.  Rename simulation: each of the eight TARGET constants a negative
   names was renamed in a scratch copy of the target that shadows the
   worktree module, and all 8/8 broke this file at a [Check] control line,
   never inside a refutation command.

--------
每一个该文件头报告的边界都固定在这里，从目标之外：文件内的反驳命令会与它所保护的常量同步重命名，因此无法检测重命名。上面的 Require 列表镜像了目标的列表，加上 Structure/SubobjectClassifier/Natural.v（用于两个在 [Sets] 中无法声明的常量）以及目标本身。

十个反驳命令 = 1 个工具检查 + 三种类型的 9 个否定 — 6 个形式性，1 个打字，2 个转换 — 通过错误文本区分：

可塑性 该错误包含一个全域条款（“全域不一致”，“无法执行 ...”）；
类型 检查 一个普通的类型不匹配，或“非法应用”，没有全域条款且没有“无法统一”；
转换 “无法统一” 出现在两个同一类型的项之间。

每个文件被一次性剥离出来，单独编译，并读取其整个错误信息。守卫覆盖情况通过去除注释的源代码进行机械测量：49 个标识符出现在反驳命令中，其中 37 个也出现在命令外；剩余的 12 个则完全是关键字 [Fail]、[Example]、[Type] 和 [eq_refl]，绑定变量 [h] 和 [p]，两个 [Fail Example] 的三个局部宇宙绑定器，两个 [Fail Example] 名称本身（它们从未进入环境），以及工具故意缺失的名称。重命名模拟：八个负名 TARGET 常量中的每一个都在目标的一个临时副本中重命名，该副本覆盖工作区模块，全部 8/8 在 [Check] 控制行中破坏了该文件，从未出现在反驳命令内。
*)

(* ------------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

(*
A refutation command that succeeds prints nothing, so the instrument
   must be exercised: this name exists nowhere.

--------
一个成功的反驳命令不会打印任何内容，因此必须使用该工具：这个名字在任何地方都不存在。
*)
Fail Check probe402_no_such_constant.

(* ------------------------------------------------------------------------ *)
(** ** Controls, outside every refutation command / ** 控制，位于每个反驳命令之外 *)

Check @classifier_classifies.
Check @char_reindex.
Check @Sub_classifier_natural.
Check @Sub_Representable.
Check @SubObj.
Check @SubobjectClassifier.
Check @Sets_Terminal.
Check @Sets_HasPullbacks.
Check @HasPullbacks.
Check @PropSetoid.
Check @Powerset_Omega.
Check @Powerset_squash.
Check @powerset_squash_prop_inert.
Check @BoolSetoid.
Check @SetoidObject.
Check @Sets.
Check @char_setoid.
Check @SetoidMorphism_Lift.
Check @Sets_Classifier.
Check @Sets_Classifier_dec.
Check @Sets_Classifier_IEM.
Check @sets_squash_mor.
Check @bridge_record_equiv.
Check @bridge_pointwise.
Check @classifier_of_small.
Check @small_of_IEM.
Check @DecImage_of_IEM.
Check @iem_routes_omega.
Check @iem_routes_char.
Check @iem_routes_truth.
Check @Untruncate.
Check @IEM.
Check @DecImage.
Check @char.
Check @Ω.
Check @truth.
Check @Monic.

(* ------------------------------------------------------------------------ *)
(** ** FORMABILITY: what is not statable at [Sets] / ** 可成形性：在 [Sets] 上无法说明的内容 *)

Section NotAtSets.
Universes o so.
Constraint o < so.
Context (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}).

(*
CONTROL: [char_reindex] IS accepted at this very [Sets], for this very
   classifier.  So the two refusals below are about their own statements,
   not about the classifier or the category.

--------
控制：[char_reindex] 在此时此刻被接受，用于这个特定的分类器。因此，下面的两个拒绝是关于他们自己的陈述，而不是关于分类器或类别的。
*)
Check (fun (x y : SetoidObject@{o o}) (f : y ~{Sets@{o so}}~> x)
           (s : @SubObj Sets@{o so} x) =>
  @char_reindex Sets@{o so} Sets_Terminal@{so o} Sets_HasPullbacks@{so o}
    HS x y f s).

(*
NEGATIVE 1 (FORMABILITY).  The classification theorem builds a
   [SetoidObject] whose carrier is [SubObj x], which forces objects ≤
   homs; [Sets@{o so} : Category@{so o o}] has o < so.  Stripped:
     universe inconsistency: Cannot enforce so = _ because _ <= _ < so

--------
负面 1（可形成性）。分类定理构建了一个载体为 [SubObj x] 的 [SetoidObject]，这迫使对象 ≤ 同态；[Sets@{o so} : Category@{so o o}] 有 o < so。简化后：
宇宙不一致：无法强制 so = _ 因为 _ <= _ < so
*)
Fail Check (@classifier_classifies Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

(*
NEGATIVE 2 (FORMABILITY).  Awodey's naturality clause, same wall, same
   error shape.

--------
负面 2（可成形性）。Awodey 的自然性条款，相同的墙，相同的错误形状。
*)
Fail Check (@Sub_classifier_natural Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

(*
NEGATIVE 3 (FORMABILITY).  [Sub_Representable] is built on that
   isomorphism, so it inherits the refusal.

--------
负面 3（可形成性）。[Sub_Representable] 建立在该同构之上，因此它继承了这种拒绝。
*)
Fail Check (@Sub_Representable Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

End NotAtSets.

Section CarrierWall.
Universes o so.
Constraint o < so.

(* CONTROL: a hom-setoid IS an object of [Sets] at these very levels. / CONTROL: a hom-setoid IS an object of [Sets] at these very levels. / 控制：一个同态等价集合是 [Sets] 在这些层次上的一个对象。 *)
Check (fun (a b : SetoidObject@{o o}) =>
  ({| carrier := a ~{Sets@{o so}}~> b |} : obj[Sets@{o so}])).

(*
NEGATIVE 4 (FORMABILITY).  [SubObj x] is a [Type@{so}], so no setoid on
   it is an object of [Sets@{o so}].  Stripped:
     universe inconsistency: Cannot enforce _ = o because o < so <= _

--------
负 4（可构造性）。[SubObj x] 是一个 [Type@{so}]，因此其上没有集合等价是 [Sets@{o so}] 的对象。简化后：
  宇宙不一致：无法强制 _ = o 因为 o < so <= _
*)
Fail Check (fun (x : SetoidObject@{o o}) =>
  ({| carrier := @SubObj Sets@{o so} x |} : obj[Sets@{o so}])).

(*
CONTROLS: the two truth objects this file actually uses ARE objects of
   [Sets] at one level.

--------
控制：这个文件实际使用的两个真值对象是 [Sets] 在某一个层级的对象。
*)
Check (Powerset_Omega@{o} : obj[Sets@{o so}]).
Check (BoolSetoid@{o} : obj[Sets@{o so}]).

(*
NEGATIVE 5 (FORMABILITY).  Instance/Sets/Classifier.v's truth-value
   setoid is not.  Stripped:
     universe inconsistency: Cannot enforce so = o because o < so

--------
负 5（可形成性）。Instance/Sets/Classifier.v 的真值集合不是等价集合。精简版：宇宙不一致：无法强制 so = o 因为 o < so
*)
Fail Check (PropSetoid@{o so} : obj[Sets@{o so}]).

End CarrierWall.

Section SquashWall.
Universes o.

(*
CONTROL: over a [Prop] the impredicative truncation is inert, so it CAN
   be eliminated -- which is what makes [Untruncate] the extra hypothesis
   and not a restatement of the goal.

--------
控制：在 [Prop] 上，不可确定的截断是惰性的，所以它可以被消除——这正是使 [Untruncate] 成为额外假设而不是目标重述的原因。
*)
Check (fun (P : Prop) => proj1 (powerset_squash_prop_inert@{o} P)).

(*
NEGATIVE 6 (FORMABILITY).  The naive elimination at a [Type@{o}]
   instantiates the impredicative quantifier outside [Prop].  Stripped:
     universe inconsistency: Cannot enforce o <= Prop
   This refusal is exactly what [Untruncate] buys.

--------
负 6（可构造性）。在 [Type@{o}] 处的天真消去将不可具体化量词实例化到了 [Prop] 之外。简化为：
  宇宙不一致：无法强制 o <= Prop
这种拒绝正是 [Untruncate] 所买到的。
*)
Fail Check (fun (P : Type@{o}) (h : Powerset_squash@{o} P) =>
              h P (fun p => p)).

End SquashWall.

(* ------------------------------------------------------------------------ *)
(** ** TYPING: the class takes two arguments, not three / ** TYPING：该类接受两个参数，而不是三个 *)

Section ClassArity.
Universes o so.
Constraint o < so.

(* CONTROL: the two-argument form, which is what the target inhabits. / 控制：双参数形式，即目标所在的形式。 *)
Check (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}).

(*
NEGATIVE 7 (TYPING).  [HasPullbacks] is a Context variable of the
   declaring section that the CLASS body never mentions, so it is
   discharged onto the theorems below the class and not onto the class.
   Stripped:
     Illegal application (Non-functional construction)
   -- no universe clause, no "cannot unify".

--------
负数 7（类型）。[HasPullbacks] 是声明部分的上下文变量，CLASS 本体从未提及，所以它被转移到类下方的定理上，而不是转移到类上。精简后：非法应用（非函数式构造）-- 没有宇宙子句，没有“无法统一”。
*)
Fail Check (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o}).

End ClassArity.

(* ------------------------------------------------------------------------ *)
(** ** CONVERSION: the two grades of the bridge, and the two IEM routes / ** 转换：桥梁的两个等级，以及两个IEM路线 *)

Section Grades.
Universes o so sso.
Constraint o < so.
Constraint so < sso.

(*
CONTROLS: the bridge holds at [eq_refl] on VALUES, and at ≈ as
   [SetoidMorphism] records one universe up.

--------
控制：桥在 VALUES 的 [eq_refl] 处保持，在 ≈ 处，[SetoidMorphism] 记录一个宇宙向上。
*)
Check (fun (U : Untruncate@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
           (b : carrier x) => @bridge_pointwise@{o so} U u x m M b).
Check (fun (U : Untruncate@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m) =>
         @bridge_record_equiv@{o so sso} U u x m M).

(*
NEGATIVE 8 (CONVERSION).  The same identification as whole
   [SetoidMorphism] records is refused: the two [proper_morphism]
   certificates are separately elaborated.  Stripped:
     cannot unify "SetoidMorphism_Lift (char m M)" and
                  "sets_squash_mor ∘ char_setoid m"
   -- two terms of ONE type.

--------
负 8（转换）。与整个 [SetoidMorphism] 记录相同的标识被拒绝：两个 [proper_morphism] 证书单独展开。剥离：无法统一“SetoidMorphism_Lift (char m M)”和“sets_squash_mor ∘ char_setoid m”——同一类型的两个项。
*)
Fail Example bridge_record@{o' so' sso'} (U : Untruncate@{o'})
  {u x : SetoidObject@{o' o'}} (m : u ~{Sets@{o' so'}}~> x)
  (M : @Monic Sets@{o' so'} u x m) :
  SetoidMorphism_Lift@{o' so'}
    (@char Sets@{o' so'} Sets_Terminal@{so' o'}
       (Sets_Classifier@{o' so'} U) u x m M)
    = sets_squash_mor@{o' so' sso'}
        ∘[Sets@{so' sso'}] char_setoid@{o' so'} m := eq_refl.

(*
CONTROLS: the two routes from [IEM] to a classifier agree on ALL THREE
   data fields -- Ω, char and truth -- at [eq_refl].

--------
控制：从 [IEM] 到分类器的两条路径在 [eq_refl] 上的所有三个数据字段——Ω、字符和真实性——都一致。
*)
Check (fun (E : IEM@{o}) => @iem_routes_omega@{o so} E).
Check (fun (E : IEM@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
           (b : carrier x) => @iem_routes_char@{o so} E u x m M b).
Check (fun (E : IEM@{o}) => @iem_routes_truth@{o so} E).

(*
NEGATIVE 9 (CONVERSION).  The whole RECORDS do not agree: what differs
   is exactly the two LAW fields, [char_pullback] and [char_unique], which
   the two routes elaborate separately.  Stripped:
     cannot unify "classifier_of_small (small_of_IEM E)" and
                  "Sets_Classifier_dec (DecImage_of_IEM E)"

--------
负 9（转换）。整个记录不一致：不同的正是两个法律字段，[char_pullback] 和 [char_unique]，这两个路径分别展开。简化后：无法统一“classifier_of_small (small_of_IEM E)”和“Sets_Classifier_dec (DecImage_of_IEM E)”
*)
Fail Example iem_routes@{o' so'} (E : IEM@{o'}) :
  classifier_of_small@{o' so'} (small_of_IEM@{o'} E)
    = Sets_Classifier_dec@{o' so'} (DecImage_of_IEM@{o' so'} E) := eq_refl.

End Grades.
