Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Theory.Lindenbaum.

Generalizable All Variables.

(** * Probe for Instance/Theory/Lindenbaum.v (issue #390) / * 探测实例/理论/Lindenbaum.v（问题 #390） *)

(*
Mac Lane §IV.6, printed p. 98, Exercise 2 (maclane:IV.6:ex2).

   This file pins, from OUTSIDE the target, every boundary the target's
   header records.  An in-file negative renames in lockstep with the
   constant it guards and so cannot detect a rename; these can.

   Eight negatives in THREE kinds, told apart by the error TEXT rather
   than by label:

     FORMABILITY  ends in a universe clause "Cannot enforce ..."
       N1  [Lind]'s hom universe is identified with its proof universe
       N2  ...and that is [Proset]'s doing, with no [Lind] in the command
       N3  a Type-valued entailment is not a stdlib [relation]
     TYPING       plain "has type ... expected ...", no "cannot unify"
       N4  [Terminal] where [Cartesian] is wanted
       N5  a derivation at one theory is not one at another
     CONVERSION   ends in "cannot unify"
       N6  the two categories of section (G) are not convertible
       N7  the exponential's orientation: q ^ p is s_imp p q, not q p
       N8  [eval] is not the rule [ent_eval] on the nose, only up to ≈

   Plus one scope-free instrument check.  Each negative was stripped ONE
   AT A TIME, the file compiled alone, and the WHOLE error read.

   Every constant a negative names is also named outside every [Fail],
   in the control blocks below.

--------
Mac Lane §IV.6，第98页，练习2 (maclane:IV.6:ex2)。

该文件从目标之外固定目标头记录的每个边界。文件内的负重命名会与它所保护的常量同步，因此无法检测重命名；而这些可以。

三种类型的八个否定，通过错误文本而不是标签区分：

可形成性 以宇宙子句 '无法强制执行 ...' 结束
       N1  [Lind] 的同类宇宙被识别为其证明宇宙
       N2  ...这是 [Proset] 的操作，命令中没有 [Lind]
       N3  一个类型值的蕴含不是标准库中的 [relation]
     类型检查       单纯 '具有类型 ... 期望 ...'，没有 '无法统一'
       N4  [Terminal] 期望的是 [Cartesian]
       N5  一个理论上的推导在另一个理论上不成立
     转换   以 '无法统一' 结束
       N6  第 (G) 节的两类不可转换
       N7  指数的方向：q ^ p 是 s_imp p q，而不是 q p
       N8  [eval] 不是规则 [ent_eval] 的本身，只是等价于 ≈

再加一次无范围限制的仪器检查。每个阴性结果都是一次剥离，然后单独编译文件，并读取整个错误。

每个名为负数的常量也会在每个 [Fail] 之外命名，在下面的控制块中。
*)

(** ** Instrument check: this must be rejected for the trivial reason / ** 仪器检查：这必须因微不足道的原因被拒绝 *)

Fail Check probe390_no_such_constant_anywhere.

(** ** Controls: every constant the negatives name, outside any [Fail] / ** 控制：每个常数否定的名称，位于任何 [Fail] 之外 *)

Check @Sent.
Check @s_var.
Check @s_top.
Check @s_and.
Check @s_imp.
Check @Theo.
Check @Entails.
Check @ent_refl.
Check @ent_cut.
Check @ent_ax.
Check @ent_top.
Check @ent_pair.
Check @ent_fst.
Check @ent_snd.
Check @ent_curry.
Check @ent_eval.
Check @entails_PreOrder.
Check @Lind.
Check @lind_thin.
Check @lind_any_Faithful.
Check @Lind_Terminal.
Check @Lind_Cartesian.
Check @lind_uncurry.
Check @Lind_Closed.
Check @sdenote.
Check @ent_soundness.
Check @LindSound.
Check @LindSound_Faithful.
Check @entails_weaken.
Check @LindWeaken.
Check @sv.
Check @T_empty.
Check @T_mp.
Check @T_all.
Check @not_entails_empty.
Check @entails_mp.
Check @empty_sub_mp.
Check @empty_sub_all.
Check @weaken_not_Full.
Check @no_full_functor_empty_to_all.
Check @no_equivalence_empty_to_all.
Check @sound_not_Full.
Check @sound_misses_False.
Check @sound_not_EssentiallySurjective.

(* Donor constants named by the negatives. / 由负数命名的供体常数。 *)
Check @Proset.
Check @Category.
Check @terminal_obj.
Check @product_obj.
Check @exponent_obj.
Check @eval.
Check @Thin.
Check @Full.
Check @EssentiallySurjective.
Check @EquivalenceOfCategories.
Check @Props.
Check @Relation_Definitions.relation.
Check @RelationClasses.PreOrder.

(** ** N1, N2: the hom = proof identification, and its donor / ** N1，N2：同源 = 证明身份及其供体 *)

(*
[Lind@{u u0 u1} : Theo@{u0 u1} V -> Category@{u0 u u}] reuses one
   level for hom and for proof in the BINDER, while its constraint block
   carries no equation at all.  Both facts have to be read to get this
   right, and only the binder shows it.

   The two negatives below are rejected at levels declared strictly
   apart; the control on the line before each shows the very same
   application accepted at those levels once hom and proof coincide.

--------
[Lind@{u u0 u1} : Theo@{u0 u1} V -> Category@{u0 u u}] 在 BINDER 中对 hom 和 proof 重用了一个级别，而它的约束块根本没有方程。必须阅读这两个事实才能理解这一点，并且只有 binder 显示了这一点。

下面的两个否定在严格分开的声明级别上被拒绝；每行之前的控制显示在那些级别上一旦 hom 和 proof 重合时，同样的应用就会被接受。
*)

Section UniverseProbe.

Universe lo lh lp.
Constraint lh < lp.

Context (Vu : Type@{lo}) (Tu : Theo@{lo lp} Vu).

(* Controls: the category, its objects and a hom all elaborate here. / Controls: the category, its objects and a hom all elaborate here. / 控件：类别、其对象以及一个同类在此处详细说明。 *)
Check (Lind Tu : Category@{lo lh lh}).
Check (obj[Lind Tu]).
Check (fun p q : Sent@{lo} Vu => p ~{Lind Tu}~> q).

(* N1 (FORMABILITY): "Cannot enforce lh = lp because lh < lp". / N1（可成型性）："无法强制 lh = lp，因为 lh < lp" *)
Fail Check (Lind Tu : Category@{lo lh lp}).

Context (Au : Type@{lo}) (Ru : Relation_Definitions.relation Au)
        (Pu : RelationClasses.PreOrder Ru).

(* Control for N2, at the same declared levels. / 在相同的声明水平下控制 N2。 *)
Check (Proset Pu : Category@{lo lh lh}).

(*
N2 (FORMABILITY): the donor alone, with no [Lind] in the command,
   is rejected with the identical clause — so the identification is
   inherited from [Proset] and the target introduces none of its own.

--------
N2（可成形性）：仅使用捐赠者，在命令中没有 [Lind]，会被相同的条款拒绝——因此识别是从 [Proset] 继承的，目标不会引入其自身的任何条款。
*)
Fail Check (Proset Pu : Category@{lo lh lp}).

End UniverseProbe.

(** ** N3: entailment must be Prop-valued for [Proset] to accept it / ** N3：为了让 [Proset] 接受，推理结果必须是命题值 *)

(*
The target's design note says a Type-valued entailment would not fit
   [Proset], whose relation argument is a stdlib [relation A].  Here is
   a Type-valued one, and the rejection.

--------
目标的设计说明指出，一个类型值的蕴涵不适合 [Proset]，其关系参数是一个 stdlib [relation A]。这里是一个类型值的例子，以及被拒绝的理由。
*)

Inductive TEnt {V : Type} (T : Theo V) : Sent V -> Sent V -> Type :=
  | tent_refl p : TEnt p p
  | tent_cut p q r : TEnt p q -> TEnt q r -> TEnt p r.

(*
Controls: the Prop-valued one IS a stdlib relation, and the
   Type-valued one does elaborate as a family.

--------
控件：取 Prop 值的那个是一个标准库关系，而取 Type 值的那个则详尽地作为一个族展开。
*)
Check (Entails T_empty : Relation_Definitions.relation (Sent bool)).
Check (TEnt T_empty).

(*
N3 (FORMABILITY): "Cannot enforce <level> <= Prop".  Note the kind:
   the message opens like a typing mismatch but closes with a universe
   clause, so it is counted with the formability negatives and not with
   N4/N5, whose messages carry no universe clause at all.

--------
N3（可构造性）：“无法强制 <level> <= Prop”。注意类型：消息开头像是类型不匹配，但结尾带有宇宙子句，因此它被归入可构造性负面，而不是 N4/N5，后者的消息完全不带宇宙子句。
*)
Fail Definition probe390_tent_relation :
  Relation_Definitions.relation (Sent bool) := TEnt T_empty.

(** ** N4, N5: two typing rejections / ** N4，N5：两次打字拒绝 *)

Section TypingProbe.

Context {V : Type} (T : Theo V) (p q r : Sent V).

(* Control: the product object with the right structure supplied. / 控制：提供了具有正确结构的产品对象。 *)
Check (@product_obj (Lind T) (Lind_Cartesian T) p q).

(*
N4 (TYPING): "The term Lind_Terminal T has type Terminal while it is
   expected to have type Cartesian" — a plain mismatch, no
   "cannot unify" and no universe clause.  The three structures are
   three distinct classes on one category.

--------
N4（打字）："术语 Lind_Terminal T 的类型是 Terminal，而期望类型是 Cartesian" — 一个普通的不匹配，没有 "无法统一" 和没有宇宙子句。这三个结构是在同一类别上的三个不同类。
*)
Fail Check (@product_obj (Lind T) (Lind_Terminal T) p q).

End TypingProbe.

(* Control: the derivation exists at its own theory. / 控制：该推导存在于它自己的理论中。 *)
Check (entails_mp : Entails T_mp (sv true) (sv false)).

(*
N5 (TYPING): a derivation at [T_mp] is not one at [T_empty].  The
   theory is an INDEX of the hom-type, so this is a type mismatch and
   not a unification report.

--------
N5（输入）：在 [T_mp] 处的派生不是在 [T_empty] 处的派生。该理论是同类的 INDEX，因此这是类型不匹配，而不是统一报告。
*)
Fail Check (entails_mp : Entails T_empty (sv true) (sv false)).

(** ** N6, N7, N8: three conversion rejections / ** N6, N7, N8：三次转换被拒 *)

(* Control: each category is convertible with itself. / 控制：每个类别都可以与自身转换。 *)
Definition probe390_lind_self : Lind T_empty = Lind T_empty := eq_refl.

(*
N6 (CONVERSION): different axiom sets, different categories — the
   two [Category] records do not convert.  (Section (G) of the target
   upgrades this from a conversion remark to the statement that no full
   functor, hence no equivalence, connects them.)

--------
N6（转换）：不同的公理集，不同的类别——这两个 [Category] 记录无法转换。（目标的第 (G) 节将其从转换备注升级为声明：没有完整函子，因此没有等价性将它们连接。）
*)
Fail Definition probe390_two_theories :
  Lind T_empty = Lind T_mp := eq_refl.

Section OrientationProbe.

Context {V : Type} (T : Theo V) (p q : Sent V).

(* Control: Mac Lane's q ^ p IS "p implies q". / 控制：Mac Lane 的 q ^ p 是 “p 蕴含 q” 。 *)
Definition probe390_exp_orientation :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(*
N7 (CONVERSION): and it is not "q implies p".  This guards the one
   place where the library's [exponent_obj x y = y ^ x] convention and
   the book's q^p could silently drift apart.

--------
N7（转换）：它不是“q 蕴含 p”。这可以防止库的 [exponent_obj x y = y ^ x] 约定和书中的 q^p 在某个地方悄悄地偏离。
*)
Fail Definition probe390_exp_flipped :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp q p := eq_refl.

(*
Control: [eval] IS [lind_uncurry] at the identity derivation, and it
   is ≈-equal to the evaluation RULE, since the category is thin.

--------
控制：[eval] 在身份推导中是 [lind_uncurry]，并且它与评估规则近似相等，因为范畴是稀疏的。
*)
Definition probe390_eval_unfold :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = lind_uncurry (ent_refl T (s_imp p q)) := eq_refl.

Definition probe390_eval_equiv :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    ≈ ent_eval T p q := lind_thin T _ _ _ _.

(*
N8 (CONVERSION): but it is not [ent_eval] on the nose.  This is what
   thinness buys and what it does not: the two derivations are
   identified by ≈ and by nothing stronger.

--------
N8（转换）：但它在本质上并不是 [ent_eval]。这就是纤薄的价值所在和它不具备的：两个导出项用 ≈ 来表示，并没有更强的标记。
*)
Fail Definition probe390_eval_strict :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = ent_eval T p q := eq_refl.

End OrientationProbe.

(** ** The [Defined] on [entails_weaken] is load-bearing downstream / ** [entails_weaken]上的[Defined]是承重下游 *)

(*
Within the target, flipping either [Defined] to [Qed] changes
   nothing.  This readback is what makes the one on [entails_weaken]
   matter: with [Qed] it is rejected with "cannot unify".

--------
在目标中，将 [Defined] 翻转为 [Qed] 不会改变任何东西。正是这种读回使得 [entails_weaken] 上的设置变得重要：使用 [Qed] 时，它会被拒绝，并显示“无法统一”。
*)
Example probe390_weaken_reduces (p : Sent bool) :
  entails_weaken empty_sub_mp (ent_refl T_empty p) = ent_refl T_mp p
  := eq_refl.

Example probe390_weaken_fmap (p q : Sent bool) (f : Entails T_empty p q) :
  fmap[LindWeaken empty_sub_mp] f = entails_weaken empty_sub_mp f
  := eq_refl.

(** ** The exercise's claims, exercised from outside / ** 该练习的主张，从外部施加 *)

(*
Product is conjunction, terminal is truth, exponential is
   implication — at Leibniz equality of objects.

--------
乘积是合取，终端是真，指数是蕴含——在莱布尼茨意义上是对象的等价。
*)
Example probe390_structure {V} (T : Theo V) (p q : Sent V) :
  (@terminal_obj (Lind T) (Lind_Terminal T) = s_top)
  * (@product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q)
  * (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
       = s_imp p q)
  := (eq_refl, eq_refl, eq_refl).

(* The category is thin, so the transpose is unique for free. / 该范畴是稀薄的，所以转置是免费的且唯一的。 *)
Example probe390_thin {V} (T : Theo V) : Thin (Lind T) := lind_thin T.

(*
Two axiom sets, two categories: derivable on one side, refuted on
   the other, and no full functor between them.

--------
两个公理集，两个类别：一边可推导，另一边被反驳，并且它们之间没有完整函子。
*)
Example probe390_derivable : Entails T_mp (sv true) (sv false) :=
  entails_mp.

Example probe390_underivable :
  Entails T_empty (sv true) (sv false) -> False := not_entails_empty.

Example probe390_not_full :
  Full (LindWeaken empty_sub_mp) -> False := weaken_not_Full.

Example probe390_no_equiv (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False := no_equivalence_empty_to_all F.

(*
The comparison with Props: a functor preserving 1, × and ^ on the
   nose, faithful, but neither full nor essentially surjective.

--------
与 Props 的比较：一个函子准确地保持 1、× 和 ^，是忠实的，但既不满也不是本质上充满的。
*)
Example probe390_sound_functor : Lind T_empty ⟶ Props :=
  LindSound T_empty val_true val_true_empty.

Example probe390_sound_faithful : Faithful (LindSound T_empty val_true
  val_true_empty) := LindSound_Faithful T_empty val_true val_true_empty.

Example probe390_sound_not_full :
  Full (LindSound T_empty val_true val_true_empty) -> False :=
  sound_not_Full.

Example probe390_sound_not_eso :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False := sound_not_EssentiallySurjective.
