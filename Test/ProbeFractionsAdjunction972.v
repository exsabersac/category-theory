Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Construction.Fractions.Weak.
Require Import Category.Construction.Fractions.Adjunction.
Require Import Category.Construction.Groupoid.Core.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(**
* Probe for Construction/Fractions/Weak.v and
      Construction/Fractions/Adjunction.v

    Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
    printed p. 137.  Issue #972.

    The import list above is the UNION of the two target files' own import
    lists, unabbreviated.  A short prefix is what makes a probe pass
    vacuously, so nothing is trimmed even where a require is redundant.

    This file guards the strength claims of those two files.  Every
    statement asserted to be refuted below has been STRIPPED of its refutation keyword
    in a copy of this WHOLE file, compiled alone, and its complete error
    read; a refutation that holds prints nothing under this repo's coqc, so a
    whole-file rc=0 would establish only THAT each command does not
    typecheck and never WHY.  Each negative is classified by the error
    TEXT:

      TYPING      - "The term T has type X while it is expected to have
                    type Y", with NO trailing "cannot unify" clause and no
                    universe clause.
      CONVERSION  - the same, with a trailing "(cannot unify A and B)".

    ** TALLY

    Seven positive controls and eleven negatives: NINE typing (N1-N7, N10,
    N11) and TWO conversion (N8, N9).  No negative here is a universe
    inconsistency, and that was checked rather than assumed -- see the note
    on N1 and N2 below.

    ** THE PRINTED FORM OF N1 AND N2 HIDES WHAT SEPARATES THEM

    N1 and N2 are the two cross-transfers between the strict universal
    property ([Construction/Fractions.v]'s [Fractions_UMP_groupoid]) and the
    weak one ([Construction/Fractions/Weak.v]'s [Fractions_UMP_weak]).  Both
    are [Unique] records, and the `∃!` notation hides the [Setoid] instance,
    so with default printing the two types in each message print
    identically and Coq falls back to disambiguating them by UNIVERSE
    INSTANCE.  That display invites the reading that these two negatives
    measure a universe clash rather than a strength difference, and they do
    not: re-run under [Set Printing All] each message reads

      "@Unique (@Functor (Fractions C) D) (@Functor_Setoid (Fractions C) D) …"
      versus
      "@Unique (@Functor (Fractions C) D)
         (@Functor_StrictEq_Setoid (Fractions C) D) …"

    with the two setoid arguments differing and no universe clause
    anywhere.  Both are therefore TYPING, and the thing they separate is
    the hom-setoid.

    ** WHAT THE NEGATIVES PIN

    N1  the weak universal property is NOT the strict one -- it cannot be
        read at [Functor_StrictEq_Setoid].  This is the whole point of the
        weak file: the statement it proves is genuinely weaker, and nothing
        in the tree should be able to launder it back.
    N2  the strict universal property is NOT the weak one either.  Its
        EXISTENCE half transfers along [strict_equiv_implies_fun_equiv],
        but the packaged [Unique] record does not, because its uniqueness
        clause quantifies over the wrong setoid.  This is the measured
        obstruction issue #972 was left open on.
    N3  [Fractions_proj_epic_weak]'s conclusion is at [Functor_Setoid] and
        cannot be read as [Construction/Fractions.v]'s [Fractions_proj_epic].
    N4  the original refusal, reproduced: feeding [Fractions_UMP_groupoid]
        straight to [universal_arrow_from_UMP].  The head of this message is
        quoted in [Construction/Fractions.v]'s header (there with the older
        spelling [frac_obj C] for what is now [frac_grpd C]).
    N5  [Incl_Core_Adjunction] is [Grpd_Incl ⊣ Core] and not its converse.
    N6  [Fractions_Incl_Adjunction] is [FractionsF ⊣ Grpd_Incl] and not its
        converse.
    N7  the triple does not survive exchanging its two ends: the left
        adjoint of the inclusion is the localization and the right adjoint
        is the core, not the other way round.
    N8  [FractionsF]'s action on MORPHISMS agrees with the hand-written
        [FractionsMap] only up to `≈`.  Unlike the object agreement (P3),
        this one is not [eq_refl], and the header of the adjunction file
        says so.
    N9  the unit of [Fractions_Incl_Adjunction] is [FractionsProj] only up
        to `≈` (P7 is the positive form).  In this message Coq prints the
        adjunction's [unit] projection bare, as "unit", which reads like
        the type of the same name; the environment line above it
        disambiguates.
    N10 the strict uniqueness lemma [FractionsLift_unique] does NOT accept a
        [Functor_Setoid] hypothesis.  This is the guard against the one
        shortcut the issue forbids -- restating the strict result under a
        weaker-sounding name by strengthening its hypothesis back to object
        equality.
    N11 [strict_equiv_implies_fun_equiv] runs strict-to-weak only; the
        reverse reading of it is refused.  This is why uniqueness had to be
        reproved rather than transported.

--------
* 探测 Construction/Fractions/Weak.v 和 Construction/Fractions/Adjunction.v

Riehl，《语境中的范畴论》，第2版，第§4.1节，例4.1.15，第137页印刷版。问题 #972。

上面的导入列表是两个目标文件各自导入列表的联合，未缩写。一个简短的前缀会使探测自动通过，所以即使某个 require 是多余的，也不会进行任何裁剪。

此文件保护那两个文件的强度声明。下面每个声称被驳斥的语句都已在此整个文件的副本中被去掉了其驳斥关键字，单独编译，并读取其完整错误；在本仓库的 coqc 下，成立的驳斥不会打印任何内容，因此整个文件的 rc=0 只能证明每个命令无法通过类型检查，而永远无法说明原因。每个否定项按错误文本分类：

输入      - “术语 T 的类型是 X，而预期类型是 Y”，没有尾随的“无法统一”子句，也没有宇宙子句。
转换  - 同样，不过有尾随的“（无法统一 A 和 B）”。

** 计数

七个阳性对照和十一个阴性对照：九个分型（N1-N7、N10、N11）和两个转换（N8、N9）。这里没有阴性是宇宙不一致的，这是经过检查而非假定的——参见下文关于N1和N2的说明。

** N1 和 N2 的印刷形式掩盖了分隔它们的东西

N1 和 N2 是严格泛性质（[Construction/Fractions.v] 的 [Fractions_UMP_groupoid]）与弱泛性质（[Construction/Fractions/Weak.v] 的 [Fractions_UMP_weak]）之间的两个交叉转换。两者都是 [Unique] 记录，而 `∃!` 符号隐藏了 [Setoid] 实例，因此在默认打印下，每条消息中的两个类型打印结果相同，Coq 退而通过 UNIVERSE INSTANCE 来进行歧义消解。这种显示容易让人误以为这两个负项衡量的是宇宙冲突而非强度差异，实际上并非如此：在 [Set Printing All] 下重新运行，每条消息都是按

"@Unique (@Functor (Fractions C) D) (@Functor_Setoid (Fractions C) D) …"  
      与  
      "@Unique (@Functor (Fractions C) D)  
         (@Functor_StrictEq_Setoid (Fractions C) D) …"

两个集合论参数不同，并且没有任何宇宙条款。因此两者都是类型化的，它们所区分的东西是同态集合论。

** 负极针是什么

N1 弱的全称性质不是严格的全称性质——它不能在 [Functor_StrictEq_Setoid] 上被读取。这就是弱文件的全部意义：它所证明的陈述确实更弱，并且树中的任何内容都不应能将其转换回去。 N2 严格的全称性质也不是弱的全称性质。它的存在性部分可以沿着 [strict_equiv_implies_fun_equiv] 转移，但封装的 [Unique] 记录不能，因为它的唯一性条款量化的是错误的等价类集。这就是问题 #972 留下的测量阻碍问题。 N3 [Fractions_proj_epic_weak] 的结论在 [Functor_Setoid] 上，不能被读取为 [Construction/Fractions.v] 的 [Fractions_proj_epic]。 N4 原始拒绝，重现：直接将 [Fractions_UMP_groupoid] 输入到 [universal_arrow_from_UMP]。
该消息的开头在 [Construction/Fractions.v] 的头部中引用（其中使用较旧的拼写 [frac_obj C]，现为 [frac_grpd C]）。N5  [Incl_Core_Adjunction] 是 [Grpd_Incl ⊣ Core]，而不是相反。N6  [Fractions_Incl_Adjunction] 是 [FractionsF ⊣ Grpd_Incl]，而不是相反。N7  三元组在交换两端时不保持不变：包含的左伴随是局部化，右伴随是核心，而不是相反。N8  [FractionsF] 对 MORPHISMS 的作用仅与手写的 [FractionsMap] 在 `≈` 下相符。与对象的一致性（P3）不同，这个并不是 [eq_refl]，并且伴随文件的头部也说明了这一点。N9  [Fractions_Incl_Adjunction] 的单位仅在 `≈` 下是 [FractionsProj]（P7 是正形式）。
在此消息中，Coq 以“unit”的形式打印了伴随的 [unit] 投影的原始形式，看起来就像同名类型；它上面的环境行进行了消歧。注意严格唯一性引理 [FractionsLift_unique] 不接受 [Functor_Setoid] 假设。这是对问题禁止的唯一捷径的防护——通过将假设加强回对象相等来以一个听起来较弱的名字重新陈述严格结果。注意 [strict_equiv_implies_fun_equiv] 仅进行严格到弱的转换；其逆向读取被拒绝。这就是为什么必须重新证明唯一性而不是进行迁移。
*)

(** ** Positive controls / ** 阳性对照 *)

(*
The objects of the localization ARE the objects of the source, and the
   projection is the identity on them -- the two conversions the weak
   uniqueness argument rests on.

--------
局部化的对象就是源对象，并且投影在它们上是恒等的——弱唯一性论证依赖的两个转换。
*)

Example P1 (C : Category) : @obj (Fractions C) = @obj C := eq_refl.

Example P2 (C : Category) (x : C) : fobj[FractionsProj C] x = x := eq_refl.

(*
The generated left adjoint's object map is the category of fractions on
   the nose.

--------
生成的左伴随的对象映射就是精确的分数范畴。
*)

Example P3 (C : Cat) : fobj[FractionsF] C = frac_grpd C := eq_refl.

(* The two adjunctions in the directions that ARE proved, and the triple. / The two adjunctions in the directions that ARE proved, and the triple. / 在已经被证明的方向上的两个伴随，以及三元组。 *)

Example P4 : Adjunction FractionsF Grpd_Incl := Fractions_Incl_Adjunction.

Example P5 : Adjunction Grpd_Incl Core := Incl_Core_Adjunction.

Example P6 : AdjointTriple FractionsF Grpd_Incl Core := riehl_4_1_15.

(*
The unit is the projection up to `≈`; N9 is the same statement at
   [eq_refl] and is refused.

--------
该单位是投影到 `≈`；N9 是在 [eq_refl] 上的相同声明，但被拒绝。
*)

Example P7 (C : Cat) :
  @equiv _ (@Functor_Setoid C (Fractions C))
    (@unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C)
    (FractionsProj C)
  := Fractions_unit_is_proj C.

(** ** Negatives, at an abstract source, target and functor / ** 否定，在抽象的源、目标和函子上 *)

Section Negatives.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

(*
Both universal properties exist at their own strength; only the transfers
   are refused.

--------
两种普遍属性各自以自己的强度存在；只有转移被拒绝。
*)

Example P8 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C))
  := Fractions_UMP_weak Dg F.

Example P9 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C))
  := Fractions_UMP_groupoid Dg F.

(* N1 *)
Fail Definition N1 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C)) :=
  Fractions_UMP_weak Dg F.

(* N2 *)
Fail Definition N2 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  Fractions_UMP_groupoid Dg F.

(* N3 *)
Fail Definition N3 (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D) L L' :=
  Fractions_proj_epic_weak L L' E.

(* N10 *)
Fail Definition N10 (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (FractionsLift F (fun x y f => Dg (F x) (F y) (fmap[F] f))) L :=
  FractionsLift_unique F (fun x y f => Dg (F x) (F y) (fmap[F] f)) L E.

(* N11 *)
Fail Definition N11 (G H : C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) G H) :
  @equiv _ (@Functor_StrictEq_Setoid C D) G H :=
  strict_equiv_implies_fun_equiv G H E.

End Negatives.

(** ** Negatives about the adjunction itself / ** 关于附加本身的负面因素 *)

(* N4 *)
Fail Definition N4 (C : Cat) : UniversalArrow C Grpd_Incl :=
  universal_arrow_from_UMP C Grpd_Incl (frac_grpd C) (FractionsProj C)
    (fun d' f => Fractions_UMP_groupoid (`2 d') f).

(* N5 *)
Fail Definition N5 : Adjunction Core Grpd_Incl := Incl_Core_Adjunction.

(* N6 *)
Fail Definition N6 : Adjunction Grpd_Incl FractionsF := Fractions_Incl_Adjunction.

(* N7 *)
Fail Definition N7 : AdjointTriple Core Grpd_Incl FractionsF :=
  {| triple_left  := Fractions_Incl_Adjunction;
     triple_right := Incl_Core_Adjunction |}.

(* N8 *)
Fail Example N8 (C D : Cat) (F : C ~{Cat}~> D) :
  `1 (fmap[FractionsF] F) = FractionsMap F := eq_refl.

(* N9 *)
Fail Example N9 (C : Cat) :
  @unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C
    = FractionsProj C := eq_refl.
