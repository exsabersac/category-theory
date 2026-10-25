(**
* Probe for the reflection of limits and coequalizers (issue #481)

    Pins the measured boundaries of what #481 adds for Mac Lane, §VI.7,
    the Definition of reflecting colimits and Exercises 1 and 3 (book
    pp. 154-155, PDF pp. 163-164; catalog items maclane:VI.7:def2,
    maclane:VI.7:ex1, maclane:VI.7:ex3), and for Riehl, §3.4, Definition
    3.4.1 (ii), Lemma 3.4.5 and Exercise 3.4.iii (printed pp. 104, 105
    and 108; riehl:3.4:def1, riehl:3.4:lem5, riehl:3.4:exiii), read from
    the page images.  The targets are Structure/Limit/Reflection.v, whose
    header cites the refutations R1 and R2 and the controls here,
    Structure/Coequalizer.v's [parallel_cocone_coequalizer_colimit] and
    the three full and faithful names of Theory/Equivalence/Limit.v.

    THE IMPORT LIST: the first target's thirteen [Require] lines in its
    own order, and that target.  Under them [Print Libraries] in a
    scratch file loads 35 [Category] modules, exactly the set a [Require]
    of the target alone loads (compared by script).  Three later
    sections add, in turn and after every command above them, the import
    list of Theory/Equivalence/Limit.v and that module (the section on
    left adjoints after it adds none); the import list of
    Structure/Limit/Finite.v and that module; and the import lists of
    Instance/One.v, Instance/Sets.v, Instance/Sets/Quotient.v and
    Instance/Sets/Coequalizer.v and those modules.  So nothing above each
    is elaborated under its imports.  A shorter import list is what makes
    a probe pass for no reason.

    DISCIPLINE.  Every negative other than the instrument is a
    [Definition], never a [Check], so that an open evar cannot satisfy
    it.  Each of the three refutation lines (the instrument, R1 and R2)
    was stripped of its refutation keyword in a copy of this WHOLE file,
    one at a time, compiled, and its error read; each copy stops inside
    the stripped command.  Each of the thirty command heads below that
    is not a refutation and opens with [Definition], [Example] or
    [Theorem] (the twenty-eight controls other than C18, and the two
    definitions that C15 uses), wrapped in the refutation keyword in a
    copy of this WHOLE file, stops the build at that command with the
    message Rocq prints for a refutation whose command succeeds; so does
    C18, a [Class], wrapped by hand.  Quotations are Rocq 9.1.1's under
    this file's import list.

    KINDS.  Three refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE, the instrument (one); CONVERSION,
    R1, the colimit predicate against the limit predicate of the
    opposites, with every statement well typed; UNIVERSE, R2,
    [ReflectsIsos] over a target whose hom level is strictly above C's.

    THE REFUSALS, with the parenthetical each stripped copy prints.
      The instrument (NAME-ABSENCE): The reference p481_absent_name was
        not found in the current environment.
      R1, the opposite (control C3): (cannot unify
        "Cone (F^op ◯ K^op)" and "Cone (F ◯ K)^op")
      R2, the hom level of Exercise 3 (controls C6, C7; C19): (universe
        inconsistency: Cannot enforce dh = ch because ch < dh)

    CONTROLS.  C1 reads Mac Lane's definition off [ReflectsColimitCocone]
    at [eq_refl]; C2 reads Exercise 1 at cone level as the reflection
    field of the creation; C3 converts the opposite reading in one line;
    C4 reads the lift of 3.4.iii as the given limit; C5 reads Exercise 3
    as the cone-level theorem at the walking parallel pair; C6 and C7
    accept the elementary predicates over a target whose hom level is
    strictly above C's; C8 and C9 give [ReflectsAllLimits] and
    [ReflectsAllColimits] of every full and faithful functor (Riehl's
    3.4.5); C10 reads [ff_ReflectsLimitCone] as [ff_reflect_ump]; C11
    and C12 instantiate the forms over a class of shapes at
    Structure/Limit/Finite.v's [FiniteCategory], all finite shapes; C13
    to C16 are the boundary at the functor from [Sets] to the point:
    every fork there is a coequalizer (C13), so it preserves
    coequalizers (C14); it does not reflect them (C15); and so, by
    Exercise 3, it is not conservative (C16).  C17 reads Exercise 1
    over every diagram of parallel-pair shape as the per-pair theorem at
    the restriction of its hypothesis.
    C18 to C20 are the twin of R2: [ReflectsIsos]'s declaration copied
    with its binders written out (C18) is formable over the target R2 is
    refused at (C19) and gives the class itself at one hom level (C20),
    so R2's tie is the class's unannotated binders, not conservativity.
    C21 is the left adjoint's preservation of coequalizers in one line.
    C22 applies Exercise 3 at the identity on [Sets], whose three
    hypotheses hold together.  C23 to C29 read the forms over a class of
    shapes S back as the forms over the class of diagrams
    [fun J _ => S J], at [eq_refl]: the two maps between the reflection
    predicates are each other's inverses (C23 and C24, and on the
    colimit side C25 and C26), a conservative functor's reflection over S
    is its reflection over [fun J _ => S J] through the map (C27, and
    C28 on the colimit side), and Riehl's 3.4.iii over S is the exercise
    over [fun J _ => S J], pointwise (C29).  C17 to C29 were added after
    the first sixteen and are numbered in their own order through the
    file.

    NOT PINNED HERE.  (a) [About] readbacks as such: the target header's
    universe census.  (b) The closure of the targets under [Print
    Assumptions]: the Makefile's print-assumptions gate names the same
    59 names as the guards below.  (c) The absences the header records:
    an absence has no command.  (d) The reading of the books, from the
    page images.  (e) The closure under [Print Assumptions] of C8, C9
    and C12 to C29, proved here and not refutations: checked by hand,
    not gated.  (f) The refusals with ch < dh that the target header
    records beyond R2 ([Full], [Faithful] and the cone-level predicates),
    and the annotated copies of [Full] and [Faithful] accepted there:
    measured in a scratch file.

    The two guard blocks name the 59 names: the 55 heads of the first
    target's [.glob] (51 [def] entries, one [rec] and its three [proj]
    entries), which has no [Program] obligations, and the four names
    this issue adds to Structure/Coequalizer.v and Theory/
    Equivalence/Limit.v, so that a rename breaks this file.  Each is
    written fully qualified and with [@], so that no short name in scope
    can stand in for it.

--------
* 探讨极限和共同余子的反射（问题 #481）

固定#481为Mac Lane的§VI.7所增加内容的测量边界，包括反射余极限的定义和练习1及3（书本第154-155页，PDF第163-164页；目录项 maclane:VI.7:def2, maclane:VI.7:ex1, maclane:VI.7:ex3），以及Riehl的§3.4，定义3.4.1 (ii)、引理3.4.5和练习3.4.iii（印刷本第104、105和108页；riehl:3.4:def1, riehl:3.4:lem5, riehl:3.4:exiii），从页面图像中读取。目标是Structure/Limit/Reflection.v，其头部引用了反例R1和R2以及这里的控制，以及Structure/Coequalizer.v的[parallel_cocone_coequalizer_colimit]和Theory/Equivalence/Limit.v的三个全忠实名称。

导入列表：第一个目标的十三行 [Require] 按其自身顺序，以及该目标。在它们下方，[Print Libraries] 在一个临时文件中加载 35 个 [Category] 模块，这正是目标单独加载的一组（通过脚本比较）。随后三个部分依次添加，并在它们上方的每个命令之后，Theory/Equivalence/Limit.v 及其模块的导入列表（在它之后的左伴随部分未添加任何内容）；Structure/Limit/Finite.v 及其模块的导入列表；以及 Instance/One.v、Instance/Sets.v、Instance/Sets/Quotient.v 和 Instance/Sets/Coequalizer.v 及其模块的导入列表。因此，上方的内容在其导入下未被展开。更短的导入列表是使探针无缘无故通过的原因。

纪律。除了工具以外，每个负面都是 [Definition]，从来不是 [Check]，因此一个未完成的 evar 无法满足它。在这整个文件的副本中，每三条反驳线（工具、R1 和 R2）的反驳关键字被逐一去掉、编译，并读取其错误信息；每个副本都会在被去掉命令的位置停止。下面的三十个命令头中没有一个是反驳，并且以 [Definition]、[Example] 或 [Theorem] 开头（C18 以外的二十八个控制，以及 C15 使用的两个定义），在这整个文件的副本中用反驳关键字包裹后，会在该命令处停止构建，并显示 Rocq 对命令成功的反驳信息；C18 也是如此，一个 [Class]，手动包裹。在此文件的导入列表中，引用的是 Rocq 9.1.1。

类型。三种驳斥，被计算为以驳斥关键字开头的行：NAME-ABSENCE，工具（一个）；CONVERSION，R1，针对对立的极限谓词的余积谓词，每个陈述类型良好；UNIVERSE，R2，[ReflectsIsos] 在目标之上，其同态水平严格高于C。

拒绝，每个带括号的副本打印。
      工具（NAME-ABSENCE）：在当前环境中未找到引用 p481_absent_name。
      R1，相反（控制 C3）：（无法统一 "Cone (F^op ◯ K^op)" 和 "Cone (F ◯ K)^op"）
      R2，练习 3 的同构层次（控制 C6, C7; C19）：（宇宙不一致：无法强制 dh = ch 因为 ch < dh）

控制。
C1 在 [ReflectsColimitCocone] 的 [eq_refl] 处读取 Mac Lane 的定义；C2 将锥体层次上的习题 1 读取为创生的反射场；C3 在一行中转换相反的读法；C4 将 3.4.iii 的提升读取为给定的极限；C5 将习题 3 读取为行走平行对处的锥体层定理；C6 和 C7 接受在同伦层严格高于 C 的目标上的基本谓词；C8 和 C9 给出了每个完全且忠实函子（Riehl 的 3.4.5）的 [ReflectsAllLimits] 和 [ReflectsAllColimits]；C10 将 [ff_ReflectsLimitCone] 读取为 [ff_reflect_ump]；C11 和 C12 在 Structure/Limit/Finite.v 的 [FiniteCategory] 处对一类形状实例化形式，所有有限形状；C13 到 C16 是从 [Sets] 到点函子的边界：那里的每个叉子都是余等化器（C13），因此它保留余等化器（C14）；它不反映它们（C15）；因此，根据习题 3，它不是保守的（C16）。
C17 在每个平行对形状的图上阅读练习 1，按照每对定理在其假设的限制下。C18 到 C20 是 R2 的双生：[ReflectsIsos] 的声明被复制，其绑定器完整写出 (C18) 可在目标 R2 上形成，但在 (C19) 被拒绝，并在一个同类水平上给出类本身 (C20)，所以 R2 的绑定是类的未标注绑定器，而不是保守性。C21 是左伴随在一行中对等化子的保持。C22 在 [Sets] 上的恒等式应用练习 3，其三个假设同时成立。
C23 到 C29 将关于形状类 S 的形式阅读为关于图类 [fun J _ => S J] 的形式，在 [eq_refl] 处：两个反射谓词之间的映射互为逆映射（C23 和 C24，以及在余极限一侧的 C25 和 C26），一个保守函子在 S 上的反射是它通过映射在 [fun J _ => S J] 上的反射（C27，以及在余极限一侧的 C28），而 Riehl 的 3.4.iii 在 S 上就是在 [fun J _ => S J] 上逐点的习题（C29）。C17 到 C29 是在前十六个之后添加的，并在整个文件中按自己的顺序编号。

未在此固定。（a）[About] 的回读如下：目标头的宇宙普查。（b）在 [Print Assumptions] 下目标的闭包：Makefile 的 print-assumptions 门命名的 59 个名称与下面的守卫相同。（c）头记录的缺席：缺席没有命令。（d）从页面图像读取书本。（e）C8、C9 和 C12 到 C29 在 [Print Assumptions] 下的闭包，在此证明而非反驳：手工检查，未设门。（f）目标头记录 R2 以后的 ch < dh 拒绝 ([Full]、[Faithful] 及圆锥级谓词)，以及那里接受的 [Full] 和 [Faithful] 注释副本：在临时文件中测量。

这两个保护块列出了59个名称：第一个目标的[.glob]的55个头（51个[def]条目，一个[rec]及其三个[proj]条目），它没有[Program]义务，以及此问题添加到Structure/Coequalizer.v和Theory/Equivalence/Limit.v中的四个名称，以便重命名会破坏此文件。每个名称都以完全限定的形式写出，并带有[@]，因此范围内没有短名称可以替代它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Limit.Reflection.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument / ** 乐器 *)

(* The instrument / 乐器 *)
Fail Check p481_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane's definition, and Exercise 1 read off creation / ** Mac Lane 的定义，以及练习 1 的读出创建 *)

Section Readbacks.

Context {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}.

(*
C1: Mac Lane's definition, per diagram, is #427's predicate: a cocone
   whose image cocone is colimiting is colimiting.

--------
C1：根据图示，Mac Lane 的定义是 #427 的谓词：一个其像余锥是余极限的余锥是余极限的。
*)
Example p481_c1_definition :
  ReflectsColimitCocone K F
    = (∀ N : Cocone K, IsColimitCocone (FCocone F N) → IsColimitCocone N)
  := eq_refl.

(*
C2: Exercise 1 at cone level is the reflection field of the creation,
   the image cocone read over F^op ◯ K^op.

--------
C2：锥体层次的练习1是创造的反射场，图像余锥在 F^op ◯ K^op 上读取。
*)
Example p481_c2_exercise1 (CR : CreatesColimit K F) :
  creates_reflects_colimits CR
    = fun N H => @creates_reflect (J^op) (C^op) (D^op) (K^op) (F^op) CR N
                   (islimitcone_op_comp H)
  := eq_refl.

(* R1 *)
Fail Definition p481_r1_op (H : ReflectsLimitCone (K^op) (F^op)) :
  ReflectsColimitCocone K F := H.

(* C3: the two predicates are one apart, through islimitcone_op_comp. / C3：两个谓词相差一，通过 islimitcone_op_comp。 *)
Definition p481_c3_op (H : ReflectsLimitCone (K^op) (F^op)) :
  ReflectsColimitCocone K F :=
  fun N HN => H N (islimitcone_op_comp HN).

(*
C4: Riehl's Exercise 3.4.iii lifts every limiting cone downstairs to
   the given limit upstairs, on the nose.

--------
C4：Riehl 的练习 3.4.iii 将每个极限锥精确地提升到给定的上层极限。
*)
Example p481_c4_lift (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
  creates_lift (CreatesLimit := preserves_conservative_creates_limit L P R)
    N HN = @limit_cone _ _ _ L := eq_refl.

End Readbacks.

(*
C5: Exercise 3 is the cone-level theorem at the walking parallel pair,
   read back through the bridges.

--------
C5：练习3是在行走平行对处的圆锥级定理，回读桥梁部分。
*)
Example p481_c5_exercise3 {C D : Category} {F : C ⟶ D}
  (HC : HasCoequalizers C) (P : PreservesCoequalizers F)
  (R : ReflectsIsos F) :
  conservative_reflects_coequalizers HC P R
    = ReflectsColimitCocones_ReflectsCoequalizers
        (preserves_conservative_reflects_colimits_of_shape Parallel
           (HasCoequalizers_HasColimitsOfShape HC)
           (PreservesCoequalizers_PreservesColimitCocones P) R)
  := eq_refl.

(*
C17: Exercise 1 over every diagram of parallel-pair shape is the
   per-pair theorem at the restriction of its hypothesis.

--------
C17：每个平行对形状的图表上的练习1是在其假设限制下的每对定理。
*)
Example p481_c17_exercise1_restriction {C D : Category} {F : C ⟶ D}
  (CR : CreatesCoequalizers F) :
  creates_reflects_coequalizers CR
    = creates_reflects_coequalizers_of_pairs (fun x y f g => CR (APair f g))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** A class of shapes is the class of all diagrams of those shapes / ** 一种形状的类是所有这些形状的图表的类 *)

(*
C23: from the class of shapes S to the class of diagrams
   [fun J _ => S J] and back is the identity ...

--------
C23：从形状类 S 到图表类 [fun J _ => S J]，再返回，是恒等映射...
*)
Example p481_c23_over_class_over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsLimitConesOver S F) :
  ReflectsLimitConesOfClass_Over (ReflectsLimitConesOver_OfClass H) = H
  := eq_refl.

(* C24: ... and so is the round trip from [fun J _ => S J]. / C24: ……[fun J _ => S J] 的往返也是如此。 *)
Example p481_c24_class_over_class {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsLimitConesOfClass (fun J _ => S J) F) :
  ReflectsLimitConesOver_OfClass (ReflectsLimitConesOfClass_Over H) = H
  := eq_refl.

(* C25: C23 on the colimit side. / C25：C23 在余极限一侧。 *)
Example p481_c25_colimit_over_class_over {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsColimitCoconesOver S F) :
  ReflectsColimitCoconesOfClass_Over (ReflectsColimitCoconesOver_OfClass H)
    = H
  := eq_refl.

(* C26: C24 on the colimit side. / C26：C24 在余极限一侧。 *)
Example p481_c26_colimit_class_over_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsColimitCoconesOfClass (fun J _ => S J) F) :
  ReflectsColimitCoconesOver_OfClass (ReflectsColimitCoconesOfClass_Over H)
    = H
  := eq_refl.

(*
C27: a conservative functor's reflection over a class of shapes is its
   reflection over the class of diagrams [fun J _ => S J], through the
   map.

--------
C27：一个保守函子对一个形状类的反射是它通过映射在图类 [fun J _ => S J] 上的反射。
*)
Example p481_c27_reflects_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  preserves_conservative_reflects_limits_over S HL P R
    = ReflectsLimitConesOfClass_Over
        (preserves_conservative_reflects_limits_of_class (fun J _ => S J)
           (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R)
  := eq_refl.

(* C28: C27 on the colimit side. / C28：C27 在余极限侧。 *)
Example p481_c28_reflects_colimits_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Colimit K)
  (P : ∀ J : Category, S J → PreservesColimitCoconesOfShape J F)
  (R : ReflectsIsos F) :
  preserves_conservative_reflects_colimits_over S HL P R
    = ReflectsColimitCoconesOfClass_Over
        (preserves_conservative_reflects_colimits_of_class (fun J _ => S J)
           (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R)
  := eq_refl.

(*
C29: Riehl's Exercise 3.4.iii over a class of shapes is the exercise
   over the class of diagrams [fun J _ => S J], pointwise.

--------
C29：Riehl 的练习 3.4.iii 针对一类形状的练习是针对类图 [fun J _ => S J] 的逐点练习。
*)
Example p481_c29_creates_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  preserves_conservative_creates_limits_over S HL P R
    = fun J HJ K =>
        preserves_conservative_creates_limits_of_class (fun J _ => S J)
          (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R J K HJ
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the hom level of the target / ** 宇宙：目标的宿主级别 *)

(*
C6: the elementary reflection of coequalizers, over a target whose hom
   level is strictly above C's.

--------
C6：在目标的同态层级严格高于 C 的情况下，共等化的初等反射。
*)
Definition p481_c6_reflects_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ReflectsCoequalizers F.

(* C7: and the elementary preservation. / C7：以及基本的保存。 *)
Definition p481_c7_preserves_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  PreservesCoequalizers F.

(* R2 *)
Fail Definition p481_r2_conservative_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ReflectsIsos F.

(*
C18: Structure/Limit/Preservation.v's [ReflectsIsos], its declaration
   copied with its binders written out ...

--------
C18: Structure/Limit/Preservation.v 与 [ReflectsIsos]，其声明及其绑定器的复制写出...
*)
Class p481_c18_ReflectsIsos@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) := {
  p481_c18_reflects_iso {x y : C} (f : x ~> y) :
    IsIsomorphism (fmap[F] f) → IsIsomorphism f
}.

(* C19: ... is formable over the target R2 is refused at ... / C19: ... 在目标 R2 上可形成被拒绝于 ... *)
Definition p481_c19_conservative_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  p481_c18_ReflectsIsos F.

(* C20: ... and, at one hom level, gives the class itself. / C20: ……并且，在某个同质层次上，给出了类本身。 *)
Definition p481_c20_copy_is_class@{co ch do +}
  {C : Category@{co ch ch}} {D : Category@{do ch ch}} {F : C ⟶ D}
  (R : p481_c18_ReflectsIsos F) : ReflectsIsos F :=
  @Build_ReflectsIsos C D F
    (fun x y f I => @p481_c18_reflects_iso C D F R x y f I).

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the targets, by name / ** Guardian：按名称列出目标的每个常量 *)

Check @Category.Structure.Coequalizer.parallel_cocone_coequalizer_colimit.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfShape.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOver.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfClass.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOver_OfClass.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfClass_Over.
Check @Category.Structure.Limit.Reflection.ReflectsAllLimits.
Check @Category.Structure.Limit.Reflection.ReflectsAllLimits_Over.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfShape.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOver.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfClass.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOver_OfClass.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfClass_Over.
Check @Category.Structure.Limit.Reflection.ReflectsAllColimits.
Check @Category.Structure.Limit.Reflection.ReflectsAllColimits_Over.
Check @Category.Structure.Limit.Reflection.ReflectsIsos_op.
Check @Category.Structure.Limit.Reflection.creates_reflects_colimits.
Check @Category.Structure.Limit.Reflection.creates_reflects_all_limits.
Check @Category.Structure.Limit.Reflection.creates_reflects_all_colimits.
Check @Category.Structure.Limit.Reflection.MacLaneCreatesLimit.
Check @Category.Structure.Limit.Reflection.mlc_lift.
Check @Category.Structure.Limit.Reflection.mlc_limiting.
Check @Category.Structure.Limit.Reflection.mlc_unique.
Check @Category.Structure.Limit.Reflection.maclane_creates_reflects.
Check @Category.Structure.Limit.Reflection.maclane_CreatesLimit.
Check @Category.Structure.Limit.Reflection.iso_unique_lift_reflects.
Check @Category.Structure.Limit.Reflection.id_maclane_creates.
Check @Category.Structure.Limit.Reflection.MacLaneCreatesColimit.
Check @Category.Structure.Limit.Reflection.conservative_reflects_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_of_shape.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_of_class.
Check @Category.Structure.Limit.Reflection.conservative_reflects_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_of_shape.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_of_class.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limits_of_class.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_colimits_of_class.
Check @Category.Structure.Limit.Reflection.ReflectsCoequalizers.
Check @Category.Structure.Limit.Reflection.PreservesCoequalizers.
Check @Category.Structure.Limit.Reflection.CreatesCoequalizers.
Check @Category.Structure.Limit.Reflection.ReflectsCoequalizers_ReflectsColimitCocones.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCocones_ReflectsCoequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCocones_ReflectsCoequalizers.
Check @Category.Structure.Limit.Reflection.PreservesCoequalizers_PreservesColimitCocones.
Check @Category.Structure.Limit.Reflection.PreservesColimitCocones_PreservesCoequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.PreservesColimitCocones_PreservesCoequalizers.
Check @Category.Structure.Limit.Reflection.creates_reflects_coequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.maclane_creates_reflects_coequalizers.
Check @Category.Structure.Limit.Reflection.creates_reflects_coequalizers.
Check @Category.Structure.Limit.Reflection.conservative_reflects_coequalizers.

(* ------------------------------------------------------------------------ *)
(** ** Riehl's Lemma 3.4.5: full and faithful functors / ** Riehl 的引理 3.4.5：满且忠实的函子 *)

(*
Required here, after every other command above, so that the sections
   above are elaborated under the first target's import list alone: the
   import list of Theory/Equivalence/Limit.v and that module.

--------
此处需要，在上面每个命令之后，以便上述各部分仅在第一个目标的导入列表下进行阐述：Theory/Equivalence/Limit.v 的导入列表及该模块。
*)
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Limit.

Check @Category.Theory.Equivalence.Limit.ff_ReflectsLimitCone.
Check @Category.Theory.Equivalence.Limit.ff_reflects_colimit.
Check @Category.Theory.Equivalence.Limit.ff_ReflectsColimitCocone.

Section FullFaithful.

Context {C D : Category} {F : C ⟶ D}.
Context `{HF : @Full C D F} `{HfF : @Faithful C D F}.

(* C8: the limit half at every diagram, Riehl's "any limits". / C8：在每个图表上的极限半，Riehl 的“任意极限”。 *)
Definition p481_c8_ff_all_limits : ReflectsAllLimits F :=
  fun J K => ff_ReflectsLimitCone K.

(* C9: and the colimit half. / C9：以及余极半。 *)
Definition p481_c9_ff_all_colimits : ReflectsAllColimits F :=
  fun J K => ff_ReflectsColimitCocone K.

(* C10: the limit half is [ff_reflect_ump] with the legs by reflexivity. / C10: 极限半部分是 [ff_reflect_ump]，通过反身性与这些引脚连接。 *)
Example p481_c10_ff_readback {J : Category} (K : J ⟶ C) :
  ff_ReflectsLimitCone K
    = fun N H => @ff_reflect_ump C D F HF HfF J K N (limitcone_isalimit H)
                   (fun x => reflexivity _)
  := eq_refl.

End FullFaithful.

(* ------------------------------------------------------------------------ *)
(** ** Left adjoints preserve coequalizers, in one line / ** 左伴随保持共等化子，一行总结 *)

(*
C21: under the import list of the section above, which includes
   Adjunction/Continuity.v, the elementary preservation of coequalizers
   by a left adjoint is that file's cone-level theorem read through the
   bridge.

--------
C21：在上述部分的导入列表下，其中包括 Adjunction/Continuity.v，一个左伴随保持共等化子的基本性质是通过桥读取该文件的圆锥级定理。
*)
Definition p481_c21_left_adjoint_preserves {C D : Category}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) : PreservesCoequalizers F :=
  PreservesColimitCocones_PreservesCoequalizers
    (fun K => left_adjoint_PreservesColimitCocone A K).

(* ------------------------------------------------------------------------ *)
(** ** A class of shapes: all finite shapes / ** 一类形状：所有有限形状 *)

(*
Required here, after every other command above: the import list of
   Structure/Limit/Finite.v and that module.

--------
在这里必需，在上面每个其他命令之后：Structure/Limit/Finite.v 的导入列表以及该模块。
*)
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Category.Structure.Limit.Finite.

(* C11: reflection of every finite limit, from reflection of all. / C11：每个有限极限的反射，从所有反射中得到。 *)
Definition p481_c11_finite {C D : Category} {F : C ⟶ D}
  (H : ReflectsAllLimits F) : ReflectsLimitConesOver FiniteCategory F :=
  ReflectsAllLimits_Over H.

(* C12: Riehl's Exercise 3.4.iii at the class of finite shapes. / C12：在有限形状类上的Riehl练习3.4.iii。 *)
Definition p481_c12_finite_creates {C D : Category} {F : C ⟶ D}
  (HL : ∀ J : Category, FiniteCategory J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver FiniteCategory F) (R : ReflectsIsos F) :
  ∀ J : Category, FiniteCategory J → CreatesLimitsOfShape J F :=
  preserves_conservative_creates_limits_over FiniteCategory HL P R.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 3's conservativity is needed: the functor to the point / ** 练习 3 的保守性是必要的：函子指向点 *)

(*
Required here, after every other command above: the import lists of
   Instance/One.v, Instance/Sets.v, Instance/Sets/Quotient.v and
   Instance/Sets/Coequalizer.v, and those modules.

--------
在此所需，在上述每个其他命令之后：Instance/One.v、Instance/Sets.v、Instance/Sets/Quotient.v 和 Instance/Sets/Coequalizer.v 的导入列表，以及那些模块。
*)
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Coequalizer.

(* C13: in the point every fork is a coequalizer. / C13：在该点，每个叉都是一个等化器。 *)
Definition p481_c13_point_coequalizer {x y : _1} (f g : x ~{_1}~> y)
  (q : _1) (e : y ~{_1}~> q) : IsCoequalizer f g q e.
Proof.
  unshelve econstructor.
  - destruct e, f, g; reflexivity.
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact ttt.
    + destruct h; reflexivity.
    + intros v _; destruct v; reflexivity.
Defined.

(* C14: so the functor from Sets to the point preserves coequalizers. / C14：所以从集合到一点的函子保留了共同化子。 *)
Definition p481_c14_erase_preserves : PreservesCoequalizers (Erase Sets) :=
  fun x y f g q e _ => p481_c13_point_coequalizer _ _ _ _.

(* The two-element setoid, and its map onto the singleton. / 双元素宿主集及其映射到单元素集。 *)
Definition p481_bool : SetoidObject :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition p481_collapse : p481_bool ~{Sets}~> unit_setoid_object.
Proof.
  exact (@Build_SetoidMorphism bool (eq_Setoid bool) poly_unit unit_setoid
           (fun _ => ttt) (fun _ _ _ => eq_refl)).
Defined.

(*
C15: and it does not reflect them: the fork (1, 1, collapse) becomes a
   coequalizer in the point, and is none in Sets, where the descent u of
   the identity would have u ttt = true and u ttt = false.

--------
C15: 它并没有反映它们：分叉 (1, 1, collapse) 在点中成为一个等值化器，而在集合中则不是等值化器，其中恒等的下降 u 会有 u ttt = true 和 u ttt = false。
*)
Theorem p481_c15_erase_not_reflects :
  ReflectsCoequalizers (Erase Sets) → False.
Proof.
  intro R.
  assert (E : IsCoequalizer (@id Sets p481_bool) id unit_setoid_object
                p481_collapse).
  { apply R.
    - reflexivity.
    - apply p481_c13_point_coequalizer. }
  destruct (coeq_desc E (@id Sets p481_bool) (reflexivity _)) as [u Hu _].
  pose proof (Hu true) as Ht.
  pose proof (Hu false) as Hf.
  simpl in Ht, Hf.
  rewrite Ht in Hf.
  discriminate.
Qed.

(*
C16: Sets has coequalizers and the functor preserves them, so by
   Exercise 3 it is not conservative.

--------
C16：集合具有共余子，并且函子保持它们，因此根据习题 3，它不是保守的。
*)
Definition p481_c16_erase_not_conservative :
  ReflectsIsos (Erase Sets) → False :=
  fun R => p481_c15_erase_not_reflects
             (conservative_reflects_coequalizers Sets_HasCoequalizers
                p481_c14_erase_preserves R).

(*
C22: the three hypotheses of Exercise 3 hold together at the identity
   on Sets, which therefore reflects coequalizers.

--------
C22：练习3的三个假设在集合上的恒等映射处同时成立，因此集合反映共轭化子。
*)
Definition p481_c22_identity_reflects : ReflectsCoequalizers (@Id Sets) :=
  @conservative_reflects_coequalizers Sets Sets (@Id Sets)
    Sets_HasCoequalizers (fun x y f g q e E => E)
    (@Build_ReflectsIsos Sets Sets (@Id Sets) (fun x y f I => I)).
