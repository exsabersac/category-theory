(**
* Probe for the split fork C² ⇉ C → 1 in Cat (issue #478)

    Pins the measured boundaries of what #478 adds for Mac Lane, §VI.6,
    the example of a fork in Cat, book p. 150 (PDF p. 159), catalog item
    maclane:VI.6:remark1, read from the page image ("If C has a terminal
    object a₀, this fork is split by the functor s which sends the unique
    object of 1 to a₀, and the functor t which sends each c ∈ C to the
    unique arrow c → a₀").  The target is Instance/Cat/SplitFork.v, whose
    header cites the refutations R1 to R8 and the controls C25 and C27
    here.  Each of the twenty-six [Example]s of the target has a control
    that restates it independently of the constant that states it
    (RESTATEMENTS, below).

    THE IMPORT LIST: the target's twenty-two [Require] lines in its own
    order, and the target.  Under them [Print Libraries] in a scratch file
    loads eighty-six [Category] modules, exactly the set a [Require] of
    the target alone loads (compared by script).  A shorter import list
    is what makes a probe pass for no reason.
    CORRECTION (#480): eighty-seven, the two sets still equal, since
    Structure/Coequalizer/Absolute.v requires Structure/Coequalizer/
    Contractible.v.

    DISCIPLINE.  Every negative other than the instrument is an
    [Example] or a [Definition], never a [Check], so that an open evar
    cannot satisfy it.  Each of the nine refutation lines (the
    instrument and R1 to R8) was stripped of its refutation keyword in a
    copy of this WHOLE file, one at a time, compiled, and its error read;
    each copy stops inside the stripped command.  Each control, wrapped
    in the refutation keyword in a copy of this WHOLE file, stops the
    build at that command with the message Rocq prints for a refutation
    whose command succeeds.  Quotations are Rocq 9.1.1's under this
    file's import list.

    KINDS.  Nine refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE, the instrument (one); CONVERSION,
    [eq_refl] refused with a "cannot unify" parenthetical, every
    statement being well typed (R1 to R6 and R8: seven); and UNIVERSE
    (R7: one), the statement refused by a universe inconsistency.
    CAUSES, read from the terms: R1 and R2 compare the value of a
    constant functor at a variable object or arrow of 1 with that
    variable itself, and [poly_unit] has no eta rule; R3 to R6 compare
    two functor records whose law fields are different proof terms,
    [Compose]'s obligations applied to different functors or [Id]'s, and
    R4's object maps differ besides; R8 compares a component of the
    pushed split fork's law 3 with the identity, and that component
    stops at opaque constants outside #478, the obligations the setoid
    rewriting in Split.v's [functor_preserves_split] goes through and
    those of [StrictCat_to_Cat] (the target's STRENGTHS).  Measured:
    every refutation still stops inside its command, and every control
    is still accepted, in a copy of the target and this file under a
    renamed logical root with all four [Qed]s of the target turned
    [Defined]; so none is the opacity of #478's own proofs.

    THE REFUSALS, with the message each stripped copy prints.  Rocq
    prints [_1] and the terminal object alike as 1, so [Diagonal _1 a₀]
    reads "fobj[Diagonal 1] 1".
      The instrument (NAME-ABSENCE): The reference p478_absent_name was
        not found in the current environment.
      R1, law 2 on a variable object of 1 (controls C1, C2):
        (cannot unify "fobj[Erase C ◯ fobj[Diagonal 1] 1] x" and
        "fobj[Id[1]] x")
      R2, law 2 on a variable arrow of 1 (controls C3, C4):
        (cannot unify "fmap[Erase C ◯ fobj[Diagonal 1] 1] f" and
        "fmap[Id[1]] f")
      R3, law 1 as an equality of functor records (controls C5 to C8):
        (cannot unify "Erase C ◯ Arrow_dom" and "Erase C ◯ Arrow_cod")
      R4, law 2 likewise (control C9):
        (cannot unify "Erase C ◯ fobj[Diagonal 1] 1" and "Id[1]")
      R5, law 3 likewise (controls C10 to C12):
        (cannot unify "Arrow_dom ◯ arrow_fork_t" and "Id[C]")
      R6, law 4 likewise (controls C13 to C15):
        (cannot unify "Arrow_cod ◯ arrow_fork_t" and
        "fobj[Diagonal 1] 1 ◯ Erase C")
      R7, law 1 at a category whose hom level exceeds its object level
        (UNIVERSE; control C16): The term "Arrow_dom" has type
        "(?C ⃗) ⟶ ?C" while it is expected to have type "?x ~{ Cat }~> C"
        (universe inconsistency: Cannot enforce X = h because X <= Y < h),
        where X and Y stand for two universes Rocq names by serial
        number.  C² is an object of [Cat] beside C only at C's object
        level o, its hom level is C's, h, and [Arrow]'s own block puts
        its hom level at or below its object level: h <= o, against the
        declared o < h.
      R8, law 3's component in the pushed split fork in Cat as the
        identity (control C27, at the direct one):
        (cannot unify "to (projT1 (scoeq_law3 arrow_fork_split) c)" and
        "id{C}")

    RESTATEMENTS.  [arrow_fork_e_one] C17, [arrow_fork_e_one_strict] C18,
    [arrow_fork_law1_obj] C5, [arrow_fork_law1_map] C6,
    [arrow_fork_s_obj] C19, [arrow_fork_t_obj] C20, [arrow_fork_t_map]
    C21, [arrow_fork_law3_strict_component] C28,
    [arrow_fork_law4_strict_component] C29, [arrow_fork_law2_obj] C1,
    [arrow_fork_law2_map] C3, [arrow_fork_law3_obj] C10,
    [arrow_fork_law3_map] C11, [arrow_fork_law4_obj] C13,
    [arrow_fork_law4_map] C14, [arrow_fork_split_e] C22,
    [arrow_fork_split_s] C23, [arrow_fork_split_t] C24,
    [arrow_fork_law3_direct_component] C30,
    [arrow_fork_law4_direct_component] C31, [arrow_fork_split_direct_e]
    C32, [arrow_fork_split_direct_s] C33, [arrow_fork_split_direct_t]
    C34, [arrow_fork_preserved_absolute_strict] C35,
    [arrow_fork_preserved_absolute] C36 and
    [arrow_fork_not_coequalizer_0] C26: twenty-six readbacks, each named
    once.  C2 and C4 are the case analyses R1 and R2 refuse to do by
    conversion; C7, C8, C9, C12 and C15 are the laws at ≈, the twins of
    R3 to R6; C16 is the twin of R7; C27, R8's statement at
    [arrow_fork_split_direct], is the twin of R8.  C25 restates none: it
    instantiates [arrow_fork_split] at [Cat] with Instance/One.v's
    [Cat_Terminal], so that the hypothesis of the splitting is shown
    satisfiable.

    NOT PINNED HERE.  (a) [About] readbacks as such: the target header's
    universe census.  (b) The flips and copies described above, made in
    scratch copies.  (c) The closure of the target under
    [Print Assumptions]: the Makefile's print-assumptions gate names the
    same forty-five names as the guard below.  (d) The absences the
    header records: an absence has no command.  (e) The reading of the
    book, from the page images.  (f) [arrow_fork_not_coequalizer], a
    theorem of the target proved without an axiom, and not a
    refutation.  (g) The target header's scratch measurements: the
    convertibility of the actions as functions, the normal form behind
    R8, and the components of laws 1 and 2 of the direct split fork.

    The guard block names the forty-five names of the target, so that a
    rename breaks this file: exactly the entries [Print Module] gives for
    the new module, which has no [Program] obligations.  Each is written
    fully qualified and with [@], so that no short name in scope can
    stand in for it.

--------
* 在 Cat 中探查分裂叉 C² ⇉ C → 1（问题 #478）

固定了 #478 为 Mac Lane §VI.6 增加的内容的测量边界，Cat 中叉子的例子，书本第 150 页（PDF 第 159 页），目录项 maclane:VI.6:remark1，从页面图像中读取（“如果 C 有一个终对象 a₀，则这个叉子被函子 s 分裂，s 将 1 的唯一对象映射到 a₀，以及函子 t，将每个 c ∈ C 映射到唯一箭头 c → a₀”）。目标是 Instance/Cat/SplitFork.v，其头部引用了这里的驳斥 R1 到 R8 和控制 C25 与 C27。目标的二十六个 [Example] 中，每一个都有一个控制，它独立于声明它的常量重新声明它（见下文的 RESTATEMENTS）。

导入列表：目标自身顺序中的二十二条 [Require] 行，以及目标。在它们下面，[Print Libraries] 在一个临时文件中加载八十六个 [Category] 模块，正好是目标单独加载的一组 [Require]（通过脚本比较）。导入列表较短才会使探针无缘无故通过。修正（#480）：八十七，两个集合仍然相等，因为 Structure/Coequalizer/Absolute.v 需要 Structure/Coequalizer/Contractible.v。

纪律。除工具之外的每一个负例都是 [Example] 或 [Definition]，从来不是 [Check]，因此一个开放的 evar 无法满足它。这九条反驳线（工具以及 R1 到 R8）中的每一条在这个整个文件的副本中都被逐一去掉了反驳关键字，编译后读取其错误；每个副本都在被去掉命令的地方停止。每个控制，在这个整个文件的副本中被反驳关键字包裹时，会在该命令处停止构建，并显示 Rocq 对命令成功的反驳所打印的信息。引文来自 Rocq 9.1.1 在此文件导入列表下的内容。

种类。九种反驳，被计为以反驳关键字开头的行：NAME-ABSENCE，工具（一个）；CONVERSION，[eq_refl] 拒绝，并带有“无法统一”的括号，每个语句类型良好（R1 到 R6 和 R8：七个）；以及 UNIVERSE（R7：一个），该语句因宇宙不一致而被拒绝。原因，从术语中读取：R1 和 R2 比较变量对象或箭头为 1 的常量函子与该变量本身的值，而 [poly_unit] 没有 eta 规则；R3 到 R6 比较两个函子记录，其法律字段是不同的证明项，[Compose] 的义务应用于不同的函子，或者 [Id] 的，而 R4 的对象映射除了还有差异；R8 比较被推送的分裂叉的法律 3 的一个组件与恒等式，并且该组件在 #478 之外的不透明常量处停止，在 Split.v 中的 [functor_preserves_split] 的集合重写通过了，而 [StrictCat_to_Cat] 的（目标的 STRENGTHS）也通过了。衡量：
    每一次反驳仍然在其命令内部停止，每一次控制
    仍然被接受，在目标的副本以及此文件中，在重命名的逻辑根下，
    将目标的所有四个 [Qed] 转为 [Defined]；因此，没有一个是 #478 自身证明的不可见性。

拒绝，以及每个被剥离副本打印的消息。Rocq 将 [_1] 和终端对象都打印为 1，因此 [Diagonal _1 a₀] 读取为“fobj[Diagonal 1] 1”。工具（NAME-ABSENCE）：在当前环境中未找到引用 p478_absent_name。R1，法则 2 对变量对象 1（控制 C1、C2）：
 （无法统一“fobj[Erase C ◯ fobj[Diagonal 1] 1] x”和
 “fobj[Id[1]] x”）
 R2，变量箭头 1 上的定律 2（控制 C3、C4）：
 （无法统一“fmap[Erase C ◯ fobj[Diagonal 1] 1] f”和
 “fmap[Id[1]] f”）
 R3，法则 1 作为函子记录的等式（控制 C5 到 C8）：
 （不能统一“擦除C◯Arrow_dom”和“擦除C◯Arrow_cod”）
 R4，法则2同样（对照C9）：
 （无法统一“擦除C ◯ fobj[Diagonal 1] 1”和“Id[1]”）
 R5，法则 3 同样（控制 C10 至 C12）：
 （无法统一“Arrow_dom ◯ arrow_fork_t”和“Id[C]”）
 R6，法则 4 同样（控制 C13 至 C15）：
 （无法统一“Arrow_cod ◯ arrow_fork_t”和
 “fobj[Diagonal 1] 1 ◯ 擦除 C”）
 R7，定律 1，其本位电平超过其对象电平的类别
 （UNIVERSE；控制 C16）：术语“Arrow_dom”具有类型
 "(?C ⃗) ⟶ ?C" 而预期类型为 "?x ~{ Cat }~> C"
 （宇宙不一致：无法强制 X = h，因为 X <= Y < h），
 其中 X 和 Y 代表两个宇宙 Rocq 名称的序列号
 数量。C² 是 [Cat] 的一个对象，位于 C 旁边，仅在 C 的对象层级 o 上，其同态层级是 C 的 h，而 [Arrow] 自身的块将其同态层级置于其对象层级之下或相等：h <= o，与声明的 o < h 相冲突。R8，法律 3 在 Cat 中压入的分叉组件中的组成部分作为恒等（控制 C27，在直接位置）：
（无法统一 "to (projT1 (scoeq_law3 arrow_fork_split) c)" 和 "id{C}"）

重述。[arrow_fork_e_one] C17、[arrow_fork_e_one_strict] C18、[arrow_fork_law1_obj] C5、[arrow_fork_law1_map] C6、[arrow_fork_s_obj] C19、[arrow_fork_t_obj] C20、[arrow_fork_t_map] C21、[arrow_fork_law3_strict_component] C28、[arrow_fork_law4_strict_component] C29、[arrow_fork_law2_obj] C1、[arrow_fork_law2_map] C3、[arrow_fork_law3_obj] C10、[arrow_fork_law3_map] C11、[arrow_fork_law4_obj] C13、[arrow_fork_law4_map] C14、[arrow_fork_split_e] C22、[arrow_fork_split_s] C23、[arrow_fork_split_t] C24、[arrow_fork_law3_direct_component] C30、[arrow_fork_law4_direct_component] C31、[arrow_fork_split_direct_e] C32、[arrow_fork_split_direct_s] C33、[arrow_fork_split_direct_t] C34、[arrow_fork_preserved_absolute_strict] C35、[arrow_fork_preserved_absolute] C36 以及 [arrow_fork_not_coequalizer_0] C26：二十六个回读，每个只命名一次。C2 和 C4 是 R1 和 R2 拒绝通过转换进行的案例分析；C7、C8、C9、C12 和 C15 是 ≈ 处的定律，是 R3 到 R6 的孪生；C16 是 R7 的孪生；C27，即 R8 在 [arrow_fork_split_direct] 的陈述，是 R8 的孪生。C25 没有重述任何内容：它在 [Cat] 处实例化 [arrow_fork_split]，使用 Instance/One.v 的 [Cat_Terminal]，从而显示拆分的假设是可满足的。

未固定在此处。(a) [About] 读取如下：目标头文件的宇宙普查。(b) 上述翻转和复制，均在临时副本中进行。(c) 在 [Print Assumptions] 下目标的闭包：Makefile 的 print-assumptions 门列出的名称与下面的保护名称相同，共四十五个名称。(d) 头文件记录的缺失：一个缺失没有命令。(e) 从页面图像中读取书籍。(f) [arrow_fork_not_coequalizer]，一个在没有公理的情况下证明的目标定理，并非反驳。(g) 目标头的临时测量：动作作为函数的可转换性，R8 背后的范式，以及直接分叉的法则 1 和 2 的组成部分。

守卫块列出了目标的四十五个名称，因此重命名会破坏此文件：正是 [Print Module] 为新模块提供的条目，而新模块没有 [Program] 的义务。每个名称都以完全限定形式和 [@] 写出，因此作用域内没有短名称可以代替它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.SplitFork.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument / ** 乐器 *)

(* The instrument / 乐器 *)
Fail Check p478_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** Law 2 at a variable object or arrow of 1 / ** 针对 1 的可变对象或箭头的法则 2 *)

Section LawTwo.

Context {C : Category}.
Context `{T : @Terminal C}.

(* C1: at the object of 1, on the nose. / C1：在1的物体上，正中鼻子。 *)
Example p478_c1_law2_obj :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] ttt = fobj[Id[_1]] ttt
  := eq_refl.

(* R1 *)
Fail Example p478_r1_law2_obj_var (x : _1) :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] x = fobj[Id[_1]] x
  := eq_refl.

(* C2: at every object, by a case analysis. / C2：对每个对象，通过案例分析。 *)
Lemma p478_c2_law2_obj_cases (x : _1) :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] x = fobj[Id[_1]] x.
Proof. destruct x; reflexivity. Qed.

(* C3: at the identity arrow of 1, on the nose. / C3：在 1 的身份箭头上，正中。 *)
Example p478_c3_law2_map :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] (@id _1 ttt)
    = fmap[Id[_1]] (@id _1 ttt) := eq_refl.

(* R2 *)
Fail Example p478_r2_law2_map_var (f : ttt ~{_1}~> ttt) :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] f = fmap[Id[_1]] f
  := eq_refl.

(* C4: at every arrow, by a case analysis. / C4：通过分类讨论，对每个箭头进行分析。 *)
Lemma p478_c4_law2_map_cases (f : ttt ~{_1}~> ttt) :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] f = fmap[Id[_1]] f.
Proof. destruct f; reflexivity. Qed.

End LawTwo.

(* ------------------------------------------------------------------------ *)
(** ** The laws are not equalities of functor records / ** 这些定律不是函子记录的等式 *)

Section Records.

Context {C : Category}.

(* C5: law 1 on objects, on the nose. / C5：关于物体的法律1，正中要害。 *)
Example p478_c5_law1_obj (x : @Arrow C) :
  fobj[Erase C ◯ Arrow_dom] x = fobj[Erase C ◯ Arrow_cod] x := eq_refl.

(* C6: law 1 on arrows, on the nose. / C6：关于箭的法律1，关于鼻子。 *)
Example p478_c6_law1_map {x y : @Arrow C} (f : x ~> y) :
  fmap[Erase C ◯ Arrow_dom] f = fmap[Erase C ◯ Arrow_cod] f := eq_refl.

(* R3 *)
Fail Example p478_r3_law1_records :
  Erase C ◯ Arrow_dom = Erase C ◯ Arrow_cod := eq_refl.

End Records.

(* C7: law 1 in StrictCat. / C7：StrictCat 中的定律 1。 *)
Definition p478_c7_law1_strict@{o h +} (C : Category@{o h h}) :
  Erase C ∘[StrictCat] Arrow_dom ≈[StrictCat] Erase C ∘[StrictCat] Arrow_cod
  := arrow_fork_law1_strict C.

(* C8: law 1 in Cat. / C8：猫中的法律1 *)
Definition p478_c8_law1@{o h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

Section RecordsSplit.

Context {C : Category}.
Context `{T : @Terminal C}.

(* R4 *)
Fail Example p478_r4_law2_records :
  Erase C ◯ Diagonal _1 (@terminal_obj C T) = Id[_1] := eq_refl.

(* C10: law 3 on objects, on the nose. / C10：关于物体的法律3，正中要害。 *)
Example p478_c10_law3_obj (c : C) :
  fobj[Arrow_dom ◯ arrow_fork_t] c = c := eq_refl.

(* C11: law 3 on arrows, on the nose. / C11：关于箭的法律3，关于鼻子。 *)
Example p478_c11_law3_map {c d : C} (f : c ~> d) :
  fmap[Arrow_dom ◯ arrow_fork_t] f = f := eq_refl.

(* R5 *)
Fail Example p478_r5_law3_records :
  Arrow_dom ◯ arrow_fork_t = Id[C] := eq_refl.

(* C13: law 4 on objects, on the nose. / C13：关于物体的法律4，正中要害。 *)
Example p478_c13_law4_obj (c : C) :
  fobj[Arrow_cod ◯ arrow_fork_t] c = @terminal_obj C T := eq_refl.

(* C14: law 4 on arrows, on the nose. / C14：关于箭的法律，第4条，关于鼻子。 *)
Example p478_c14_law4_map {c d : C} (f : c ~> d) :
  fmap[Arrow_cod ◯ arrow_fork_t] f = @id C (@terminal_obj C T) := eq_refl.

(* R6 *)
Fail Example p478_r6_law4_records :
  Arrow_cod ◯ arrow_fork_t = Diagonal _1 (@terminal_obj C T) ◯ Erase C
  := eq_refl.

End RecordsSplit.

(* C9: law 2 in StrictCat. / C9：StrictCat 中的法律 2。 *)
Definition p478_c9_law2_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[StrictCat] Diagonal _1 (@terminal_obj C T)
    ≈[StrictCat] @id StrictCat _1 := arrow_fork_law2_strict.

(* C12: law 3 in StrictCat. / C12：StrictCat 中的定律 3。 *)
Definition p478_c12_law3_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[StrictCat] arrow_fork_t ≈[StrictCat] @id StrictCat C
  := arrow_fork_law3_strict.

(* C15: law 4 in StrictCat. / C15：StrictCat 中的法律 4。 *)
Definition p478_c15_law4_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[StrictCat] arrow_fork_t
    ≈[StrictCat] Diagonal _1 (@terminal_obj C T) ∘[StrictCat] Erase C
  := arrow_fork_law4_strict.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the fork needs h <= o / ** 宇宙：分叉需要 h <= o *)

(* R7 *)
Fail Definition p478_r7_law1_o_lt_h@{o h + | o < h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

(* C16: the same at h < o. / C16：在 h < o 时相同。 *)
Definition p478_c16_law1_h_lt_o@{o h + | h < o +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

(* ------------------------------------------------------------------------ *)
(** ** Restatements of the target's readbacks / ** 对目标回读的重述 *)

Section Readbacks.

Context {C : Category}.
Context `{T : @Terminal C}.

(* C17: e is Cat's terminal map. / C17：e 是 Cat 的终端地图。 *)
Example p478_c17_e_one : Erase C = @one Cat Cat_Terminal C := eq_refl.

(* C18: e is StrictCat's terminal map. / C18：e 是 StrictCat 的终映射。 *)
Example p478_c18_e_one_strict :
  Erase C = @one StrictCat StrictCat_Terminal C := eq_refl.

(* C19: s sends the object of 1 to a₀. / C19: s 将 1 的对象发送到 a₀。 *)
Example p478_c19_s_obj (x : _1) :
  fobj[Diagonal _1 (@terminal_obj C T)] x = @terminal_obj C T := eq_refl.

(* C20: t sends c to the unique arrow c → a₀. / C20：t 将 c 发送到唯一的箭头 c → a₀。 *)
Example p478_c20_t_obj (c : C) :
  fobj[arrow_fork_t] c = ((c, @terminal_obj C T); @one C T c) := eq_refl.

(* C21: t sends f to the square (f, 1). / C21：它将车移动到格子 (f, 1)。 *)
Example p478_c21_t_map {c d : C} (f : c ~> d) :
  `1 (fmap[arrow_fork_t] f) = (f, @id C (@terminal_obj C T)) := eq_refl.

End Readbacks.

(* C22: the split fork in Cat has e for its coequalizing arrow. / C22：猫中的分叉有 e 作为其同等化箭头。 *)
Example p478_c22_split_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e (@arrow_fork_split C T) = Erase C := eq_refl.

(* C23: ... s for the section of e. / C23: ... 用于 e 的部分。 *)
Example p478_c23_split_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s (@arrow_fork_split C T) = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

(* C24: ... and t for the section of ∂₀. / C24: ... 并且 t 用于 ∂₀ 的部分。 *)
Example p478_c24_split_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t (@arrow_fork_split C T) = @arrow_fork_t C T := eq_refl.

(* C25: the splitting at C := Cat, whose terminal object is 1. / C25：在 C := Cat 的分裂，其终端对象是 1。 *)
Definition p478_c25_split_at_Cat :
  @SplitCoequalizer Cat (@Arrow Cat) Cat Arrow_dom Arrow_cod :=
  @arrow_fork_split Cat Cat_Terminal.

(* C26: at the empty category, e is not a coequalizer. / C26：在空类别中，e 不是一个共同等化器。 *)
Example p478_c26_not_coequalizer_0 :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase _0) → False :=
  arrow_fork_not_coequalizer _0 (fun x => match x with end).

(* ------------------------------------------------------------------------ *)
(** ** The components of the two split forks in Cat / ** 猫中两个分叉叉子的组件 *)

(* R8 *)
Fail Example p478_r8_split_law3_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (scoeq_law3 (@arrow_fork_split C T)) c) = id := eq_refl.

(* C27: the same at the direct split fork. / C27：在直接分叉处相同。 *)
Example p478_c27_split_direct_law3_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (scoeq_law3 (@arrow_fork_split_direct C T)) c) = id := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Restatements: components, the direct split fork, the Corollary / ** 重述：组成部分、直接分叉、推论 *)

(* C28: law 3 in StrictCat has the object component [eq_refl]. / C28：StrictCat 中的法则 3 的对象成分是 [eq_refl]。 *)
Example p478_c28_law3_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law3_strict C T) = fun _ => eq_refl := eq_refl.

(* C29: ... and so has law 4. / C29: ……法律4也是如此。 *)
Example p478_c29_law4_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law4_strict C T) = fun _ => eq_refl := eq_refl.

(* C30: law 3 in Cat, directly, has identity components. / C30：在猫中，定律3直接具有同一性成分。 *)
Example p478_c30_law3_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law3_direct C T) c) = id := eq_refl.

(* C31: ... and so has law 4. / C31：……法律4也是如此。 *)
Example p478_c31_law4_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law4_direct C T) c) = id := eq_refl.

(* C32: the direct split fork has e for its coequalizing arrow. / C32：直接分叉的等化箭头是 e。 *)
Example p478_c32_split_direct_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e (@arrow_fork_split_direct C T) = Erase C := eq_refl.

(* C33: ... s for the section of e. / C33: ... 用于 e 的部分。 *)
Example p478_c33_split_direct_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s (@arrow_fork_split_direct C T) = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

(* C34: ... and t for the section of ∂₀. / C34: ... 并且 t 用于 ∂₀ 的部分。 *)
Example p478_c34_split_direct_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t (@arrow_fork_split_direct C T) = @arrow_fork_t C T := eq_refl.

(* C35: the corollary out of StrictCat is the Corollary, applied. / C35：StrictCat 的推论是推论本身的应用。 *)
Example p478_c35_preserved_absolute_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  @arrow_fork_preserved_strict C T D F = @arrow_fork_absolute_strict C T D F
  := eq_refl.

(* C36: ... and so is the one out of Cat. / C36: ……外面的猫也是如此。 *)
Example p478_c36_preserved_absolute@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  @arrow_fork_preserved C T D F = @arrow_fork_absolute C T D F := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the target, by name / ** Guardian：目标的每一个常量，按名称 *)

Check @Category.Instance.Cat.SplitFork.arrow_fork_e_one.
Check @Category.Instance.Cat.SplitFork.arrow_fork_e_one_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_s_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_strict_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_strict_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_e.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_s.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_direct_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_direct_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_e.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_s.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_coequalizer_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_coequalizer.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved.
Check @Category.Instance.Cat.SplitFork.arrow_fork_absolute_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_absolute.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_absolute_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_absolute.
Check @Category.Instance.Cat.SplitFork.arrow_fork_not_coequalizer.
Check @Category.Instance.Cat.SplitFork.arrow_fork_not_coequalizer_0.
