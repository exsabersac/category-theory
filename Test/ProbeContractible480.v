(**
* Probe for contractible pairs (issue #480)

    Pins the measured boundaries of what #480 adds for Mac Lane, §VI.6,
    Exercise 2, book p. 150 (PDF p. 159), catalog item maclane:VI.6:ex2,
    read from the page image ("A parallel pair ∂₀, ∂₁ : a ⇉ b is said to
    be contractible (Beck) if there is an arrow t : b → a with ∂₀t = 1
    and ∂₁t∂₀ = ∂₁t∂₁").  The targets are Structure/Coequalizer/
    Contractible.v, whose header cites the refutations R1 and R2 and the
    controls here, and the one constant #480 adds to Structure/
    Coequalizer/Absolute.v, [contractible_coequalizer_absolute].  Each of
    the eleven [Example]s of Contractible.v has a control that restates
    it independently of the constant that states it (RESTATEMENTS,
    below).  Donors named by controls: #479's Instance/Grp/Coequalizer.v
    (C16 to C19, C24) and Instance/Presented/Cyclic.v (C20 to C23).

    THE IMPORT LIST.  Target by target in dependency order: the six
    [Require] lines of Contractible.v and that target; the nine lines
    Absolute.v adds and that target.  Under them [Print Libraries] in a
    scratch file loads 48 [Category] modules, exactly the set a [Require]
    of the two targets alone loads (compared by script).  The last two
    sections add, in turn and after every command above them, the nine
    lines Instance/Grp/Coequalizer.v (#479) adds to the list above, in
    its order, and that module; then the seven lines Instance/Presented/
    Cyclic.v adds and that module.  So nothing above each is elaborated
    under its imports.  A shorter import list is what makes a probe pass
    for no reason.

    DISCIPLINE.  Every negative other than the instrument is an
    [Example], never a [Check], so that an open evar cannot satisfy it.
    Each of the three refutation lines (the instrument, R1 and R2) was
    stripped of its refutation keyword in a copy of this WHOLE file, one
    at a time, compiled, and its error read; each copy stops inside the
    stripped command.  Each of the twenty-eight controls, wrapped in the
    refutation keyword in a copy of this WHOLE file, stops the build at
    that command with the message Rocq prints for a refutation whose
    command succeeds.  Quotations are Rocq 9.1.1's under this file's
    import list.

    KINDS.  Three refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE, the instrument (one), and
    CONVERSION, [eq_refl] refused with a "cannot unify" parenthetical,
    every statement being well typed (R1, R2: two).  CAUSES, read from
    the terms: R1 compares the split fork's s with the s of the round
    trip, which is the descent of g ∘ t through the coequalizer of Mac
    Lane's Lemma; Split.v's [Qed]-closed [split_coeq_desc] hides that
    descent, and transparent it is (g ∘ t) ∘ s, which is s only up to ≈.
    R2 compares the given proof of the second equation with the one (a)
    rebuilds from the laws of the split fork (b) builds.  Measured in a
    scratch file under the first import list above: with transparent
    copies of [split_coeq_desc] and of Mac Lane's Lemma the round trip's
    s is (g ∘ t) ∘ s at [eq_refl], and R1's statement is still refused;
    and the normal form of R2's left side ([Eval cbv]) names no constant
    but projections of the variables C, P and E, its head ([Eval hnf])
    the transitivity of C's own hom-setoid, where [contr_cofork P] is a
    projection of the variable P.  So neither refusal is the opacity of
    a proof.

    THE REFUSALS, with the parenthetical each stripped copy prints.
      The instrument (NAME-ABSENCE): The reference p480_absent_name was
        not found in the current environment.
      R1, (b) after (a), the split fork's s (controls C1 to C4):
        (cannot unify "scoeq_s (every_coequalizer_split S
        (split_coequalizer_is_coequalizer f g S))" and "scoeq_s S")
      R2, (a) after (b), the proof of the second equation (controls C5
        and C6): (cannot unify "contr_cofork
        (split_coequalizer_contractible (contractible_coequalizer_split
        P E))" and "contr_cofork P")

    RESTATEMENTS.  [split_coequalizer_contractible_t] C7,
    [contractible_coequalizer_split_obj] C8,
    [contractible_coequalizer_split_e] C9,
    [contractible_coequalizer_split_s] C10,
    [contractible_coequalizer_split_t] C11, [every_coequalizer_split_e]
    C12, [functor_preserves_contractible_t] C13,
    [every_coequalizer_split_obj] C25, [every_coequalizer_split_t] C26,
    [coequalizer_splits_idempotent_idem] C27 and
    [coequalizer_splits_idempotent_r] C28: eleven readbacks, each named
    once.  C1 to C3, C5 and C6 are the round trips at [eq_refl]; C4 is
    R1's twin at ≈.  C14 and C15 accept the two corollaries with the
    target's hom level strictly above C's, the universe claims of the
    targets' headers.  C16 to C19 are the boundary at Z/4 over {0, 2}:
    the common section of #479's [semidirect_reflexive] there is
    x ↦ ⟨x, 0⟩, #479's [semidirect_refl] (C16, at [eq_refl]), so Mac
    Lane's pair is reflexive (C17); #479's projection coequalizes it
    (C18); and by (b) it is not contractible (C19).  C24, C19's positive
    control: the pair at A₃ ◁ S₃ is contractible, by (a) at #479's split
    fork [S3_A3_Grp_split].  C20 to C23 are the boundary at Awodey's
    idempotent s ∘ s = s (Instance/Presented/Cyclic.v's [IdemCat]): the
    pair (1, s) is contracted by 1 ([idempotent_contractible], C20), has
    no coequalizer (C21, by [coequalizer_splits_idempotent] and the
    enumeration of the category's two arrows) and is not reflexive
    (C22); C23, C21's positive control, coequalizes (s, s) by 1.  The
    numbers follow the order in which the controls were written, not
    the file's.

    NOT PINNED HERE.  (a) [About] readbacks as such: the target headers'
    universe censuses.  (b) The transparent copies and the head normal
    form described above, made in a scratch file.  (c) The closure of the
    targets under [Print Assumptions]: the Makefile's print-assumptions
    gate names the same twenty-four names as the guard below.  (d) The
    absences the header records: an absence has no command.  (e) The
    reading of the book, from the page images.  (f) The closure of this
    file's twenty-eight constants under [Print Assumptions], C19, C21 and
    C22, which are theorems proved here and not refutations, among them:
    checked by hand, every one closed, and not gated.

    The guard block names the twenty-four constants of the targets, so
    that a rename breaks this file: the [def], [prf], [rec] and [proj]
    entries of Contractible.v's [.glob], which has no [Program]
    obligations, and the one constant #480 adds to Absolute.v.  Each is
    written fully qualified and with [@], so that no short name in scope
    can stand in for it.

--------
* 探查可收缩对（问题 #480）

固定#480为Mac Lane第§VI.6章添加的测量边界，练习2，书本第150页（PDF第159页），目录项maclane:VI.6:ex2，从页面图像读取（"若一对平行箭头∂₀, ∂₁ : a ⇉ b被称为可收缩（Beck），当存在箭头t : b → a，使得∂₀t = 1并且∂₁t∂₀ = ∂₁t∂₁"）。目标是Structure/Coequalizer/Contractible.v，其头部引用了反驳R1和R2及此处的控制，以及#480添加到Structure/Coequalizer/Absolute.v的常量[contractible_coequalizer_absolute]。Contractible.v中的每一个十一[Example]都有一个控制，能够独立于声明它的常量重新陈述它（下文的重述）。由控制命名的捐赠者：#479的Instance/Grp/Coequalizer.v（C16到C19，C24）和Instance/Presented/Cyclic.v（C20到C23）。

导入列表。按依赖顺序逐个目标：Contractible.v 的六行 [Require] 和该目标；Absolute.v 添加的九行以及该目标。在它们之下，[Print Libraries] 在一个临时文件中加载 48 个 [Category] 模块，正好是 [Require] 的两个目标单独加载的集合（通过脚本比较）。最后两个部分依次添加，在它们上面的每个命令之后，Instance/Grp/Coequalizer.v 的九行（#479）按其顺序添加到上述列表中，以及该模块；然后是 Instance/Presented/Cyclic.v 的七行添加以及该模块。因此，上面每个元素在其导入内容下都没有被展开。更短的导入列表会使探针无故通过。

纪律。除工具之外的每一个否定都是 [Example]，绝不是 [Check]，因此一个开放的 evar 无法满足它。三个反驳行（工具、R1 和 R2）中的每一个都在这个 WHOLE 文件的副本中被剥去其反驳关键字，一次剥去一个，编译后读取其错误；每个副本都在剥去的命令处停止。二十八个控制中的每一个，在这个 WHOLE 文件的副本中被反驳关键字包裹时，都在该命令处停止构建，并显示 Rocq 对命令成功的反驳所打印的消息。引文来自 Rocq 9.1.1，在此文件的导入列表下。

类型。三个反驳，被视为以反驳关键字开头的行：NAME-ABSENCE，工具（一），以及CONVERSION，[eq_refl] 拒绝，并带有“cannot unify”的括号，每个语句都是良好类型化的（R1，R2：两个）。原因，从项中读取：R1 将分叉叉的 s 与往返的 s 进行比较，往返是 g ∘ t 通过 Mac Lane 引理的共同等化器的下降；Split.v 的 [Qed]-封闭 [split_coeq_desc] 隐藏了该下降，而它透明的是 (g ∘ t) ∘ s，这只是 s 的近似（≈）。R2 将第二个方程的给定证明与从分叉叉定律 (b) 重建的证明 (a) 进行比较。
在上述第一个导入列表下的一个草稿文件中测量：用 [split_coeq_desc] 和 Mac Lane 引理的透明副本，往返的 s 在 [eq_refl] 处为 (g ∘ t) ∘ s，而 R1 的声明仍然被拒绝；并且 R2 左边的正规形式（[Eval cbv]）没有命名常量，而是变量 C、P 和 E 的投影，其头部（[Eval hnf]）是 C 自身同类集合的传递性，其中 [contr_cofork P] 是变量 P 的一个投影。因此，这两次拒绝都不是证明的不透明性。

拒绝，带括号的每个剥离副本打印。
      工具（NAME-ABSENCE）：在当前环境中未找到参考 p480_absent_name。
      R1，（b）在（a）之后，分叉的 s（控制 C1 到 C4）：
        （无法统一“scoeq_s（every_coequalizer_split S（split_coequalizer_is_coequalizer f g S））”和“scoeq_s S”）
      R2，（a）在（b）之后，第二个等式的证明（控制 C5 和 C6）：（无法统一“contr_cofork（split_coequalizer_contractible（contractible_coequalizer_split P E））”和“contr_cofork P”）

重述。[split_coequalizer_contractible_t] C7， [contractible_coequalizer_split_obj] C8， [contractible_coequalizer_split_e] C9， [contractible_coequalizer_split_s] C10， [contractible_coequalizer_split_t] C11，[every_coequalizer_split_e] C12，[functor_preserves_contractible_t] C13， [every_coequalizer_split_obj] C25，[every_coequalizer_split_t] C26， [coequalizer_splits_idempotent_idem] C27 和 [coequalizer_splits_idempotent_r] C28：十一条回读，每条只命名一次。C1 到 C3、C5 和 C6 是在 [eq_refl] 的往返；C4 是 R1 在 ≈ 的镜像。C14 和 C15 接受两条推论，前提是目标的同类级别严格高于 C，并考虑目标头部的全息声明。C16 到 C19 是 {0, 2} 上 Z/4 的边界：#479 的 [semidirect_reflexive] 的公共部分为 x ↦ ⟨x, 0⟩，#479 的 [semidirect_refl]（C16，在 [eq_refl]），因此 Mac Lane 的对是自反的（C17）；#479 的投影使其共等化（C18）；根据 (b) 它不可收缩（C19）。C24，C19 的正控制：在 A₃ ◁ S₃ 上的对是可收缩的，根据 (a) 在 #479 的分岔叉 [S3_A3_Grp_split]。
C20 到 C23 是 Awodey 的自幂元 s ∘ s = s（Instance/Presented/Cyclic.v 的 [IdemCat]）中的边界：对 (1, s) 被 1 收缩（[idempotent_contractible]，C20），没有共同余子（C21，根据 [coequalizer_splits_idempotent] 和该范畴两个箭头的枚举），也不是自反的（C22）；C23，C21 的正控制，通过 1 对 (s, s) 进行共同余化。这些数字遵循控制写入的顺序，而不是文件的顺序。

未在此固定。 (a) [About] 的回读如下：目标头的普查。 (b) 上述描述的透明副本和头部标准形式，在临时文件中制作。 (c) 在 [Print Assumptions] 下目标的闭包：Makefile 的 print-assumptions 门与下方守卫的二十四个名称相同。 (d) 头部记录的缺失：缺失没有命令。 (e) 从页面图像读取书籍。 (f) 在 [Print Assumptions] 下，本文件的二十八个常数的闭包，C19、C21 和 C22 是此处证明的定理，而非反驳，其间：手工检查，每个都已闭合，且未被门控。

守卫块为目标命名二十四个常量，因此重命名会破坏此文件：Contractible.v 的 [.glob] 条目的 [def]、[prf]、[rec] 和 [proj]，它没有 [Program] 义务，而唯一的常量 #480 添加到 Absolute.v。每个常量都是完全限定并带有 [@] 写出的，因此没有任何作用域内的简短名称可以代替它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Contractible.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Lift.
Require Import Category.Structure.Coequalizer.Absolute.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument / ** 乐器 *)

(* The instrument / 乐器 *)
Fail Check p480_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** (b) after (a): a split fork, through Mac Lane's Lemma, and back / ** (b) 在 (a) 之后：一个分裂叉，通过 Mac Lane 引理，然后回去 *)

Section FromSplit.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context (S : SplitCoequalizer f g).

(* C1: the object comes back on the nose. / C1：物体回到鼻子上。 *)
Example p480_c1_split_round_obj :
  scoeq_obj (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_obj S := eq_refl.

(* C2: so does e. / C2：e也是如此。 *)
Example p480_c2_split_round_e :
  scoeq_e (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_e S := eq_refl.

(* C3: so does t. / C3：t也是如此。 *)
Example p480_c3_split_round_t :
  scoeq_t (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_t S := eq_refl.

(* R1 *)
Fail Example p480_r1_split_round_s :
  scoeq_s (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_s S := eq_refl.

(* C4: s comes back up to ≈, by the uniqueness of the descent. / C4：s 因下落的唯一性而回升到 ≈。 *)
Definition p480_c4_split_round_s :
  scoeq_s (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    ≈ scoeq_s S :=
  contractible_coequalizer_split_s_unique (split_coequalizer_contractible S)
    (split_coequalizer_is_coequalizer f g S) (scoeq_s S) (scoeq_law4 S).

End FromSplit.

(* ------------------------------------------------------------------------ *)
(** ** (a) after (b): a contraction, through a coequalizer, and back / ** (a) 之后 (b)：通过等化器收缩，然后返回 *)

Section FromContractible.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context (P : ContractiblePair f g) {q : C} {e : y ~> q}.
Context (E : IsCoequalizer f g q e).

(* C5: the contraction comes back on the nose. / C5：收缩回到鼻子上。 *)
Example p480_c5_contr_round_t :
  contr_t (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_t P := eq_refl.

(* C6: so does the proof of the first equation. / C6: 第一条方程的证明也是如此。 *)
Example p480_c6_contr_round_section :
  contr_section
    (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_section P := eq_refl.

(* R2 *)
Fail Example p480_r2_contr_round_cofork :
  contr_cofork
    (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_cofork P := eq_refl.

End FromContractible.

(* ------------------------------------------------------------------------ *)
(** ** Restatements of the target's readbacks / ** 对目标回读的重述 *)

Section Readbacks.

Context {C : Category} {x y : C} {f g : x ~> y}.

(* C7: (a)'s t is the split fork's t. / C7: (a) 的 t 是分叉的 t。 *)
Example p480_c7_a_t (S : SplitCoequalizer f g) :
  contr_t (split_coequalizer_contractible S) = scoeq_t S := eq_refl.

Context {q : C} {e : y ~> q}.

(* C8: (b)'s object is the coequalizer's. / C8: (b) 的对象是共等化器的对象。 *)
Example p480_c8_b_obj (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_obj (contractible_coequalizer_split P E) = q := eq_refl.

(* C9: (b)'s e is the coequalizing arrow. / C9: (b) 的 e 是共同等化箭头。 *)
Example p480_c9_b_e (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_e (contractible_coequalizer_split P E) = e := eq_refl.

(* C10: (b)'s s is the descent of g ∘ t. / C10: (b) 的 s 是 g ∘ t 的下降。 *)
Example p480_c10_b_s (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_s (contractible_coequalizer_split P E)
    = unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) := eq_refl.

(* C11: (b)'s t is the contraction. / C11: (b)的 t 是收缩形式。 *)
Example p480_c11_b_t (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_t (contractible_coequalizer_split P E) = contr_t P := eq_refl.

(* C12: every coequalizer of a split pair is split on its own arrow. / C12: every coequalizer of a split pair is split on its own arrow. / C12：每个分裂对的余等化器在其自身箭头上是分裂的。 *)
Example p480_c12_every_e (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_e (every_coequalizer_split S E) = e := eq_refl.

(* C25: ... and on its own object. / C25: ...以及它自身的对象。 *)
Example p480_c25_every_obj (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_obj (every_coequalizer_split S E) = q := eq_refl.

(* C26: ... by the given split fork's t. / C26: ... 通过给定分叉的 t。 *)
Example p480_c26_every_t (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_t (every_coequalizer_split S E) = scoeq_t S := eq_refl.

End Readbacks.

(* C13: a functor's image of a contraction is contracted by F t. / C13：函子对收缩的像被 F t 收缩。 *)
Example p480_c13_functor_t {C D : Category} (F : C ⟶ D) {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) :
  contr_t (functor_preserves_contractible F f g P) = fmap[F] (contr_t P)
  := eq_refl.

Section Idempotent.

Context {C : Category} {x : C} (i : x ~> x) (I : Idempotent i).
Context {q : C} {r : x ~> q} (E : IsCoequalizer id i q r).

(* C27: a coequalizer of (1, i) splits i itself ... / C27：（1, i）的共同等化器本身分裂 i ... *)
Example p480_c27_idem_idem :
  @split_idem C x q (coequalizer_splits_idempotent i I E) = i := eq_refl.

(* C28: ... through the coequalizer r. / C28: ...通过等化器 r。 *)
Example p480_c28_idem_r :
  @split_idem_r C x q (coequalizer_splits_idempotent i I E) = r := eq_refl.

End Idempotent.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the targets' hom levels may lie strictly above C's / ** 宇宙：目标的霍姆水平可能严格高于C的 *)

(* C14: absoluteness at a target hom level strictly above C's. / C14：在严格高于C的目标同调级别上的绝对性。 *)
Definition p480_c14_absolute_above@{co ch xo xh + | ch < xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e :=
  contractible_coequalizer_absolute P E.

(* C15: a functor into a category whose hom level is strictly above C's. / C15：一个函子，映射到其同态层次严格高于C的范畴。 *)
Definition p480_c15_functor_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} {f g : x ~> y} (P : ContractiblePair f g) :
  ContractiblePair (fmap[F] f) (fmap[F] g) :=
  functor_preserves_contractible F f g P.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the targets, by name / ** Guardian：按名称列出目标的每个常量 *)

Check @Category.Structure.Coequalizer.Contractible.ContractiblePair.
Check @Category.Structure.Coequalizer.Contractible.contr_t.
Check @Category.Structure.Coequalizer.Contractible.contr_section.
Check @Category.Structure.Coequalizer.Contractible.contr_cofork.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_contractible.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_contractible_t.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_obj.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_e.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_s.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_t.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_s_unique.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_obj.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_e.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_t.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_iff_contractible.
Check @Category.Structure.Coequalizer.Contractible.idempotent_contractible.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent_idem.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent_r.
Check @Category.Structure.Coequalizer.Contractible.functor_preserves_contractible.
Check @Category.Structure.Coequalizer.Contractible.functor_preserves_contractible_t.
Check @Category.Structure.Coequalizer.Absolute.contractible_coequalizer_absolute.

(* ------------------------------------------------------------------------ *)
(** ** A reflexive pair with a coequalizer that is not contractible / ** 一个具有非可收缩共同化子的自反对 *)

(*
Required here, after every other command, so that the sections above
   are elaborated under the targets' import lists alone: the lines
   Instance/Grp/Coequalizer.v adds to them, in its order, and that
   module.

--------
在这里，在每个其他命令之后要求，以便上面的各部分仅在目标的导入列表下进行详细说明：行 Instance/Grp/Coequalizer.v 按其顺序添加到它们中，以及该模块。
*)
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Coequalizer.

(*
C16: the common section of #479's reflexive pair at Z/4 over {0, 2} is
   #479's [semidirect_refl], x ↦ ⟨x, 0⟩, 0 being the subgroup's unit.

--------
C16：#479 的自反对在 Z/4 上对 {0, 2} 的公共部分是 #479 的 [semidirect_refl]，x ↦ ⟨x, 0⟩，其中 0 是子群的单位元。
*)
Example p480_c16_z4_section (a : carrier Z4) :
  grp_map (refl_section (semidirect_reflexive Z4_two)) a
    = (a, snd (sdp_unit Z4_two)) := eq_refl.

(* C17: so Mac Lane's pair is reflexive, by #479's [semidirect_reflexive]. / C17：所以 Mac Lane 的对是自反的，根据 #479 的 [semidirect_reflexive]。 *)
Definition p480_c17_z4_reflexive :
  ReflexivePair (semidirect_d0 Z4_two) (semidirect_d1 Z4_two) :=
  semidirect_reflexive Z4_two.

(* C18: it has a coequalizer, the projection onto Z/4 / {0, 2} (#479). / C18：它有一个余等化器，投影到 Z/4 / {0, 2} (#479)。 *)
Definition p480_c18_z4_coequalizer :
  IsCoequalizer (semidirect_d0 Z4_two) (semidirect_d1 Z4_two)
    (QuotientGrp Z4_two) (quot_proj Z4_two) :=
  quot_proj_IsCoequalizer Z4_two.

(*
C19: and it is not contractible: by (b) its coequalizer would split,
   which #479 refutes.

--------
C19：并且它不可收缩：根据 (b) 它的等化器会分裂，这与 #479 相矛盾。
*)
Definition p480_c19_z4_not_contractible :
  ContractiblePair (semidirect_d0 Z4_two) (semidirect_d1 Z4_two) → False :=
  fun P => Z4_two_not_split_in_Grp
             (contractible_coequalizer_split P p480_c18_z4_coequalizer).

(*
C24: C19's positive control: the pair at A₃ ◁ S₃, which #479 splits in
   Grp, is contractible, by (a).

--------
C24：C19的阳性对照：位于A₃ ◁ S₃的那一对，#479在Grp中拆分，是可收缩的，由(a)。
*)
Definition p480_c24_a3_contractible :
  ContractiblePair (semidirect_d0 A3) (semidirect_d1 A3) :=
  split_coequalizer_contractible S3_A3_Grp_split.

(* ------------------------------------------------------------------------ *)
(** ** A contractible pair with no coequalizer, and not reflexive / ** 一个没有余等的可缩对，并且不是自反的 *)

(*
Required here, after every other command; the lines
   Instance/Presented/Cyclic.v adds to the lists above, and that
   module.

--------
这里需要，在每个其他命令之后；Instance/Presented/Cyclic.v 中的行添加到上面的列表，以及该模块。
*)
Require Import Category.Lib.TList.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Construction.Deloop.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Presented.Cyclic.

(*
C20: in Awodey's one-object category of the idempotent s ∘ s = s,
   the pair (1, s) is contracted by 1.

--------
C20：在 Awodey 的单对象幂等算子类别 s ∘ s = s 中，配对 (1, s) 被 1 缩约。
*)
Definition p480_c20_idem_contractible :
  @ContractiblePair IdemCat ttt ttt id (spath 1) :=
  @idempotent_contractible IdemCat ttt (spath 1)
    (@Build_Idempotent IdemCat ttt (spath 1) idem_rel).

(*
C21: and it has no coequalizer: one would split s through it, with
   e ∘ s' ≈ 1 and s' ∘ e ≈ s, and the arrows are 1 and s alone.

--------
C21：它没有余等化器：人们会通过它拆分 s，满足 e ∘ s' ≈ 1 和 s' ∘ e ≈ s，并且箭头只有 1 和 s 本身。
*)
Theorem p480_c21_idem_no_coequalizer (q : IdemCat) (e : ttt ~{IdemCat}~> q) :
  @IsCoequalizer IdemCat ttt ttt id (spath 1) q e → False.
Proof.
  destruct q.
  intro E.
  pose (S := @coequalizer_splits_idempotent IdemCat ttt (spath 1)
               (@Build_Idempotent IdemCat ttt (spath 1) idem_rel) ttt e E).
  pose proof (@split_idem_rs _ _ _ S) as L2.
  pose proof (@split_idem_sr _ _ _ S) as L4.
  change (e ∘ @split_idem_s _ _ _ S ≈ id) in L2.
  change (@split_idem_s _ _ _ S ∘ e ≈ spath 1) in L4.
  destruct (idem_exhaust e) as [re [Hre He]].
  destruct (idem_exhaust (@split_idem_s _ _ _ S)) as [rs [Hrs Hs]].
  rewrite He, Hs in L2.
  rewrite He, Hs in L4.
  destruct re as [|[|re]]; [ | | lia ];
  destruct rs as [|[|rs]]; [ | | lia | | | lia ];
  [ apply (rho_nf_of_spath_eq 1 1 0 1) in L4
  | apply (rho_nf_of_spath_eq 1 1 1 0) in L2
  | apply (rho_nf_of_spath_eq 1 1 1 0) in L2
  | apply (rho_nf_of_spath_eq 1 1 2 0) in L2 ];
  discriminate.
Qed.

(*
C22: nor is (1, s) reflexive: a common section r would have
   s ∘ r ≈ 1, and the arrows are 1 and s alone.

--------
C22：也不是 (1, s) 自反的：一个常见的截面 r 会有 s ∘ r ≈ 1，并且箭头只有 1 和 s。
*)
Theorem p480_c22_idem_not_reflexive :
  @ReflexivePair IdemCat ttt ttt id (spath 1) → False.
Proof.
  intros R.
  pose proof (refl_section_f R) as Hf.
  pose proof (refl_section_g R) as Hg.
  destruct (idem_exhaust (refl_section R)) as [rr [Hrr Hr]].
  rewrite Hr in Hf, Hg.
  destruct rr as [|[|rr]]; [ | | lia ];
  [ apply (rho_nf_of_spath_eq 1 1 1 0) in Hg
  | apply (rho_nf_of_spath_eq 1 1 1 0) in Hf ];
  discriminate.
Qed.

(* C23: C21's positive control: (s, s) has a coequalizer there, 1. / C23：C21 的正对照：（s，s）在那里有一个余等化子，1。 *)
Definition p480_c23_idem_ss_coequalizer :
  @IsCoequalizer IdemCat ttt ttt (spath 1) (spath 1) ttt id.
Proof.
  unshelve econstructor.
  - reflexivity.
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_right.
    + intros v Hv.
      rewrite <- Hv.
      rewrite id_right.
      reflexivity.
Defined.
