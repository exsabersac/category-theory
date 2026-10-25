Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Adj.Bicategory.

Generalizable All Variables.

(** * Probe for Instance/Adj/Bicategory.v / * 探针用于实例/形容词/双类别.v *)

(*
Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.8,
   book p. 104 (PDF p. 113): Theorem 2, display (1), Exercise 1 and the
   closing remark; catalog ids maclane:IV.8:thm2, maclane:IV.8:ex1,
   maclane:IV.8:remark1.  Those passages are quoted verbatim in the header
   of Instance/Adj/Bicategory.v and are not repeated here.

   This file guards the strict claims of that header.  Every statement
   below that is asserted to be refuted has been STRIPPED into its own
   scratch copy carrying this file's whole prefix, compiled ALONE, and its
   complete error read; under this repo's coqc a passing [Fail] prints
   nothing, so a whole-file rc=0 alone would establish only THAT each
   command does not typecheck and never WHY.  Each negative is classified
   by the error TEXT, not by expectation:

     CONVERSION  - the message carries a "cannot unify A and B" clause and
                   no universe clause.
     TYPING      - a plain "The term T has type X while it is expected to
                   have type Y"; NO "cannot unify", no universe clause.
     FORMABILITY - "(universe inconsistency: Cannot enforce ...)", naming
                   the levels the enclosing section declares.

   ** TALLY

   27 [Fail] commands = 1 instrument check + 26 negatives, in three kinds:
   ELEVEN conversion (N4-N11, N13-N15), FOUR typing (N1-N3, N12) and ELEVEN
   formability (N16-N26).

   ** ONE KIND DIVERGES FROM THE BRIEF'S EXPECTATION

   N15 -- feeding [Build_Bicategory'] the arguments [Adj_Bicategory] feeds
   to the raw [Build_Bicategory] -- was expected to be a plain typing
   mismatch; the Core report (§M6g) assigns it no kind and quotes the
   message in a form that stops after the expected type.  Stripped and read
   WHOLE here it carries a trailing "(cannot unify ...)" clause past where
   that quotation ends, so it is CONVERSION, not TYPING.  Two scope notes.
   What cannot unify are two TYPES -- a functor type against the
   eta-expanded record spelling of the same two categories -- rather than
   two inhabitants of one type, so it sits at the boundary of the two
   kinds; and [Build_Bicategory'] takes TWENTY arguments where
   [Build_Bicategory] takes twenty-one, since it derives [comp_assoc_sym]
   by [symmetry], so the negative passes the twenty-one minus that one.
   Deriving it is exactly what breaks record eta and is what the negative
   exhibits.

   ** ONE NEGATIVE MEASURES ITS ARGUMENT AND NOT ITS SUBJECT

   N19 names [ConjPair], and the character offsets in its error put the
   refusal on the [Cu] of its [AdjObj Cu Du] binder, not on [ConjPair].
   [ConjPair]'s two object arguments are [AdjObj]s, so it CANNOT be tested
   apart from [AdjObj], which in turn contains an [Adjunction] and cannot
   be tested apart from that: whether [ConjPair] identifies anything of its
   own is UNKNOWN, not refuted.  This is the trap recorded for
   [MonoidObject] under issue #340, and it is stated here rather than
   glossed.  N17 and N18 are in the same position with respect to
   [Adjunction].

   ** THE VERBATIM ERROR TAILS

   (The tails transcribe the unicode of the real messages as ASCII -- [o]
   for the composition circle, [-|] for the adjunction sign, [==>] for the
   transformation arrow, [(X)] for the product of categories and [-->] for
   the functor arrow -- so that this comment stays free of the glyphs the
   sources use; the shape of every message is otherwise character for
   character what coqc printed.)

   N1  TYPING
     The term "Adjunction_Compose Aa (Adjunction_Compose Bb Cc)" has type
     "H o G o F -| U o (V o W)"
     while it is expected to have type "H o (G o F) -| U o V o W".
   N2  TYPING
     The term "Adjunction_Compose Aa Adjunction_Id" has type
     "Id[C] o F -| U o Id[C]"
     while it is expected to have type "F -| U".
   N3  TYPING
     The term "Adjunction_Compose Adjunction_Id Aa" has type
     "F o Id[D] -| Id[D] o U"
     while it is expected to have type "F -| U".
   N4  CONVERSION
     The term "eq_refl" has type "H o G o F = H o G o F"
     while it is expected to have type "H o G o F = H o (G o F)"
     (cannot unify "H o G o F" and "H o (G o F)").
   N5  CONVERSION
     (cannot unify "Id[C] o F" and "F").
   N6  CONVERSION
     (cannot unify "F o Id[D]" and "F").
   N7  CONVERSION
     (cannot unify "adjobj_hcompose (AdjIdObj y) a" and "a").
   N8  CONVERSION
     (cannot unify "adjobj_hcompose a (AdjIdObj x)" and "a").
   N9  CONVERSION
     (cannot unify "adjobj_hcompose (adjobj_hcompose c b) a" and
      "adjobj_hcompose c (adjobj_hcompose b a)").
   N10 CONVERSION
     (cannot unify "adjobj_left (adjobj_hcompose (AdjIdObj y) a)" and
      "adjobj_left a").
   N11 CONVERSION
     (cannot unify
      "paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e" and
      "nat_hcompose t tb e").
   N12 TYPING
     The term "paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)"
     has type "G' o F' o Id[D] ==> Id[E] o (G o F)"
     while it is expected to have type "G' o F' ==> G o F".
   N13 CONVERSION
     The term "eq_refl" has type
     "adjunction (mA o mB) = adjunction (mA o mB)"
     while it is expected to have type
     "adjunction (mA o mB) =
      Adjunction_Compose (adjunction mA) (adjunction mB)"
     (cannot unify "adjunction (mA o mB)" and
      "Adjunction_Compose (adjunction mA) (adjunction mB)").
   N14 CONVERSION
     (cannot unify "adjobj_of_morphism (morphism_of_adjobj xo)" and "xo").
   N15 CONVERSION
     The term "@Adj_Hcompose" has type
     "forall x y z : Category, (Adj y z (X) Adj x y) --> Adj x z"
     while it is expected to have type
     "forall x y z : Category, ({| obj := obj[Adj y z]; ...;
      comp_assoc_sym := fun ... => symmetry (comp_assoc f g h) |}
      (X) {| ... |}) --> {| ... |}"
     (cannot unify "(Adj y z (X) Adj x y) --> Adj x z" and
      "({| ... |} (X) {| ... |}) --> {| ... |}").
     [the two record displays are the ten [Adj] projections plus the
      [symmetry]-derived [comp_assoc_sym], written out in full]
   N16 FORMABILITY
     The term "Fq" has type "@Functor@{co ch cp co ch cp} Du Cu"
     while it is expected to have type "@Functor@{...} ?D ?C"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N17 FORMABILITY
     The term "Cu" has type "Category@{co ch cp}"
     while it is expected to have type "Category@{... h h}"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N18 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N19 FORMABILITY  [same shape as N17, refusing at the [Cu] of [AdjObj]]
   N20 FORMABILITY
     The term "Gq" has type "@Functor@{co ch cp co ch cp} Du Eu"
     while it is expected to have type "@Functor@{...} ?D ?E"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N21 FORMABILITY
     The term "aa" has type "@Transform@{co ch cp co ch cp} Du Eu J1 K1"
     while it is expected to have type "@Transform@{...} ?D ?E ?J ?K"
     (universe inconsistency: Cannot enforce cp = ch because ch < cp).
   N22 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N23 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N24 FORMABILITY  [same shape as N17, refusing at [Cu]]
   N25 FORMABILITY
     The term "Aq" has type "Category@{ao ah ah}"
     while it is expected to have type "Category@{...}"
     (universe inconsistency: Cannot enforce ah = ... because ah < bh
      <= ...).
   N26 FORMABILITY
     The term "Bq" has type "Category@{bo bh bh}"
     while it is expected to have type "Category@{... ah ah}"
     (universe inconsistency: Cannot enforce bh = ah because ah < bh).

   ** WHAT EACH NEGATIVE PAIRS WITH

   Every negative sits beside a positive control that DOES hold, so that
   each guard measures a boundary rather than an absence.

   N1-N3 pair with two [Check]s each, of the very composites the equations
   would relate, so the refusal is of the EQUATION and not of either side.
   N4-N6 pair with [c399_n4a], [c399_n4b], [c399_n56a] and [c399_n56b]:
   [fobj] and [fmap] agree at [eq_refl] on the two bracketings, and [fobj]
   agrees on both unit paddings, so none of the three refusals is in
   [fobj].  That they are in [Compose]'s three LAW fields is the fact
   Adjunction/Pare.v and Instance/Cat/Bicategory.v already record -- it
   turns on [Functor] having primitive projections with eta and is NOT
   measured here.  N7-N10 pair with [c399_n7] to [c399_n10], the target's
   own four [eq_refl] readbacks ([hunit_left_obj_left] and its three
   siblings), which say exactly what the padded 1-cell's two adjoints ARE.
   N11 pairs with [c399_n11], the target's [routeb_tau], the same statement
   at [~=]; N12 pairs with [c399_n12], the target's [routeb_sigma], the
   same statement one level down at a COMPONENT and at [eq_refl] -- so the
   two together say that the sigma leg is the Godement product
   componentwise and the tau leg is not.  N13 pairs with two [Check]s, and
   its own error fires at [eq_refl] rather than at an argument, so both
   sides do elaborate at one and the same type; and with [c399_n13a],
   Adjunction/Compose.v's own [Adjunction_Compose_adj_comp_to], the
   positive half already in tree: the two constructions have definitionally
   equal transposes.  N14 pairs with [c399_n14], the target's
   [adjoints_round_record], the RECORD round trip at [eq_refl]; that what
   separates the two is stdlib [sigT]'s missing eta is the target header's
   attribution and is not measured here.  N15 pairs with
   [Check @Adj_Bicategory], the raw-constructor build that does typecheck.
   N16-N24 pair with five commands accepted at the very levels that refuse
   them -- a hom-set, an identity, a functor in each direction and a
   [Transform] between two functors.  N20 refutes [Compose] ALONE, with no
   adjunction and no transformation anywhere in the command, and that
   [Transform] control is accepted; so N21's refusal is ATTRIBUTED to the
   [Compose] in [nat_hcompose]'s result type, an attribution and not an
   isolation, since no [Compose]-free variant of it was compiled.  N25 and
   N26 pair with four commands accepted with the two hom levels declared
   strictly apart, so what N26 attributes to [AdjObj] is the presence of
   functors in BOTH directions and not the adjunction condition.

   ** RENAME SIMULATION

   FIFTEEN constants OF THE TARGET MODULE are named inside a negative:
   [AdjIdObj], [adjobj_hcompose], [conj_padL], [conj_padR],
   [adjobj_of_morphism], [morphism_of_adjobj], [Adj_Hcompose],
   [Adj_hunit_left], [Adj_hunit_right], [Adj_hassoc],
   [Adj_hunit_left_natural], [Adj_hunit_right_natural],
   [Adj_hassoc_natural], [Adj_triangle] and [Adj_pentagon].  (The other
   identifiers a negative names belong to donor modules, not to the target,
   and are guarded by [Check] all the same.)  Each was renamed ONE AT A
   TIME in a SCRATCH COPY of Instance/Adj/Bicategory.v -- never in place --
   compiled under [-Q ... Scratch]; a copy of this file requiring that
   scratch module instead of the library one was then compiled.  ALL
   FIFTEEN broke it, every one at a [Check] line of the guard block and
   NONE inside a [Fail]:

     AdjIdObj                  Check @AdjIdObj.
     adjobj_hcompose           Check @adjobj_hcompose.
     conj_padL                 Check @conj_padL.
     conj_padR                 Check @conj_padR.
     adjobj_of_morphism        Check @adjobj_of_morphism.
     morphism_of_adjobj        Check @morphism_of_adjobj.
     Adj_Hcompose              Check @Adj_Hcompose.
     Adj_hunit_left            Check @Adj_hunit_left.
     Adj_hunit_right           Check @Adj_hunit_right.
     Adj_hassoc                Check @Adj_hassoc.
     Adj_hunit_left_natural    Check @Adj_hunit_left_natural.
     Adj_hunit_right_natural   Check @Adj_hunit_right_natural.
     Adj_hassoc_natural        Check @Adj_hassoc_natural.
     Adj_triangle              Check @Adj_triangle.
     Adj_pentagon              Check @Adj_pentagon.

   So 15/15, with zero vacuous guards.  (Renaming a [Program Definition]
   must also rename its obligations, whose names are that constant's name
   with [_obligation_n] appended; a whole-file substitution does so.)

   ** GUARD COVERAGE, measured mechanically

   Comments stripped, the file split into commands at a period followed by
   whitespace: 183 commands, of which 27 begin with [Fail]; they mention
   118 distinct identifiers, of which 93 also occur in a command that is
   NOT a [Fail].  The twenty-five that do not are, exhaustively: the two
   keywords [Fail] and [Definition]; the seven variables bound inside the
   negatives themselves ([F1], [G1], [J1], [K1], [Uq], [aa] and [bb]); the
   fifteen names of the refuted declarations ([n1]-[n15]), which never
   enter the environment because the commands that would have declared them
   do not typecheck; and [p399_no_such_constant_anywhere], the instrument's
   deliberately absent name.  No CONSTANT that a negative names is
   unguarded.

   ** make todo

   The repo's [todo] target greps every [.v] file, case-insensitively and
   with no word boundary, for its five alternatives: [Fail], abort,
   undefined, jww and, between them, the hole-closing tactic name, which
   this comment does not spell because the aborted-sketch gate would count
   it.  This file contributes 41 such lines: the 27 [Fail] commands and 14
   lines of the prose above.  Instance/Adj/Bicategory.v contributes ZERO,
   which is the reason every refutation lives here rather than there.

   ** WHAT THIS FILE DOES NOT DO

   It proves nothing new.  It contains no proof hole of any kind, no
   hole-closing tactic, no [Axiom], no [Parameter] and no [Abort]; every
   positive control is a term, never a tactic script, so nothing here can
   drift by a change in the automation.  It does not measure universes
   beyond the two donor sections, does not count constants, does not
   compare the two Theorem-2 proof terms, and takes no position on the
   target header's prose.

--------
Mac Lane，《为工作数学家准备的范畴》，第2版，第IV.8节，书本第104页（PDF第113页）：定理2，公式(1)，练习1及结语；目录ID maclane:IV.8:thm2, maclane:IV.8:ex1, maclane:IV.8:remark1。那些段落在 Instance/Adj/Bicategory.v 的开头已逐字引用，这里不再重复。

此文件保护该头文件的严格声明。下面每个被断言为被驳斥的声明都被剥离到它自己的草稿副本中，携带此文件的整个前缀，单独编译，并读取其完整错误；在此仓库的 coqc 下，成功的 [Fail] 不打印任何内容，因此仅整个文件的 rc=0 只能证明每个命令不会类型检查，而永远不能说明原因。每个负例是根据错误文本而分类的，而不是根据预期：

转换 - 消息包含“无法统一 A 和 B”的条款，并且没有宇宙条款。
类型 - 一个普通的“项 T 的类型是 X，而期望的类型是 Y”；没有“无法统一”，没有宇宙条款。
可形成性 - “（宇宙不一致：无法强制执行…）”，命名包含该部分声明的级别。

** 计数

27 个 [Fail] 指令 = 1 个仪器检查 + 26 个阴性，共三类：十一项转换（N4-N11, N13-N15）、四项打字（N1-N3, N12）和十一项成形性（N16-N26）。

** 一种偏离了简报的预期

N15 —— 将 [Build_Bicategory'] 传递的参数 [Adj_Bicategory] 传递给原始 [Build_Bicategory] —— 原本预计只是一个简单的类型不匹配；Core 报告（§M6g）没有为它指定种类，并以在预期类型处停止的形式引用了该消息。 在这里剥离并完整读取时，它在该引用结束后带有尾随的“(cannot unify ...)”子句，因此这是转换（CONVERSION），而不是类型（TYPING）。两条范围说明。 不能统一的是两种类型 —— 一个函子类型与同样两个类别的 eta 扩展记录拼写 —— 而不是位于同一类型的两个元素，因此它处于两种种类的边界处；并且 [Build_Bicategory'] 接受二十个参数，而 [Build_Bicategory] 接受二十一个参数，因为它通过 [symmetry] 推导 [comp_assoc_sym]，因此负数通过二十一个减那个一个。正是推导它破坏了记录 eta，并且负数表现出来的也正是这个问题。

** 否定衡量的是它的论点，而不是它的主题

N19 名称为 [ConjPair]，其错误中的字符偏移将拒绝放在其 [AdjObj Cu Du] 绑定器的 [Cu] 上，而不是在 [ConjPair] 上。[ConjPair] 的两个对象参数是 [AdjObj]，因此无法与 [AdjObj] 分开测试，而 [AdjObj] 又包含一个 [Adjunction]，并且无法与其分开测试：[ConjPair] 是否识别其自身的任何内容是未知的，并未被否定。这是在问题 #340 下为 [MonoidObject] 记录的陷阱，这里陈述而非解释。N17 和 N18 在 [Adjunction] 上具有相同的位置。

**逐字错误尾

（尾部将真实消息的 Unicode 转写为 ASCII —— 组合圆圈为 [o]，附加符号为 [-|]，变换箭头为 [==>]，范畴的积为 [(X)]，函子箭头为 [-->] —— 这样此注释就不会包含来源使用的字形；每条消息的形状除外，仍然是 coqc 打印的逐字符内容。）

N1 类型检查
     项 "Adjunction_Compose Aa (Adjunction_Compose Bb Cc)" 的类型为
     "H o G o F -| U o (V o W)"
     而预期类型为 "H o (G o F) -| U o V o W"。 
N2 类型检查
     项 "Adjunction_Compose Aa Adjunction_Id" 的类型为
     "Id[C] o F -| U o Id[C]"
     而预期类型为 "F -| U"。 
N3 类型检查
     项 "Adjunction_Compose Adjunction_Id Aa" 的类型为
     "F o Id[D] -| Id[D] o U"
     而预期类型为 "F -| U"。 
N4 转换
     项 "eq_refl" 的类型为 "H o G o F = H o G o F"
     而预期类型为 "H o G o F = H o (G o F)"
     （无法统一 "H o G o F" 和 "H o (G o F)"）。 
N5 转换
     （无法统一 "Id[C] o F" 和 "F"）。 
N6 转换
     （无法统一 "F o Id[D]" 和 "F"）。
N7 转换
     （无法统一 "adjobj_hcompose (AdjIdObj y) a" 和 "a"）。 N8 转换
     （无法统一 "adjobj_hcompose a (AdjIdObj x)" 和 "a"）。 N9 转换
     （无法统一 "adjobj_hcompose (adjobj_hcompose c b) a" 和
      "adjobj_hcompose c (adjobj_hcompose b a)"）。 N10 转换
     （无法统一 "adjobj_left (adjobj_hcompose (AdjIdObj y) a)" 和
      "adjobj_left a"）。 N11 转换
     （无法统一
      "paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e" 和
      "nat_hcompose t tb e"）。 N12 类型检查
     术语 "paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb)" 的类型为 "G' o F' o Id[D] ==> Id[E] o (G o F)"
     而预期的类型为 "G' o F' ==> G o F"。
N13 转换
     术语 “eq_refl” 的类型为
     “adjunction (mA o mB) = adjunction (mA o mB)”
     而期望的类型为
     “adjunction (mA o mB) =
      Adjunction_Compose (adjunction mA) (adjunction mB)”
     （无法统一 “adjunction (mA o mB)” 和
      “Adjunction_Compose (adjunction mA) (adjunction mB)”）。 N14 转换
     （无法统一 “adjobj_of_morphism (morphism_of_adjobj xo)” 和 “xo”）。 N15 转换
     术语 “@Adj_Hcompose” 的类型为
     “forall x y z : Category, (Adj y z (X) Adj x y) --> Adj x z”
     而期望的类型为
     “forall x y z : Category, ({| obj := obj[Adj y z]; ...;
      comp_assoc_sym := fun ... => symmetry (comp_assoc f g h) |}
      (X) {| ... |}) --> {| ... |}”
     （无法统一 “(Adj y z (X) Adj x y) --> Adj x z” 和
      “({| ... |} (X) {| ... |}) --> {| ... |}”）。
[the two record displays are the ten [Adj] 投影加上 [symmetry] 衍生的 [comp_assoc_sym]，完整写出]
   N16 可形成性
     术语“Fq”的类型为“@Functor@{co ch cp co ch cp} Du Cu”，
     而预期类型为“@Functor@{...} ?D ?C”
     （宇宙不一致：无法强制 cp = ch 因为 ch < cp）。
   N17 可形成性
     术语“Cu”的类型为“Category@{co ch cp}”，
     而预期类型为“Category@{... h h}”
     （宇宙不一致：无法强制 cp = ch 因为 ch < cp）。
   N18 可形成性  [same shape as N17, refusing at [Cu]]
   N19 可形成性  [same shape as N17, refusing at the [Cu] 属于 [AdjObj]]
   N20 可形成性
     术语“Gq”的类型为“@Functor@{co ch cp co ch cp} Du Eu”，
     而预期类型为“@Functor@{...} ?D ?E”
     （宇宙不一致：无法强制 cp = ch 因为 ch < cp）。
N21 可形成性
     术语“aa”的类型为“@Transform@{co ch cp co ch cp} Du Eu J1 K1”，
     而预期类型为“@Transform@{...} ?D ?E ?J ?K”
     （宇宙不一致：无法强制 cp = ch，因为 ch < cp）。N22 可形成性  [same shape as N17, refusing at [Cu]]
   N23 可形成性  [same shape as N17, refusing at [Cu]]
   N24 可形成性  [same shape as N17, refusing at [Cu]]
   N25 可形成性
     术语“Aq”的类型为“Category@{ao ah ah}”，
     而预期类型为“Category@{...}”
     （宇宙不一致：无法强制 ah = ...，因为 ah < bh
      <= ...）。N26 可形成性
     术语“Bq”的类型为“Category@{bo bh bh}”，
     而预期类型为“Category@{... ah ah}”
     （宇宙不一致：无法强制 bh = ah，因为 ah < bh）。

** 每个否定词的搭配

每个阴性样本都放在一个确实有效的阳性对照旁边，因此每个守护样本测量的是一个界限，而不是缺失。

N1-N3 各与两个 [Check] 配对，这些是方程将要关联的复合体，因此拒绝的是方程本身，而不是任一方。N4-N6 与 [c399_n4a]、[c399_n4b]、[c399_n56a] 和 [c399_n56b] 配对：[fobj] 和 [fmap] 在 [eq_refl] 上对两个括号表示一致，[fobj] 在两个单元填充上也一致，因此这三个拒绝都不在 [fobj] 中。它们处于 [Compose] 的三个 LAW 字段中，这是 Adjunction/Pare.v 和 Instance/Cat/Bicategory.v 已经记录的事实——它取决于 [Functor] 拥有带 eta 的原始投影，这里未进行测量。N7-N10 与 [c399_n7] 到 [c399_n10] 配对，对应目标自身的四个 [eq_refl] 回读（[hunit_left_obj_left] 及其三个兄弟），它们准确地说明了填充 1-单元的两个伴随是什么。
N11 与 [c399_n11] 配对，目标的 [routeb_tau]，在 [~=] 的相同声明；N12 与 [c399_n12] 配对，目标的 [routeb_sigma]，在 COMPONENT 和 [eq_refl] 的相同声明下降一级——因此两者一起表示 sigma 分支是按分量的 Godement 乘积，而 tau 分支不是。N13 与两个 [Check] 配对，其自身的错误在 [eq_refl] 触发，而不是在参数处，因此两边都在同一个类型上展开；并且在 [c399_n13a] 中，Adjunction/Compose.v 自身的 [Adjunction_Compose_adj_comp_to]，树中已经存在正半部分：这两种构造具有定义上相等的转置。N14 与 [c399_n14] 配对，目标的 [adjoints_round_record]，RECORD 在 [eq_refl] 的往返；将两者区分开的是 stdlib [sigT] 缺少的 eta 是目标头的归属，这在此处未被衡量。
N15 与 [Check @Adj_Bicategory] 配对，即进行类型检查的原始构造器版本。N16-N24 与五个在拒绝它们的级别上被接受的命令配对——一个同态集、一个恒等式、每个方向的一个函子以及两个函子之间的 [Transform]。N20 单独驳斥 [Compose]，在命令中没有伴随也没有变换，并且该 [Transform] 控制被接受；因此 N21 的拒绝被归因于 [nat_hcompose] 结果类型中的 [Compose]，这是一种归因而非孤立，因为没有编译出其不含 [Compose] 的变体。N25 和 N26 与四个命令配对，这些命令在严格分开的两个同态级别下被接受，因此 N26 归因于 [AdjObj] 的是双向存在的函子，而不是伴随条件。

** 重命名模拟

目标模块的十五个常量在一个负面中被命名为：
   [AdjIdObj], [adjobj_hcompose], [conj_padL], [conj_padR],
   [adjobj_of_morphism], [morphism_of_adjobj], [Adj_Hcompose],
   [Adj_hunit_left], [Adj_hunit_right], [Adj_hassoc],
   [Adj_hunit_left_natural], [Adj_hunit_right_natural],
   [Adj_hassoc_natural], [Adj_triangle] 和 [Adj_pentagon]。（其他负面命名的标识符属于捐赠模块，而不是目标模块，并且同样受到 [Check] 的保护。）每个常量在 Instance/Adj/Bicategory.v 的临时副本中一次重命名一次——从未在原地重命名——在 [-Q ... Scratch] 下编译；然后将需要该临时模块而非库模块的该文件副本进行编译。所有十五个都导致了错误，每一个都出现在保护块的 [Check] 行上，没有一个出现在 [Fail] 内：

AdjIdObj                  检查 @AdjIdObj。
     adjobj_hcompose           检查 @adjobj_hcompose。
     conj_padL                 检查 @conj_padL。
     conj_padR                 检查 @conj_padR。
     adjobj_of_morphism        检查 @adjobj_of_morphism。
     morphism_of_adjobj        检查 @morphism_of_adjobj。
     Adj_Hcompose              检查 @Adj_Hcompose。
     Adj_hunit_left            检查 @Adj_hunit_left。
     Adj_hunit_right           检查 @Adj_hunit_right。
     Adj_hassoc                检查 @Adj_hassoc。
     Adj_hunit_left_natural    检查 @Adj_hunit_left_natural。
     Adj_hunit_right_natural   检查 @Adj_hunit_right_natural。
     Adj_hassoc_natural        检查 @Adj_hassoc_natural。
     Adj_triangle              检查 @Adj_triangle。
     Adj_pentagon              检查 @Adj_pentagon。

所以是15/15，没有空洞的保护。（重命名一个[Program Definition]也必须重命名它的义务，这些义务的名称是该常量的名称加上[_obligation_n]；整个文件替换可以做到这一点。）

** 护罩覆盖范围，机械测量

注释已去除，文件按句点后跟空白分割为命令：共183条命令，其中27条以[Fail]开头；它们提到118个不同的标识符，其中93个也出现在不是[Fail]的命令中。不出现的25个标识如下：两个关键字[Fail]和[Definition]；七个在否定命令内部绑定的变量（[F1]、[G1]、[J1]、[K1]、[Uq]、[aa]和[bb]）；十五个被驳回的声明名称（[n1]-[n15]），它们永远不会进入环境，因为可能声明它们的命令类型检查不通过；以及[p399_no_such_constant_anywhere]，该工具有意缺失的名称。没有任何负命名所引用的常量是无保护的。

** 制作待办事项

该仓库的 [todo] 目标对每个 [.v] 文件进行搜索，不区分大小写且不考虑单词边界，查找其五个替代项：[Fail]、abort、undefined、jww 以及它们之间的填补漏洞策略名称，这个注释没有拼写它，因为中止草图门会计入该名称。该文件提供了 41 行这样的内容：27 条 [Fail] 命令和上面的 14 行文字。Instance/Adj/Bicategory.v 贡献为零，这就是为什么每个反驳都在这里而不在那里的原因。

** 本文件不做的事情

它没有证明任何新内容。它不包含任何形式的证明漏洞，没有漏洞修补策略，没有 [Axiom]、[Parameter]，也没有 [Abort]；每一个正向控制都是一个术语，从来不是策略脚本，因此这里没有任何东西会因自动化的变化而偏移。它不衡量两个捐赠者部分之外的宇宙，不计算常量，不比较两个定理2的证明项，也不对目标标题的文字表述采取任何立场。
*)

(* ---------------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so / INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so / 仪器。 在这个仓库的 coqc 下，经过的 [Fail] 什么也不打印，因此 *)
(* this command establishes that [Fail] is doing anything at all. / 这个命令确定 [Fail] 正在做任何事情。          *)
(* ---------------------------------------------------------------------- *)

Fail Check p399_no_such_constant_anywhere.

(* ---------------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names, target and / 守卫块。每个负数下面命名的常量、目标和  *)
(* donor alike, is named here OUTSIDE every [Fail], so that renaming any / donor alike, is named here OUTSIDE every [Fail], so that renaming any / 类似的捐赠者，在这里被命名为 OUTSIDE 每个 [Fail]，因此重命名任何   *)
(* one of them breaks this file at a [Check] line rather than turning a / one of them breaks this file at a [Check] line rather than turning a / 其中一个在 [Check] 行处中断了这个文件，而不是转换一个    *)
(* negative vacuously green. / 消极地徒然绿色。                                              *)
(* ---------------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Transform.
Check @Adjunction.
Check @Compose.
Check @Id.
Check @Isomorphism.
Check @Bicategory.
Check @eq.
Check @obj.
Check @hom.
Check @homset.
Check @id.
Check @compose.
Check @compose_respects.
Check @id_left.
Check @id_right.
Check @comp_assoc.
Check @comp_assoc_sym.
Check @fobj.
Check @fmap.
Check @transform.
Check @nat_hcompose.

Check @Adjunction_Compose.
Check @Adjunction_Id.
Check @Adjunction_Compose_adj_comp_to.
Check @Adjunction_Compose_adj_comp_from.
Check @paste_v_sigma.
Check @paste_v_tau.
Check @Adjoints.
Check @adjunction.
Check @free_functor.
Check @forgetful_functor.
Check @Cat_Hcompose.
Check @Build_Bicategory.
Check @Build_Bicategory'.

Check @AdjObj.
Check @ConjPair.
Check @Adj.
Check @adjobj_left.
Check @adjobj_right.
Check @adjobj_adj.

Check @conjugate_hcompose.
Check @conj_padL.
Check @conj_padR.
Check @routeb_hyp.
Check @routeb_sigma.
Check @routeb_tau.
Check @conjugate_hcompose_via_square.
Check @nat_hcompose_interchange.
Check @AdjIdObj.
Check @adjobj_hcompose.
Check @conj_pair_hcompose.
Check @Adj_Hcompose.
Check @Adj_Hcompose_shape.
Check @hcomp_obj_adj.
Check @hcomp_obj_left.
Check @hcomp_obj_right.
Check @hcomp_left_is_nat_hcompose.
Check @hcomp_right_is_nat_hcompose.
Check @conj_interchange.
Check @Adj_hunit_left.
Check @Adj_hunit_right.
Check @Adj_hassoc.
Check @hunit_left_obj_left.
Check @hunit_left_obj_right.
Check @hunit_right_obj_left.
Check @hunit_right_obj_right.
Check @adj_hcomp2.
Check @Adj_hunit_left_natural.
Check @Adj_hunit_right_natural.
Check @Adj_hassoc_natural.
Check @Adj_triangle.
Check @Adj_pentagon.
Check @Adj_Bicategory.
Check @Adj_bicat_is_Adj.
Check @adjobj_of_morphism.
Check @morphism_of_adjobj.
Check @adjoints_round_record.

(* ====================================================================== *)
(* (1) N1-N6.  The 1-cell layer of [Adj] is WEAK: neither associativity / (1) N1-N6。[Adj] 的单细胞层很弱：既不具备结合性   *)
(*     nor either unit law of [Adjunction_Compose] is even statable, and / [Adjunction_Compose] 的任何单元法都无法表述，并且  *)
(*     one level down the functor equations are statable and refused at / 向下一级，函子方程可以被陈述并拒绝   *)
(*     conversion. / 转换                                                        *)
(* ====================================================================== *)

Section P399Assoc.

Context {D C E Z : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (Aa : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (Bb : G ⊣ V).
Context {H : E ⟶ Z} {W : Z ⟶ E} (Cc : H ⊣ W).

(* -- N1 (TYPING).  CONTROLS: both bracketings elaborate; what is        -- / -- N1（打字）。控制：两种括号说明详细；是什么        -- *)
(* -- refused is the EQUATION, whose two sides do not share a type.      -- / -- 拒绝的是方程，其两边不属于同一类型。      -- *)

Check (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc).
Check (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)).

Fail Example n1 :
  @eq (@Adjunction Z D (H ◯ (G ◯ F)) (U ◯ V ◯ W))
      (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc)
      (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)) := eq_refl.

(* -- N2/N3 (TYPING).  CONTROLS: both padded composites elaborate.       -- / -- N2/N3（打字）。 控制：两个带衬垫的复合材料详述。       -- *)

Check (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C)).
Check (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa).

Fail Example n2 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C))
  := eq_refl.

Fail Example n3 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa)
  := eq_refl.

(* -- N4-N6 (CONVERSION).  CONTROLS: [fobj] and [fmap] agree on the      -- / -- N4-N6（转换）。 控制：[fobj] 和 [fmap] 同意      -- *)
(* -- nose on both sides, so what the three negatives locate is the      -- / -- 两侧都有鼻子，所以三个否定所定位的是 -- *)
(* -- three LAW fields of [Compose] and neither data field.              -- / -- [Compose] 的三个 LAW 字段，且没有数据字段。 -- *)

Example c399_n4a (o : D) :
  @eq (obj[Z]) (fobj[H ◯ G ◯ F] o) (fobj[H ◯ (G ◯ F)] o) := eq_refl.

Example c399_n4b (o1 o2 : D) (f : o1 ~> o2) :
  @eq (fobj[H ◯ G ◯ F] o1 ~{Z}~> fobj[H ◯ G ◯ F] o2)
      (fmap[H ◯ G ◯ F] f) (fmap[H ◯ (G ◯ F)] f) := eq_refl.

Fail Example n4 : @eq (D ⟶ Z) (H ◯ G ◯ F) (H ◯ (G ◯ F)) := eq_refl.

Example c399_n56a (o : D) :
  @eq (obj[C]) (fobj[Id[C] ◯ F] o) (fobj[F] o) := eq_refl.

Example c399_n56b (o : D) :
  @eq (obj[C]) (fobj[F ◯ Id[D]] o) (fobj[F] o) := eq_refl.

Fail Example n5 : @eq (D ⟶ C) (Id[C] ◯ F) F := eq_refl.

Fail Example n6 : @eq (D ⟶ C) (F ◯ Id[D]) F := eq_refl.

End P399Assoc.

(* ====================================================================== *)
(* (2) N7-N10.  The same three laws one level up, at [AdjObj]: both unit / (2) N7-N10。在[AdjObj]上同样的三条法律，高一个层级：两个单元  *)
(*     laws, associativity, and the left-adjoint component of the first. / 定律、结合性，以及第一个的左伴随分量。  *)
(* ====================================================================== *)

Section P399AdjObj.

Context {x y z w : Category}.
Context (a : AdjObj x y) (b : AdjObj y z) (c : AdjObj z w).

(* -- CONTROLS: the target's own four [eq_refl] readbacks, which say     -- / -- 控制：目标自身的四个 [eq_refl] 读取值，它们显示     -- *)
(* -- what the padded 1-cell's two adjoints ARE.                         -- / -- 填充的 1 单元的两个伴随是什么。                         -- *)

Example c399_n7 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a ◯ Id[y])
  := @hunit_left_obj_left x y a.

Example c399_n8 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose (AdjIdObj y) a))
              (Id[y] ◯ adjobj_right a)
  := @hunit_left_obj_right x y a.

Example c399_n9 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose a (AdjIdObj x)))
              (Id[x] ◯ adjobj_left a)
  := @hunit_right_obj_left x y a.

Example c399_n10 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose a (AdjIdObj x)))
              (adjobj_right a ◯ Id[x])
  := @hunit_right_obj_right x y a.

Fail Example n7 :
  @eq (AdjObj x y) (adjobj_hcompose (AdjIdObj y) a) a := eq_refl.

Fail Example n8 :
  @eq (AdjObj x y) (adjobj_hcompose a (AdjIdObj x)) a := eq_refl.

Fail Example n9 :
  @eq (AdjObj x w) (adjobj_hcompose (adjobj_hcompose c b) a)
                   (adjobj_hcompose c (adjobj_hcompose b a)) := eq_refl.

Fail Example n10 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a) := eq_refl.

End P399AdjObj.

(* ====================================================================== *)
(* (3) N11, N12.  Route (b): the sigma leg of Adjunction/Square.v's / (3) N11, N12。 路线 (b)：Adjunction/Square.v 的 sigma leg       *)
(*     vertical paste IS the Godement product componentwise; the tau leg / 垂直粘贴确实是逐分量 Godement 积；τ 腿  *)
(*     is not, and as a WHOLE transformation neither leg has the type / is not, and as a WHOLE transformation neither leg has the type / 不是，并且作为整体转换，两条腿都没有这种类型     *)
(*     [nat_hcompose] has. / [nat_hcompose] 有。                                                *)
(* ====================================================================== *)

Section P399RouteB.

Context {C D E : Category}.
Context {F F' : D ⟶ C} {U U' : C ⟶ D}.
Context {G G' : C ⟶ E} {V V' : E ⟶ C}.

(* -- CONTROL for N11: the target's [routeb_tau], the same statement     -- / -- 控制 N11：目标的 [routeb_tau]，相同的声明     -- *)
(* -- at [~=], one application of [naturality].                          -- / -- 在 [~=]，[naturality] 的一个应用。 -- *)

Example c399_n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e
    ≈ nat_hcompose t tb e
  := @routeb_tau C D E U U' V V' t tb e.

(* -- CONTROL for N12: the target's [routeb_sigma], the sigma leg at a   -- / -- N12 控制：目标的 [routeb_sigma]，σ 腿在一个 -- *)
(* -- COMPONENT and at [eq_refl].                                        -- / -- 组件并在 [eq_refl]。                                        -- *)

Example c399_n12 (s : F' ⟹ F) (sb : G' ⟹ G) (o : D) :
  paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb) o
    = nat_hcompose sb s o
  := @routeb_sigma C D E F F' G G' s sb o.

Fail Example n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  @eq (fobj[U] (fobj[V] e) ~{D}~> fobj[U'] (fobj[V'] e))
      (paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e)
      (nat_hcompose t tb e) := eq_refl.

Fail Example n12 (s : F' ⟹ F) (sb : G' ⟹ G) :
  @eq (@Transform D E (G' ◯ F') (G ◯ F))
      (paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb))
      (nat_hcompose sb s) := eq_refl.

End P399RouteB.

(* ====================================================================== *)
(* (4) N13, N14.  The bridge to Instance/Adjoints.v: that category / (4) N13，N14。通向 Instance/Adjoints.v 的桥梁：那个范畴        *)
(*     composes by [adj_comp], whose composite is NOT [Adjunction_Compose] / 由 [adj_comp] 创作，其作品并非 [Adjunction_Compose] *)
(*     at conversion though the two share a type; and the sigT round trip / at conversion though the two share a type; and the sigT round trip / 在转换过程中，两者虽然共享一种类型；以及 sigT 往返 *)
(*     does not close where the record one does. / 不会在记录一处关闭。                          *)
(* ====================================================================== *)

Section P399Adjoints.

Context {A1 B1 C1 : Category}.
Context (mA : B1 ~{Adjoints}~> C1) (mB : A1 ~{Adjoints}~> B1).
Context (xo : AdjObj A1 B1).

(* -- CONTROLS for N13: both sides elaborate, at one and the same type.  -- / -- N13 的控制：双方都详细说明，同时进行。 -- *)

Check (adjunction (mA ∘ mB)).
Check (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)).

(* -- CONTROL for N13, the positive half already in tree: the two        -- / -- N13的控制，正半已经在树中：这两个        -- *)
(* -- constructions have definitionally equal transposes.                -- / -- 构造在定义上具有相等的转置。 -- *)

Example c399_n13a (o : C1) (p : A1)
  (f : fobj[free_functor mB] (fobj[free_functor mA] o) ~{A1}~> p) :
  to (@adj _ _ _ _ (@Adjunction_Compose B1 C1 A1
        (free_functor mA) (forgetful_functor mA)
        (free_functor mB) (forgetful_functor mB)
        (adjunction mA) (adjunction mB)) o p) f
    ≈ to (@adj _ _ _ _ (adj_comp (free_functor mB) (forgetful_functor mB)
            (free_functor mA) (forgetful_functor mA)
            (adjunction mB) (adjunction mA)) o p) f
  := @Adjunction_Compose_adj_comp_to B1 C1 A1
       (free_functor mA) (forgetful_functor mA)
       (free_functor mB) (forgetful_functor mB)
       (adjunction mA) (adjunction mB) o p f.

(* -- CONTROL for N14: the RECORD round trip closes at [eq_refl].        -- / -- 控制 N14：记录往返在 [eq_refl] 处关闭。        -- *)

Example c399_n14 : morphism_of_adjobj (adjobj_of_morphism mA) = mA
  := @adjoints_round_record B1 C1 mA.

Fail Example n13 :
  @eq (@Adjunction A1 C1 (free_functor mB ◯ free_functor mA)
                   (forgetful_functor mA ◯ forgetful_functor mB))
      (adjunction (mA ∘ mB))
      (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)) := eq_refl.

Fail Example n14 :
  @eq (AdjObj A1 B1) (adjobj_of_morphism (morphism_of_adjobj xo)) xo
  := eq_refl.

End P399Adjoints.

(* ====================================================================== *)
(* (5) N15.  [Build_Bicategory'] churns: its [symmetry]-derived / (5) N15. [Build_Bicategory'] 泡沫：它的 [symmetry] 衍生           *)
(*     [comp_assoc_sym] breaks record eta, [bicat x y] is then no longer / [comp_assoc_sym] 打破了记录 eta，[bicat x y] 随后不再存在  *)
(*     [Adj x y], and [Adj_Hcompose] no longer typechecks against / [Adj x y] 和 [Adj_Hcompose] 不再进行类型检查         *)
(*     [hcompose].  The twenty arguments below are the twenty-one / [hcompose]。下面的二十个论点是二十一         *)
(*     [Adj_Bicategory] passes to the raw constructor, less the / [Adj_Bicategory] 传递给原始构造函数，减去           *)
(*     [comp_assoc_sym] that this one derives. / [comp_assoc_sym] 这是这个的来源。                            *)
(* ====================================================================== *)

(* -- CONTROL: the raw-constructor build, which does typecheck.          -- / -- 控制：原始构造函数构建，会进行类型检查。          -- *)

Check @Adj_Bicategory.

Fail Definition n15 : Bicategory :=
  Build_Bicategory'
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

(* ====================================================================== *)
(* (6) N16-N24 (FORMABILITY): hom = proof.  The identification every / (6) N16-N24（可成形性）：hom = 证明。每一个鉴定      *)
(*     constant of the target carries in its BINDER is INHERITED, and / 目标携带的常量在其 BINDER 中是继承的，并且     *)
(*     [Compose] is a donor of it on its own -- N20 refuses [Gq (o) Fq] / [Compose] 本身就是它的供体 —— N20 拒绝 [Gq (o) Fq]   *)
(*     with no adjunction and no transformation anywhere in the command, / 在命令中任何地方都没有附加和变化，  *)
(*     while a [Transform] between two functors is accepted. / 当两个函子之间存在 [Transform] 时是可以接受的。              *)
(* ====================================================================== *)

Section P399UnivHomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du Eu : Category@{co ch cp}).

(* CONTROLS, all accepted at these very levels. / 控制，所有在这些层级都被接受。 *)

Check (fun o1 o2 : Cu => o1 ~{Cu}~> o2).
Check (fun o : Cu => @id Cu o).
Check (Cu ⟶ Du).
Check (Du ⟶ Cu).
Check (fun Fq Gq : Cu ⟶ Du => Fq ⟹ Gq).

(* -- N16.  [Adjunction] is a donor.                                     -- / -- N16. [Adjunction] 是捐赠者。 -- *)

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Fq ⊣ Uq).

(* -- N17-N19.  [AdjObj], [Adj] and [ConjPair] inherit it.  NOTE that    -- / -- N17-N19。[AdjObj]、[Adj] 和 [ConjPair] 继承它。注意    -- *)
(* -- [AdjObj] contains an [Adjunction] and [ConjPair] two [AdjObj]s, so -- / -- [AdjObj] 包含一个 [Adjunction] 和 [ConjPair] 两个 [AdjObj]，所以 -- *)
(* -- neither can be tested apart from its donor: N17-N19 record that     -- / -- 两者都无法脱离其供体进行测试：N17-N19 记录表明 -- *)
(* -- the identification reaches them, not that they add one.            -- / -- 识别信息到达他们，而不是他们添加一个。 -- *)

Fail Check (AdjObj Cu Du).

Fail Check (Adj Cu Du).

Fail Check (fun o1 o2 : AdjObj Cu Du => @ConjPair Cu Du o1 o2).

(* -- N20, N21.  [Compose] refuses on its own; [nat_hcompose] refuses    -- / -- N20, N21。[Compose] 自行拒绝；[nat_hcompose] 拒绝 -- *)
(* -- because its result type mentions [Compose], the [Transform]        -- / -- 因为它的结果类型提到 [Compose]，[Transform] -- *)
(* -- control above having been accepted.                                -- / -- 控制已被接受。 -- *)

Fail Check (fun (Fq : Cu ⟶ Du) (Gq : Du ⟶ Eu) => Gq ◯ Fq).

Fail Check (fun (F1 G1 : Cu ⟶ Du) (J1 K1 : Du ⟶ Eu)
                (aa : J1 ⟹ K1) (bb : F1 ⟹ G1) => nat_hcompose aa bb).

(* -- N22-N24.  Cat's own horizontal composition and the target's two    -- / -- N22-N24。猫自身的水平构图以及目标的两个-- *)
(* -- 1-cell and bifunctor constants, all inheriting.                    -- / -- 1-元胞和二函子常数，全部继承。                    -- *)

Fail Check (@Cat_Hcompose Cu Du Eu).

Fail Check (@adjobj_hcompose Cu Du Eu).

Fail Check (@Adj_Hcompose Cu Du Eu).

End P399UnivHomProof.

(* ====================================================================== *)
(* (7) N25, N26 (FORMABILITY): the two categories' HOM LEVELS.  Functors / (7) N25, N26（可成形性）：这两个类别的 HOM 水平。函数符  *)
(*     in BOTH directions identify them before any adjunction is formed, / 在两种方向上，在形成任何附加之前识别它们，  *)
(*     and [AdjObj] carries functors in both directions. / 并且 [AdjObj] 在两个方向上携带函子。                  *)
(* ====================================================================== *)

Section P399UnivHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Aq : Category@{ao ah ah}).
Context (Bq : Category@{bo bh bh}).

Check (Aq ⟶ Bq).
Check (fun o1 o2 : Aq => o1 ~{Aq}~> o2).
Check (fun o1 o2 : Bq => o1 ~{Bq}~> o2).
Check (fun o : Aq => @id Aq o).

Fail Check (Bq ⟶ Aq).

Fail Check (AdjObj Aq Bq).

End P399UnivHomLevels.
