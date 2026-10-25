Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.
Require Import Category.Structure.Limit.Power.Adjunction.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(**
* Probe for Structure/Limit/Power/Adjunction.v

    Every boundary that file MEASURES is pinned here, from OUTSIDE it: an
    in-file [Fail] renames in lockstep with the constant it guards and so
    cannot detect a rename.  The [Require] list above is the target's own,
    which is what keeps a negative from failing for a reason it never
    measured.

    FIFTEEN [Fail] commands = ONE instrument check + FOURTEEN negatives of
    THREE kinds, told apart by the error TEXT rather than by a label: nine
    CONVERSION (each ends "cannot unify" between two terms of ONE type),
    three TYPING (a plain "has type ... while it is expected to have type",
    with NO "cannot unify" and no universe clause), two FORMABILITY (each
    ends in a universe clause).  Negatives 2 and 3 are the SAME equation at two
    spellings and come out as two DIFFERENT kinds, which is why the kind is
    read off the error and never guessed.  Each was stripped ONE AT A TIME,
    compiled ALONE, and its whole error read; each produced exactly one
    [Error], at the command that was stripped.

    Negatives 12 and 13 pin the two load-bearing [Defined]s the target
    reports but does not guard; negative 2 replaces a spelling that was a
    FALSE GUARD, which its own comment records rather than hides; negative
    14 pins the consumer-facing consequence of the four universe equations
    the target's §B paragraph records -- at an index universe strictly above
    [C]'s hom level the §A functors are accepted and the pinned adjunction
    is refused.

    Plus one COUNTERMODEL, which is a positive theorem and not a [Fail]: it
    refutes the CANONICAL arrow action over [Sets] as the index category --
    the [fmap_respects] obligation of the copower mediator of the
    injections -- outright, rather than recording that the obvious proof
    does not go through; it says nothing about other arrow actions with the
    same object action, and none is claimed.  It is axiom-free,
    measured and not assumed -- [Print Assumptions sets_index_respects_
    absurd] and [Print Assumptions blur_equal] both report "Closed under the
    global context".

    GUARD COVERAGE IS COMPLETE, checked mechanically rather than by eye:
    every identifier occurring inside a [Fail] also occurs outside every
    [Fail], with two classes of exception, both of them vacuous.  Twelve of
    the fifteen [Fail]s declare a name; those twelve names never enter the
    environment, so there is nothing to rename and nothing to guard.  The
    thirteenth exception is the instrument's deliberately absent name.  (The
    remaining three [Fail]s are [Fail Check]s, which declare nothing.)

    RENAME-SIMULATED 15/15, ZERO VACUOUS GUARDS.  Each of the thirteen
    TARGET constants a negative names was renamed IN THE LIBRARY FILE ALONE
    -- a whole-file rename is a no-op by construction and would give a false
    verdict -- the library recompiled, and this probe recompiled: every one
    broke it, and every break landed on a [Check] control line, never inside
    a [Fail].  The two constants negatives 12 and 13 reach only through
    their [Qed] clones, [cp_pa_adj] and [ex1_pa_adj], were simulated the
    same way, for 15.  The library file was byte-identical afterwards.

--------
* 探针用于结构/极限/权力/附加.v

文件 MEASURES 的每个边界都固定在这里，从外部来看：文件内的 [Fail] 会与它保护的常量同步重命名，因此无法检测重命名。上面的 [Require] 列表是目标自身的，这就是为什么它不会因为一个从未测量过的原因而导致否定失败。

十五个 [Fail] 命令 = 一次仪器检查 + 十四个三种类型的负例，这些负例通过错误文本而不是标签区分：九个 CONVERSION（每个以“cannot unify”结束，表示两个相同类型的项无法统一），三个 TYPING（简单的“has type ... while it is expected to have type”，没有“cannot unify”也没有 universe 子句），两个 FORMABILITY（每个以 universe 子句结束）。负例 2 和 3 是同一个方程的两种拼写形式，但被认定为两种不同的类型，这就是为什么类型是从错误中读取的而不是猜测的。每个负例都是一次性剥离，单独编译，并读取其完整错误；每个负例在被剥离的命令中正好生成一个 [Error]。

负号12和13将两个承重的[Defined]钉在目标报告上，但不进行防护；负号2替换了一个拼写错误，该拼写是一个虚假防护，其注释记录了这一点而不是隐藏；负号14钉住了目标§B段落记录的四个宇宙方程的面向消费者的后果——在严格高于[C]同质层次的索引宇宙中，§A函子被接受，而被钉的联接被拒绝。

加上一个 COUNTERMODEL，它是一个正定理，而不是 [Fail]：它直接驳斥了作为索引范畴的 [Sets] 上的 CANONICAL 箭头作用——注入的 copower 调解者的 [fmap_respects] 义务——而不是记录显然的证明不能成立；它不涉及具有相同对象作用的其他箭头作用，也没有声称有。它不依赖公理，经过测量而非假设——[Print Assumptions sets_index_respects_absurd] 和 [Print Assumptions blur_equal] 都报告“在全局上下文下闭合”。

保护覆盖是完整的，通过机械方式检查而不是目测：在每个 [Fail] 内出现的每个标识符也出现在每个 [Fail] 外部，有两个类别的例外，这两个例外都是空的。十五个 [Fail] 中有十二个声明了一个名称；这十二个名称从未进入环境，因此没有需要重命名的，也没有需要保护的。第十三个例外是仪器故意缺失的名称。（其余三个 [Fail] 是 [Fail Check]，它们没有声明任何东西。）

重命名模拟 15/15，零空守护。十三个 TARGET 常量中的每一个负名字仅在库文件中被重命名——通过构建进行整个文件重命名是无操作的，并会给出错误判定——库重新编译了，这个探针也重新编译了：每一个都打破了它，并且每一个破坏都落在 [Check] 控制行上，从未在 [Fail] 内部。两个常量 negatives 12 和 13 只能通过它们的 [Qed] 克隆，[cp_pa_adj] 和 [ex1_pa_adj] 达到，也以同样的方式进行了模拟，达到 15。库文件之后字节完全相同。
*)

#[local] Obligation Tactic := idtac.

(*
Instrument check: the harness reports a genuine failure, and a [Fail]
   that succeeds prints nothing, so this must be here.

--------
仪器检查：安全带报告了一个真正的故障，而成功的 [Fail] 不会打印任何内容，所以它必须在这里。
*)
Fail Check probe_366_no_such_constant.

(** ** Controls: everything the negatives name, named outside a [Fail] / ** 控制：负面所命名的一切，命名在 [Fail] 外 *)

Check @Power_Functor.
Check @Copower_Functor.
Check @Copower_Power_Adjunction.
Check @cp_adj_iso.
Check @cp_middle.
Check @power_fmap.
Check @power_ev.
Check @copower_inj.
Check @copower_desc.
Check @copower_ump.
Check @power_WeightedLimit.
Check @power_of_weighted.
Check @copower_WeightedColimit.
Check @power_weight.
Check @power_diagram.
Check @copower_diagram.
Check @index_setoid.
Check @wrt_ev.
Check @wrt_inj.
Check @Copower_Bifunctor.
Check @cp_pa_iso.
Check @cp_pa_adj.
Check @Copower_ParametrizedAdjunction.
Check @Power_Bifunctor.
Check @Copower_Bifunctor_Iso.
Check @MacLane_Ex1_hom_bifunctor.
Check @HomAllStrict.
Check @One_HasIndexedCoproducts.
Check @Sets_HasIndexedCoproducts.
Check @Opposite.
Check @Opposite_Functor.
Check @WeightedLimit.
Check @Partial_l.
Check @_1.
Check @cp_pa_adj.
Check @ex1_pa_adj.
Check @Ex1_Bifunctor.
Check @HomCoq.
Check @counit.
Check @unique_property.
Check Coq.

(** ** A. §A: the direct copower functor agrees on DATA, not as a record / ** A. §A：直接共幂函子在 DATA 上一致，而不是作为记录 *)

Section DirectCopower.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition cfd (b b' : C) (g : b ~> b') : copower J b ~> copower J b' :=
  unique_obj (copower_desc (copower_ump J b)
                (fun j : J => copower_inj J b' j ∘ g)).

Lemma cfd_inj {b b' : C} (g : b ~> b') (j : J) :
  cfd b b' g ∘ copower_inj J b j ≈ copower_inj J b' j ∘ g.
Proof. exact (unique_property (copower_desc (copower_ump J b) _) j). Qed.

Program Definition Copower_Functor_direct : C ⟶ C := {|
  fobj := fun b => copower J b;
  fmap := fun b b' g => cfd b b' g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply (uniqueness (copower_desc (copower_ump J b) _)).
  intros j; rewrite cfd_inj; now rewrite Hg.
Qed.
Next Obligation.
  intros b.
  apply (uniqueness (copower_desc (copower_ump J b) _)).
  intros j; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros x y z f g.
  apply (uniqueness (copower_desc (copower_ump J x) _)).
  intros j.
  rewrite <- comp_assoc, cfd_inj, comp_assoc, cfd_inj.
  now rewrite <- comp_assoc.
Qed.

(* POSITIVE CONTROLS: both DATA fields agree on the nose. / 阳性对照：两个数据字段完全一致。 *)
Example direct_obj (b : C) :
  fobj[Copower_Functor_direct] b = fobj[Copower_Functor J] b := eq_refl.

Example direct_fmap {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor_direct] g = fmap[Copower_Functor J] g := eq_refl.

(*
NEGATIVE 1, CONVERSION.  The WHOLE RECORD is refused: the three
   [Program]-rebuilt law fields differ.  Verbatim:
     ... (cannot unify "Copower_Functor_direct" and "Copower_Functor J").

--------
否定 1，转换。整个记录被拒绝：三个 [Program] 重建的法律字段不同。逐字如下：...（无法统一 "Copower_Functor_direct" 和 "Copower_Functor J"）。
*)
Fail Example direct_is_op_record :
  Copower_Functor_direct = Copower_Functor J := eq_refl.

End DirectCopower.

(**
** B. §A: the copower functor is [Opposite_Functor] OF the op-power
    functor, and is NOT that functor

--------
** B. §A：协幂函子是幂对偶函子的 [Opposite_Functor]，但不是那个函子
*)

Section CopowerNotPower.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(*
NEGATIVE 2, TYPING.  Against the OP-POWER functor the two constants do
   not share a type, and the error says so, naming BOTH types with no
   "cannot unify" clause and no universe clause:
     The term "Power_Functor J" has type "C^op ⟶ C^op"
     while it is expected to have type "C ⟶ C".
   It fires at the STATEMENT -- at the right-hand TERM -- and not at
   [eq_refl], which is what makes it a claim about the two types.

   WRITING [C] EXPLICITLY ON THE LEFT IS LOAD-BEARING, NOT TIDINESS, AND
   THE EPISODE IS RECORDED RATHER THAN QUIETLY FIXED.  Spelled with the
   left category implicit, as [Copower_Functor J = @Power_Functor (C^op)
   HC J], this negative is a FALSE GUARD: the elaborator re-solves the LEFT
   side's implicit category as [C^op] so that the two types agree, and
   leaves a dangling evar (measured under [Set Printing All]):
     @eq (@Functor (Opposite C) (Opposite C))
       (@Copower_Functor (Opposite C) ?HC J)
       (@Power_Functor (Opposite C) HC J)
   where [?HC : HasIndexedCoproducts (Opposite C)] is unresolved.  That
   command does fail, but at [eq_refl] and on an unresolved implicit, with
   BOTH constants at ONE category -- so what it actually refutes is
   NEGATIVE 3's fact restated at [C^op], and not a claim about types at
   all.  Same family as the false guard [Test/ProbeFiniteProducts335.v]
   records (there [obj[?C]]).  The explicit form below cannot leave an evar,
   and fails at the statement instead.

--------
否定 2，类型检查。在 OP-POWER 函子上，这两个常量没有共享类型，错误信息也表明了这一点，列出了两个类型，没有“无法统一”条款，也没有宇宙条款：
     术语 "Power_Functor J" 的类型是 "C^op ⟶ C^op"
     而期望的类型是 "C ⟶ C"。
它在 STATEMENT 上触发——在右侧 TERM 上——而不是在 [eq_refl] 上触发，这使得它是关于这两种类型的陈述。

在左边明确写出 [C] 是承重的，而不是整齐的，并且该事件是被记录下来的，而不是被静默修复的。用左类别隐含拼写为 [Copower_Functor J = @Power_Functor (C^op) HC J] 时，这个负号是一个 FALSE GUARD：展开器将左边隐含类别重新解析为 [C^op]，使两个类型一致，并留下一个悬挂的 evar（在 [Set Printing All] 下测量）：
  @eq (@Functor (Opposite C) (Opposite C))
    (@Copower_Functor (Opposite C) ?HC J)
    (@Power_Functor (Opposite C) HC J)
其中 [?HC : HasIndexedCoproducts (Opposite C)] 尚未解决。该命令确实失败，但发生在 [eq_refl] 并且在一个未解析的隐含值上，两个常量都在同一类别 —— 因此它实际反驳的是在 [C^op] 重述的 NEGATIVE 3 的事实，而不是关于类型的声明。与 false guard [Test/ProbeFiniteProducts335.v] 同一类
记录（在那里是 [obj[?C]]）。下面的显式形式不能留下 evar，并且直接在语句处失败。
*)
Fail Example copower_is_op_power :
  @Copower_Functor C HC J = @Power_Functor (C^op) HC J := eq_refl.

(*
NEGATIVE 3, CONVERSION.  Against the power functor AT [C] the two DO
   share a type, so the same refutation reports "cannot unify" instead --
   which is why the kind of a negative has to be read off the error text and
   not guessed from the statement.

--------
负 3，转换。针对幂函子 AT [C]，两个 DO 确实共享一个类型，所以同样的反驳报告了“无法统一”——这就是为什么负值的种类必须从错误文本中读取，而不能从语句中猜测的原因。
*)
Fail Example copower_is_power :
  Copower_Functor J = Power_Functor J := eq_refl.

(* POSITIVE CONTROL: what DOES hold on the nose is the double opposite. / POSITIVE CONTROL: what DOES hold on the nose is the double opposite. / 阳性对照：真正作用于鼻子的，是完全相反的两者。 *)
Example double_op :
  Opposite_Functor (Copower_Functor J) = @Power_Functor (C^op) HC J
  := eq_refl.

(* POSITIVE CONTROLS for negative 3: each donor lands at [cp_middle J b c]. / 阴性3的阳性对照：每个供体都会降落在[cp_middle J b c]。 *)
Example copower_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle J b c) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

Example power_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C b (power J c)
     ; is_setoid := @homset C b (power J c) |} (cp_middle J b c) :=
  power_hom_iso_at (@power_ump C HP J c) b.

(*
NEGATIVE 4, TYPING.  At the SWAPPED middle the ascription is refused, and
   the error prints the donor's real target -- which is what shows the two
   ascriptions above are not vacuous through a coercion.

--------
负 4，正在输入。在交换的中间，归属被拒绝，而错误打印出捐赠者的真实目标——这正显示上面的两个归属通过强制转换并非空洞。
*)
Fail Example copower_at_swapped_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle J c b) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

End CopowerNotPower.

(**
** C. ALL THREE of the target's load-bearing [Defined]s

    The target reports THREE proof terminators as load-bearing, measured by
    flipping each alone to [Qed]: [Copower_Power_Adjunction] (§B),
    [cp_pa_adj] (§E) and [ex1_pa_adj] (§D2).  A counterfactual about a
    terminator is not by itself pinnable -- nothing in the build notices
    that a [Qed] WOULD have broken something -- but an OPAQUE CLONE turns
    each into an ordinary [Fail]: the clone is the very same term closed
    with [Qed], so the readback that the target's own [Example] gets for
    free is refused for the clone and for no other reason.  All three are
    pinned here; the target itself pinned only the first.

--------
** C. 目标的三个承重 [Defined]

    目标报告三个终结器为承重，测量方法是将每个单独翻转为 [Qed]：[Copower_Power_Adjunction] (§B)、[cp_pa_adj] (§E) 和 [ex1_pa_adj] (§D2)。关于某个终结器的反事实本身并不能固定——构建通知中没有任何内容表明 [Qed] 本会破坏某些东西——但一个不透明克隆将每个终结器变成普通的 [Fail]：该克隆是同一个终结器，用 [Qed] 封闭，因此目标自己的 [Example] 免费获得的回读被拒绝给克隆，这没有其他原因。这里固定了全部三个；目标本身只固定了第一个。
*)

Section QedClone.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* An OPAQUE clone: the same adjunction, closed with [Qed]. / 一个不透明的克隆：相同的连接，由 [Qed] 封闭。 *)
Definition cp_adj_qed : Copower_Functor J ⊣ Power_Functor J.
Proof. exact (Copower_Power_Adjunction J). Qed.

(* POSITIVE CONTROL: the target's [Defined] version DOES read back. / 阳性对照：目标的 [Defined] 版本确实可以读取回传。 *)
Example defined_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J)
    (Copower_Power_Adjunction J) b c = cp_adj_iso J b c := eq_refl.

(* NEGATIVE 5, CONVERSION: the [Qed] clone does not. / 负5，转换：[Qed] 克隆没有。 *)
Fail Example qed_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J) cp_adj_qed b c
  = cp_adj_iso J b c := eq_refl.

(*
The §E adjunction, same treatment.  The readback at stake is the
   target's own [pa_adj_iso_is_cp_adj_iso], which is what makes §E's
   bijection §B's rather than a second one.

--------
§E 连接，同样处理。所涉及的回读是目标自身的 [pa_adj_iso_is_cp_adj_iso]，这正是使 §E 的双射成为 §B 的双射而不是第二个双射的原因。
*)
Definition cp_pa_adj_qed : Partial_l Copower_Bifunctor J ⊣ Power_Functor J.
Proof. exact (cp_pa_adj J). Qed.

(* POSITIVE CONTROL. / 阳性对照。 *)
Example pa_defined_readback (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    (cp_pa_adj J) b c = cp_adj_iso J b c := eq_refl.

(*
NEGATIVE 12, CONVERSION.  Verbatim tail:
     (cannot unify "adj[cp_pa_adj_qed]" and "cp_adj_iso J b c").

--------
负 12，转换。逐字尾部：
     （无法统一 "adj[cp_pa_adj_qed]" 和 "cp_adj_iso J b c"）。
*)
Fail Example pa_qed_readback (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    cp_pa_adj_qed b c = cp_adj_iso J b c := eq_refl.

End QedClone.

(**
** C'. The §D2 adjunction's [Defined], for the same reason

    Here what the transparency buys is not an [eq_refl] but an [exact]: the
    counit of [ex1_pa_adj] REDUCES to the [copower_desc] mediator, so the
    target's [ex1_counit_inj] is that mediator's [unique_property] and
    nothing else.  Against the opaque clone the same term is refused, and
    the error exhibits exactly what stopped reducing (verbatim, with only
    the printer's line breaks closed up):
      (cannot unify "unique_obj (copower_desc (copower_ump (a ~{ C }~> c) a)
       (λ i : a ~{ C }~> c, i))" and "counit").

--------
** C'。由于同样的原因，§D2 伴随的 [Defined]

这里透明性带来的不是 [eq_refl] 而是 [exact]：[ex1_pa_adj] 的辅单位 REDUCES 到 [copower_desc] 中介，因此目标的 [ex1_counit_inj] 就是该中介的 [unique_property]，除此之外没有其他。 对比不透明克隆，同一项将被拒绝，并且错误精确显示了停止简化的内容（逐字，只有印刷机的换行被合并）：
  (无法统一 "unique_obj (copower_desc (copower_ump (a ~{ C }~> c) a) (λ i : a ~{ C }~> c, i))" 与 "counit")。
*)

Section QedCloneEx1.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (HS : HomAllStrict C).

Definition ex1_pa_adj_qed (a : C) :
  Partial_l Ex1_Bifunctor a ⊣ HomCoq HS a.
Proof. exact (ex1_pa_adj HS a). Qed.

(*
POSITIVE CONTROL: with the transparent original the counit reduces, so
   the mediator's [unique_property] closes it with no tactic at all.

--------
阳性对照：在透明原件下，分立单位减少，所以中介的 [unique_property] 会在没有任何策略的情况下将其关闭。
*)
Example ex1_counit_defined (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq HS a)
    (ex1_pa_adj HS a) c ∘ copower_inj (a ~> c) a g ≈ g :=
  unique_property
    (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g.

(* NEGATIVE 13, CONVERSION. / 负13，转换。 *)
Fail Example ex1_counit_qed (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq HS a)
    (ex1_pa_adj_qed a) c ∘ copower_inj (a ~> c) a g ≈ g :=
  unique_property
    (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g.

End QedCloneEx1.

(** ** D. §C: why the copower half is built directly over [1^op] / ** D. §C：为什么共电力半部分直接建在 [1^op] 上 *)

Section WeightedShapes.

Context {C : Category}.
Context (b : C).

(* NEGATIVE 6, CONVERSION: the colimit shape is NOT the limit shape. / 负 6，转换：余极限形状不是极限形状。 *)
Fail Example one_op_is_one : Opposite _1 = _1 := eq_refl.

(*
NEGATIVE 7, TYPING: nor is the opposite of the constant diagram the
   constant diagram at the opposite category -- the SHAPES differ, so the
   copower half of §C is not an op-instantiation of the power half.

--------
负七，输入：常数图的对偶也不是相反范畴下的常数图——形状不同，因此 §C 的共值部分不是幂部分的对偶实例化。
*)
Fail Example op_diagram_is_diagram :
  Opposite_Functor (copower_diagram b) = @power_diagram (C^op) b := eq_refl.

(* POSITIVE CONTROL: the two weights agree on the single object's value. / POSITIVE CONTROL: the two weights agree on the single object's value. / 阳性对照：两个权重在单个物体的价值上达成一致。 *)
Example weight_values_agree (J : Type) :
  fobj[copower_weight J] ttt = fobj[power_weight J] ttt := eq_refl.

End WeightedShapes.

(** ** E. §C: the weighted round trip leaves ONE identity residue / ** E. §C：加权往返留下一个身份残留 *)

Section WeightedRoundTripPin.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

(* POSITIVE CONTROLS: the residues, exhibited. / 阳性对照：显示出的残留物。 *)
Example ev_residue (j : J) : wrt_ev J b j = power_ev J b j ∘[C] id := eq_refl.
Example inj_residue (j : J) :
  wrt_inj J b j = id ∘[C] copower_inj J b j := eq_refl.

(* NEGATIVES 8 and 9, CONVERSION: strict is refuted on both sides. / 否定句 8 和 9，转换：严格在双方都被反驳。 *)
Fail Example ev_strict (j : J) : wrt_ev J b j = power_ev J b j := eq_refl.
Fail Example inj_strict (j : J) :
  wrt_inj J b j = copower_inj J b j := eq_refl.

End WeightedRoundTripPin.

(**
** F. §E: the §B ISO ascribes at the partial functor; the §B
    ADJUNCTION does not, because [Adjunction] is indexed by the functor
    RECORD and not by its two actions

--------
** F. §E：§B ISO 将其归于部分函子；§B ADJUNCTION 没有，因为 [Adjunction] 是由函子 RECORD 索引的，而不是由它的两个作用索引的
*)

Section PartialAscription.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* POSITIVE CONTROLS: both actions agree, and so the ISO ascribes. / 阳性对照：两个动作一致，因此 ISO 归因。 *)
Example partial_obj (b : C) :
  fobj[Partial_l Copower_Bifunctor J] b = fobj[Copower_Functor J] b
  := eq_refl.

Example iso_ascribes (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Copower_Bifunctor J] b) c
     ; is_setoid := @homset C (fobj[Partial_l Copower_Bifunctor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  cp_adj_iso J b c.

(*
NEGATIVE 10, CONVERSION.  The error names the offending field:
     (cannot unify "λ (x y : obj[C^op^op]) (f g : x ~{ C^op^op }~> y),
                    fmap_respects y x f g"
      and "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J").

--------
负 10，转换。错误指出了出错的字段：
     （无法统一 "λ (x y : obj[C^op^op]) (f g : x ~{ C^op^op }~> y),
                    fmap_respects y x f g"
      和 "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J"）。
*)
Fail Definition adjunction_ascribes :
  Partial_l Copower_Bifunctor J ⊣ Power_Functor J :=
  Copower_Power_Adjunction J.

End PartialAscription.

(**
** G. §C: where the index/hom identification enters

    [power_WeightedLimit] carries the block equation [u0 = u3], identifying
    [C]'s hom-and-proof universe with the INDEX universe.  It enters at
    [WeightedLimit] -- when the weight and the hom-diagram are required to be
    functors into ONE [Sets] -- and NOT at the weight, the diagram, the
    hom-diagram or the power, each of which is accepted at the very levels
    where the class is refused.

--------
** G. §C：索引/Hom 识别介入的位置

[power_WeightedLimit] 携带块方程 [u0 = u3]，将 [C] 的 Hom 与证明宇宙标识为 INDEX 宇宙。它在 [WeightedLimit] 介入——当权重和 Hom 图需要作为单一 [Sets] 的函子时——而不是在权重、图、Hom 图或幂上介入，每一项都在类被拒绝的确切级别被接受。
*)

Section IndexPin.

Universes co ch ji.
Constraint ch < ji.
Context (Cu : Category@{co ch ch}) (HPu : @HasIndexedProducts Cu)
        (Ju : Type@{ji}) (bu cu : obj[Cu]).

Check (@power Cu HPu Ju bu).
Check (@power_ev Cu HPu Ju bu).
Check (@Power_Functor Cu HPu Ju).
Check (index_setoid Ju).
Check (power_weight Ju).
Check (@power_diagram Cu bu).
Check (HomDiagram cu (@power_diagram Cu bu)).

(*
NEGATIVE 11, FORMABILITY.  Verbatim tail:
     (universe inconsistency: Cannot enforce ch = ... because ch < ji <= ...).
   [power_WeightedLimit] and [power_of_weighted] are refused with it, their
   types mentioning this one.

--------
否定 11，可成形性。逐字尾部：
     （宇宙不一致：无法强制 ch = ... 因为 ch < ji <= ...）。
   [power_WeightedLimit] 和 [power_of_weighted] 被拒绝，其类型提到此项。
*)
Fail Check (WeightedLimit (power_weight Ju) (@power_diagram Cu bu)).

End IndexPin.

(**
** G'. The four §B universe equations, as a boundary a consumer meets

    The target's §B paragraph records that [cp_adj_iso] and
    [Copower_Power_Adjunction] carry the four block equations
    [u0 = u1], [u0 = u2], [u0 = u4], [u0 = u5], inherited from #321's two
    [_at] donors, while [Power_Functor] and [Copower_Functor] carry bounds
    only.  Stated as something a consumer can trip over: at an index
    universe strictly ABOVE [C]'s hom level, the §A functors and the arrow
    action are ACCEPTED and the pinned adjunction is REFUSED.  The three
    controls are what make the refusal attributable to the adjunction's own
    universe instance and not to the index or the functors.

--------
** G'. 四个 §B 宇宙方程，作为消费者遇到的边界

目标的 §B 段落记录了 [cp_adj_iso] 和 [Copower_Power_Adjunction] 携带四个方块方程 [u0 = u1]、[u0 = u2]、[u0 = u4]、[u0 = u5]，这些方程继承自 #321 的两个 [_at] 捐赠者，而 [Power_Functor] 和 [Copower_Functor] 只携带界限。表述为消费者可能会碰到的情况：在严格高于 [C] 的层级的索引宇宙中，§A 函子和箭头操作被接受，而固定的伴随被拒绝。三个控制因素使得这种拒绝可以归因于伴随自身的宇宙实例，而不是索引或函子。
*)

Section IndexAboveHom.

Universes co ch ji.
Constraint ch < ji.
Context (Cu : Category@{co ch ch}) (HPu : @HasIndexedProducts Cu)
        (HCu : @HasIndexedCoproducts Cu) (Ju : Type@{ji}).

Check (@Power_Functor Cu HPu Ju).
Check (@Copower_Functor Cu HCu Ju).
Check (@power_fmap Cu HPu Ju).

(*
NEGATIVE 14, FORMABILITY.  Verbatim tail:
     The term "Ju" has type "Type@{ji}" while it is expected to have type
     "Type@{...}" (universe inconsistency: Cannot enforce ji <= ...
     because ... < ji).
   [cp_adj_iso] is refused at the same levels, carrying the same four
   equations.

--------
负 14，成形性。逐字尾巴：
     术语“Ju”的类型为“Type@{ji}”，而预期它具有类型
     “Type@{...}”（宇宙不一致：无法强制 ji <= ...
     因为 ... < ji）。
   [cp_adj_iso] 在相同级别被拒绝，携带相同的四个方程。
*)
Fail Check (@Copower_Power_Adjunction Cu HPu HCu Ju).

End IndexAboveHom.

(**
** H. The canonical action over [Sets] as index is REFUTED, not unproved

    The copower injections are indexed by ELEMENTS, so the [fmap_respects]
    obligation of the CANONICAL arrow action of [(S, a) ↦ |S| · a] over
    [Sets] -- the copower mediator of the injections, which is what any
    arrow action commuting with the injections must be -- asks for
    [f j = f' j] at LEIBNIZ equality from [f ≈ f'].  Below is an axiom-free
    countermodel: a two-element setoid whose [≈] is the total relation
    makes two visibly different maps equal, and their copower injections
    are then provably distinct.  This is why the file's index category is
    [Coq].  Read the scope: [SetsIndexRespects] is THAT obligation, so what
    is refuted is that action; no other arrow action over [Sets] is
    investigated and none is claimed refuted.

--------
** H. 关于 [Sets] 作为指标的典型作用是被反驳的，而不是未被证明的

    余幂注入是由 ELEMENTS 索引的，所以 [fmap_respects] 的典型箭头作用的义务 [(S, a) ↦ |S| · a] 在 [Sets] 上——注入的余幂中介，这正是任何与注入交换的箭头作用必须满足的——要求从 [f ≈ f'] 得到 [f j = f' j] 在莱布尼茨等式下。下面是一个无公理的反例模型：一个两元素的集合序列，其 [≈] 是全关系，使两个显然不同的映射相等，并且它们的余幂注入随后可被证明是不同的。这就是为什么该文件的指标范畴是 [Coq]。阅读作用范围：[SetsIndexRespects] 是该义务，所以被反驳的是该作用；没有调查其他在 [Sets] 上的箭头作用，也没有声称它们被反驳。
*)

Definition blur_equivalence : Equivalence (fun _ _ : bool => True) :=
  {| Equivalence_Reflexive := fun _ => I
   ; Equivalence_Symmetric := fun _ _ _ => I
   ; Equivalence_Transitive := fun _ _ _ _ _ => I |}.

Definition BoolBlur : obj[Sets] :=
  {| carrier := bool
   ; is_setoid := Build_Setoid bool (fun _ _ => True) blur_equivalence |}.

Definition ProbePt : obj[Sets] := Sets_discrete Datatypes.unit.

Definition blur_id : Sets_discrete bool ~{Sets}~> BoolBlur.
Proof.
  unshelve econstructor.
  - exact (fun b : bool => b).
  - intros x y H; exact I.
Defined.

Definition blur_neg : Sets_discrete bool ~{Sets}~> BoolBlur.
Proof.
  unshelve econstructor.
  - exact negb.
  - intros x y H; exact I.
Defined.

Lemma blur_equal : blur_id ≈ blur_neg.
Proof. intro b; exact I. Qed.

(* The [fmap_respects] obligation, written out at the shape it takes. / [fmap_respects] 义务，按照其所呈现的形式写出。 *)
Definition SetsIndexRespects : Type :=
  ∀ (S S' a : Sets) (f f' : S ~{Sets}~> S'), f ≈ f' → ∀ j : S,
    @copower_inj Sets Sets_HasIndexedCoproducts (carrier S') a (f j)
      ≈ @copower_inj Sets Sets_HasIndexedCoproducts (carrier S') a (f' j).

Theorem sets_index_respects_absurd : SetsIndexRespects → False.
Proof.
  intro H.
  destruct (H (Sets_discrete bool) BoolBlur ProbePt
              blur_id blur_neg blur_equal true tt) as [e _].
  simpl in e; discriminate e.
Qed.

(** ** I. The two parametrizations are BOTH inhabited / ** I. 这两种参数化都是有解的 *)

Check (@Copower_ParametrizedAdjunction).
Check (@Copower_Object_ParametrizedAdjunction).
Check One_Ex1_ParametrizedAdjunction.
Check (@Copower_Bifunctor_Iso).
