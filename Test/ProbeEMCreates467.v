(**
* Probe for "G^T creates limits" (issue #467)

    Pins the measured boundaries of Monad/Eilenberg/Moore/Limit.v and
    Monad/Eilenberg/Moore/Limit/Examples.v against Mac Lane, §VI.2,
    Exercise 2, "Show that G^T : X^T → X creates limits", book p. 142
    (PDF p. 151), catalog item maclane:VI.2:ex2, read with the unnumbered
    Definition of §V.1 (p. 112): (i) to every limiting cone τ: x →· VF
    there is exactly one pair ⟨a, σ⟩ with Va = x and Vσ = τ, and (ii) σ is
    limiting.  Limit.v's header maps the clauses onto the tree; the
    controls here restate each [eq_refl] strength independently, and the
    two refutation commands pin the two places where [eq_refl] is refused.

    THE IMPORT LIST.  Limit.v's thirteen [Require] lines in its own order,
    and that target; then the seven lines Examples.v adds
    (Monad/Strong.v, Structure/Terminal.v, Structure/Limit/Terminal.v,
    Instance/Zero.v, Instance/Coq.v, Instance/Sets.v, Instance/One.v), and
    that target: twenty-two lines, all naming [Category] modules.  Under
    this list [Print Libraries] in a scratch file loads fifty-nine
    [Category] modules, exactly the union of the two targets' dependency
    closures (compared by script with the closure of their [Require]
    lines).  A shorter import list is what makes a probe pass for no
    reason.

    DISCIPLINE.  Every negative is an [Example], never a [Check], so that
    an open evar cannot satisfy it.  Each of the two refutation lines was
    stripped of its refutation keyword in a copy of this WHOLE file, one at
    a time, compiled, and its error read; each copy stops inside the
    stripped command (by the File line of its error, compared by script
    with the command's extent), with the error quoted below.  Each of the
    sixteen controls, wrapped in the refutation keyword in a copy of
    this WHOLE file, stops the build at that command with the message
    Rocq prints for a refutation whose command succeeds (sixteen of
    sixteen, by the same script).  Quotations are Rocq 9.1.1's under
    this file's import list, with the error's environment block left out;
    Rocq prints the "cannot unify" parenthetical with the short names in
    scope.  The two targets and this file also compile on Coq 8.19.2 and
    8.20.1, with no warning from any of them, overlaid on copies of the
    dependency closure whose fifty-nine sources are this tree's byte for
    byte (compared by [cmp]).  Each of the two stripped copies is refused
    there inside the stripped command with the Rocq 9.1.1 error,
    environment block included (compared by script), and every wrapped
    control reports there that its command succeeded (sixteen of sixteen
    on each version).

    KINDS.  Both refutations are CONVERSION: [eq_refl] refused with a
    "cannot unify" parenthetical.  R1's CAUSE is STRUCTURAL, argued and
    not measured by a flip (below).

    LABELS.  The labels are the ones docs/INDEX.md's bullet for
    Monad/Eilenberg/Moore/Limit.v cites; they are not constants.  C1 is
    [p467_c1_apex], C2 [p467_c2_legs], C2b [p467_c2_legs_class], C3
    [p467_c3_leg_family], C4 [p467_c4_slift_eq], C5 [p467_c5_structure],
    C6 [p467_c6_iso_id], C7 [p467_c7_created_legs] and C8
    [p467_c8_record_but_coherence]; R1 is [p467_r1_fcone]; E1 is
    [p467_e1_carriers], E2 [p467_e2_legs], E3 [p467_e3_lift_leg], E4
    [p467_e4_iso], E5 [p467_e5_iso_id], E6 [p467_e6_refutation] and E7
    [p467_e7_refutation_limiting]; "the instrument" is
    [p467_instrument].  Each of the two refutations carries its label in
    a comment on the line above it, the instrument's reading "The
    instrument".

    ** The generic clauses, for every monad T and diagram K

    Controls, at [eq_refl], for the strict lift [em_strict_lift] of a
    limiting cone N: clause (i)'s Va = x ([p467_c1_apex]) and its
    transport, which IS [eq_refl] ([p467_c4_slift_eq]); clause (i)'s
    Vσ = τ leg by leg ([p467_c2_legs]), through the class projection
    [screates] ([p467_c2_legs_class]) and as the leg family
    ([p467_c3_leg_family]); the created structure map is the mediator of
    the action cone ([p467_c5_structure]); the forward map of the iso of
    the iso-invariant class is [id] ([p467_c6_iso_id]); the created limit's
    legs are [em_leg] ([p467_c7_created_legs]); and the image cone,
    rebuilt with N's own coherence field in place of its own, IS N
    ([p467_c8_record_but_coherence]).
    R1 (CONVERSION).  The image cone itself against N:
      (cannot unify "FCone (EM_Forget T) (slift_cone (em_strict_lift T K N
      HN))" and "N")
    With [p467_c8_record_but_coherence], the refusal lies in the
    coherence field alone: the image cone's is built from
    [fcone_coherence] (Structure/Limit/Preservation.v) applied to the
    lift, N's is [cone_coherence] of N's own [coneFrom], a projection of
    the variable N.  CAUSE: STRUCTURAL (argued, not flip-measured): the
    first is an application of [fcone_coherence], a [Qed] lemma whose
    body is a rewrite chain over D's abstract hom-setoids, the second a
    stuck projection of a variable, and making [fcone_coherence]
    transparent would expose the chain, not turn it into that
    projection.

    ** The counterexample (Examples.v)

    Control: the two algebras [A_id] and [A_true] have the same carrier on
    the nose ([p467_e1_carriers]).
    The instrument (CONVERSION).  The two algebras themselves:
      (cannot unify "A_id" and "A_true")
    Their inequality is the theorem [A_id_ne_A_true].
    Controls: the legs [leg_id_from] of the two lifts agree on the nose
    ([p467_e2_legs]), and a lift's leg is [N1]'s after the transport
    ([p467_e3_lift_leg]); Examples.v's [em_lift_alg_unique_Sets] is
    [em_lift_alg_unique] applied at the example, on the nose
    ([p467_e4_iso]), and its isomorphism's underlying map is [id] on the
    nose there ([p467_e5_iso_id]).  The two refutations are restated
    against the library constants, so that weakening either statement
    stops this file ([p467_e6_refutation],
    [p467_e7_refutation_limiting]).

--------
* 探测 "G^T 创建限制"（问题 #467）

将 Monad/Eilenberg/Moore/Limit.v 和 Monad/Eilenberg/Moore/Limit/Examples.v 的测量边界与 Mac Lane，第 VI.2 节，练习 2 对照，“证明 G^T : X^T → X 创建极限”，书本第 142 页（PDF 第 151 页），目录条目 maclane:VI.2:ex2，结合第 V.1 节（第 112 页）未编号的定义阅读：(i) 对于每一个极限锥 τ: x →· VF，恰有一对 ⟨a, σ⟩ 满足 Va = x 且 Vσ = τ；(ii) σ 是极限。Limit.v 的标题将条款映射到树上；此处的控件独立重述每个 [eq_refl] 强项，而两个反驳命令固定了拒绝 [eq_refl] 的两个位置。

导入列表。Limit.v 按照它自己的顺序有十三行 [Require]，然后是那个目标；接着是 Examples.v 添加的七行（Monad/Strong.v、Structure/Terminal.v、Structure/Limit/Terminal.v、Instance/Zero.v、Instance/Coq.v、Instance/Sets.v、Instance/One.v），以及那个目标：二十二行，全部命名为 [Category] 模块。在这个列表下，[Print Libraries] 在一个临时文件中加载五十九个 [Category] 模块，正好是两个目标依赖闭包的并集（通过脚本与它们 [Require] 行的闭包比较）。更短的导入列表正是让探针无故通过的原因。

纪律。每个否定都是 [Example]，而绝不是 [Check]，因此一个开放的 evar 无法满足它。在此整个文件的副本中，每条反驳线都被剥离了其反驳关键字，一次一条，编译，然后读取其错误；每个副本都在被剥离的命令内停止（通过其错误的文件行，与命令的范围通过脚本比较），下面引用了错误信息。在此整个文件的副本中，将十六个控制中的每一个包装在反驳关键字中，在该命令处停止构建，并显示 Rocq 对命令成功的反驳打印的消息（十六个中十六个，由同一脚本）。引文是 Rocq 9.1.1 在此文件的导入列表下的内容，省略了错误的环境块；Rocq 打印“无法统一”的括号内容及作用域内的简称。
这两个目标和此文件也能在 Coq 8.19.2 和 8.20.1 上编译，且没有任何警告，基于依赖闭包的副本叠加，其五十九个源文件与该树的字节完全一致（通过 [cmp] 比较）。这两个剥离的副本在剥离命令内部被拒绝，出现 Rocq 9.1.1 错误，并包含环境块（通过脚本比较），每个封装的控制报告显示其命令成功（每个版本均为十六个中的十六个）。

类型。两种反驳都是转换：[eq_refl] 拒绝，并附有“无法统一”的括号说明。R1 的原因是结构性的，经过论证，而不是通过下面的翻转来衡量。

标签。标签是 docs/INDEX.md 中 Monad/Eilenberg/Moore/Limit.v 列出的项目引用的标签；它们不是常量。C1 是 [p467_c1_apex]，C2 是 [p467_c2_legs]，C2b 是 [p467_c2_legs_class]，C3 是 [p467_c3_leg_family]，C4 是 [p467_c4_slift_eq]，C5 是 [p467_c5_structure]，C6 是 [p467_c6_iso_id]，C7 是 [p467_c7_created_legs]，C8 是 [p467_c8_record_but_coherence]；R1 是 [p467_r1_fcone]；E1 是 [p467_e1_carriers]，E2 是 [p467_e2_legs]，E3 是 [p467_e3_lift_leg]，E4 是 [p467_e4_iso]，E5 是 [p467_e5_iso_id]，E6 是 [p467_e6_refutation]，E7 是 [p467_e7_refutation_limiting]；“仪器”是 [p467_instrument]。每个反驳在其上方一行的注释中带有其标签，仪器的注释为“仪器”.

** 泛型子句，对于每个单子 T 和图 K

控制，在 [eq_refl]，针对限制锥 N 的严格上极限 [em_strict_lift]：条款 (i) 的 Va = x ([p467_c1_apex]) 及其传输，它是 [eq_refl] ([p467_c4_slift_eq])；条款 (i) 的 Vσ = τ 分支逐段 ([p467_c2_legs])，通过类投影 [screates] ([p467_c2_legs_class]) 并作为分支族 ([p467_c3_leg_family])；所创建的结构映射是作用锥的媒介 ([p467_c5_structure])；同构不变量类的同构的正向映射是 [id] ([p467_c6_iso_id])；所创建极限的分支是 [em_leg] ([p467_c7_created_legs])；且图像锥，用 N 自身的相干场重建以替代其自身， 是 N ([p467_c8_record_but_coherence])。R1（转换）。
将像锥体自身与 N 比较：
      （无法统一 "FCone (EM_Forget T) (slift_cone (em_strict_lift T K N HN))" 和 "N"）
    使用 [p467_c8_record_but_coherence] 时，拒绝仅存在于相干性领域：像锥体的是由 [fcone_coherence]（Structure/Limit/Preservation.v）应用于升起构建的，N 的的是 N 自身的 [cone_coherence] 的 [coneFrom]，这是变量 N 的一个投影。原因：结构性（已论证，非翻转测量）：第一个是对 [fcone_coherence] 的应用，[Qed] 引理，其主体是 D 的抽象同态集上的重写链，第二个是变量的卡住投影，使 [fcone_coherence] 透明会暴露该链，而不会将其变成那个投影。

** 反例 (Examples.v)

控制：两个代数 [A_id] 和 [A_true] 在本身上有相同的载体（[p467_e1_carriers]）。
仪器（转换）。这两个代数本身：
  （无法统一 “A_id” 和 “A_true”）
它们的不等式是定理 [A_id_ne_A_true]。
控制：两个提升的腿 [leg_id_from] 完全一致（[p467_e2_legs]），并且一个提升的腿在运输后是 [N1]（[p467_e3_lift_leg]）；Examples.v 的 [em_lift_alg_unique_Sets] 是在例子上直接应用的 [em_lift_alg_unique]（[p467_e4_iso]），其同构的基础映射在那里是直接的 [id]（[p467_e5_iso_id]）。
两个反驳陈述是针对库常量重新表述的，因此削弱任何一个陈述都会停止该文件（[p467_e6_refutation]，[p467_e7_refutation_limiting]）。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Monad.Eilenberg.Moore.Limit.
Require Import Category.Monad.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Monad.Eilenberg.Moore.Limit.Examples.

Generalizable All Variables.
(** ** The generic clauses / ** 一般条款 *)

Example p467_c1_apex@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  EM_Forget T
    (vertex_obj[slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)])
    = vertex_obj[N] := eq_refl.

Example p467_c2_legs@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) (j : J) :
  fmap[EM_Forget T]
    (cone_leg (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)) j)
    = cone_leg N j := eq_refl.

Example p467_c2_legs_class@{o h jo eo e l l0 c c0} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) (j : J) :
  fmap[EM_Forget T]
    (cone_leg (slift_cone (@screates _ _ _ _ _
       (em_forget_StrictlyCreatesLimit@{o h jo h eo e l l0 c c0} T K) N HN)) j)
    = cone_leg N j := eq_refl.

Example p467_c3_leg_family@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  (fun j => fmap[EM_Forget T]
     (cone_leg (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))
        j))
    = (fun j => cone_leg N j) := eq_refl.

Example p467_c4_slift_eq@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  slift_eq (em_strict_lift@{o h jo h eo e l l0 s} T K N HN) = eq_refl
  := eq_refl.

Example p467_c5_structure@{o h jo eo e l} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (L : Limit@{l jo h o} (EM_Forget T ◯ K)) :
  t_alg[`2 (em_apex T K L)]
    = limit_med (limit_is_alimit L) (em_act_cone T K L) := eq_refl.

Example p467_c6_iso_id@{o h jo eo e l l0 c c0} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  to `1 (@creates_lift_over _ _ _ _ _
           (em_forget_CreatesLimit@{o h jo h eo e l l0 c c0} T K) N HN)
    = id := eq_refl.

Example p467_c7_created_legs@{o h jo eo e l} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (L : Limit@{l jo h o} (EM_Forget T ◯ K)) (j : J) :
  limit_leg (em_created T K L) j = em_leg T K L j := eq_refl.

Example p467_c8_record_but_coherence@{o h jo eo e l l0 s}
  {D : Category@{o h h}} (T : D ⟶ D) `{H : @Monad D T}
  {J : Category@{jo h h}} (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  @Build_Cone J D (EM_Forget T ◯ K)
    (vertex_obj[FCone (EM_Forget T)
       (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))])
    (@Build_ACone J D _ (EM_Forget T ◯ K)
       (fun j => cone_leg (FCone (EM_Forget T)
          (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN))) j)
       (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N)))
    = N := eq_refl.

(* R1 *)
Fail Example p467_r1_fcone@{o h jo eo e l l0 s} {D : Category@{o h h}}
  (T : D ⟶ D) `{H : @Monad D T} {J : Category@{jo h h}}
  (K : J ⟶ EilenbergMoore@{eo o e h} T)
  (N : Cone (EM_Forget T ◯ K)) (HN : IsLimitCone@{l l0 jo h o} N) :
  FCone (EM_Forget T)
    (slift_cone (em_strict_lift@{o h jo h eo e l l0 s} T K N HN)) = N
  := eq_refl.

(** ** The counterexample / ** 反例 *)

Example p467_e1_carriers@{o so} : `1 A_id@{o so} = `1 A_true@{o so}
  := eq_refl.

(* The instrument / 乐器 *)
Fail Example p467_instrument@{o so} : A_id@{o so} = A_true@{o so}
  := eq_refl.

Example p467_e2_legs@{o so} :
  fmap[EM_Forget IdS@{o so}] (leg_id_from@{o so} (fun _ => true))
    = fmap[EM_Forget IdS@{o so}] (leg_id_from@{o so} (fun b => b))
  := eq_refl.

Example p467_e3_lift_leg@{j o so} :
  hom_rew eq_refl
    (fmap[EM_Forget IdS@{o so}]
       (cone_leg (slift_cone (lift1_at@{j o so} A_true eq_refl
                                (leg_id_from (fun _ => true)) (fun _ => I)))
          ttt))
    = cone_leg N1@{j o so} ttt := eq_refl.

Example p467_e4_iso@{l l0 j o so} (f : bool → bool) :
  em_lift_alg_unique_Sets@{l l0 j o so} f
    = em_lift_alg_unique@{so o j so so l l0} IdS K1 N1
        N1_limiting@{l l0 j o so}
        (lift1_at (existT _ Bool2 (alg_of f)) eq_refl (leg_id_from f)
           (fun _ => I)) := eq_refl.

Example p467_e5_iso_id@{l l0 j o so} (f : bool → bool) :
  t_alg_hom[to `1 (em_lift_alg_unique_Sets@{l l0 j o so} f)] = id
  := eq_refl.

Example p467_e6_refutation@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       vertex_obj[σ] = vertex_obj[σ']) → False
  := em_lift_not_unique_leibniz@{l l0 j o so}.

Example p467_e7_refutation_limiting@{l l0 j o so} :
  (∀ τ : Cone (EM_Forget IdS@{o so} ◯ K1@{j o so}),
     IsLimitCone@{l l0 j o so} τ →
     ∀ (σ σ' : Cone K1@{j o so})
       (p : EM_Forget IdS (vertex_obj[σ]) = vertex_obj[τ])
       (p' : EM_Forget IdS (vertex_obj[σ']) = vertex_obj[τ]),
       (∀ x, hom_rew p (fmap[EM_Forget IdS] (cone_leg σ x)) = cone_leg τ x) →
       (∀ x, hom_rew p' (fmap[EM_Forget IdS] (cone_leg σ' x))
               = cone_leg τ x) →
       IsLimitCone@{l l0 j o so} σ → IsLimitCone@{l l0 j o so} σ' →
       vertex_obj[σ] = vertex_obj[σ']) → False
  := em_limiting_lift_not_unique_leibniz@{l l0 j o so}.
