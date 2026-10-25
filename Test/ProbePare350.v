(**
* Probe: boundaries of Paré's criterion

    Guards the strength claims of Adjunction/Pare.v from OUTSIDE that
    file — an in-file [Fail] renames in lockstep with the constant it
    guards and so cannot detect a rename.

    That file's header MEASURES a cluster of rejections and says plainly
    that they are "not guarded here, probes being out of scope for this
    file".  This file closes that gap.  The cluster is one phenomenon:
    [Compose] is not associative on the nose and [Id] is not a strict
    unit for it, so Mac Lane's own composites [Gε ∘ ρG] and [εK ∘ Kρ]
    are not formable as written — they would land at [Id[X] ◯ G ⟹ G ◯
    Id[A]] and [K ◯ Id[X] ⟹ Id[A] ◯ K] rather than at [G ⟹ G] and
    [K ⟹ K].

    The obstruction is LOCATED rather than asserted, and it is MEASURED
    rather than inferred.  [Functor] has primitive projections WITH ETA
    CONVERSION (Rocq reports this on [Print Functor]), so record equality
    IS field equality — which is exactly what makes the localization
    sharp, and neither this file nor the target said so before.  The
    [fobj]/[fmap] controls show two of the five fields agree; negatives
    5-7 show each of the remaining THREE fails individually, so the
    confinement is a measurement and not an inference from a head count.

    ALL NEGATIVES HERE ARE ONE KIND: CONVERSION.  An earlier revision of
    this file labelled negative 4 TYPING and claimed "two kinds", with
    the method "each stripped and its kind read off the error".  Applying
    that method refutes the claim: all of them report
    [The term "..." has type "..." while it is expected to have type
    "..." (cannot unify ...)] and negative 4 carries NO distinguishing
    marker — no [cannot satisfy constraint], no [Illegal application],
    which is how this tree's genuine TYPING negatives are told apart
    (Instance/Cat/Pullback.v and Theory/Morphisms/CokernelPair.v).  Only
    the POSITION of the mismatch differs.  The claim is withdrawn.

    The import list mirrors Adjunction/Pare.v's in full; a short prefix
    is what makes a probe pass vacuously, and a vacuity check cannot
    detect it.

--------
* 探针：帕雷准则的界限

从该文件外部保护 Adjunction/Pare.v 的 strength 声明——文件内的 [Fail] 会与它所保护的常量同步重命名，因此无法检测重命名。

该文件的标题测量了一组拒绝，并明确说明它们“在此未受保护，探针超出此文件的范围”。这个文件弥补了这一空白。该集群是一个现象：[Compose] 本身不是结合的，[Id] 也不是它的严格单位，因此 Mac Lane 自己的复合 [Gε ∘ ρG] 和 [εK ∘ Kρ] 不能按原来的形式构成——它们会落在 [Id[X] ◯ G ⟹ G ◯ Id[A]] 和 [K ◯ Id[X] ⟹ Id[A] ◯ K] 上，而不是 [G ⟹ G] 和 [K ⟹ K] 上。

阻塞是被定位的，而不是被断言的，并且它是被测量的，而不是被推断的。[Functor] 具有带 ETA 转换的原始投影（Rocq 在 [Print Functor] 上报告了这一点），因此记录相等就是字段相等——这正是使定位精确的原因，而且之前这个文件或目标都没有说明过。[fobj]/[fmap] 控制显示五个字段中有两个字段一致；负面 5-7 显示其余三个字段各自都未通过，因此限制是一次测量，而不是从人数推断出来的。

这里的所有负例都是同一种：转换（CONVERSION）。 该文件的早期修订版将负例4标记为类型错误（TYPING）并声称有“两种类型”，方法是“每个都剥离并读取错误的类型”。 应用该方法会反驳这一说法：它们全部报告
[术语 "..." 的类型为 "..."，而预期类型为 "..."（无法统一 ...）]，而负例4没有任何区别标记——没有 [cannot satisfy constraint]，也没有 [Illegal application]，这是该树中真正的TYPING负例的识别方式（Instance/Cat/Pullback.v 和 Theory/Morphisms/CokernelPair.v）。 唯一不同的是不匹配的位置。 该声明已撤回。

导入列表完全反映了 Adjunction/Pare.v 的内容；一个短前缀使探针徒然通过，而空值检查无法检测到它。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Construction.Karoubi.Universal.
Require Import Category.Adjunction.Pare.

Generalizable All Variables.

Section ProbeAssoc.

Context {A X : Category}.
Context (G : A ⟶ X).
Context (K : X ⟶ A).

(* INSTRUMENT CHECK: scope-free, and it must fail. / 仪器检查：范围自由，并且它必须失败。 *)
Fail Definition instrument_check : True = False := eq_refl.

(*
CONTROLS: the object and arrow actions DO agree on the nose, on both
   sides of associativity and of the left unitor.  These are what make
   the negatives below locate the failure in the LAW fields.

--------
控制：对象和箭头的动作在本质上完全一致，在结合性的两边以及左单位元上也是如此。这些正是使下面的负号能够在律域中定位失败的原因。
*)
Example ctl_assoc_fobj :
  @fobj A X ((G ◯ K) ◯ G) = @fobj A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_assoc_fmap :
  @fmap A X ((G ◯ K) ◯ G) = @fmap A X (G ◯ (K ◯ G)) := eq_refl.

Example ctl_unitor_fobj :
  @fobj A X (Id[X] ◯ G) = @fobj A X G := eq_refl.

Example ctl_unitor_fmap :
  @fmap A X (Id[X] ◯ G) = @fmap A X G := eq_refl.

(*
NEGATIVE 1 (CONVERSION): the whole functor records do NOT agree, even
   though both actions above do.  [Compose] is not associative on the
   nose.

--------
负1（转化）：整个函子记录不一致，尽管上述两个操作是相符的。[Compose] 本身不是结合的。
*)
Fail Definition neg_assoc_record :
  ((G ◯ K) ◯ G) = (G ◯ (K ◯ G)) := eq_refl.

(* NEGATIVE 2 (CONVERSION): nor is [Id] a strict unit for it. / 负 2（转换）：[Id] 对此也不是一个严格的单位。 *)
Fail Definition neg_unitor_record : (Id[X] ◯ G) = G := eq_refl.

(*
NEGATIVE 3 (CONVERSION): the right unitor fails as well, so repairing
   the middle would still leave the endpoints wrong.

--------
负 3（转换）：右单位元同样失败，所以修复中间部分仍会让端点错误。
*)
Fail Definition neg_unitor_right : (G ◯ Id[A]) = G := eq_refl.

(*
NEGATIVES 5-7 (CONVERSION): each of [Functor]'s three LAW fields fails
   individually across the associativity re-bracketing.  [Functor] has
   primitive projections WITH ETA, so record equality IS field equality;
   together with the [fobj]/[fmap] controls above, these MEASURE the
   confinement that the target's header infers from a field count.

--------
NEGATIVES 5-7（转换）：[Functor] 的三个 LAW 字段在结合律重新分组时各自单独失败。[Functor] 具有带 ETA 的原始投影，因此记录相等即字段相等；再加上上述的 [fobj]/[fmap] 控制，这些测量了目标头从字段计数推断的限制。
*)
Fail Definition neg_law_respects :
  @fmap_respects A X ((G ◯ K) ◯ G) = @fmap_respects A X (G ◯ (K ◯ G))
  := eq_refl.

Fail Definition neg_law_id :
  @fmap_id A X ((G ◯ K) ◯ G) = @fmap_id A X (G ◯ (K ◯ G)) := eq_refl.

Fail Definition neg_law_comp :
  @fmap_comp A X ((G ◯ K) ◯ G) = @fmap_comp A X (G ◯ (K ◯ G)) := eq_refl.

End ProbeAssoc.

Section ProbeTyping.

Context {A X : Category}.
Context (P : PareData A X).

(*
CONTROL: the whiskered composites ARE formable at the types the file
   gives them.

--------
控制：长须复合材料在文件给定的类型下是可成形的。
*)
Check (pare_Geps P).
Check (pare_rhoG P).
Check (pare_epsK P).
Check (pare_Krho P).

(* CONTROL: and the idempotent IS formable at [K ⟹ K]. / 控制：并且幂等 IS 可在 [K ⟹ K] 上形成。 *)
Check (pare_idem P : pare_K P ⟹ pare_K P).

(*
NEGATIVE 4 (CONVERSION): Mac Lane's [εK ∘ Kρ] cannot be assembled at
   all — which is why the file builds its idempotent explicitly instead
   of as this composite.

   READ THE CAUSE OFF THE ERROR, NOT OFF THE INTENTION.  It fails at the
   MIDDLE object: [cannot unify "K ◯ (G ◯ K)" and "K ◯ G ◯ K"], i.e.
   ASSOCIATIVITY — negative 1's phenomenon.  The endpoints agree on both
   sides ([K ◯ Id[X]] appears in each), so the UNITORS are never reached.
   An earlier revision of this comment attributed the failure to
   negatives 2 and 3; that was wrong, and the endpoint half of the
   "three identifications are missing" finding is therefore guarded only
   INDIRECTLY here, by negatives 2 and 3 as bare facts about [G], never
   inside the composite.

   The ascription is written [_ ∙ _] with NO type annotation on purpose:
   annotating it [: pare_K P ⟹ pare_K P] is INERT — measured, the error
   is byte-identical with and without, to the character range — so an
   annotated form would suggest the endpoint is what fails when it is
   not.

--------
负 4（转换）：Mac Lane 的 [εK ∘ Kρ] 根本无法组装——这就是为什么该文件显式构建其幂等性，而不是作为这个复合体。

阅读错误的原因，而不是意图的原因。它在中间对象：[cannot unify "K ◯ (G ◯ K)" and "K ◯ G ◯ K"] 处失败，即结合性——负一现象。两边的端点一致（每边都出现 [K ◯ Id[X]），所以单位子从未达到。对此评论的早期修订将失败归因于负二和负三；那是错误的，因此“缺少三个标识”的发现的端点部分在这里仅通过负二和负三作为关于 [G] 的基本事实间接地得到保护，而从未在复合体中出现。

这个归属被写作 [_ ∙ _]，没有类型注释是故意的：
   给它注释为 [: pare_K P ⟹ pare_K P] 是无效的——经过测量，这个错误在有无注释时字节完全相同，与字符范围一致——所以带注释的形式会让人误以为是端点出错，而实际上并非如此。
*)
Fail Check ((pare_epsK P) ∙ (pare_Krho P)).

End ProbeTyping.

Section ProbeRoundTrip.

Context {A X : Category}.
Context (P : PareData A X).
Context (F : X ⟶ A).
Context (r : pare_K P ⟹ F) (s : F ⟹ pare_K P).
Context (Hsr : ∀ x, transform[s] x ∘ transform[r] x
                      ≈ transform[pare_idem P] x).
Context (Hrs : ∀ x, transform[r] x ∘ transform[s] x ≈ id).

(* CONTROL: the adjunction built from the splitting exists. / 控制：由分裂构建的附加存在。 *)
Check (pare_Adjunction P F r s Hsr Hrs).

(* CONTROL: and so does the section recovered back out of it. / 控制：从中恢复的部分也是如此。 *)
Check (pare_r P F (pare_Adjunction P F r s Hsr Hrs)).

(*
NEGATIVE 8 (CONVERSION): but recovering the section from the
   adjunction built out of it does NOT return it.  The target's header
   discloses this as measured and delivers NO round trip in any form,
   [≈] included; an earlier revision of this probe pinned the OTHER
   disclosed cluster and left this one unguarded, so the commit message's
   plural was wrong.  Pinned here.

--------
负 8（转换）：但是从由它构建的附加部分中恢复该部分并不会返回它。目标的头部将其作为测量结果披露，并且不会以任何形式返回，包括 [≈]；该探针的早期版本固定了另一个披露的集群，而将这个未加保护，所以提交信息中使用的复数是错误的。已在此固定。
*)
Fail Definition neg_round_trip :
  pare_r P F (pare_Adjunction P F r s Hsr Hrs) = r := eq_refl.

End ProbeRoundTrip.

(*
Names the negatives depend on must also be named OUTSIDE a [Fail],
   or a rename would leave this file compiling and the guard green.

--------
依赖于的负面名称也必须在 [Fail] 外部命名，否则重命名将导致此文件编译并且保护显示为绿色。
*)
Check @pare_idem.
Check @pare_idem_Idempotent.
Check @pare_unit.
Check @pare_counit.
Check @pare_Adjunction.
Check @pare_SplitIdempotent.
Check @pare_left_adjoint_iff_splits.
Check @PareSplits.
Check @PareLeftAdjoint.
Check @pare_epsK.
Check @pare_Krho.
Check @PareData.
Check @nat_compose.
Check @pare_r.
Check @fmap_respects.
Check @fmap_id.
Check @fmap_comp.
