(**
* Boundary probe for Structure/Limit/Components.v (issue #355)

    Mac Lane CWM 2nd ed. §IV.2, book p. 90, Exercise 7.

    WHY THIS FILE EXISTS AT ALL.  [Structure/Limit/Components.v] carries
    two [Fail]s of its own (an earlier revision said four; the two
    universe ones there were repaired at the same time as N1/N2 below),
    and they are well formed -- each is stripped and its whole error read,
    each sits beside a control that must succeed.  What an in-file
    negative CANNOT do is survive a rename: a
    whole-file rename moves the [Fail] and the constant it names in
    lockstep, so the guard stays green while the thing it guarded is
    gone.  Every negative below therefore names a constant of the TARGET,
    and the file mirrors ALL 23 of the target's [Require] lines -- a
    probe built on a short prefix of that list is the classic way to
    make a negative pass
    for a reason it never measured (a missing coercion, an absent
    notation), certifying nothing.

    KINDS, separated by the error TEXT rather than by label:
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`
    A [Fail] that SUCCEEDS prints NOTHING under this repo's [coqc], so
    every negative here was stripped and run alone before being trusted.

    WHAT IS PINNED, and what each negative is FOR:

    N1, N2 -- REPAIRED, and recorded as a correction.  An earlier revision
          read:

            "N1 -- the [iprod] reading of part (a) carries a [Set] pin
             that the ELEMENTARY reading does not.  This is the reason
             part (a) is stated first at [IsIndexedProduct] and only then
             read through [iprod]: [iprod] is defined over
             [Limit (DiscreteCat_Functor f)] and so pins the ambient
             category's hom AND proof universes to the literal [Set].  The
             issue's own reviewer check asks that the right-hand side use
             [iprod]; taken alone that would have confined the theorem to
             [Set]-homed categories WITHOUT SAYING SO.  The controls show
             the elementary vocabulary is formable at levels where the
             [iprod] one is not, so the pin is attributable to the DONOR
             and not to anything the target adds.
             N2 -- the same, one layer out, at the target's own corollary.
             Both [Set]-pin negatives report `Cannot enforce Set = uh`,
             which names the declared level, so neither can be passing for
             an unrelated reason."

          The attribution to the DONOR was right, and the donor was one
          step further out than [iprod]: [DiscreteCat_Functor], declared
          with bare binders and minimized to [DiscreteCat@{u Set Set}].
          Annotated in place in the PR "algebraic carriers are sets"
          (2026-09-17), Instance/Discrete.v, both commands are ACCEPTED
          and are kept as positive controls at the same levels, so
          dropping the annotation refuses them again and breaks this file.
          Part (a) is still stated first at [IsIndexedProduct], which is
          now a presentational choice and not a universe obligation.
          NO FORMABILITY REFUSAL REMAINS IN THIS FILE.

    N3 -- [component_diagram] is not [summand] of the transported functor
          on the nose; the comparison is at [≈] with identity components.

--------
* Structure/Limit/Components.v 的边界探测（问题 #355）

Mac Lane 《CWM》第2版 §IV.2，第90页，练习7。

为什么这个文件会存在。[Structure/Limit/Components.v] 自己包含两个 [Fail]（早期版本说是四个；那两个 universe 的在下面的 N1/N2 同时被修复），它们都是格式良好的——每一个都被剥离，读取了全部错误，每一个都旁边有一个必须成功的控制。文件内部的负向操作不能做的是在重命名时存活：整文件重命名会同步移动 [Fail] 及其命名的常量，所以在其守护的东西消失时，保护依然显示正常。因此，下列每一个否定都表示目标的一个常量，且该文件镜像了目标的所有 23 行 [Require] —— 基于该列表的短前缀构建的探测，是制造否定结果的经典方法，用于它从未测量过的原因（缺失的强制转换、缺少的标注），并不能证明任何事情。

类型，按错误文本而不是按标签分开：
      转换 以 `(cannot unify "X" and "Y")` 结尾
      可形成性 以 `(universe inconsistency: Cannot enforce ...)` 结尾
    在这个仓库的 [coqc] 下，一个成功的 [Fail] 什么也不打印，所以这里的每个负例都是单独运行并通过后才被信任。

什么是固定，以及每个负面作用的用途：

N1, N2——已修复，并记录为更正。早期的修订版本写道：

N1 -- [iprod] 对部分 (a) 的 reading 带有 ELEMENTARY reading 所没有的 [Set] 引脚。这就是部分 (a) 为什么首先在 [IsIndexedProduct] 中陈述，然后才通过 [iprod] 进行读取的原因：[iprod] 是在 [Limit (DiscreteCat_Functor f)] 上定义的，因此将环境类别的 hom 和 proof 宇宙固定到字面上的 [Set]。该问题的审阅者检查要求右侧使用 [iprod]；单独考虑，这将把定理限制在 [Set] 驻留的类别中，而未予说明。控制显示，基础词汇可以在 [iprod] 无法达到的级别上形成，因此该引脚应归因于 DONOR，而不是目标添加的内容。N2 —— 同样，在目标自身的对应层上，另一层也是如此。两个 [Set] 引脚为负的报告都是 `Cannot enforce Set = uh`，它标明了声明的级别，因此都不可能因无关原因而通过。

对捐赠者的归属是正确的，捐赠者比 [iprod] 稍进一步：[DiscreteCat_Functor]，用裸绑定声明并最小化到 [DiscreteCat@{u Set Set}]。在 PR 中就地注释“代数承载体是集合”（2026-09-17），Instance/Discrete.v，两个命令都被接受，并保持在相同的正对照水平，因此删除该注释会再次拒绝它们并破坏该文件。部分 (a) 仍然首先在 [IsIndexedProduct] 处声明，现在这是一个表现选择，而不是宇宙义务。该文件中不再存在可形成性拒绝。

N3 -- [component_diagram] 不是被传输函子的 [summand]；比较是在具有恒等分量的 [≈] 上进行的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Initial.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Limit.Components.

(** ** Instrument check — must ERROR ("The command has not failed!"). / ** 仪器检查 — 必须错误（“命令没有失败！”）。 *)
Fail Fail Check Category.

(**
** The former [Set] pin of the [iprod] reading, now lifted.

    Declared with the ambient homs strictly ABOVE [Set], the elementary
    statements elaborate and, since [DiscreteCat_Functor] was annotated,
    so do the [iprod] ones.  The two former negatives are kept here as
    positive controls; see N1/N2 in the header.

--------
** [iprod] 读数的前 [Set] 引脚，现在已解除。

声明时将环境 homs 严格置于 [Set] 之上，基本语句进行了详细说明，并且由于 [DiscreteCat_Functor] 已经被注释，[iprod] 的语句也是如此。这里保留了两个以前的阴性作为阳性对照；请参见标题中的 N1/N2。
*)

Section IprodSetPin.

Universe uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).
Context (Js : bool → Category@{uo uh uh}).

(*
CONTROLS: the elementary vocabulary IS formable at these levels, and
   the controls are APPLIED -- an unapplied polymorphic constant never
   meets [Cu] and would discriminate nothing.

--------
控制：基础词汇在这些级别上是可形成的，并且控制是已应用的——一个未应用的多态常量从不符合 [Cu]，也不会区分任何东西。
*)

Check (fun (A : Type) (f : A → Cu) (p : Cu)
           (pr : ∀ a : A, p ~{Cu}~> f a) => IsIndexedProduct f p pr).

Check (fun (F : SigmaCat Js ⟶ Cu) (p : Cu) => IsALimit F p).

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (p : Cu) (pr : ∀ k : bool, p ~{Cu}~> L k)
           (HP : IsIndexedProduct L p pr) => coprod_IsALimit F HL HP).

(* Former N1: the donor is formable here. / 前 N1：供体在这里是可形成的。 *)
Check (fun (A : Type) (f : A → Cu)
           (P : Limit (DiscreteCat_Functor f)) => iprod f P).

(* Former N2: and so is the target's own corollary over it. / 前N2：目标自身对此的推论也是如此。 *)
Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (P : Limit (DiscreteCat_Functor L)) =>
         coprod_IsALimit_iprod F HL P).

End IprodSetPin.

(**
** CONVERSION — the transported diagram is not the summand on the
    nose.  The control is the [≈] form, which the target proves.

--------
** 转换——所传输的图不是明确的加数。控制是 [≈] 形式，由目标证明。
*)

Section DiagramConversion.

Context {J C : Category}.
Context (D : ComponentDecomposition J).
Context (F : J ⟶ C).

(* CONTROL: the [≈] comparison exists and is what the target delivers. / 控制：[≈] 比较存在，并且是目标交付的内容。 *)
Check (component_diagram_equiv D F).

(* N3. *)
Fail Example probe_component_diagram_strict (k : cd_index D) :
  component_diagram D F k = summand (F ◯ cd_compare D) k := eq_refl.

End DiagramConversion.

(**
** POSITIVE CONTROLS naming the rest of the surface, so that a rename
    of any of these breaks this file at a NON-[Fail] line.

--------
** POSITIVE CONTROLS 命名其余的表面，以便对其中任何一个重命名都会在非 [Fail] 行中破坏此文件。
*)

Check @coprod_IsALimit.
Check @coprod_IsLimitCone.
Check @coprod_Limit.
Check @coprod_limit_iso.
Check @coprod_limit_iso_legs.
Check @coprod_proj_is_restriction.
Check @coprod_IsALimit_HasIndexedProducts.
Check @coprod_Limit_iprod.
(*
[coprod_IsALimit_iprod] and [component_diagram] are named by NEGATIVES
   only; without these two controls a rename of either would leave the
   corresponding [Fail] passing for the WRONG reason (reference not
   found), i.e. a vacuous guard.  Found by rename simulation, not by
   inspection.

--------
[coprod_IsALimit_iprod] 和 [component_diagram] 仅由 NEGATIVES 命名；如果没有这两个控制，一个的重命名会导致对应的 [Fail] 出现错误的通过（找不到引用），即空洞的保护。通过重命名模拟发现，而不是通过检查发现。
*)
Check @coprod_IsALimit_iprod.
Check @component_diagram.
(*
[iprod], [Limit] and [DiscreteCat_Functor] are DONOR names that the
   negatives name and no control did.  Their exposure is narrower than a
   leaf's -- renaming any of them breaks the target too -- but a rename
   would still leave the two formability negatives passing for
   reference-not-found rather than for the universe fact, so they are
   guarded here.  Found by rename simulation, not by inspection.

--------
[iprod]、[Limit] 和 [DiscreteCat_Functor] 是 DONOR 名称，而负面名称和无控制名称不是。它们的暴露范围比一片叶子还窄——重命名它们中的任何一个也会破坏目标——但重命名仍然会让两个可形成性负面通过引用未找到，而不是通过宇宙事实，因此它们在这里受到保护。是通过重命名模拟发现的，而不是通过检查。
*)
Check @iprod.
Check @Limit.
Check @DiscreteCat_Functor.
Check @ComponentDecomposition.
Check @cd_index.
Check @cd_rep.
Check @cd_part.
Check @cd_join.
Check @cd_sep.
Check @cd_compare.
Check @cd_equivalence.
Check @cd_bundled_equivalence.
Check @components_IsALimit.
Check @components_Limit.
Check @naive_pi0_sum.
Check @naive_pi0_sum_not_connected.
Check @no_ESO_into_naive_pi0_sum.
Check @TwoSum_not_connected.
Check @CoqPair_IsALimit.
Check @CoqPair_med_computes.
