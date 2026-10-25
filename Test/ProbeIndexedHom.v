(**
* Boundary probes for the indexed hom-set bijections

    Companion to Structure/Limit/Indexed/Hom.v (issue #320; Mac Lane §III.3
    def 2, Riehl §3.1 Remark 3.1.27 clauses (i) and (ii)).  **If the [Fail]
    commands below stop failing, this file breaks the build.**

    THE TWO KINDS OF NEGATIVE ARE NOT THE SAME AND ARE NOT DESCRIBED WITH
    ONE WORD.

    (1) FORMABILITY.  Five [Fail Check]s, in two groups, both about
    universes.

    Group (1a), three negatives.  The comparison map
    [iprod_hom_transform] — and everything built on it — requires the INDEX
    universe to sit at or below the ambient category's HOM universe.  The
    reason is that its source is the hom-functor [Curried_CoHom C q], whose
    objects ARE the hom-setoids of [C]; a [SetoidObject] carries its
    [Setoid] as a field, and neither record is cumulative in this library
    (measured: lifting a [Setoid@{a a}] to a [Setoid@{b b}] with [a < b] is
    rejected, and likewise for [SetoidObject]), so the target [Sets]'
    carrier universe is forced EQUAL to [C]'s hom universe rather than
    merely above it.  The bound on the index follows.
    The bound is NOT inherited: the target functor [iprod_hom_functor]
    alone tolerates a strictly larger index (its object action builds a
    fresh dependent-function type through [Sets_iprod_obj], which lifts),
    and so does the hom-functor alone, so the two positive controls of this
    group locate the rejection at the [Transform] that puts them in ONE
    functor category, not at either functor.

    Group (1b), two negatives.  The two LIMIT-shaped bridges
    [limit_hom_iso] and [colimit_hom_iso] are stated with [{A : Set}], and
    that binder is the group (1a) bound taken at [C]'s hom universe.

    RECORDED CORRECTION.  An earlier revision said the binder was "the
    COMBINATION of a donor restriction with the group (1a) bound — neither
    alone forces it", and named the donor restriction as
    "[Structure/Limit/Product.v]'s [iprod] is over
    [C : Category@{u Set Set}] (the [DiscreteCat] hom-setoid is strict
    equality), with its INDEX universe free".  There is no donor
    restriction: [iprod]'s [Set] was a universe-minimization artifact of
    Instance/Discrete.v's unannotated [DiscreteCat_Functor], repaired in
    the PR "algebraic carriers are sets" (2026-09-17).  MEASURED after the
    repair, in a copy of this whole file: re-declaring §(1b)'s [C] at
    [Category@{uo uh uh}] with [Set < uh] leaves both controls passing and
    both negatives refusing, unchanged.  So the two negatives are the
    group (1a) bound alone, and §(1b)'s [C] is still written
    [Category@{uo Set Set}] only because that is the instance the bridges'
    [{A : Set}] binder is about.  The two controls still show
    [Limit (DiscreteCat_Functor f)] and [iprod f L] formable at a large
    index over such a [C].

    Scope these two negatives precisely: they fail because the bridges are
    DECLARED [{A : Set}], so they would fail for that reason whatever the
    universe situation, and they cannot by themselves detect that the binder
    is forced rather than stylistic.  The separating power comes from the two
    controls plus [iprod_hom_transform]'s own signature, and NOT from these
    two negatives alone.  The half they do not measure was checked outside
    the tree and holds: writing either bridge with [{A : Type}] is rejected
    ("cannot ensure that [Type@{u}] is a subtype of [Set]"), so the binder is
    forced.  That variant is not landed here as a sixth negative; it is the
    one that would notice if the pin ever stopped being necessary.

    (2) CONVERSION.  Two claims of Leibniz equality are rejected because
    the round trip through the mediator is not definitional — it is what the
    universal property's uniqueness clause proves.  These are [Fail
    Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed
    is convertibility of the two terms.  Five controls across the two
    sections are the strict readings that DO hold, so the rejection is
    attributable
    to the round trip and not to the [transform]/[morphism] projections
    being stuck; at [Sets] a further control shows the agreement holding one
    level in, at the underlying map, which locates the rejection precisely at
    the [proper_morphism] certificate.

    COUNTS.  Seven negatives — five formability, two conversion — and ten
    positive controls.  This is not a one-to-one pairing: the controls of
    each group serve that group's negatives jointly.  The instrument itself
    was checked — wrapping [Fail] around a succeeding command reports "The
    command has not failed!" and aborts compilation — and every negative was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended one:

      - group (1a), three reports of "universe inconsistency: Cannot
        enforce ua <= uh because uh < ua", naming the declared universes;
      - group (1b), two reports of "universe inconsistency: Cannot enforce
        ub <= Set";
      - group (2), two "cannot unify" conversion errors.

    The import list is the target file's own, in the target file's order,
    plus the target file itself.

--------
* 用于索引同类集合双射的边界探针

Structure/Limit/Indexed/Hom.v 的补充文件（问题 #320；Mac Lane §III.3 定义 2，Riehl §3.1 注解 3.1.27 条款 (i) 和 (ii)）。**如果下面的 [Fail] 命令不再失败，此文件将导致构建失败。**

这两种否定不同，并不能用一个词来描述。

(1) 成形性。五个 [Fail Check]，分为两组，都关于宇宙。

组（1a），三个否定。比较映射 [iprod_hom_transform] —— 以及建立在其上的所有内容 —— 需要 INDEX 宇宙位于或低于环境类别的 HOM 宇宙。原因是它的源是同态函子 [Curried_CoHom C q]，其对象是 [C] 的同态集合（hom-setoid）；一个 [SetoidObject] 将其 [Setoid] 作为字段携带，并且在此库中两个记录都不是累积的（衡量：将一个 [Setoid@{a a}] 提升到带有 [a < b] 的 [Setoid@{b b}] 是被拒绝的，对于 [SetoidObject] 也是如此），因此目标 [Sets] 的承载宇宙被迫等于 [C] 的同宇宙，而不仅仅是高于它。指数的界限随之而来。这个界限不是继承的：目标函子 [iprod_hom_functor] 本身能够容忍更大的指数（它的对象作用通过 [Sets_iprod_obj] 构建一个新的依赖函数类型，该类型被提升），同样，单独的同态函子也是如此，因此这一组的两个正控制将拒绝定位在将它们放入同一个函子范畴的 [Transform] 上，而不是在任一函子上。

第1b组，两个否定。两个LIMIT形状的桥[limit_hom_iso]和[colimit_hom_iso]与[{A : Set}]一起说明，并且该结合剂是第1a组在[C]的同源宇宙中结合的。

记录更正。早期的修订版本称，绑定器是“带有组 (1a) 绑定的捐赠者限制的组合——单独任何一项都不会强制绑定”，并将捐赠者限制命名为“[Structure/Limit/Product.v] 的 [iprod] 位于 [C : Category@{u Set Set}] 之上（[DiscreteCat] 同质集合是严格相等的），其 INDEX 宇宙是自由的”。实际上没有捐赠者限制：[iprod] 的 [Set] 是 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor] 的宇宙最小化产物，该问题在 PR “代数载体是集合”（2026-09-17）中已修复。在修复后测量，在此整个文件的一个副本中：重新声明§(1b)的[C]为[Category@{uo uh uh}]并使用[Set < uh]，两种控制都通过，两种阴性都拒绝，没有变化。因此，这两个阴性是单独绑定的第(1a)组，而§(1b)的[C]仍然只写作[Category@{uo Set Set}]，因为这是桥接的[{A : Set}]绑定器所涉及的实例。这两个控制仍然显示[Limit (DiscreteCat_Functor f)]和[iprod f L]可在如此[C]上以大索引形成。

准确地限定这两个否定：它们失败的原因是桥被声明为 [{A : Set}]，所以无论宇宙情况如何，它们都会因此失败，而且它们自身无法检测绑定器是被强制而非风格性的。分离能力来自这两个控制加上 [iprod_hom_transform] 自己的特性，而不是仅靠这两个否定。它们未测量的那一半在树之外已经检查过且有效：用 [{A : Type}] 编写任一桥都会被拒绝（“无法确保 [Type@{u}] 是 [Set] 的子类型”），因此绑定器是被强制的。那个变体并没有作为第六个负面出现在这里；它是那个会注意到别针是否不再必要的东西。

(2) 转换。两个莱布尼茨等式的声明被拒绝，因为通过中介进行的往返不是定义性的 —— 它是由通用属性的唯一性条款所证明的。这些是 [Fail Definition ... := eq_refl] 而不是 [Fail Example ... : T.]：失败的类型指定只会保护语句，而声明的是两个项的可转换性。在这两个部分中有五个控制是严格读取且确实成立的，因此拒绝是由于往返过程，而不是因为 [transform]/[morphism] 投影被卡住；在 [Sets]，进一步的控制显示协议在底层地图中的一个级别上仍然成立，这将拒绝精确地定位在 [proper_morphism] 证书上。

计数。七个否定测试——五个可形成性，两个转换——以及十个积极对照。这不是一对一的配对：每组的对照共同用于该组的否定测试。仪器本身已被检查——将 [Fail] 包裹在一个后续命令周围会报告“命令未失败！”并中止编译——每个否定测试都曾在去除 [Fail] 的情况下编译一次，以确认错误是预期的错误：

- 组（1a），三条“宇宙不一致：无法强制 ua <= uh 因为 uh < ua”的报告，标明了声明的宇宙；
- 组（1b），两条“宇宙不一致：无法强制 ub <= Set”的报告；
- 组（2），两条“无法统一”转换错误。

导入列表是目标文件自身的，以目标文件的顺序排列，加上目标文件本身。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.

Generalizable All Variables.

(** ** (1a) An index universe strictly above the ambient hom universe / ** (1a) 严格高于环境同类宇宙的索引宇宙 *)

Section IndexAboveHoms.

Universes uo uh ua.
Constraint uh < ua.

Context (C : Category@{uo uh uh}) (A : Type@{ua}) (f : A -> C).

(*
Positive control 1: the TARGET functor alone accepts the large index —
   its object action is a fresh dependent-function setoid, which lifts.

--------
阳性对照 1：仅目标函子接受大索引——其对象动作是一个新的依赖函数等价类，并且可以提升。
*)
Check (iprod_hom_functor f).

(* Positive control 2: the coproduct-side target functor likewise. / 阳性对照2：共产物侧的目标函子同样。 *)
Check (icoprod_hom_functor f).

(*
Positive control 3: the SOURCE functor is formable at this category, so
   neither half of the comparison is what gets rejected.

--------
正向对照3：在该类别中可以形成SOURCE函子，因此比较的两半都不是被拒绝的部分。
*)
Check (fun q : C => fobj[Curried_CoHom C] q).

(*
Negative 1: the comparison map itself is not formable — the two functors
   have to live in ONE [Sets], and the hom-functor pins that [Sets]' carrier
   universe to [C]'s hom universe.

--------
负面 1：比较图本身无法形成——两个函子必须存在于同一个 [Sets] 中，并且同态函子将 [Sets] 的承载宇宙固定到 [C] 的同态宇宙。
*)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a) =>
              @iprod_hom_transform C A f q proj).

(* Negative 2: hence neither is the isomorphism. / 负 2：因此同构也不是。 *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a)
                (H : @IsIndexedProduct C A f q proj) =>
              @iprod_hom_iso C A f q proj H).

(*
Negative 3: the coproduct side is the same statement at [C^op] and
   inherits the same bound.

--------
负3：副产品侧在[C^op]处是相同的陈述，并继承相同的约束。
*)
Fail Check (fun (p : C) (inj : forall a : A, f a ~> p) =>
              @icoprod_hom_transform C A f p inj).

End IndexAboveHoms.

(** ** (1b) The limit-shaped bridges, and why they carry [{A : Set}] / ** (1b) 极限形桥梁，以及为什么它们承载 [{A : Set}] *)

Section LimitShapeIndex.

Universes uo ub.
Constraint Set < ub.

(*
[C]'s homs are written at [Set] because that is the instance the
   bridges' [{A : Set}] binder is about, NOT because anything forces it:
   see the header's recorded correction.  [Limit (DiscreteCat_Functor f)]
   leaves both [C]'s hom universe and the INDEX free since
   [DiscreteCat_Functor] was annotated.

--------
[C] 的 homs 被写在 [Set]，因为那是桥接的 [{A : Set}] 绑定器所涉及的实例，而不是因为有什么强制要求：参见标题记录的更正。[Limit (DiscreteCat_Functor f)] 在 [DiscreteCat_Functor] 被注释后，保持了 [C] 的 hom 宇宙和索引的自由。
*)
Context (C : Category@{uo Set Set}) (A : Type@{ub}) (f : A -> C).

(* Positive control 4: the limit shape IS formable at this large index. / 阳性对照 4：在这个大指数下，该极限形状是可形成的。 *)
Check (Limit (DiscreteCat_Functor f)).

(* Positive control 5: so is the product object read off it. / 阳性对照5：因此产品对象也是从中读取的。 *)
Check (fun L : Limit (DiscreteCat_Functor f) => @iprod C A f L).

(*
Negative 4: the hom-set bijection at that limit is not — the group (1a)
   bound now reads "index at or below [Set]".

--------
负4：该极限处的同态集双射不是——该群（1a）绑定现在显示为“索引在 [Set] 或以下”。
*)
Fail Check (fun L : Limit (DiscreteCat_Functor f) => @limit_hom_iso C A f L).

(* Negative 5: dually. / 负五：双重地。 *)
Fail Check (fun L : Limit (@DiscreteCat_Functor A (C^op) f) =>
              @colimit_hom_iso C A f L).

End LimitShapeIndex.

(** ** (2) The round trip is not definitional / ** (2) 往返行程不是定义性的 *)

Section Conversion.

Context {C : Category}.
Context {A : Type}.
Context {f : A -> C}.
Context {q : C}.
Context {proj : forall a : A, q ~> f a}.
Context (H : IsIndexedProduct f q proj).
Context (c : C).
Context (u : c ~> q).
Context (fam : forall a : A, c ~> f a).

(* Positive control 6: the forward leg IS the comparison map, on the nose. / 阳性对照6：前腿就是比较地图，正好如此。 *)
Definition probe_to_control :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

(*
Positive control 7: the backward leg's value IS the mediator named by the
   pre-existing [∃!] accessor, on the nose.

--------
阳性对照 7：后腿的数值就是由预先存在的 [∃!] 访问器命名的中介，正是如此。
*)
Definition probe_from_control :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(*
Positive control 8: and the forward leg computes to restriction along the
   projections.

--------
阳性对照 8：并且前腿计算为沿投影的限制。
*)
Definition probe_transform_control :
  transform (to (iprod_hom_iso H)) c u = fun a : A => proj a ∘ u := eq_refl.

(*
Negative 6: but the round trip does NOT compute.  Recovering [u] from the
   family it restricts to is exactly the uniqueness clause of [iprod_desc],
   a [≈]-level fact with no definitional content; [iso_from_to] is where it
   is discharged.

--------
负6：但是往返是不成立的。从它所限制的族中恢复 [u] 恰恰是 [iprod_desc] 的唯一性条款，这是一个 [≈] 级别的事实，没有定义内容；[iso_from_to] 是它被解除的地方。
*)
Fail Definition probe_roundtrip :
  transform (from (iprod_hom_iso H)) c
    (transform (to (iprod_hom_iso H)) c u) = u := eq_refl.

End Conversion.

Section ConversionSets.

Context {A : Type}.
Context (F : A -> obj[Sets]).
Context (c : obj[Sets]).
Context (fam : forall a : A, c ~{Sets}~> F a).
Context (u : c ~{Sets}~> Sets_iprod_obj F).

(*
Positive control 9: at [Sets] the backward leg computes to the tupling
   map of Instance/Sets/Products.v.

--------
阳性对照 9：在 [Sets] 上，后向腿计算为 Instance/Sets/Products.v 的成对映射。
*)
Definition probe_sets_from_control :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

(*
Negative 7: the round trip still does not compute, even at the concrete
   [Sets] product where both legs reduce.  [SetoidMorphism] has primitive
   projections with eta conversion, so the comparison descends to the two
   fields, and it is the [proper_morphism] field that differs: the tupling
   rebuilds it as its own obligation.  Control 10, just below, is exactly
   that diagnosis — the [morphism] field DOES agree, on the nose.

--------
负面 7：即使在具体的 [Sets] 产品中，往返仍然无法计算，两段都减少了。[SetoidMorphism] 具有带有 eta 转换的原始投影，因此比较会下降到两个字段，而不同的是 [proper_morphism] 字段：元组将其重新构建为自身的义务。下面的控制 10 正是该诊断 — [morphism] 字段完全一致。
*)
Fail Definition probe_sets_roundtrip :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) = u := eq_refl.

(*
Positive control 10: the agreement holds one level further in, at the
   underlying map, so the rejection above is about the certificate field and
   not about either leg being stuck.

--------
阳性对照10：协议在更深一级的底层映射中仍然成立，因此上面的拒绝是关于证书字段的，而不是关于任一环节被卡住。
*)
Definition probe_sets_roundtrip_value_control (x : c) :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) x = u x := eq_refl.

End ConversionSets.
