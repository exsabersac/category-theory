(**
* Boundary probes for group congruences and normal subgroups

    Companion to Instance/Grp/Congruence.v (issue #301, Mac Lane §II.8
    Exercise 2; Awodey §4.2 and §4.5 Exercise 1).  That file makes six
    strength claims whose negative side is a conversion boundary.  A
    measurement made outside the tree would not be noticed by a refactor,
    so it is pinned here.  **If the [Fail] commands below stop being
    rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED, for
    the reason Test/ProbeQuiverConstructions.v and Test/ProbeGrpQuotient.v
    give: a [Fail] alone passes just as happily when a name has been
    renamed out from under it.  The instrument itself was checked --
    wrapping [Fail] around a succeeding command aborts compilation with
    "The command has not failed!" -- and every negative below was compiled
    once with the [Fail] stripped, to confirm the rejection is the
    intended one and not a syntax, scope or resolution error.  All six
    report a conversion error ("The term ... has type ... while it is
    expected to have type ...", followed by "cannot unify X and Y").

    The import list below is Instance/Grp/Congruence.v's own, in its
    order, INCLUDING the deliberate placement of the [Instance.Grp]
    satellites last.  That matters twice over: a short prefix would leave
    coercions unresolved and the negatives would then be reported as
    illegal applications rather than as the conversion errors they are;
    and a different order would make the unqualified [GrpObject]
    Construction/Deloop.v's rather than Instance/Grp.v's, so the
    statements would be about a different record.

    THE SIX BOUNDARIES.

    (1) THE TWO GROUPOID WITNESSES ARE NOT THE SAME TERM.
    [deloop_GrpObject_agrees] shows that the record conversion
    [grp_deloop_GrpObject] deloops to Instance/Grp/Free.v's [grp_deloop]
    by [eq_refl], and [grp_deloop_ginv] that the chosen inverse is the
    group inverse.  What does NOT follow is that
    [Deloop_IsGroupoid (grp_deloop_GrpObject H)] and
    [grp_deloop_IsGroupoid H] are one term: the first routes through
    Construction/Deloop.v's [Deloop_group_invertible], a [Program
    Instance] whose two obligations are [Qed]-opaque, the second names
    Instance/Grp.v's [grp_mul_inv_r] and [grp_mul_inv_l] directly.  The
    DATA agree (control), the records do not (negative 1).

    (2) THE MEMBERSHIP ROUND TRIP IS A BICONDITIONAL, NOT A CONVERSION.
    [ns_of_cong_of_ns] says the members of [cong_ns (ns_rel N)] are the
    members of N, and it is [quot_rel_unit_iff] applied.  It is an [iff]
    and not an equality of types because the recovered membership unfolds
    to "a * e⁻¹ lies in N", not to "a lies in N"; the control shows
    exactly what it DOES convert to, so the negative is located rather
    than merely observed.

    (3) THE QUOTIENT CATEGORY IS NOT LEIBNIZ-EQUAL TO THE DELOOPING OF THE
    QUOTIENT GROUP.  Since the PR "algebraic carriers are sets"
    (2026-09-17) [deloop_quotient] is built from [ns_prel], the
    propositional truncation of [ns_rel], because [QuotientGrp]'s own
    equality is now the truncation of [quot_rel]; the two had to move in
    lockstep or one leg of the isomorphism would have been an elimination
    of a [Prop] into a [Type].  Every control and every negative in this
    section was re-measured after that change and all still hold, with
    their text unchanged.  [deloop_quotient_iso] is stated at
    [≅[StrictCat]],
    the genuine isomorphism of categories.  Exactly FOUR of the ten
    fields a [Category] record literal supplies are convertible -- [obj],
    [hom], [id] and [compose] (the class's [uhom], [dom] and [cod] are
    [:=] definitions derived from them, not data either construction
    chooses) -- and the three controls below exhibit the last three
    ([obj] is [poly_unit] on both sides by inspection).  The other six are
    built twice: [homset], whose two [Equivalence] witnesses are
    [Quotient_equivalence] and [QuotientGrp]'s own [Program] obligation,
    both [Qed]; and with it [compose_respects], [id_left], [id_right],
    [comp_assoc] and [comp_assoc_sym], which [Quotient] assembles from
    [cong_comp]/[cong_incl] and [Deloop] from the monoid's law fields.  So
    the whole records are not convertible (negative 3).  Without this
    probe "isomorphism of categories" could drift into being read as
    "equal".

    (4) THE TWO MEDIATORS AGREE ON THE MAP, NOT AS RECORDS.
    [cat_med_is_quot_med] is [eq_refl] on the underlying map: the
    categorical route through [QuotientLift] lands on #313's [quot_med].
    The [GrpHom] records are not convertible, their unit- and
    product-preservation fields being separately built (one by
    [Build_GrpHom'] from [fmap_comp], the other by [Program]).

    (5) THE CATEGORICAL KERNEL IS COEXTENSIVE WITH [KernelNS], NOT EQUAL.
    [kernel_ns] is obtained with no group-level obligation, from
    [FunctorKernel_Congruence] and [cong_ns].  Its members are the a with
    h a ≈ h e; #313's [KernelNS] collects the a with h a ≈ e.
    [grp_map_unit h] is the one step between them, and it is a proof, not
    a conversion.  The control shows what the categorical membership IS.

    (6) THE PROJECTION FUNCTORS AGREE ON ARROWS, NOT ON OBJECTS.
    [deloop_proj_fmap] is [eq_refl]; [deloop_proj_fobj] needs a [destruct].
    The reason is Construction/Deloop/Transform.v's, quoted in the
    target file: [poly_unit] is an ordinary inductive with no definitional
    eta, so the constant function at [ttt] and the identity on a
    one-element type are different terms.  This probe pins that the
    difference is real and not an artifact of how the lemma was written.

    WHAT IS DELIBERATELY *NOT* PROBED.  The [≅[Cat]] reading derived from
    [deloop_quotient_iso] carries no conversion claim at all, and the
    setoid isomorphism [ns_cong_iso] is a statement about setoids whose
    equivalences are logical, so neither has a strict side to pin.

--------
* 用于群同余和正规子群的边界探针

《Instance/Grp/Congruence.v 的配套文件》（问题 #301，Mac Lane §II.8 练习 2；Awodey §4.2 和 §4.5 练习 1）。该文件提出了六个强度声明，其负面方面是一个转换边界。在树外进行的测量不会被重构检测到，因此在这里固定。**如果下面的 [Fail] 命令不再被拒绝，该文件将导致构建失败。**

每一个阴性测试都配有一个必须成功的阳性对照，原因是 Test/ProbeQuiverConstructions.v 和 Test/ProbeGrpQuotient.v 显示：单独的 [Fail] 即使在名称已被重命名后仍然可以顺利通过。该工具本身也已被检查——在一个成功的命令周围包裹 [Fail] 会中止编译，并显示“命令未失败！”——下面的每一个阴性测试都曾在去掉 [Fail] 的情况下编译过一次，以确认拒绝是预期的，而不是语法、作用域或解析错误。所有六个测试都报告了转换错误（“术语...的类型为...，而期望类型为...”，随后出现“无法统一 X 和 Y”）。

下面的导入列表是 Instance/Grp/Congruence.v 自己的列表，按照它自己的顺序，包括特意将 [Instance.Grp] 卫星最后放置。这一点有两个重要影响：短前缀会导致强制转换未解决，然后负值将被报告为非法应用，而不是它们实际上是的转换错误；不同的顺序会让未限定的 [GrpObject] 构造属于 Construction/Deloop.v，而不是 Instance/Grp.v，因此这些语句将涉及不同的记录。

六个边界。

(1) 这两个群体见证不是同一个项。  
[deloop_GrpObject_agrees] 显示记录转换  
[grp_deloop_GrpObject] 通过 [eq_refl] 解绕到 Instance/Grp/Free.v 的 [grp_deloop]，并且 [grp_deloop_ginv] 表示所选的逆元是群逆元。 但不随之而来的结论是 [Deloop_IsGroupoid (grp_deloop_GrpObject H)] 和 [grp_deloop_IsGroupoid H] 是相同的项：第一个通过 Construction/Deloop.v 的 [Deloop_group_invertible]（一个[程序实例]，其两个义务是 [Qed] 不透明的），第二个直接命名 Instance/Grp.v 的 [grp_mul_inv_r] 和 [grp_mul_inv_l]。数据一致（控制），记录不一致（负 1）。

(2) 成员往返是一个双条件，而不是转换。[ns_of_cong_of_ns] 表示 [cong_ns (ns_rel N)] 的成员是 N 的成员，并且应用了 [quot_rel_unit_iff]。它是一个 [iff]，而不是类型的等式，因为恢复的成员展开为“a * e⁻¹ 属于 N”，而不是“a 属于 N”；控制精确地显示了它转换成的内容，所以否定是被定位的，而不仅仅是被观察的。

(3) 商范畴不等于商群的去环绕。由于 PR “代数承载体是集合”（2026-09-17）[deloop_quotient] 是由 [ns_prel] 构建的，即 [ns_rel] 的命题截断，因为 [QuotientGrp] 自身的等式现在是 [quot_rel] 的截断；两者必须同步移动，否则同构的一个部分将是将 [Prop] 消去到 [Type]。在此更改之后，本节中的每个控制和每个负号都经过重新测量，且全部仍然成立，文本未变。[deloop_quotient_iso] 在 [≅[StrictCat] 中陈述，为范畴的真正同构。
在十个由 [Category] 记录字面量提供的字段中，恰好有四个是可转换的——[obj]、[hom]、[id] 和 [compose]（该类的 [uhom]、[dom] 和 [cod] 是从它们派生的 [:=] 定义，不是任一构造选择的数据）——下面的三个控件展示了最后三个（通过检查，[obj] 在两边都是 [poly_unit]）。其余六个是构建了两次的：[homset]，其两个 [Equivalence] 证人是 [Quotient_equivalence] 和 [QuotientGrp] 自身的 [Program] 义务，两者都是 [Qed]；以及随之的 [compose_respects]、[id_left]、[id_right]、[comp_assoc] 和 [comp_assoc_sym]，这些是 [Quotient] 从 [cong_comp]/[cong_incl] 和来源于幺半群定律字段的 [Deloop] 组装的。所以整个记录不可转换（负 3）。
没有这个探针，“范畴同构”可能会被理解为“相等”。

(4) 两个中介在地图上达成一致，而不是在记录上。  
[cat_med_is_quot_med] 在基础地图上是 [eq_refl]：通过 [QuotientLift] 的分类路径落在 #313 的 [quot_med] 上。  
[GrpHom] 记录不可转换，它们的单位和产品保存字段是分别构建的（一个由 [Build_GrpHom'] 从 [fmap_comp] 构建，另一个由 [Program] 构建）。

(5) 范畴核与 [KernelNS] 是共延的，但不相等。[kernel_ns] 是在没有群组级义务的情况下，从 [FunctorKernel_Congruence] 和 [cong_ns] 获得的。它的成员是满足 h a ≈ h e 的 a；#313 的 [KernelNS] 收集的是满足 h a ≈ e 的 a。[grp_map_unit h] 是它们之间的一步，它是一个证明，而不是一个转换。控制显示了范畴成员资格的具体情况。

(6) 投影函子在箭头上是一致的，但在对象上不一致。
[deloop_proj_fmap] 是 [eq_refl]；[deloop_proj_fobj] 需要一个 [destruct]。
原因是 Construction/Deloop/Transform.v 中的内容，在目标文件中引用：[poly_unit] 是一个普通归纳类型，没有定义性 eta，因此在 [ttt] 上的常函数和在单元素类型上的恒等函数是不同的项。该探针证明了这种差异是真实的，而不是引理编写方式造成的假象。

什么是故意*不*探测的。从 [deloop_quotient_iso] 得到的 [≅[Cat]] 读数根本不包含任何转换声明，而且集合同构 [ns_cong_iso] 是一个关于集合的声明，其等价性是逻辑性的，所以二者都没有一个严格的方面可以依附。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Congruence.

Generalizable All Variables.

(** ** Negative 1: the two groupoid witnesses are not the same term / ** 负1：两个群体见证不是同一个项 *)

(*
POSITIVE CONTROL: the record conversion deloops to the tree's own
   delooping, and the chosen inverses agree, both by [eq_refl].

--------
正对照：记录转换与树自身的去环操作相对应，并且所选择的逆元一致，均由 [eq_refl] 进行。
*)
Example control_deloop_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example control_ginv_agrees (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(*
...and for the OTHER witness too, so that "the data agree" is about
   both of the terms the negative separates and not just one of them.

--------
...并且也针对另一个证人，这样“数据一致”就涉及被否定所分开的两个术语，而不仅仅是其中的一个。
*)
Example control_ginv_agrees_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* NEGATIVE: the whole [IsGroupoid] structures are not convertible. / 否定：整个 [IsGroupoid] 结构不可转换。 *)
Fail Definition negative_isgroupoid_record (H : GrpObject) :
  grp_deloop_IsGroupoid' H = grp_deloop_IsGroupoid H := eq_refl.

(** ** Negative 2: the membership round trip is a biconditional / ** 否定2：会员往返是一个双条件 *)

(* POSITIVE CONTROL: what the recovered membership DOES convert to. / 阳性对照：恢复的会员资格确实转换成的内容。 *)
Example control_round_unfolds {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a
    = quot_rel N a (grp_unit G) := eq_refl.

(* NEGATIVE: it is not membership in N on the nose. / 否定：它并不是严格属于 N 的成员。 *)
Fail Definition negative_round_strict {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a = sub_mem N a := eq_refl.

(** ** Negative 3: the quotient category is not the delooping, on the nose / ** 负 3：商范畴不是严格意义上的去环化 *)

(*
POSITIVE CONTROLS: objects, hom type, identity and composition agree by
   [eq_refl] -- the four items Instance/Grp/Congruence.v claims.  The
   object leg was measured but unguarded until the PR "algebraic carriers
   are sets" (2026-09-17); it is [control_quotient_obj] below.

--------
阳性对照：对象、同类类型、同一性和组合通过 [eq_refl] 达成一致 —— 即 Instance/Grp/Congruence.v 声称的四项内容。对象部分已经测量，但在 PR “代数承载体是集合”(2026-09-17) 之前没有受保护；下面是 [control_quotient_obj]。
*)
Example control_quotient_obj {G : GrpObject} (N : NormalSubgroup G) :
  obj[deloop_quotient N] = obj[grp_deloop (QuotientGrp N)] := eq_refl.

Example control_quotient_hom {G : GrpObject} (N : NormalSubgroup G) :
  (ttt ~{deloop_quotient N}~> ttt)
    = (ttt ~{grp_deloop (QuotientGrp N)}~> ttt) := eq_refl.

Example control_quotient_id {G : GrpObject} (N : NormalSubgroup G) :
  @id (deloop_quotient N) ttt = @id (grp_deloop (QuotientGrp N)) ttt := eq_refl.

Example control_quotient_compose {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) :
  @compose (deloop_quotient N) ttt ttt ttt f g
    = @compose (grp_deloop (QuotientGrp N)) ttt ttt ttt f g := eq_refl.

(* NEGATIVE: the whole categories are not convertible. / 否定：整个类别不可转换。 *)
Fail Definition negative_quotient_category {G : GrpObject}
  (N : NormalSubgroup G) :
  deloop_quotient N = grp_deloop (QuotientGrp N) := eq_refl.

(** ** Negative 4: the two mediators agree on the map, not as records / ** 负4：两个调解员同意地图，而不是作为记录 *)

(* POSITIVE CONTROL: the underlying maps are the same term. / 阳性对照：基础地图是相同的术语。 *)
Example control_med_map {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) (a : carrier (QuotientGrp N)) :
  grp_map (cat_med N p) a = grp_map (quot_med N p) a := eq_refl.

(* NEGATIVE: the homomorphism records are not. / 消极：同态记录不存在。 *)
Fail Definition negative_med_record {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) : cat_med N p = quot_med N p := eq_refl.

(** ** Negative 5: the categorical kernel is coextensive, not equal / ** 负五：范畴核是共延的，不是相等的 *)

(* POSITIVE CONTROL: what the categorical kernel's membership IS. / 阳性对照：类别核的隶属关系是什么。 *)
Example control_kernel_unfolds {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = (grp_map h a ≈ grp_map h (grp_unit G)) := eq_refl.

(* NEGATIVE: it is not #313's kernel membership on the nose. / 消极：它并不是#313的核心成员身份本身。 *)
Fail Definition negative_kernel_strict {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = sub_mem (KernelNS h) a := eq_refl.

(** ** Negative 6: the projection functors agree on arrows, not on objects / ** 负6：投影函子在箭头上相同，而在对象上不相同 *)

(* POSITIVE CONTROL: the arrow actions are the same term. / 阳性对照：箭头动作是相同的术语。 *)
Example control_proj_fmap {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

(* NEGATIVE: the object actions are not. / 消极：对象动作不存在。 *)
Fail Definition negative_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x := eq_refl.
