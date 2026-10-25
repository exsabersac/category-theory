(**
* Probe for Functor/Hom/Continuous.v (issue #428)

    Pins the measured boundaries of the isomorphism form of hom-functor
    continuity: one CONVERSION refusal (N1: the two presentations of the
    hom-diagram, [HomFrom c ◯ F] and [HomDiagram c F], agree on objects and
    on the action of [fmap] but not at the [fmap] field, an opaque
    [Program] obligation) and two UNIVERSE refusals (N2: the carrier and
    relation levels of every set in the target are pinned to the hom level
    of the source, so the hom-functor of a fixed category cannot be read
    into a strictly larger universe of sets — only the level of the universe
    holding Sets' objects is free; Mac Lane's Remark 1 as far as it holds;
    N3: the [Sets] limit of the hom-diagram needs the
    shape's object level at or below that carrier level, while #331's
    preservation theorem does not — Riehl's large-diagram footnote).  Each
    refutation was stripped one at a time in a copy of the whole file; the
    import list mirrors the target's.  Section D's readbacks and the guard
    block are positive controls.

--------
* 探针用于函子/霍姆/连续.v（问题 #428）

固定同态函子同构形式的测量边界连续性：一个转换拒绝（N1：同态图的两种表示形式 [HomFrom c ◯ F] 和 [HomDiagram c F] 在对象及 [fmap] 的作用上是一致的，但在 [fmap] 字段上不一致，这是一个不透明的 [Program] 义务）以及两个宇宙拒绝（N2：目标中每个集合的承载者和关系层次被固定在源的同态层次上，因此不能将固定范畴的同态函子读取到严格更大的集合宇宙中——只有承载 Sets' 对象的宇宙层次是自由的；只要 Mac Lane 的备注1成立；N3：同态图的 [Sets] 极限需要形状对象的层次在或低于该承载者层次，而 #331 的保持定理则不需要——Riehl 的大图注释）。每一个反驳在整个文件的副本中一次被剥离；导入列表与目标的相同。D节的回读和保护块是阳性对照。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.End.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Functor.Hom.Continuous.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe428_absent_name.

(**
** A: the two presentations of the hom-diagram agree on objects and on
       the action of [fmap], not at the [fmap] field

--------
** A：同态图的两个表示在对象上以及在 [fmap] 的作用上是一致的，而在 [fmap] 域上则不一致
*)

Section Presentations.

Context {J C : Category} (c : C) (F : J ⟶ C).

(* controls: objects, and the action on an element, both convert / 控件：对象，以及对元素的操作，两者都转换 *)
Example p428_fobj : fobj[@HomFrom C c ◯ F] = fobj[HomDiagram c F] := eq_refl.

Example p428_fmap_value {j j' : J} (g : j ~{J}~> j') (h : c ~{C}~> F j) :
  fmap[@HomFrom C c ◯ F] g h = fmap[HomDiagram c F] g h := eq_refl.

(*
N1 CONVERSION: the whole [fmap] field does not — the setoid morphism's
   respectfulness proof is an opaque [Program] obligation:
   [Curried_Hom_obligation_1], auto-discharged in Functor/Hom.v, against
   [HomDiagram]'s written-out one in Structure/Limit/Weighted.v

--------
N1 转换：整个 [fmap] 字段不——集合态态射的尊重性证明是一个不透明的 [Program] 义务：[Curried_Hom_obligation_1]，在 Functor/Hom.v 中自动解决，相对于 Structure/Limit/Weighted.v 中写出的 [HomDiagram] 证明
*)
Fail Example p428_fmap_field {j j' : J} (g : j ~{J}~> j') :
  fmap[@HomFrom C c ◯ F] g = fmap[HomDiagram c F] g := eq_refl.

(* controls: the carriers Remark 2 and the Riehl items compute with / 控制：承运人备注2和Riehl项目进行计算 *)
Example p428_image_apex (N : Cone F) :
  carrier (vertex_obj[FCone (@HomFrom C c) N]) = (c ~{C}~> vertex_obj[N])
  := eq_refl.

Example p428_limit_carrier :
  carrier (Sets_limit_obj (HomDiagram c F)) = Sets_limit_carrier (HomDiagram c F)
  := eq_refl.

Example p428_cone_carrier :
  carrier (fobj[ConePresheaf F] c) = @ACone J C c F := eq_refl.

End Presentations.

(** ** B: Remark 1 — which universe of sets / ** B: 备注 1 — 哪个集合的宇宙 *)

Section Universes.

Universe o1 h1 hbig sbig.
Constraint h1 < hbig.
Constraint hbig < sbig.

Context (Cw : Category@{o1 h1 h1}) (cw : Cw).

(*
control: the level of the universe HOLDING Sets' objects is free above
   the carrier level ([Sets@{o so} : Category@{so o o}], Instance/Sets.v)

--------
控制：宇宙 HOLDING Sets 的对象的水平在承载级别之上是自由的（[Sets@{o so} : Category@{so o o}]，实例/Sets.v）
*)
Check (@HomFrom Cw cw : Cw ⟶ Sets@{h1 sbig}).
Check (@hom_continuous_at Cw cw
       : ContinuousFunctor (@HomFrom_at Cw cw : Cw ⟶ Sets@{h1 sbig})).

(*
N2 UNIVERSE: the CARRIER level — and with it, [SetoidObject@{o o}], the
   relation level — is pinned to the hom level of the source: the
   hom-functor of a FIXED category cannot be read into a strictly larger
   universe of sets

--------
N2 宇宙：承载层——以及随之而来的 [SetoidObject@{o o}]，即关系层——被固定在源的同层上：固定范畴的同函子不能被读入严格更大的集合宇宙
*)
Fail Check (@HomFrom Cw cw : Cw ⟶ Sets@{hbig sbig}).

End Universes.

(**
** C: smallness — Remark 2's [Sets]-side limit needs the shape's objects
       at or below the carrier level; #331's theorem does not

--------
** C: 小尺寸 —— 备注2的 [Sets] 侧限需要形状的对象在承载层级之上或之下；#331 的定理则不需要
*)

Section Smallness.

Universe jo h.
Constraint h < jo.

Context (Jw : Category@{jo h h}) (Cw : Category@{h h h}) (cw : Cw).

(* controls: the hom-diagram forms and #331's preservation applies / 控制：同态图的形式和#331的保持适用 *)
Check (fun F : Jw ⟶ Cw => @HomFrom Cw cw ◯ F).
Check (fun F : Jw ⟶ Cw => hom_PreservesLimitCone cw F).

(*
N3 UNIVERSE: the [Sets] limit of the hom-diagram is refused —
   [Sets_Limit] needs the shape's object level at or below [Sets]' carrier
   level, here [h]

--------
N3 宇宙：同源图的 [Sets] 极限被拒绝——
[Sets_Limit] 需要形状的对象级别在 [Sets] 的承载级别或以下，这里是 [h]
*)
Fail Check (fun F : Jw ⟶ Cw => Sets_Limit (@HomFrom Cw cw ◯ F)).

End Smallness.

(** ** D: readbacks / ** D：复读 *)

Section Readbacks.

Context {J C : Category} {F : J ⟶ C} (L : Limit F) (c : C).

Check (remark2_iso L c).
Check (remark2_natural L).
Check (remark2_comparison_iso L c).
Check (end_Limit c F).
Check (cone_nat_iso (F:=F) c).
Check (limtuple_cone_iso (F:=F) c).

(* the alias names the issue asks to audit / 该别名名称是问题要求审核的 *)
Check (hom_preserves_limits c).
Check (@cohom_carries_colimits_to_limits C c).

End Readbacks.

(** ** Guard block / ** 防守格挡 *)

Check @HomFrom.
Check @HomTo.
Check @HomDiagram.
Check @Sets_Limit.
Check @Sets_limit_obj.
Check @Sets_limit_carrier.
Check @ConePresheaf.
Check @ACone.
Check @FCone.
Check @Cone.
Check @Limit.
Check @hom_PreservesLimitCone.
Check @hom_ContinuousFunctor.
Check @hom_continuous_at.
Check @HomFrom_at.
Check @PreservesLimitCone_transport.
Check @ContinuousFunctor_transport.
Check @remark2_iso.
Check @remark3_iso.
Check @hom_iprod_iso.
Check @cohom_icoprod_iso.
Check @end_Limit.
Check @fmap.
Check @fobj.
Check @carrier.
Check @vertex_obj.
