Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Theory.Concrete.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Finite.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Functor.Construction.Postcompose.

Generalizable All Variables.

(** * Probes guarding Functor/Construction/Postcompose.v / * 保护 Functor/Construction/Postcompose.v 的探针 *)

(*
This file pins every strict attempt that Functor/Construction/Postcompose.v
   MADE AND LOST, so that a later change which quietly makes one of them
   succeed — or which renames the constants out from under the claim — breaks
   the build loudly instead of leaving the header's prose stale.  It follows
   the convention of Test/ProbeFunnyPoly.v and Test/ProbeQuiverConstructions.v.

   The import list is the target file's, in the target file's order, with
   Instance/Sets/Powerset.v (needed only by Group 4) and then the target
   itself appended.  That matters: a probe compiled against a short PREFIX of
   the real imports can fail for a missing-coercion or missing-notation
   reason and thereby pass VACUOUSLY.  (Instance/Field/Frac.v records an
   episode of exactly that.)  A superset does not carry that risk, and the
   target is Required last, so its names win any contest.

   TWO KINDS, KEPT LEXICALLY APART.

     CONVERSION negatives are written [Fail Definition ... := eq_refl] and say
     that two well-typed terms are not definitionally equal.

     FORMABILITY negatives are written [Fail Check] and say that a term
     cannot be elaborated at all, here always because of a universe
     constraint.

   Each negative was stripped of its [Fail] and the resulting error read, and
   the diagnosis is recorded beside it.  Positive controls accompany each
   group; the instrument is sanity-checked by a control that differs from the
   negative in exactly the disputed spot.

   Inventory: 5 conversion negatives, 4 formability negatives, 12 positive
   controls.

--------
此文件固定了 Functor/Construction/Postcompose.v 中的每一次严格尝试，无论成功还是失败，这样之后的任何更改如果悄悄使其中某个尝试成功——或者将常量重命名以避开声明——都会大声地破坏构建，而不是让头文件的说明变得过时。它遵循了 Test/ProbeFunnyPoly.v 和 Test/ProbeQuiverConstructions.v 的惯例。

导入列表是目标文件的，以目标文件的顺序排列，先是 Instance/Sets/Powerset.v（只为第4组需要），然后附加目标文件本身。这很重要：如果探针是针对真实导入的短前缀编译的，可能会因缺少类型转换或缺少符号而失败，从而虚假地通过。（Instance/Field/Frac.v 记录了正是这种情况。）超集不会有这种风险，并且目标文件是最后必需的，因此其名称在任何竞争中都占上风。

两种类型，词汇上分开。

CONVERSION 负例写作 [Fail Definition ... := eq_refl]，并表示两个类型良好的项在定义上不相等。

可形成性负面写作 [Fail Check]，并说明某个术语根本无法展开，这里总是由于宇宙约束。

每个阴性样本都去除了其 [Fail]，并读取由此产生的错误，同时在其旁边记录诊断结果。每组样本都有阳性对照；仪器通过一个在正好有争议的位置与阴性样本不同的对照进行合理性检查。

库存：5个转换负片，4个可成型性负片，12个阳性对照片。
*)

(** ** Group 1 (CONVERSION): the Hcompose route's arrow action / ** 第1组（转换）：Hcompose 路线的箭头动作 *)

Section HcomposeConversion.

Context {D E E' : Category}.
Context (J : E ⟶ E').
Context (K L : D ⟶ E).
Context (θ : K ⟹ L).

(*
POSITIVE CONTROL 1.  The OBJECT actions of the two routes DO agree on the
   nose, so the instrument is not simply rejecting everything about
   [PostcomposeViaHcompose].

--------
阳性对照 1. 两条路径的对象动作在鼻子上确实一致，因此该仪器并不是在简单地拒绝 [PostcomposeViaHcompose] 的所有信息。
*)
Definition control_hcompose_obj :
  fobj[PostcomposeViaHcompose J] K = fobj[Postcompose J] K := eq_refl.

(*
POSITIVE CONTROL 2.  The Hcompose route's component IS
   [fmap[J] id ∘ fmap[J] (θ x)] on the nose — this is what the negative
   below is measuring the presence of.

--------
阳性对照 2. Hcompose 路径的组件是 [fmap[J] id ∘ fmap[J] (θ x)] — 这正是下面的阴性对照所测量的内容。
*)
Definition control_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = fmap[J] (@id E (L x)) ∘ fmap[J] (transform[θ] x) := eq_refl.

(*
NEGATIVE 1 (conversion).  The arrow actions are not Leibniz-equal.  Cause,
   read off the stripped error: [Partial_r]'s [fmap] is [bimap F id g], i.e.
   [fmap[Cat_Hcompose] (id, g)], and [Cat_Hcompose]'s [fmap] is the Godement
   product [nat_hcompose], whose component at x is
   [transform[ε] (L x) ∘ fmap[J] (transform[η] x)] with ε the IDENTITY
   transformation — and [nat_id]'s component is [fmap[J] id], not [id].  So
   the Hcompose route carries a unit that left whiskering does not.

--------
负面 1（转换）。箭头操作不是莱布尼茨等价的。原因，读取剥离后的错误：[Partial_r] 的 [fmap] 是 [bimap F id g]，即 [fmap[Cat_Hcompose]（id，g）]，而 [Cat_Hcompose] 的 [fmap] 是 Godement 积 [nat_hcompose]，其在 x 处的分量是 [transform[ε]（L x）∘ fmap[J]（transform[η] x）]，其中 ε 是恒等变换——且 [nat_id] 的分量是 [fmap[J] id]，而非 [id]。所以 Hcompose 路径携带了左鞭策没有的单位。
*)
Fail Definition negative_hcompose_fmap :
  fmap[PostcomposeViaHcompose J] θ = fmap[Postcompose J] θ := eq_refl.

(*
NEGATIVE 2 (conversion).  A fortiori the two functor records are not
   Leibniz-equal.  This is stated separately from Negative 1 because the two
   could in principle come apart: [Postcompose]'s three law fields are
   [Program] obligations, hence opaque, so even had the [fmap]s converted the
   records would not.

--------
否定 2（转换）。更进一步，这两个函子记录并非莱布尼茨相等。之所以将其与否定 1 分开陈述，是因为理论上二者可能会分离：[Postcompose] 的三个法律字段是 [Program] 的义务，因此是不可见的，所以即使 [fmap] 转换了，记录也不会相等。
*)
Fail Definition negative_hcompose_functor :
  PostcomposeViaHcompose J = Postcompose J := eq_refl.

(* NEGATIVE 3 (conversion).  Not even componentwise at a fixed x. / 负 3（转换）。甚至在固定的 x 处也不是按分量的。 *)
Fail Definition negative_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = transform[fmap[Postcompose J] θ] x := eq_refl.

(*
POSITIVE CONTROL 3.  All three hold up to `≈`, which is the strength the
   library file claims.

--------
阳性对照 3。所有三个都能承受 `≈`，这是库文件所声称的强度。
*)
Definition control_hcompose_equiv :
  fmap[PostcomposeViaHcompose J] θ ≈ fmap[Postcompose J] θ :=
  postcompose_via_hcompose_fmap J K L θ.

End HcomposeConversion.

(** ** Group 2 (CONVERSION): [prefmap] does not compute / ** 第2组（转换）：[prefmap] 无法计算 *)

Section PrefmapConversion.

(*
POSITIVE CONTROL 4.  The FORWARD leg of the isomorphism computes: it is
   the functor's own action on 2-cells, on the nose.

--------
正控制 4。同构的正向部分计算的是：它是函子对 2-胞的自身作用，完全精确。
*)
Definition control_iso_to (θ : finpost_K ⟹ finpost_K) :
  to finpost_hom_iso θ = fmap[SubPostcompose FinSets] θ := eq_refl.

(*
NEGATIVE 4 (conversion).  The BACKWARD leg does not.  Cause, read off the
   stripped error: the [Full] instance in play is produced by
   Construction/Subcategory.v's [Full_Implies_Full_Functor], which is a
   `Qed` lemma; its [prefmap] field is therefore an opaque constant and no
   component of it reduces.  The obstruction is the donor's opacity — nothing
   about this construction, and nothing about [Full] as a class.

--------
负数 4（转换）。反向的部分不产生。原因，请读取剥离的错误：正在使用的 [Full] 实例是由 Construction/Subcategory.v 的 [Full_Implies_Full_Functor] 生成的，它是一个 `Qed` 引理；因此它的 [prefmap] 字段是一个不透明常量，并且其任何组成部分都不会被化简。阻碍是来自捐赠者的不透明性——关于这个构造没有任何问题，也关于 [Full] 作为一个类没有任何问题。
*)
Fail Definition negative_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x = FinSets_negb := eq_refl.

(* POSITIVE CONTROL 5.  It does hold up to `≈`, by [fmap_sur]. / 阳性对照 5。它确实能承受 `≈`，由 [fmap_sur] 提供。 *)
Definition control_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x ≈ FinSets_negb :=
  finpost_preimage_component x.

(*
NEGATIVE 5 (conversion).  The round trip is `≈` and not Leibniz, for the
   same reason: [from] of [to] rebuilds a [Transform] record whose components
   are [prefmap] applied to whiskered components.

--------
负 5（转换）。往返是 `≈` 而不是莱布尼茨，原因相同：[from] 的 [to] 重建了一个 [Transform] 记录，其组成部分是应用于带须组件的 [prefmap]。
*)
Fail Definition negative_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) = finpost_theta
    := eq_refl.

(*
POSITIVE CONTROL 6.  The round trip at `≈`, which IS what
   [postcompose_hom_iso] proves.

--------
阳性对照 6. 往返于 `≈`，这正是 [postcompose_hom_iso] 证明的。
*)
Definition control_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) ≈ finpost_theta :=
  iso_from_to finpost_hom_iso finpost_theta.

End PrefmapConversion.

(** ** Group 3 (FORMABILITY): the hom universes cannot be kept apart / ** 第3组（可形成性）：同类宇宙无法被分开 *)

(*
[Postcompose] identifies the hom AND proof universes of all three of its
   categories.  The object universes stay free.  Both halves are probed.

--------
[Postcompose] 识别其三类的同类和证明宇宙。对象宇宙保持自由。两部分都被探查。
*)

Section UniverseFormability.

(*
POSITIVE CONTROL 7.  Three categories with STRICTLY INCREASING object
   universes and one shared hom universe: [Postcompose] elaborates.  So the
   object universes really are free, and the negatives below are not simply
   rejecting any annotated instantiation.

--------
阳性对照 7。三个具有严格递增对象宇宙的类别，以及一个共享的同质宇宙：[Postcompose] 进行阐述。因此，对象宇宙确实是自由的，下面的否定并不仅仅是拒绝任何注释实例化。
*)
Section ObjectsFree.
  Universes uo1 uo2 uo3 uh.
  Constraint uo1 < uo2.
  Constraint uo2 < uo3.

  Check (fun (D : Category@{uo1 uh uh}) (E : Category@{uo2 uh uh})
             (E' : Category@{uo3 uh uh}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End ObjectsFree.

(*
NEGATIVE 6 (formability).  Keeping the SOURCE and TARGET hom universes of
   J apart is rejected.  Stripping the [Fail] yields a universe inconsistency
   naming the declared constraint.  Cause: Theory/Functor.v's [Compose] is
   declared over [Category@{_ h h}] for all three of its categories, so the
   object action [J ◯ K] alone forces the identification; Instance/Fun.v's
   [Fun] independently carries [u0 = u2] between its source and target hom
   levels.  Neither pin is introduced by this development.

--------
负 6（可形成性）。保持 J 的源和目标同态宇宙分离被拒绝。去掉 [Fail] 会导致命名已声明约束的宇宙不一致。原因：Theory/Functor.v 的 [Compose] 在其三个类别上都是在 [Category@{_ h h}] 上声明的，因此对象作用 [J ◯ K] 本身就强制要求识别；Instance/Fun.v 的 [Fun] 独立地在其源和目标同态等级之间携带 [u0 = u2]。这个开发没有引入任何钉点。
*)
Section HomsApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End HomsApart.

(*
NEGATIVE 7 (formability).  Same for the SHAPE category's hom universe
   against the two others.

--------
负7（可成形性）。对于形状类别的同质宇宙来说，也是一样，相对于其他两个类别。
*)
Section ShapeHomApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh2 uh2})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End ShapeHomApart.

(*
POSITIVE CONTROL 8.  INSTRUMENT SANITY CHECK.  The two negatives differ
   from this control in exactly the disputed spot: drop the [Constraint] and
   let the three hom universes be the same, and the very same term
   elaborates.  So the rejection is attributable to the constraint and not to
   the annotation style, the explicit [@], or the section apparatus.

--------
阳性对照 8. 仪器完整性检查。这两个阴性样本与该对照在正是有争议的部分不同：去掉 [Constraint]，让三个同源宇宙保持相同，并且完全相同的术语得以展开。因此，拒绝是由于约束条件，而不是注释风格、明确的 [@] 或章节结构造成的。
*)
Section HomsTogether.
  Universes uo uh1 uh2.

  Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
             (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End HomsTogether.

End UniverseFormability.

(** ** Group 4 (FORMABILITY): the enlargement of Sets is out of reach / ** 第4组（可成形性）：集合的扩展无法实现 *)

(*
Mac Lane's remark 1 is about enlarging the ambient category of SETS.  The
   in-tree functor that does that is Instance/Sets/Powerset.v's
   [Sets_Lift : Sets@{o so} ⟶ Sets@{so sso}], the identity on carriers
   re-typed one level up.  Postcomposition along it does not exist, and the
   two probes below locate the obstruction precisely: one need not reach the
   functor category or [Postcompose] to meet it, because Theory/Functor.v's
   [Compose] already suffices — [Compose] being
   declared over three categories sharing ONE hom-and-proof level, whereas
   [Sets@{o so}] has hom level [o] and [Sets@{so sso}] has hom level [so]
   with [o < so] forced by [Sets]' own declaration.  This does NOT exculpate
   the functor category, which carries an independent wall of the same kind:
   [Fun] identifies its source and target hom levels, so the two [Sets]
   levels could not index one functor category either.

   Stripping either [Fail] yields "universe inconsistency: Cannot enforce
   ... because ... < ...", naming exactly those two levels.

--------
Mac Lane 的第 1 条评论是关于扩展 SETS 的环境范畴。完成此操作的树内函子是 Instance/Sets/Powerset.v 中的 [Sets_Lift : Sets@{o so} ⟶ Sets@{so sso}]，它是对承载者的一层上重新类型化的恒等函子。沿它的后合成不存在，而下面的两个探针精确地定位了阻碍：不需要进入函子范畴或 [Postcompose] 就能遇到它，因为 Theory/Functor.v 的 [Compose] 已经足够 — [Compose] 被声明在三个共享一个同值-证明层的范畴上，而 [Sets@{o so}] 的同值层是 [o]，[Sets@{so sso}] 的同值层是 [so]，并且 [o < so] 被 [Sets] 自身声明所强制。这并不能免除函子范畴，它同样承载着一种独立的同类障碍：[Fun] 识别了其源和目标的同值层，因此两个 [Sets] 层也无法为同一个函子范畴建立索引。

剥离任意 [Fail] 会产生“宇宙不一致：无法执行 ... 因为 ... < ...”，准确地命名那两个级别。
*)

Section SetsEnlargement.

(* NEGATIVE 8 (formability).  [Postcompose] along the lift. / 负 8（可成型性）。沿升降机使用 [Postcompose]。 *)
Fail Check (fun (D : Category) => Postcompose (D:=D) Sets_Lift).

(*
NEGATIVE 9 (formability).  And already the bare object action, with no
   functor category and no [Postcompose] in sight — which is what shows the
   wall belongs to [Compose].

--------
负 9（可成形性）。而且已经是裸对象动作，没有函子类别，也没有 [Postcompose]——这表明墙属于 [Compose]。
*)
Fail Check (fun (D : Category) (K : D ⟶ Sets) => Sets_Lift ◯ K).

(*
POSITIVE CONTROLS 9 and 10.  INSTRUMENT SANITY CHECK.  [Sets_Lift] itself
   elaborates, and the same composite shape with a LEVEL-PRESERVING functor
   in its place is fine — so the instrument is not rejecting every mention of
   [Sets_Lift], nor the shape [_ ◯ K], but exactly the composite that would
   need the two levels' hom universes identified.

--------
阳性对照 9 和 10。 仪器合理性检查。 [Sets_Lift] 本身有详细说明，并且在其位置使用具有等级保留函子（LEVEL-PRESERVING functor）的同样复合形状也是可以的——所以仪器并没有拒绝每次提到 [Sets_Lift]，也没有拒绝形状 [_ ◯ K]，而恰恰是需要识别两个等级的同构宇宙的那个复合体。
*)
Check Sets_Lift.

Check (fun (D : Category) (K : D ⟶ Sets) => (Id[Sets]) ◯ K).

End SetsEnlargement.

(** ** Group 5: the headline results are inhabited at the witness / ** 第5组：主要结果由证人居住 *)

(*
POSITIVE CONTROLS 11 and 12.  The two boundary theorems of the library
   file, each named at its full type, so that a rename or a weakening of
   either statement breaks this file.

--------
阳性对照 11 和 12。库文件的两个边界定理，每个都以其完整类型命名，因此重命名或削弱其中任何一个陈述都会破坏此文件。
*)

Definition control_finpost_iso :
  (finpost_K ⟹ finpost_K)
    ≊ (FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K) :=
  finpost_hom_iso.

Definition control_full_needed :
  Category.Theory.Functor.Full (Postcompose (D:=_1) DiscToTwo) → False :=
  postcompose_full_needs_full.
