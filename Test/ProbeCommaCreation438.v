(**
* Probe for the comma and coslice creation results (issue #438)

    Pins the measured boundaries of Construction/Comma/Creation.v's
    per-diagram and strict-creation additions and of
    Construction/Slice/Creation.v.  Every negative is now of ONE kind, and
    the recorded correction below says what the second kind was.
    CONVERSION: N1, the all-shapes [PreservesImageLimit]
    and the shape-indexed family of [PreservesLimitCone]s agree at every
    diagram — the accepted controls show both passages — but the two
    [Type]s are not convertible, one binding a [Limit] where the other
    binds a cone with its universal property; N3 and N4, the coslice is
    reached only by transport, so the transported projection's object
    action does not reduce to the first projection and the coslice is not
    the comma category on the nose; N5, the shipped [comma_CreatesLimit]'s
    [creates_lift] discards the cone it is handed and returns the lift of
    the fixed [L], so its apex is refused against that cone's apex, while
    the paired control shows the new strict lift is accepted.

    RECORDED CORRECTION: an earlier revision listed a second kind,
    UNIVERSE, for N2 — "a discrete-shape base diagram built by ELIMINATING
    the shape's [x = y] into a hom is not formable over a generic [C] —
    the elimination pins both categories to [Category@{_ Set Set}], while
    [DiscreteCat] itself leaves those universes free — which is why the
    products clause is stated elementarily over [IsIndexedProduct]".  The
    elimination was not the cause: the pin was a universe-minimization
    artifact of Instance/Discrete.v's unannotated [DiscreteCat_Functor],
    annotated in the PR "algebraic carriers are sets" (2026-09-17), and
    the base diagram IS formable.  N2 is kept as a positive control there;
    every remaining negative in this file is CONVERSION.  The products
    clause is still stated elementarily over [IsIndexedProduct], which is
    now a presentational choice, and the constant discrete diagram below
    still shows that class inhabited.

    N6, CONVERSION again: the plain coslice projection and the transported
    one are different functors, so neither file's result transfers to the
    other by conversion.

    The [eq_refl] readbacks are positive controls: the per-diagram limit
    projects onto the downstairs limit in apex and legs, so do the indexed
    product and the equalizer, and the strict lift's own two fields are
    [eq_refl] and [reflexivity].  Each refutation was stripped one at a
    time in a copy of the whole file; the import list mirrors the two
    targets'.

--------
* 探测逗号和共同切片创建结果（问题 #438）

固定了 Construction/Comma/Creation.v 的每个图表和严格创建附加的测量边界，以及 Construction/Slice/Creation.v 的测量边界。现在每个负数都是同一种类型，下面记录的修正说明了第二种类型是什么。转换：N1，全形态的 [PreservesImageLimit] 与形态索引的 [PreservesLimitCone] 系列在每个图表上都一致——已接受的控制显示了两个通道——但是两个 [Type] 是不可转换的，一个绑定一个 [Limit]，而另一个绑定一个具有其普遍性质的圆锥；N3 和 N4，余切仅通过运输到达，因此被运输的投射对象的作用不能简化为第一个投射，且余切并非严格的逗号范畴；N5，发运的 [comma_CreatesLimit] 的 [creates_lift] 放弃了其接收到的圆锥，并返回固定 [L] 的提升，因此其顶点被拒绝于该圆锥的顶点，而配对控制显示新的严格提升被接受。

记录更正：早期的修订列出了第二种类型，UNIVERSE，用于 N2 ——“通过将形状的 [x = y] 消除到 hom 而构建的离散形状基图在通用 [C] 上无法形成 —— 这种消除将两类钉到 [Category@{_ Set Set}]，而 [DiscreteCat] 本身则使这些宇宙保持自由 —— 这就是为什么产品条款在 [IsIndexedProduct] 上以基本方式陈述。”消除并不是原因：该引脚是 Instance/Discrete.v 中未注释的 [DiscreteCat_Functor] 的宇宙最小化产物，该注释在 PR “代数承载是集合” （2026-09-17）中，且基本图是可构造的。N2 在那里被保留作为阳性对照；此文件中剩余的每个阴性都是 CONVERSION。产品子句仍然以最基本的方式在 [IsIndexedProduct] 上陈述，现在这是一种展示选择，下面的常量离散图仍然显示该类是有成员的。

N6，再次转换：普通的余切片投影和传输的余切片投影是不同的函子，因此一个文件的结果无法通过转换转移到另一个文件。

[eq_refl] 的回读是阳性对照：每个示意图的限制投射到顶点和支腿的下层限制，索引产品和平衡器也是如此，而严格提升自身的两个字段是 [eq_refl] 和 [reflexivity]。每个反驳都是在整个文件的副本中一次删除一个；导入列表反映了两个目标的情况。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.Compose.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe438_absent_name.

(** ** A: CONVERSION — the two preservation hypotheses / ** A：转换——两种保存假说 *)

Section Preservation.

Context {C D : Category}.
Context {U : C ⟶ D}.

(* control: each direction of the passage exists and is proof-free / 控制：通道的每个方向都存在且无需证明 *)
Check (@PreservesImageLimit_Continuous C D U).
Check (@Continuous_PreservesImageLimit C D U).

(*
control: the all-shapes hypothesis yields the per-diagram one at every
   diagram, which is the whole content of the weakening below

--------
控制：全形状假设在每个图中产生逐图假设，这就是下面弱化的全部内容
*)
Check (fun (H : @PreservesImageLimit C D U) (J : Category) (G : J ⟶ C) =>
         (fun N HN => H J G (@Build_Limit J C G N HN))
           : PreservesLimitCone G U).

(* N1 CONVERSION: the two [Type]s are nevertheless not convertible / N1转换：然而这两个[Type]仍然不可转换 *)
Fail Example p438_types :
  @PreservesImageLimit C D U
    = (∀ (J : Category) (G : J ⟶ C), PreservesLimitCone G U) := eq_refl.

End Preservation.

(** ** B: UNIVERSE — the discrete shape is not formable here / ** B：宇宙——此处无法形成离散形状 *)

Section DiscreteShape.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {A : Type}.
Context (F : A → (=(d) ↓ U)).

(* control: the discrete functor itself is formable / 控制：离散函子本身是可形成的 *)
Check (DiscreteCat_Functor F).

(*
Former N2, now a positive control.

   RECORDED CORRECTION.  An earlier revision read: "N2 UNIVERSE: but its
   base diagram is not — building a functor out of [DiscreteCat A] by
   eliminating [x = y] into a hom pins both categories to
   [Category@{_ Set Set}]."  The diagnosis named the elimination but the
   pin was in fact a universe-MINIMIZATION artifact of the unannotated
   declaration of [DiscreteCat_Functor], not of the elimination: the
   annotated [DiscreteCat_Functor@{o h p uo uh up +}] (PR "algebraic
   carriers are sets", 2026-09-17, Instance/Discrete.v) eliminates
   [x = y] into a hom exactly as before and the base diagram IS formable.
   Kept as a positive control so that dropping the annotation breaks this
   file.

--------
前 N2，现在是正控制。

记录更正。之前的修订写道：“N2 宇宙：但它的基础图不是——通过将 [DiscreteCat A] 中的 [x = y] 消除到一个同态中来构建函子，将两个范畴固定到 [Category@{_ Set Set}]。” 诊断提到了消除，但该固定实际上是未注释声明的 [DiscreteCat_Functor] 的宇宙最小化工件，而不是消除本身：带注释的 [DiscreteCat_Functor@{o h p uo uh up +}]（PR “代数承载是集合”，2026-09-17，Instance/Discrete.v）像以前一样将 [x = y] 消除到同态中，并且基础图确实可以形成。保持为正控制，以便去掉注释会导致此文件出错。
*)
Definition p438_discrete := Gdiag (DiscreteCat_Functor F).

(* control: the elementary products clause needs no shape at all / 控制：基本产品条款根本不需要任何形式 *)
Check (@comma_IsIndexedProduct C D U d A F).

(*
control: the discrete-shape class is NOT vacuous.  A CONSTANT diagram out
   of [DiscreteCat A] eliminates nothing, so it is formable over a generic
   [C], and [comma_CreatesProducts] applies to it.

--------
控制：离散形状类不是空的。一个来自 [DiscreteCat A] 的常量图表不会消除任何内容，因此它可以在通用的 [C] 上形成，并且 [comma_CreatesProducts] 适用于它。
*)

Definition p438_const_discrete (a : (=(d) ↓ U)) : DiscreteCat A ⟶ (=(d) ↓ U) :=
  @Build_Functor (DiscreteCat A) (=(d) ↓ U)
    (fun _ => a) (fun _ _ _ => id)
    (fun x y => ltac:(intros f g Hfg; reflexivity))
    (fun x => reflexivity _)
    (fun x y z f g => symmetry (id_left _)).

Definition p438_const_creates (HU : @PreservesImageLimit C D U)
  (a : (=(d) ↓ U)) : CreatesLimit (p438_const_discrete a) comma_proj2 :=
  comma_CreatesProducts HU A (p438_const_discrete a).

End DiscreteShape.

(** ** C: CONVERSION — the coslice is reached only by transport / ** C: 转换 — 共切片只能通过运输达到 *)

Section Coslice.

Context {C : Category}.
Context (c : C).

(* control: the transported projection exists and creates every limit / 控制：被传输的投影存在并创造每一个界限 *)
Check (@coslice_comma_proj C c).
Check (@coslice_comma_proj_CreatesAllLimits C c).

(* N3 CONVERSION: its object action does not reduce to the first projection / N3 转换：其对象动作不会简化为第一次投影 *)
Fail Example p438_coslice_fobj (x : c ̸co C) :
  fobj[coslice_comma_proj c] x = `1 x := eq_refl.

(* N4 CONVERSION: and the coslice is not the comma category on the nose / N4 转换：且余切片并非严格意义上的逗号范畴 *)
Fail Example p438_coslice_cat : (c ̸co C) = (=(c) ↓ Id[C]) := eq_refl.

(*
controls: the PLAIN projection's two data fields DO reduce, which is why
   strict creation is available for it where it is not for the transported
   one — the n3 refusal above is about [coslice_comma_proj], not about
   coslice projections in general

--------
控制：PLAIN 投影的两个数据字段确实会减少，这就是为什么严格创建在它上可用，而在传输投影上不可用——上面的 n3 拒绝是关于 [coslice_comma_proj] 的，不是关于余切投影的一般情况
*)
Example p438_plain_fobj (x : c ̸co C) :
  fobj[Coslice_Proj c] x = `1 x := eq_refl.

Example p438_plain_fmap {x y : c ̸co C} (f : x ~{c ̸co C}~> y) :
  fmap[Coslice_Proj c] f = `1 f := eq_refl.

(*
N6 CONVERSION: the plain and the transported projections are DIFFERENT
   functors, so what is proved of one does not transfer to the other by
   conversion

--------
N6 转换：平凡投影和传递投影是不同的函子，因此在一个上证明的内容不能通过转换转移到另一个上
*)
Fail Example p438_projs_agree :
  Coslice_Proj c = coslice_comma_proj c := eq_refl.

End Coslice.

(** ** C': the plain coslice projection's strict lift / ** C': 平凡余切投影的严格提升 *)

Section PlainCoslice.

Context {C : Category}.
Context (c : C).
Context {J : Category}.
Context (K : J ⟶ (c ̸co C)).

(* the lift lies over the GIVEN cone, apex and legs, with no hypothesis / 提升位于给定的圆锥、顶点和底边上，没有假设 *)

Example p438_coslice_apex (N : Cone (Coslice_Proj c ◯ K)) (HN : IsLimitCone N) :
  fobj[Coslice_Proj c]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := Coslice_Proj_StrictlyCreatesLimit c K)
          N HN)])
    = vertex_obj[N] := eq_refl.

Example p438_coslice_legs (N : Cone (Coslice_Proj c ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  fmap[Coslice_Proj c]
    (cone_leg (slift_cone
       (screates (StrictlyCreatesLimit := Coslice_Proj_StrictlyCreatesLimit c K)
          N HN)) j)
    = cone_leg N j := eq_refl.

(* the lifted object's structure map is the mediator, on the nose / 被抬起物体的结构图是中介，正中 *)
Example p438_coslice_structure (N : Cone (Coslice_Proj c ◯ K))
  (HN : IsLimitCone N) :
  `2 (coslice_lift_obj c K N HN) = coslice_med c K N HN := eq_refl.

End PlainCoslice.

(** ** D: CONVERSION — the shipped lift against the strict one / ** D：转换 — 发货的升降机与严格的那个 *)

Section ShippedLift.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HU : @PreservesImageLimit C D U).
Context (L : Limit (Gdiag K)).

Definition p438_HK : PreservesLimitCone (Gdiag K) U :=
  fun N HN => HU J (Gdiag K) (@Build_Limit J C (Gdiag K) N HN).

(* control: the NEW strict lift lies over the given cone on the nose / 控制：新的严格升力位于鼻子上的给定圆锥上 *)
Example p438_new_lift (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  fobj[comma_proj2]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := comma_StrictlyCreatesLimit K p438_HK)
          N HN)])
    = vertex_obj[N] := eq_refl.

(*
N5 CONVERSION: the shipped [creates_lift] discards its cone argument and
   returns the lift of the fixed [L] instead

--------
N5 转换：已发运的 [creates_lift] 会丢弃其锥体参数，并返回固定的 [L] 的提升
*)
Fail Example p438_old_lift (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  fobj[comma_proj2]
    (vertex_obj[creates_lift (CreatesLimit := comma_CreatesLimit HU K L) N HN])
    = vertex_obj[N] := eq_refl.

(* control: what the shipped one DOES say, at its own [L] / 控制：已出货的那个在它自己的 [L] 上到底说了什么 *)
Example p438_shipped_strict :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L] := eq_refl.

End ShippedLift.

(** ** E: readbacks / ** E：复读 *)

Section Readbacks.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (L : Limit (Gdiag K)).

Example p438_at_apex :
  comma_proj2 (vertex_obj[comma_limit_at K HK L]) = vertex_obj[L] := eq_refl.

Example p438_at_legs (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit_at K HK L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

Example p438_slift_eq (N : Cone (Gdiag K)) (HN : IsLimitCone N) :
  slift_eq (comma_strict_lift K HK N HN) = eq_refl := eq_refl.

(* the issue's name IS the constant it aliases, not merely its type / 问题的名称是它所别名的常量，而不仅仅是它的类型 *)
Example p438_alias_limits :
  comma_proj_creates_limits K HK = comma_StrictlyCreatesLimit K HK := eq_refl.

End Readbacks.

Example p438_alias_equalizers {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) :
  comma_creates_equalizers K HK E = comma_equalizer_at K HK E := eq_refl.

Example p438_alias_products {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HP : IsIndexedProduct (comma_prod_fam F) p proj)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  comma_creates_products F p proj HP HU = comma_IsIndexedProduct F p proj HP HU
  := eq_refl.

Example p438_prod_apex {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  comma_proj2 (comma_prod_apex F p proj HU) = p := eq_refl.

Example p438_prod_leg {C D : Category} {U : C ⟶ D} {d : D} {A : Type}
  (F : A → (=(d) ↓ U)) (p : C) (proj : ∀ a, p ~{C}~> comma_prod_fam F a)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) (a : A) :
  fmap[comma_proj2] (comma_prod_proj F p proj HU a) = proj a := eq_refl.

Example p438_equalizer_apex {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_equalizer_at K HK E]) = vertex_obj[E] := eq_refl.

(** ** F: a concrete witness — every coslice of [Sets] is complete / ** F：一个具体的证人——[Sets] 的每一片都是完整的 *)

(*
[Complete C] is the only hypothesis the coslice results consume that is
   not discharged in tree with no premise at all, and [Sets_Complete]
   discharges it.  The witness lives here because instantiating a theorem
   at a concrete category is a [Test/] concern; it is NOT because a
   Construction/ file may not reach [Instance/Sets], which
   Construction/Slice/Creation.v already does transitively through
   Adjunction/Compose.v.

--------
[Complete C] 是唯一一个被 coslice 结果使用的假设，而在没有任何前提的树中它不会被解除，而 [Sets_Complete] 解除它。证人存在于此处是因为在具体范畴上实例化定理是 [Test/] 的问题；这不是因为 Construction/ 文件可能无法达到 [Instance/Sets]，而 Construction/Slice/Creation.v 已经通过 Adjunction/Compose.v 传递地达到了它。
*)

Example p438_sets_coslice_complete (X : Sets) : @Complete (X ̸co Sets) :=
  Coslice_Complete X Sets_Complete.

(** ** G: guard block / ** G：守卫模块 *)

Check @comma_at_image.
Check @comma_at_phi.
Check @comma_at_phi_commutes.
Check @comma_at_apex_obj.
Check @comma_at_apex_leg.
Check @comma_at_apex_coherence.
Check @comma_at_apex_cone.
Check @comma_at_med.
Check @comma_at_ump.
Check @comma_limit_at.
Check @comma_limit_at_apex.
Check @comma_limit_at_legs.
Check @comma_reflect_at.
Check @comma_strict_lift.
Check @comma_StrictlyCreatesLimit.
Check @comma_CreatesLimit_at.
Check @comma_prod_fam.
Check @comma_prod_phi.
Check @comma_prod_phi_commutes.
Check @comma_prod_apex.
Check @comma_prod_proj.
Check @comma_IsIndexedProduct.
Check @comma_prod_apex_strict.
Check @comma_prod_leg_strict.
Check @comma_equalizer_at.
Check @comma_equalizer_apex_strict.
Check @comma_equalizer_leg_strict.
Check @comma_StrictlyCreatesEqualizers.
Check @comma_CreatesAllLimits.
Check @comma_CreatesProducts.
Check @comma_proj_creates_limits.
Check @comma_creates_equalizers.
Check @comma_creates_products.
Check @coslice_structure_coherence.
Check @coslice_structure_cone.
Check @coslice_reflect_at.
Check @coslice_med.
Check @coslice_med_commutes.
Check @coslice_lift_obj.
Check @coslice_lift_leg.
Check @coslice_lift_coherence.
Check @coslice_lift_cone.
Check @coslice_lift_ump.
Check @coslice_limit_at.
Check @coslice_strict_lift.
Check @coslice_lift_apex.
Check @coslice_lift_legs.
Check @Coslice_Proj_StrictlyCreatesLimit.
Check @Coslice_Proj_CreatesLimit.
Check @Coslice_Proj_CreatesAllLimits.
Check @Coslice_Complete_direct.
Check @Coslice_Proj.
Check @Id_PreservesImageLimit.
Check @coslice_comma_StrictlyCreatesLimit.
Check @coslice_comma_CreatesAllLimits.
Check @coslice_comma_Complete.
Check @coslice_comma_Complete_via_adjoint.
Check @Coslice_to_Comma.
Check @Coslice_Comma_Equivalence.
Check @Coslice_to_Comma_CreatesAllLimits.
Check @Coslice_Complete.
Check @coslice_comma_proj.
Check @coslice_comma_proj_CreatesLimit.
Check @coslice_comma_proj_CreatesAllLimits.
Check @comma_CreatesLimit.
Check @comma_creates_reflect.
Check @comma_strict_apex.
Check @comma_strict_legs.
Check @comma_image_limitcone.
Check @rbase_cone.
Check @rbase_coherence.
Check @PreservesImageLimit_Continuous.
Check @Continuous_PreservesImageLimit.
Check @StrictlyCreatesLimit.
Check @StrictLift.
Check @CreatesLimit.
Check @CreatesAllLimits.
Check @PreservesLimitCone.
Check @PreservesImageLimit.
Check @IsIndexedProduct.
Check @Equalizer.
Check @Comma_Coslice.
Check @Adjunction_Id.
