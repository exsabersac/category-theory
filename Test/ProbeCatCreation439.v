(**
* Probe for Instance/Cat/Creation.v (issue #439)

    Pins the measured boundaries of Mac Lane §V.6 Exercises 3 and 4 as they
    are actually delivered — over the tree's FIBRE PRODUCT of categories,
    not over a pullback square in [Cat], which `Instance/Cat/Pullback.v`
    refutes for this object.  Negatives of two kinds, kept lexically apart.

    CONVERSION: n1, the composite [FP_snd ◯ Comma_to_FP] has the same object
    and arrow action as [comma_proj2] — both accepted, at [eq_refl] — but is
    not the same functor RECORD, which is exactly why
    [CreatesLimit_transport] is needed to get from one to the other; n2, the
    comma category is not the fibre product on the nose either, so
    [Comma_FP_iso] is doing real work.

    TYPING: n3, an object of a fibre product stores a LEIBNIZ equality
    between the two images, and an isomorphism does not ascribe there — this
    is the measured reason the bottom functor must create limits STRICTLY
    rather than up to isomorphism, and the accepted control beside it builds
    the same object from an equality.

    The [eq_refl] readbacks are positive controls: the strict lift's apex
    and legs lie over the given cone downstairs, and the two
    Verification-block aliases are the constants they name.  Each
    refutation was stripped one at a time in a copy of the whole file, and
    the import list contains the target's in full (plus the target itself
    and Construction/Comma/Creation, which the negatives name) — an earlier
    revision said "mirrors the target's" while omitting
    Category.Adjunction.Continuity and Category.Instance.Adjoints, the
    short-import shape that makes probes pass vacuously.

    One caveat on [p439_square], stated so it is not read for more than it
    is: [fp_square_obj]'s definiens IS [`2 (K j)], so that readback pins the
    definition's TRANSPARENCY, not the commutation of the square.  The other
    seven accepted controls compare genuinely distinct expressions.

--------
* 探测实例/Cat/Creation.v（问题 #439）

固定Mac Lane §V.6 第3和第4练习的测量边界，因为它们实际上是通过类别的树纤维积传递的，而不是通过[Cat]中的拉回图，其中 `Instance/Cat/Pullback.v` 对该对象进行了驳斥。两种类型的否定，保持在词汇上分开。

转换：n1，复合 [FP_snd ◯ Comma_to_FP] 具有与 [comma_proj2] 相同的对象和箭头作用 —— 在 [eq_refl] 上都被接受 —— 但不是同一个函子 RECORD，这正是为什么需要 [CreatesLimit_transport] 来从一个得到另一个的原因；n2，逗号范畴本身也不是纤维积，因此 [Comma_FP_iso] 正在发挥实际作用。

类型：n3，纤维产品的一个对象存储两个图像之间的莱布尼茨等式，而一个同构并不在那里指定——这是底函子必须严格创建极限而不是仅仅到同构的原因，并且其旁边的已接受控制从等式构建相同的对象。

[eq_refl] 读回是阳性对照：严格升降机的顶点和支腿位于楼下给定的圆锥上，而两个 Verification-block 别名是它们所命名的常量。每个驳斥在整个文件的副本中一次被剥离，而导入列表完整包含了目标的内容（加上目标本身以及负面命名的 Construction/Comma/Creation）——早期的修订版说“镜像目标的”，同时忽略了 Category.Adjunction.Continuity 和 Category.Instance.Adjoints，这种短导入形式使探针自动通过。

关于 [p439_square] 的一个警告，如此陈述是为了不被理解得超过其本意：[fp_square_obj] 的定义项是 [`2 (K j)]，因此回读固定了定义的透明性，而不是方形的换位。其他七个已接受的控制则是真正比较不同的表达式。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Adjoints.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Pullback.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Cat.Creation.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe439_absent_name.

(** ** A: CONVERSION — the transported projection against [comma_proj2] / ** A：转换 — 针对 [comma_proj2] 的传输投影 *)

Section Transported.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

(* controls: object and arrow actions agree on the nose / 控制：对象和箭头动作完全一致 *)

Example p439_fobj (x : (=(d) ↓ U)) :
  fobj[FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d] x
    = fobj[@comma_proj2 _1 C D (=(d)) U] x := eq_refl.

Example p439_fmap {x y : (=(d) ↓ U)} (f : x ~> y) :
  fmap[FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d] f
    = fmap[@comma_proj2 _1 C D (=(d)) U] f := eq_refl.

(* n1 CONVERSION: the two FUNCTORS are nevertheless different records / n1 转换：这两个函子仍然是不同的记录 *)
Fail Example p439_same_functor :
  (FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d)
    = (@comma_proj2 _1 C D (=(d)) U) := eq_refl.

(*
n2 CONVERSION: and the comma category is not the fibre product on the
   nose, so the isomorphism is doing real work

--------
n2 转换：并且逗号范畴在具体意义上不是纤维积，所以同构正在发挥真正的作用
*)
Fail Example p439_same_category :
  (=(d) ↓ U) = FibreProduct (@Coslice_Proj D d) U := eq_refl.

End Transported.

(** ** B: TYPING — why the bottom functor must create limits STRICTLY / ** B: 类型 — 为什么底部函子必须严格地创建极限 *)

Section Strictness.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).

(*
control: an object of the fibre product is a pair plus a LEIBNIZ
   equality between the two images

--------
控制：纤维积的一个对象是一个对以及两个像之间的莱布尼茨等式
*)
Example p439_fp_obj (a : A) (b : B) (e : F a = G b) : FibreProduct F G :=
  ((a, b); e).

(*
n3 TYPING: an isomorphism does not ascribe in that slot, which is why the
   created apex needs [slift_eq] and not a [ConeIso]

--------
n3 输入：同构体不会在该槽上进行归属，这就是为什么创建的顶点需要 [slift_eq] 而不是 [ConeIso]
*)
Fail Example p439_fp_obj_iso (a : A) (b : B) (i : F a ≅ G b) :
  FibreProduct F G := ((a, b); i).

End Strictness.

(** ** C: readbacks / ** C：回读 *)

Section Readbacks.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).
Context {J : Category}.
Context (K : J ⟶ FibreProduct F G).
Context (SC : StrictlyCreatesLimit (FP_fst F G ◯ K) F).
Context (HG : PreservesLimitCone (FP_snd F G ◯ K) G).

(* the square commutes definitionally at every index / 这个方阵在每个索引上从定义上是交换的 *)
Example p439_square (j : J) :
  fp_square_obj F G K j = `2 (K j) := eq_refl.

(* the strict lift lies over the GIVEN cone, apex and legs / 严格的提升位于给定圆锥、顶点和母线上方 *)

Example p439_lift_apex (N : Cone (FP_snd F G ◯ K)) (HN : IsLimitCone N) :
  fobj[FP_snd F G]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := fp_snd_StrictlyCreatesLimit F G K SC HG)
          N HN)])
    = vertex_obj[N] := eq_refl.

Example p439_lift_legs (N : Cone (FP_snd F G ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  fmap[FP_snd F G]
    (cone_leg (slift_cone
       (screates (StrictlyCreatesLimit := fp_snd_StrictlyCreatesLimit F G K SC HG)
          N HN)) j)
    = cone_leg N j := eq_refl.

(* the issue's Verification-block name IS the constant it aliases / 该问题的验证块名称就是它所别名的常量 *)
Example p439_alias_ex3 :
  creation_pullback_stable F G K SC HG = fp_snd_StrictlyCreatesLimit F G K SC HG
  := eq_refl.

End Readbacks.

Example p439_alias_ex4 {C D : Category} (U : C ⟶ D) (d : D)
  (HU : ContinuousFunctor U) {J : Category} (K : J ⟶ (=(d) ↓ U)) :
  comma_creates_limits_second_proof U d HU K
    = comma_proj2_creates_second U d HU K := eq_refl.

(**
** C2: the two negatives the prose states, pinned as type ascriptions

    A bare [Check] pins existence, not the argument list.  These two pin
    what the header actually claims: Exercise 3 takes NO [ObjUIP] (its
    binders are exactly these), and [CreatesLimit_transport] carries
    CREATION, not strictness.

--------
** C2：散文中指出的两个否定，标记为类型归属

一个单独的 [Check] 固定的是存在，而不是参数列表。这两个固定了标题实际上所声称的内容：练习 3 不接受任何 [ObjUIP]（它的绑定器正是这些），而 [CreatesLimit_transport] 表示 CREATION，而不是严格性。
*)

Example p439_ex3_takes_no_uip :
  ∀ {A B C : Category} (F : A ⟶ C) (G : B ⟶ C) {J : Category}
    (K : J ⟶ FibreProduct F G),
    StrictlyCreatesLimit (FP_fst F G ◯ K) F →
    PreservesLimitCone (FP_snd F G ◯ K) G →
    StrictlyCreatesLimit K (FP_snd F G)
  := @fp_snd_StrictlyCreatesLimit.

Example p439_transport_is_creation :
  ∀ {J C D : Category} {K : J ⟶ C} {F F' : C ⟶ D},
    F ≈ F' → CreatesLimit K F → CreatesLimit K F'
  := @CreatesLimit_transport.

(** ** D: guard block / ** D：防守挡拆 *)

Check @cast_solve.
Check @cast_from_rew.
Check @cast_shuffle.
Check @cast_unit_cod.
Check @cast_unit_dom.
Check @cast_transfer.
Check @islimitcone_dtransport.
Check @islimitcone_dtransport_inv.
Check @fun_equiv_whisker_r.
Check @ctr_lift.
Check @ctr_over.
Check @ctr_fcone_iso.
Check @ctr_reflect.
Check @CreatesLimit_transport.
Check @fp_square_obj.
Check @fp_square_hom.
Check @fp_square_iso.
Check @fp_F_image_coneiso.
Check @fp_F_image_limiting.
Check @fp_med_cast.
Check @fp_med.
Check @fp_islimitcone.
Check @fp_image_cone.
Check @fp_image_limiting_at.
Check @fp_upstairs_lift.
Check @fp_lift_apex.
Check @fp_lift_leg.
Check @fp_lift_coh.
Check @fp_lift_cone.
Check @fp_strict_lift.
Check @fp_lift_limiting.
Check @fp_reflect.
Check @fp_snd_StrictlyCreatesLimit.
Check @fp_snd_CreatesLimit.
Check @fp_snd_StrictlyCreatesLimits.
Check @fp_snd_CreatesAllLimits.
Check @FP_commutes_cat.
Check @creation_pullback_stable.
Check @Comma_to_FP.
Check @FP_to_Comma.
Check @FP_round_to.
Check @FP_round_from.
Check @FP_round_iso.
Check @FP_round.
Check @Comma_round_to.
Check @Comma_round_from.
Check @Comma_round_iso.
Check @Comma_round.
Check @Comma_FP_iso.
Check @Comma_FP_Equivalence.
Check @ex4_functor_iso.
Check @ex4_fp_creates.
Check @ex4_composite.
Check @comma_proj2_creates_second.
Check @comma_proj2_CreatesAllLimits_via_pullback.
Check @comma_Complete_via_pullback.
Check @comma_creates_limits_second_proof.
Check @Id_ContinuousFunctor.
Check @coslice_comma_proj2_creates_via_pullback.
Check @coslice_comma_Complete_via_pullback.
Check @FibreProduct.
Check @FP_fst.
Check @FP_snd.
Check @FibreProduct_not_Cat_pullback.
Check @FibreProduct_IsPullback.
Check @Coslice_Proj_StrictlyCreatesLimit.
Check @comma_CreatesAllLimits.
