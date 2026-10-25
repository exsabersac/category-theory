Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Two.
Require Import Category.Instance.Fun.Morphisms.

Generalizable All Variables.

(** * Boundary probe for Instance/Fun/Morphisms.v (issue #369) / * Instance/Fun/Morphisms.v 的边界探针（问题 #369） *)

(*
Why this file exists, and what a reader may conclude from it.

   Every rejection recorded here concerns a constant of
   Instance/Fun/Morphisms.v.  An in-file [Fail] renames in lockstep with
   the constant it guards, so it cannot detect a rename; stating the
   rejections from OUTSIDE the target is what makes them guards.  The
   Require list above mirrors the target's exactly, plus the target
   itself: a short prefix is what makes a probe pass for a reason it
   never measured.

   Three KINDS of rejection appear, kept in three lexically separate
   sections and told apart by the error text rather than by label:

     CONVERSION  ends "cannot unify X and Y" with X and Y two terms of
                 ONE type;
     TYPING      a plain "has type A while it is expected to have type
                 B" with NO "cannot unify" clause and no universe
                 clause;
     FORMABILITY ends "universe inconsistency: Cannot enforce ...".

   Each negative was stripped ONE AT A TIME -- the others left as
   [Fail] -- compiled alone, and its whole error message read.  Every
   constant a negative names, the target's and the donors' alike, also
   appears in a command that must SUCCEED, so a rename breaks this file
   at a non-[Fail] line rather than turning a guard vacuously green.

--------
为什么这个文件存在，以及读者可能从中得出什么结论。

这里记录的每一次拒绝都涉及 Instance/Fun/Morphisms.v 的一个常量。文件内的 [Fail] 会与它所保护的常量同步重命名，所以它无法检测到重命名；从目标外部说明这些拒绝正是使它们成为保护的原因。上面的 Require 列表与目标的列表完全相同，外加目标本身：一个短前缀就是让探测通过一个它从未测量过的原因的原因。

出现了三种拒绝，保存在三个词汇上分开的部分中，并且通过错误文本而不是标签来区分：

转换 以“无法统一 X 和 Y”结束，其中 X 和 Y 是同一类型的两个项；
类型检查 用一个简单的“具有类型 A，但预期类型为 B”来表示，没有“无法统一”条款，也没有宇宙条款；
可构造性 以“宇宙不一致：无法强制执行 ...”结束。

每个负例都是一次剥离，一个接一个——其他的保持为 [Fail]——单独编译，并读取其完整的错误信息。每个负例所命名的常量，无论是目标的还是捐赠者的，也出现在一个必须成功的命令中，因此重命名会在非 [Fail] 的行上中断此文件，而不是让保护措施无意义地变为绿色。
*)

(*
Instrument check: a [Fail] that must fire whatever else is true, so a
   silently vacuous [Fail] elsewhere is not mistaken for a measurement.

--------
仪器检查：一个 [Fail] 必须触发，无论其他情况如何，因此其他地方一个默默空洞的 [Fail] 不会被误认为是测量。
*)
Fail Check probe369_no_such_reference.

(* ------------------------------------------------------------------ *)
(** ** CONVERSION negatives / ** 转化否定 *)

Section Conversion.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).
Context {P : C ⟶ Sets}.
Context {Q : C ⟶ Sets}.
Context (ψ : P ⟹ Q).
Context (x : C).

(*
CONVERSION 1.  The pointwise kernel-pair functor preserves identities
   only up to `≈`.  The cause is NOT the opaque [fmap_id] of P that the
   arrow action's [fmap[P] id] would seem to need: the section after
   this one instantiates at the target's own constant-functor witnesses,
   where [fmap[P] id] IS [id] and [fmap_id] IS [reflexivity] by [eq_refl],
   and the identity law still does not hold on the nose.  What blocks it
   is the REBUILD — [ker_fun] returns a fresh sigma over a fresh pair
   ([sets_pb_carrier], Instance/Sets/Pullback.v), and neither
   [sigT] nor [prod] has definitional eta here.  The `≈` form is the
   control.

--------
转换 1. 点态核对函子只保持恒等性到 `≈`。原因不是 P 的不透明 [fmap_id]，而箭头作用的 [fmap[P] id] 看起来似乎需要：本节之后在目标自身的常函子见证下实例化，那里 [fmap[P] id] 是 [id]，[fmap_id] 是 [reflexivity] 通过 [eq_refl]，而且恒等律仍然并非严格成立。阻碍它的是 REBUILD — [ker_fun] 返回一个新的 sigma，作用在新的对 ([sets_pb_carrier], Instance/Sets/Pullback.v) 上，并且在这里既没有 [sigT] 也没有 [prod] 的定义性 eta。`≈` 形式是控制因素。
*)
Fail Example ker_fmap_id_strict :
  fmap[KerPair ψ] (id[x]) = id := eq_refl.

Example ker_fmap_id_equiv : fmap[KerPair ψ] (id[x]) ≈ id.
Proof. exact (@fmap_id _ _ (KerPair ψ) x). Qed.

(*
Same for the cokernel-pair functor, whose [ck_fun] is a [match] on a
   [sum].

--------
同样适用于余核对函子，其 [ck_fun] 是在 [sum] 上的 [match]。
*)
Fail Example ck_fmap_id_strict :
  fmap[CokerPair ψ] (id[x]) = id := eq_refl.

Example ck_fmap_id_equiv : fmap[CokerPair ψ] (id[x]) ≈ id.
Proof. exact (@fmap_id _ _ (CokerPair ψ) x). Qed.

(*
CONVERSION 2.  The isomorphism [Functor_Setoid_Nat_Iso] builds from
   our componentwise family is NOT the record [componentwise_iso]
   builds, even though (controls below) both of its legs agree with ours
   on their [transform] fields at Leibniz equality, pointwise and as
   whole functions.  What differs is confined to opaque LAW fields, at
   TWO levels: the legs themselves are not the same records (CONVERSION
   3 and 4 below — the donor builds them with `abstract`ed naturality
   proofs, Instance/Fun.v), and the isomorphism records then
   carry their own inverse law fields on top.

--------
转换 2. 我们的按组件族构建的同构 [Functor_Setoid_Nat_Iso] 并不是 [componentwise_iso] 构建的记录，尽管（如下所示控制）它的两条分支在其 [transform] 字段上与我们的一致，在 Leibniz 相等下，对每一点以及整体函数也是如此。不同之处局限于不透明的 LAW 字段，有两个层面：分支本身不是同一条记录（下面的转换 3 和 4——捐赠方使用 `abstract` 的自然性证明构建它们，Instance/Fun.v），同构记录随后在其上携带自己的逆定律字段。
*)
Fail Example iso_records_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  equiv_iso (nat_iso_family θ H)
    = @IsIsoToIso ([C, D]) F G θ (componentwise_iso θ H) := eq_refl.

Example iso_to_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) (z : C) :
  transform[to (equiv_iso (nat_iso_family θ H))] z = transform[θ] z
  := eq_refl.

Example iso_from_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) (z : C) :
  transform[from (equiv_iso (nat_iso_family θ H))] z
    = transform[nat_inverse θ H] z := eq_refl.

(*
The whole transform FUNCTIONS agree as well, not merely their values
   at each z.

--------
整个变换函数也是一致的，不仅仅是它们在每个 z 点的取值。
*)
Example iso_to_transform_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  transform[to (equiv_iso (nat_iso_family θ H))] = transform[θ]
  := eq_refl.

Example iso_from_transform_agrees
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  transform[from (equiv_iso (nat_iso_family θ H))]
    = transform[nat_inverse θ H] := eq_refl.

(*
CONVERSION 3 and 4.  Neither whole LEG is ours on the nose: the data
   field agrees (the four controls above) and only the two naturality
   fields, `abstract`ed by the donor, differ.

--------
转换 3 和 4。我们并没有完全拥有整条腿：数据字段是一致的（上面的四个控制），只有由供体 `abstract` 的两个自然性字段不同。
*)
Fail Example iso_to_leg_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  to (equiv_iso (nat_iso_family θ H)) = θ := eq_refl.

Fail Example iso_from_leg_strict
  (H : ∀ z : C, IsIsomorphism (transform[θ] z)) :
  from (equiv_iso (nat_iso_family θ H)) = nat_inverse θ H := eq_refl.

End Conversion.

(* ------------------------------------------------------------------ *)
(** ** CONVERSION 1, cause discriminated at the constant-functor witnesses / ** 转换1，在常量函子证据处导致歧视 *)

(*
At [TwoOne := const_fun _ _ unit_setoid_object] the arrow action is
   [fun _ _ _ => id] and the identity law is [reflexivity _], both on the
   nose — so the opaque-[fmap_id] explanation is removed — yet the strict
   identity law for the two pointwise functors still fails, even after
   both sides are applied to an element so that the [proper_morphism]
   field plays no part.  CONVERSION 5 and 6.

--------
在 [TwoOne := const_fun _ _ unit_setoid_object] 中，箭头运算是 [fun _ _ _ => id]，恒等律是 [reflexivity _]，两者都是精确的——所以不透明的 [fmap_id] 解释被移除了——然而，即使在两边都应用于一个元素以至于 [proper_morphism] 字段不再起作用后，这两个逐点函子之间的严格恒等律仍然不成立。CONVERSION 5 和 6。
*)

Example const_fmap_is_id : fmap[TwoOne] (@id _2 TwoX) = id := eq_refl.

Example const_fmap_id_refl :
  @fmap_id _ _ TwoOne TwoX = reflexivity _ := eq_refl.

Fail Example ker_fmap_id_const (u : carrier (KerPair two_pick_nat TwoX)) :
  fmap[KerPair two_pick_nat] (@id _2 TwoX) u = u := eq_refl.

Fail Example ck_fmap_id_const (u : carrier (CokerPair two_collapse TwoX)) :
  fmap[CokerPair two_collapse] (@id _2 TwoX) u = u := eq_refl.

Example ker_fmap_id_const_equiv :
  fmap[KerPair two_pick_nat] (@id _2 TwoX) ≈ id.
Proof. exact (@fmap_id _ _ (KerPair two_pick_nat) TwoX). Qed.

Example ck_fmap_id_const_equiv :
  fmap[CokerPair two_collapse] (@id _2 TwoX) ≈ id.
Proof. exact (@fmap_id _ _ (CokerPair two_collapse) TwoX). Qed.

(* ------------------------------------------------------------------ *)
(** ** TYPING negative / ** 输入负面 *)

Section Typing.

Context {C : Category}.
Context {P : C ⟶ Sets}.
Context {Q : C ⟶ Sets}.
Context (ψ : P ⟹ Q).

(*
Being monic in [C, Sets] and being pointwise monic are DIFFERENT
   types: the first is a single [Monic] record in the functor category,
   the second a family of [Monic] records in [Sets].  The passage
   between them is the theorem, not a coercion.

--------
在 [C, Sets] 中是单射（monic）和逐点单射是不同的类型：前者是在函子范畴中的单个 [Monic] 记录，后者是在 [Sets] 中的 [Monic] 记录家族。从它们之间的转换是定理，而不是类型转换（coercion）。
*)
Fail Definition monic_is_not_pointwise (Hm : @Monic ([C, Sets]) P Q ψ) :
  ∀ z : C, Monic (transform[ψ] z) := Hm.

Definition monic_gives_pointwise (Hm : @Monic ([C, Sets]) P Q ψ) :
  ∀ z : C, Monic (transform[ψ] z) := sets_functor_monic_pointwise ψ Hm.

Definition epic_gives_pointwise (He : @Epic ([C, Sets]) P Q ψ) :
  ∀ z : C, Epic (transform[ψ] z) := sets_functor_epic_pointwise ψ He.

End Typing.

(* ------------------------------------------------------------------ *)
(** ** FORMABILITY negatives / ** 可成形性缺点 *)

(*
[Fun] takes both of its categories at ONE hom-and-proof level, so a
   functor category cannot be formed over two categories whose hom
   levels are declared strictly apart.  This is what puts the equation
   `C's hom = D's hom` into every constant of the target's general
   section; nothing in the target adds to it.

--------
[Fun] 在 ONE hom-and-proof 级别上获取其两个类别，因此不能在同态级别明确不同的两个类别上形成函子类别。这就是为什么方程 `C 的 hom = D 的 hom` 会出现在目标的一般部分的每个常量中；目标中没有任何内容会对此进行补充。
*)
Section FormabilityFun.

Universes co ch cp dro dh dp.
Constraint ch < dh.

Context {Cu : Category@{co ch cp}}.
Context {Du : Category@{dro dh dp}}.
Context (x y : Cu) (a b : Du).

Check (x ~{Cu}~> y).
Check (a ~{Du}~> b).

Fail Check (@Fun Cu Du).

End FormabilityFun.

(*
[Monic] and [Epic] take a category whose hom and proof levels
   coincide, which is the other identification the target's binders
   display.

--------
[Monic] 和 [Epic] 获取一个其 hom 和证明级别一致的类别，这也是目标的绑定器所显示的另一种标识。
*)
Section FormabilityMonic.

Universes mo mh mp.
Constraint mh < mp.

Context {Du : Category@{mo mh mp}}.
Context (a b : Du) (g : a ~{Du}~> b).

Check (a ~{Du}~> b).
Check g.

Fail Check (@Monic Du a b g).
Fail Check (@Epic Du a b g).

End FormabilityMonic.

(*
And the target's own general theorem inherits both, so it too is
   unformable over two categories whose hom levels are kept apart.

--------
目标自身的一般定理继承了两者，因此它也不能在两个保持同类层次分离的范畴上形成。
*)
Section FormabilityTarget.

Universes to2 th tp uo uh up.
Constraint th < uh.

Context {Cu : Category@{to2 th tp}}.
Context {Du : Category@{uo uh up}}.
Context (x y : Cu) (a b : Du).

Check (x ~{Cu}~> y).
Check (a ~{Du}~> b).

Fail Check (@pointwise_monic_is_monic Cu Du).
Fail Check (@pointwise_epic_is_epic Cu Du).

End FormabilityTarget.

(* ------------------------------------------------------------------ *)
(** ** Rename guards / ** 重命名守卫 *)

(*
Every declaration head the target introduces (52; its 22 [Program]
   obligations are not named here), plus the two donor constants that
   otherwise occur only inside a [Fail], each named outside a [Fail] so
   that a rename breaks this file loudly.

--------
每一个目标引入的声明头（52；其22个[Program]义务在此未命名），再加上两个捐赠者常量，这两个常量否则只出现在[Fail]内部，每个都在[Fail]外部命名，以便重命名会明显破坏此文件。
*)

Check @IsIsoToIso.
Check @Fun.
Check @pointwise_monic_is_monic.
Check @pointwise_epic_is_epic.
Check @theta_nat.
Check @ker_map_ok.
Check @ker_fun.
Check @ker_fun_proper.
Check @ker_map.
Check @KerPair.
Check @KerFst.
Check @KerSnd.
Check @ker_agree.
Check @sets_functor_monic_pointwise.
Check @sets_functor_monic_iff_pointwise.
Check @ck_Im_map.
Check @ck_fun.
Check @ck_fun_proper.
Check @ck_map.
Check @CokerPair.
Check @CkLeft.
Check @CkRight.
Check @ck_agree_nat.
Check @sets_functor_epic_pointwise.
Check @sets_functor_epic_iff_pointwise.
Check @nat_inv_natural.
Check @nat_inverse.
Check @componentwise_iso.
Check @nat_iso_pointwise.
Check @nat_iso_iff_pointwise.
Check @nat_iso_family.
Check @equiv_iso_to_is_theta.
Check @equiv_iso_from_is_nat_inverse.
Check @presheaf_monic_iff_pointwise.
Check @presheaf_epic_iff_pointwise.
Check @presheaf_monic_iff_injective.
Check @presheaf_epic_iff_surjective.
Check @const_fun.
Check TwoOne.
Check TwoBool.
Check two_pick_nat.
Check two_collapse.
Check @pick_true_Monic.
Check @collapse_Epic.
Check two_pick_Monic.
Check two_collapse_Epic.
Check @two_pick_component_not_surjective.
Check @two_pick_not_Epic.
Check @two_collapse_not_Monic.
Check TwoTwoX.
Check TwoTwoY.
Check two_arrow.
Check two_arrow_Monic.
Check two_arrow_Epic.
