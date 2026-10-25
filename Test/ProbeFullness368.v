Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.Fullness.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Fullness.v (issue #368). / * 边界探针用于附加/完全性.v（问题 #368）。 *)

(*
Why this file exists.  Every rejection recorded in the target's header
   is pinned here as a [Fail] command, from OUTSIDE the target: a [Fail]
   written inside the file it guards is renamed in lockstep with the
   constant it guards, so it cannot detect a rename.  The target's own
   [Require] list is mirrored above, plus what the instance section needs.

   Eleven negatives of THREE kinds, kept lexically apart, plus a scope-free
   instrument check (twelve [Fail] commands in all):

     - FORMABILITY (4): universe rejections localising the two
       identifications the target's headlines carry.  Error text ends in
       `universe inconsistency: Cannot enforce ...`.
     - TYPING (2): the whiskered transformations cannot be ascribed at the
       type the target's isomorphism is stated at.  Error text is a plain
       `has type ... while it is expected to have type ...` with no
       `cannot unify` and no universe clause.
     - CONVERSION (5): the inverse the target produces is not the donor's
       inverse on the nose, and the three record-level whisker-padding
       facts of the target's correction 4.  Error text ends in
       `cannot unify`.

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and compiled alone, and the WHOLE error read to confirm it
   fires at its own command.  This repo's [coqc] prints nothing for a
   [Fail] that succeeds, which is why stripping is the only check.

   Every constant a negative names appears in a succeeding positive
   control below it.

--------
为什么这个文件存在。目标头中记录的每一次拒绝都会作为 [Fail] 命令固定在这里，从目标之外：写入它所保护的文件内部的 [Fail] 会与它所保护的常量同步重命名，因此它无法检测重命名。目标自身的 [Require] 列表在上面被镜像，还有实例部分所需的内容。

三种类型的十一个否定，词汇上分开，再加一个没有范围限制的工具检查（总共十二个 [Fail] 命令）：

- 可成型性 (4)：宇宙拒绝本地化两个标识，目标的标题包含这些标识。错误文本以 `universe inconsistency: Cannot enforce ...` 结尾。
- 类型检查 (2)：有须变换不能归因于目标同构声明的类型。错误文本为简单的 `has type ... while it is expected to have type ...`，没有 `cannot unify` 也没有宇宙条款。
- 转换 (5)：目标生成的逆不是捐赠者的逆，并且目标的修正 4 的三个记录级须填充事实。错误文本以 `cannot unify` 结尾。

每个负面案例都是一次剥离一个，其他的保持为 [Fail]，并单独编译，然后读取整个错误以确认它会在自己的命令下触发。这个仓库的 [coqc] 对成功的 [Fail] 什么也不打印，这就是为什么剥离是唯一的检查方法。

每个常量a负名称出现在它下面的后续正控制中。
*)

(*
** Instrument check: a [Fail] that must fire for a reason having
   nothing to do with universes, typing or conversion.

--------
** 仪器检查：一个 [Fail] 必须触发，其原因与宇宙、打字或转换无关。
*)

Fail Check probe368_no_such_constant_anywhere.

(*
** FORMABILITY

   The target's headlines are over [C : Category@{u u0 u0}] and
   [D : Category@{u1 u2 u2}] -- hom identified with proof in both, by
   REUSE OF THE LEVEL VARIABLE IN THE BINDER, the constraint blocks
   carrying no such equation -- and their blocks additionally carry the
   equation [u0 = u2], identifying the two hom-and-proof levels.  Neither
   identification is introduced by the target; both are inherited, and
   neither is claimed unavoidable.

   Negatives 1 and 2 localise hom = proof: [Section] and [Monic] are each
   rejected ALONE at levels declared strictly apart, while a hom and an
   identity at those very levels are accepted.  [Retraction] is rejected
   too and is shown as a third rejection in the same section.  Note that
   [Functor] is NOT a donor for this equation -- see the positive control
   in section [P_hom_proof_control] -- so "the functor vocabulary" would
   be the wrong attribution.

--------
** 可成型性

目标的标题在 [C : Category@{u u0 u0}] 和 [D : Category@{u1 u2 u2}] 上——同态在两者中都带有证明被识别——通过在绑定器中复用层变量，约束块没有携带这样的方程——而且它们的块还携带方程 [u0 = u2]，识别这两个同态和证明层。目标并未引入任何识别；两者都是继承来的，且都未声称不可避免。

否定 1 和 2 将同态 = 证明本地化：[Section] 和 [Monic] 各自被单独拒绝于声明为严格分开的层，而在这些层上的同态和恒等式却被接受。[Retraction] 也被拒绝，并在同一节中显示为第三次拒绝。注意 [Functor] 不是该方程的来源——参见第 [P_hom_proof_control] 节的正向控制——因此“函子词汇”将是错误的归因。
*)

Section P_hom_proof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (x y : Cu).
Context (f : x ~{Cu}~> y).

(* Controls: the hom-set and the identity ARE formable at these levels. / Controls: the hom-set and the identity ARE formable at these levels. / 控制：在这些层次上可以形成同态集和恒等映射。 *)
Check (@id Cu x).
Check f.

(* Negative 1 (FORMABILITY). / 负 1（可成型性）。 *)
Fail Check (@Section Cu x y f).

(* Negative 2 (FORMABILITY). / 负 2（可成型性）。 *)
Fail Check (@Monic Cu x y f).

(* Negative 3 (FORMABILITY): same cause, third donor. / 阴性3（可形成性）：相同原因，第三位供体。 *)
Fail Check (@Retraction Cu x y f).

End P_hom_proof.

Section P_hom_proof_control.

Universes co ch cp do dh dp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (Du : Category@{do dh dp}).

(*
[Functor] does NOT force hom = proof: this is accepted at exactly the
   levels where [Section], [Monic] and [Retraction] are rejected.

--------
[Functor] 不强制 hom = 证明：这恰好在 [Section]、[Monic] 和 [Retraction] 被拒绝的层次上被接受。
*)
Check (Du ⟶ Cu).

End P_hom_proof_control.

Section P_hom_hom.

Universes co ch cp do dh dp.
Constraint dh < ch.

Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).

(* Control: one direction is formable. / 控制：一个方向是可形成的。 *)
Check (Du ⟶ Cu).

(*
Negative 4 (FORMABILITY): the OTHER direction is not, so the presence
   of functors both ways -- which every statement about an adjunction has
   -- is already sufficient for [u0 = u2].  No [Compose], no [Adjunction]
   and no [Full] is needed to force it.

--------
负 4（可形成性）：另一个方向不是，所以两边都有函子——每个关于伴随的陈述都有——已经足以满足 [u0 = u2]。不需要 [Compose]、[Adjunction] 或 [Full] 来强制它。
*)
Fail Check (Cu ⟶ Du).

End P_hom_hom.

(*
** TYPING

   [Transform] is a class applied to two FUNCTOR RECORDS.  `U ◯ (F ◯ U)`
   and `(U ◯ F) ◯ U` agree on [fobj] and on [fmap] but differ in their
   three law fields, and `U ◯ Id` is not `U`.  So the whiskered forms live
   at types the target's isomorphism cannot be stated at, and the
   components -- not the records -- are what the target identifies.

--------
** 输入

[Transform] 是应用于两个函子记录的类。`U ◯ (F ◯ U)` 和 `(U ◯ F) ◯ U` 在 [fobj] 和 [fmap] 上是一致的，但在它们的三个定律字段上有所不同，并且 `U ◯ Id` 不是 `U`。因此，加须形式存在于目标的同构无法表达的类型上，并且组件——而不是记录——才是目标所识别的。
*)

Section P_whisker.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition PT : F ∹ U := @Adjunction_to_Transform C D F U A.

(*
Controls: both whiskered transformations exist, at their own types,
   and both of the target's hand-built transformations exist at the type
   the isomorphism needs.

--------
控制：两种带胡须的变换各自存在于它们自己的类型中，并且目标的两种手工构建变换都存在于同构所需的类型中。
*)
Check (U ⊳ (@counit _ _ _ _ PT)).
Check ((@unit _ _ _ _ PT) ⊲ U).
Check (@whiskered_counit C D F U A : U ◯ F ◯ U ⟹ U).
Check (@whiskered_unit C D F U A : U ⟹ U ◯ F ◯ U).

(* Negative 5 (TYPING). / 负五（打字中）。 *)
Fail Check ((U ⊳ (@counit _ _ _ _ PT)) : U ◯ F ◯ U ⟹ U).

(* Negative 6 (TYPING). / 负六（打字中）。 *)
Fail Check (((@unit _ _ _ _ PT) ⊲ U) : U ⟹ U ◯ F ◯ U).

(*
The identification that DOES hold, componentwise and at [eq_refl],
   is the target's [whiskered_counit_is_whisker_left] and
   [whiskered_unit_is_whisker_right]; both are cited here so a rename of
   either breaks this file.

--------
确实有效的标识，在组件级别和 [eq_refl]， 是目标的 [whiskered_counit_is_whisker_left] 和 [whiskered_unit_is_whisker_right]；这里引用了两者，因此重命名其中任何一个都会破坏此文件。
*)
Check (@whiskered_counit_is_whisker_left C D F U A).
Check (@whiskered_unit_is_whisker_right C D F U A).

End P_whisker.

(*
** CONVERSION

   The target derives the componentwise invertibility of [fmap[U] ε] at
   the two in-tree adjunctions the issue names, and the inverse it
   produces is the unit component on the nose.  Neither donor's own
   inverse is that term.

--------
** 转换

   目标在两个树内附加处的元素中推导出了 [fmap[U] ε] 的分量可逆性，并且它产生的逆正好是单位分量。两个捐赠者自身的逆都不是该项。
*)

Section P_reflective.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(*
Controls: both isomorphisms exist, and the target's inverse is the
   unit component at [eq_refl] (this is the target's own [Example],
   restated here so a rename breaks the probe).

--------
控制：两者同构都存在，并且目标的逆是 [eq_refl] 处的单位组件（这是目标自身的 [Example]，在此重述，以便重命名会破坏探针）。
*)
Check (reflective_counit_iso R x).
Check (reflective_fmap_counit_IsIsomorphism R x).
Check (@reflective_fmap_counit_inverse C S R x).
Check (fmap[Incl C S] (from (reflective_counit_iso R x))).

(*
Negative 7 (CONVERSION).  [reflective_counit_iso] is closed with
   [Qed], so neither leg of the isomorphism it produces reduces: the two
   terms are of the same type and are NOT convertible.  The cause is
   donor opacity, not a difference of value -- nothing is claimed about
   what the donor's [from] would reduce to were it transparent, and the
   donor is not modified.

--------
负 7（转换）。[reflective_counit_iso] 与 [Qed] 一起关闭，因此它产生的同构的两个部分都不会归约：这两个项属于同一类型且不可转换。原因是捐赠者的不可见性，而不是值的差异——没有声明如果捐赠者是透明的，[from] 会归约到什么值，并且捐赠者未被修改。
*)
Fail Definition probe_reflective_inverse_strict :
  two_sided_inverse
    (IsIsomorphism := reflective_fmap_counit_IsIsomorphism R x)
  = fmap[Incl C S] (from (reflective_counit_iso R x)) := eq_refl.

End P_reflective.

Section P_equiv.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).
Context (d : D).

(* Controls. / 控制。 *)
Check (equiv_adjunction E).
Check (equiv_adjunction_counit_iso E d).
Check (equiv_fmap_counit_IsIsomorphism E d).
Check (@equiv_fmap_counit_inverse C D F E d).
Check (@equiv_fmap_counit_inverse_agrees C D F E d).

(*
Negative 8 (CONVERSION).  Here the `≈` form IS available and is
   delivered by the target as [equiv_fmap_counit_inverse_agrees]
   (control above); it is the strict form that fails.

--------
负 8（转换）。这里 `≈` 形式可用，并由目标以 [equiv_fmap_counit_inverse_agrees] 提供（上方控制）；严格形式会失败。
*)
Fail Definition probe_equiv_inverse_strict :
  two_sided_inverse (IsIsomorphism := equiv_fmap_counit_IsIsomorphism E d)
  = fmap[@quasi_inverse C D F E]
      (two_sided_inverse
         (IsIsomorphism := equiv_adjunction_counit_iso E d)) := eq_refl.

End P_equiv.

(*
** CONVERSION, the whisker padding itself

   Correction 4 of the target rests on three record-level facts beneath
   the two TYPING negatives above: the two parenthesizations of the
   triple composite are not convertible, and neither identity padding is
   convertible with the bare functor.  Each is pinned here as a CONVERSION
   negative; the controls show that [fobj] and [fmap] DO agree at
   [eq_refl] in every case, so what differs is confined to the three law
   fields.  Every statement below is an equation between two inhabitants
   of ONE type ([C ⟶ D]), which is what separates this kind from the
   TYPING pair, where the ascription itself is rejected.

--------
** 转换，本身的须毛填充  

目标的纠正 4 基于三个记录级事实，位于上面的两个类型负号之下：复合三元组的两种括号化方式不可转换，并且任何身份填充都不可与裸函子转换。每一项在此都被固定为一个转换负号；控制表明 [fobj] 和 [fmap] 在每种情况下在 [eq_refl] 上确实一致，因此不同之处仅限于三个法则字段。下面的每个陈述都是 ONE 类型（[C ⟶ D]）的两个成员之间的等式，这正是此类情况与类型配对的区别，类型配对中连赋值本身都被拒绝。
*)

Section P_padding.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Controls: the data fields agree on the nose. / 控制：数据字段完全一致。 *)
Example probe_padding_assoc_fobj :
  fobj[U ◯ (F ◯ U)] = fobj[(U ◯ F) ◯ U] := eq_refl.
Example probe_padding_assoc_fmap :
  @fmap _ _ (U ◯ (F ◯ U)) = @fmap _ _ ((U ◯ F) ◯ U) := eq_refl.
Example probe_padding_unit_r_fobj : fobj[U ◯ Id[C]] = fobj[U] := eq_refl.
Example probe_padding_unit_r_fmap :
  @fmap _ _ (U ◯ Id[C]) = @fmap _ _ U := eq_refl.
Example probe_padding_unit_l_fobj : fobj[Id[D] ◯ U] = fobj[U] := eq_refl.
Example probe_padding_unit_l_fmap :
  @fmap _ _ (Id[D] ◯ U) = @fmap _ _ U := eq_refl.

(* Negative 9 (CONVERSION): the two parenthesizations. / 负 9（转换）：两个括号化。 *)
Fail Definition probe_padding_assoc : U ◯ (F ◯ U) = (U ◯ F) ◯ U := eq_refl.

(* Negative 10 (CONVERSION): the right identity padding. / 负10（转换）：正确的身份填充。 *)
Fail Definition probe_padding_unit_r : U ◯ Id[C] = U := eq_refl.

(* Negative 11 (CONVERSION): the left identity padding. / 负11（转换）：左侧身份填充。 *)
Fail Definition probe_padding_unit_l : Id[D] ◯ U = U := eq_refl.

End P_padding.

(*
** Positive controls for the remaining headline names

   So that a rename of any name a negative or the target's header depends
   on breaks this file rather than turning a guard vacuously green.

--------
** 剩余标题名称的阳性对照

这样，任何名称被重命名为负面或目标的标题取决于打破这个文件，而不是空洞地将保护变为绿色。
*)

Section P_names.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Check (@counit_split_mono_of_full_right C D F U A).
Check (@unit_split_epi_of_full_left C D F U A).
Check (@counit_inv_of_full_right C D F U A).
Check (@unit_inv_of_full_left C D F U A).
Check (@unit_fmap_counit_of_full_right C D F U A).
Check (@unit_fmap_counit_of_full_left C D F U A).
Check (@unit_fmap_counit C D F U A).
Check (@fmap_counit_IsIsomorphism_of_full C D F U A).
Check (@fmap_unit_counit_of_full_left C D F U A).
Check (@fmap_unit_counit_of_full_right C D F U A).
Check (@fmap_unit_counit C D F U A).
Check (@counit_at_F_IsIsomorphism_of_full C D F U A).
Check (@whiskered_counit_iso_of_full C D F U A).
Check (@whiskered_counit_iso_of_full_left C D F U A).
Check (@whiskered_counit_iso_of_full_right C D F U A).
Check (@whiskered_unit_F C D F U A).
Check (@whiskered_counit_F C D F U A).
Check (@whiskered_unit_iso_of_full C D F U A).
Check (@whiskered_unit_iso_of_full_left C D F U A).
Check (@whiskered_unit_iso_of_full_right C D F U A).
Check (@unit_at_UF_of_full_right C D F U A).
Check (@unit_epic_of_full_monic C D F U A).
Check (@unit_epic_of_full_left C D F U A).
Check (@unit_iso_of_full_monic C D F U A).
Check (@unit_at_U_IsIsomorphism_of_full C D F U A).
Check (@split_inverses_agree C).

End P_names.

Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.Pointed.

Check (@Full_Erase_of_ZeroObject).
Check (@zero_erase_adjunction).
Check (@zero_erase_fmap_counit_IsIsomorphism).
Check Erase_PointedSets_not_Faithful.
Check pointed_counit_not_IsIsomorphism.
