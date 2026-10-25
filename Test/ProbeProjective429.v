(**
* Probe for Structure/Projective.v (issue #429)

    Pins the measured boundaries of the projective/injective development
    with negatives of four kinds, kept lexically apart: UNIVERSE (N1-N3: at
    a category whose hom and proof levels are declared apart, [Epic],
    [Monic] and [Projective] are all refused while the category, its homs
    and an arrow are accepted — the identification is the donors', not this
    file's); CONVERSION and TYPING (N4-N5: [Epic] in [C^op] is not [Monic]
    in [C], so [injective_extend]'s bridge [op_Epic_of_Monic] does real
    work, while the objects and homs of the duality convert); TYPING (N6: a
    Prop-valued existential over [≈] cannot be stated, [≈] being
    Type-valued — there is no "∃-statement rather than data" option, [∃]
    being [sigT]); PARSING (N7-N8: the [@Injective C] notation claims the
    token [@Injective], as [@Initial C] already claims [@Initial]).  Three
    [eq_refl] readbacks show the witnesses' lifts COMPUTE (the split epi's,
    the initial object's, the Leibniz setoid's), and are what makes those
    three [Defined] load-bearing.  Each refutation was stripped one at a
    time in a copy of the whole file; the import list mirrors the target's.
    Section E's readbacks and the guard block are positive controls.

--------
* 结构/投射探针.v（问题 #429）

固定了投射/嵌入式开发的测量边界，并将四类否定词在词汇上区分开：宇宙（N1-N3：在一个其 hom 和证明层次被分开声明的范畴中，[Epic]、[Monic] 和 [Projective] 都被拒绝，而范畴、其 hom 及一个箭头被接受——识别是捐赠者的，而不是此文件的）；转换和类型（N4-N5：[C^op] 中的 [Epic] 不是 [C] 中的 [Monic]，因此 [injective_extend] 的桥 [op_Epic_of_Monic] 执行真实的工作，而对偶性中的对象和 hom 则被转换）；类型（N6：无法陈述 [≈] 上的 Prop 值存在式，因 [≈] 为 Type 值 —— 没有“∃-陈述而非数据”选项，[∃] 为 [sigT]）；解析（N7-N8：[@Injective C] 表记法声明了标识符 [@Injective]，因为 [@Initial C] 已经声明了 [@Initial]）。
三次 [eq_refl] 读回显示了证人的提升 COMPUTE（分裂的 epi、初始对象、莱布尼兹集合类），并且正是这些使得这三个 [Defined] 具有承重能力。每次反驳都是在整个文件的副本中一次剥离的；导入列表与目标的相呼应。E 部分的读回和保护块是阳性对照。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.
Require Import Category.Structure.Projective.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe429_absent_name.

(**
** A: UNIVERSE — [Projective] identifies hom with proof, and the
       identification is [Epic]'s, not this file's

--------
** A：UNIVERSE — [Projective] 带着证明识别 hom，并且该识别属于 [Epic]，而不是此文件
*)

Section ProbeUniverse.

Universes vo vh vp.
Constraint vh < vp.

Context (Cu : Category@{vo vh vp}) (x y : Cu) (f : x ~{Cu}~> y).

(* controls: the category, its homs and an arrow all form here / 控件：类别、它的 Hom 集以及一个箭头都形成于此 *)
Check Cu.
Check (x ~{Cu}~> y).
Check f.

(* N1, N2 UNIVERSE: the donors are already refused at these levels / N1，N2 宇宙：在这些水平上捐赠者已被拒绝 *)
Fail Check (@Epic Cu x y f).
Fail Check (@Monic Cu x y f).

(* N3 UNIVERSE: and so is [Projective], inheriting the identification / N3 宇宙：[Projective] 也是如此，继承了该身份识别 *)
Fail Check (@Projective Cu x).

End ProbeUniverse.

(**
** B: CONVERSION — [Epic] in [C^op] is not [Monic] in [C]; the bridge
       [op_Epic_of_Monic] does real work, so [injective_extend] is not an
       [eq_refl] readback of the [C^op] accessor's hypothesis

--------
** B: 转换——在 [C^op] 中，[Epic] 不是 [C] 中的 [Monic]；桥接 [op_Epic_of_Monic] 做实际工作，所以 [injective_extend] 不是 [C^op] 访问器假设的 [eq_refl] 回读
*)

Section ProbeBridge.

Context {C : Category} {a b : C} (m : a ~> b).

(* controls: both types form and the bridge exists / 控制：两种类型的形式和桥都存在 *)
Check (@Epic (C^op) b a m).
Check (@Monic C a b m).
Check (@op_Epic_of_Monic C a b m).

(*
N4 CONVERSION ("cannot unify"), N5 TYPING (a [Monic] proof offered where
   an [Epic] one is expected): the two predicates are distinct records

--------
N4 转换（“无法统一”），N5 类型检查（在需要 [Epic] 证明的地方提供了 [Monic] 证明）：这两个谓词是不同的记录
*)
Fail Example p429_bridge_refl : @Epic (C^op) b a m = @Monic C a b m := eq_refl.
Fail Example p429_bridge_id (H : @Monic C a b m) : @Epic (C^op) b a m := H.

(* controls: the OBJECT of the duality is definitional / 控制：二元性的对象是定义上的 *)
Example p429_op_op : (C^op)^op = C := eq_refl.
Example p429_hom_op : (b ~{C^op}~> a) = (a ~{C}~> b) := eq_refl.

End ProbeBridge.

(** ** C: TYPING — there is no "∃-statement rather than data" option / ** C：打字——没有“∃-语句而不是数据”选项 *)

Section ProbeExists.

Context {C : Category} {a b : C}.

(*
controls: [∃] and [exists] are both [sigT]; a Prop existential over a
   Prop relation forms

--------
控制：[∃] 和 [exists] 都是 [sigT]；一个关于 Prop 关系的 Prop 存在量词形成
*)
Example p429_exists_is_sigT :
  (∃ h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Example p429_keyword_exists_is_sigT :
  (exists h : a ~> b, h ≈ h) = { h : a ~> b & h ≈ h } := eq_refl.
Check (ex (fun n : nat => n = n)).

(*
N6 TYPING: a Prop-valued existential over [≈], which is Type-valued
   ([ex] unqualified: the Prelude's constant, whose module is [Coq.] on
   8.19/8.20 and [Corelib.] on Rocq 9)

--------
N6 输入：一个在 [≈] 上的 Prop 值存在量词，其类型为 Type 值
   （[ex] 未限定：Prelude 的常量，其模块在 8.19/8.20 上为 [Coq.]，在 Rocq 9 上为 [Corelib.]）
*)
Fail Definition p429_prop_lift : Prop :=
  ex (fun h : a ~> b => h ≈ h).

End ProbeExists.

(**
** D: PARSING — the [@Injective C] notation claims the token
       [@Injective], as [@Initial C] already claims [@Initial]

--------
** D: 解析 — [@Injective C] 标记声称该令牌 [@Injective]，因为 [@Initial C] 已经声称 [@Initial]
*)

Definition Injective_placeholder : nat := 0.
Definition Initial_placeholder : nat := 0.

(* controls: without the [@] both resolve / 控制：没有 [@] 都可以解决 *)
Check Injective_placeholder.
Check Initial_placeholder.

(* N7, N8 PARSING *)
Fail Check @Injective_placeholder.
Fail Check @Initial_placeholder.

(** ** E: readbacks / ** E：复读 *)

Section Readbacks.

Context {C : Category} (p q : C).

Example p429_inj_is_op_proj : @Injective C q = @Projective (C^op) q := eq_refl.

Example p429_cohom_is_op_hom :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Example p429_hom_fmap_is_postcomp {b c : C} (g : b ~> c) (h : p ~> b) :
  fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

Check (projective_iff_hom_preserves_epi p).
Check (injective_iff_cohom_preserves_mono q).
Check (@Coprod_Projective C).
Check (@IndexedCoprod_Projective C).
Check (@sets_all_projective_entails_LEM).
Check two_projective_not_all.

(*
the witnesses' lifts COMPUTE: a split epi lifts by its retraction, the
   initial object lifts by [zero]

--------
见证者的提升 计算：一个拆分的上射通过其收缩来提升，初始对象通过 [zero] 提升
*)
Example p429_retraction_lift_is {b c : C} (g : b ~> c) (R : Retraction g)
  (f : p ~> c) : `1 (Retraction_lifts g R f) = retract ∘ f := eq_refl.

Example p429_initial_lift_is `{I : @Initial C} {b c : C} (g : b ~> c)
  (He : Epic g) (f : 0 ~> c) :
  `1 (@projective_lift C _ initial_obj_Projective b c g He f) = zero := eq_refl.

End Readbacks.

(* in Sets, the lift of a Leibniz setoid is the chosen preimage, pointwise / in Sets, the lift of a Leibniz setoid is the chosen preimage, pointwise / 在集合中，莱布尼茨集合的提升是逐点选择的原像 *)
Example p429_leibniz_lift_is (T : Type) {b c : Sets} (g : b ~> c) (He : Epic g)
  (f : LeibnizSetoid T ~{Sets}~> c) (t : T) :
  `1 (@projective_lift Sets _ (Sets_Leibniz_Projective T) b c g He f) t
    = `1 (epic_implies_surjective g He (f t)) := eq_refl.

(** ** Guard block / ** 防守格挡 *)

Check @Projective.
Check @projective_lift.
Check @injective_extend.
Check @Epic.
Check @Monic.
Check @op_Epic_of_Monic.
Check @Curried_Hom.
Check @Curried_CoHom.
Check @Category.
Check @hom.
Check (fun C : Category => Initial C).
Check @zero.
Check Prop.
