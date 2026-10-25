Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Kan.Extension.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Opposite.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(**
* Probe: the boundaries #353's two files measure

   `Adjunction/Diagonal/Limit.v` and `Theory/Equivalence/Colimit.v` between
   them record around twenty rejections and carry no [Fail] of their own. A
   measurement is not a guard: nothing in the build would notice if a donor
   changed and one of them began to succeed. **This file pins ELEVEN of
   them**, beside a control that must SUCCEED — it does NOT pin all, and an
   earlier draft of this comment claimed it did. Not pinned here, and named
   so a reader can see the gap: the dual of NEGATIVE 6 on the colimit side;
   the three law fields of the composite case individually; the coherence
   component of the round trip alone; `cone_along` against `cone_transport`;
   the transported colimit leg's `≈`-not-`=`; `Functor_Setoid` and
   `Opposite_Functor` as independent hom=proof donors; the three
   `limit_induced` donors; and `two_IsAColimit`'s `Set` pin (its twin IS
   pinned, as NEGATIVE 10).

   The import list is the UNION of the two targets' own lists, plus the two
   targets and `Instance/Cat.Opposite` (needed for the `Op` negatives). A
   probe compiled against a shorter prefix can fail for a missing-reference
   reason and read as a mathematical rejection.

   KINDS, separated by the error TEXT rather than by label:
     CONVERSION  ends `(cannot unify "X" and "Y")`
     FORMABILITY ends `(universe inconsistency: Cannot enforce ...)`
   Each negative below was stripped of its [Fail] and its whole error read.

   ONE MEASURED REJECTION IS DELIBERATELY NOT PINNED, and an earlier draft
   of this comment OVERSTATED it. The Leibniz statement
   `two_id_diagram = two_negb_diagram -> False` IS statable — `Check` on it
   returns `Prop`, so a `Fail Check` would itself fail. What `Colimit.v`
   accurately says is that it is NOT STATED, because `rewrite` cannot
   abstract over one of two universe-POLYMORPHIC constants at different
   instances (it reports the abstraction as ill-typed). What stands in its
   place is the `≈`-level `two_diagrams_differ`, which is STRICTLY STRONGER
   (two Leibniz-equal functors would have `≈`-equal arrow actions). It is
   named in a control below so a rename still breaks this file.

--------
* 探针：边界 #353 的两个文件测量

`Adjunction/Diagonal/Limit.v` 和 `Theory/Equivalence/Colimit.v` 之间记录了大约二十个拒绝，并且它们自身没有携带任何 [Fail]。一次测量不是防护：如果一个捐赠者改变了，而它们中的一个开始成功，构建过程中的任何东西都不会注意到。**这个文件固定了其中的十一项**，旁边还有一个必须成功的控制——它并没有固定所有项，这条评论的早期草稿曾声称固定了全部。这里没有固定，并且命名让读者可以看到缺口：余极 colimit 端 NEGATIVE 6 的对偶；组合情况的三个律域各自；往返的一致性组件单独；`cone_along` 对 `cone_transport`；已传输的 colimit 分支的 `≈`-非 `=`；作为独立同态=证明捐赠者的 `Functor_Setoid` 和 `Opposite_Functor`；三个 `limit_induced` 捐赠者；以及 `two_IsAColimit` 的 `Set` 钉子（它的双胞针固定了，作为 NEGATIVE 10）。

导入列表是两个目标自身列表的并集，加上这两个目标和 `Instance/Cat.Opposite`（用于 `Op` 的否定）。针对较短前缀编译的探测可能因缺失引用而失败，并被理解为数学拒绝。

类别，根据错误文本而不是标签分开：
     转换 以 `(cannot unify "X" and "Y")` 结尾
     形成性 以 `(universe inconsistency: Cannot enforce ...)` 结尾
   下面的每个负面都去掉了它的 [Fail]，并读取了整个错误。

有一个经过衡量的拒绝是故意没有固定的，而这条评论的早期草稿夸大了它。莱布尼茨语句 `two_id_diagram = two_negb_diagram -> False` 是可以陈述的 —— 在其上执行 `Check` 会返回 `Prop`，所以 `Fail Check` 本身也会失败。`Colimit.v` 准确地说的是，它没有被陈述，因为 `rewrite` 无法在两个不同实例的宇宙多态常量之一上进行抽象（它报告抽象为类型错误）。代替它的是 `≈` 级别的 `two_diagrams_differ`，它严格更强（两个莱布尼茨等价的函子会有 `≈` 等价的箭头作用）。它在下面的一个控制中被命名，因此重命名仍然会破坏此文件。
*)

(**
** Instrument check

   Must ERROR ("The command has not failed!"), confirming a [Fail] wrapping
   a SUCCEEDING command is itself rejected. Scope: it does NOT detect a
   [Fail] that accepted everything — such a [Fail] would compile here too.
   It rules out the commoner accident, a [Fail] treated as a no-op.

--------
** 仪器检查

   必须出错（"命令没有失败！"），确认包装一个成功命令的 [Fail] 本身被拒绝。范围：它不会检测接受所有内容的 [Fail] —— 这样的 [Fail] 在这里也会编译。它排除了更常见的错误，即 [Fail] 被当作无操作处理。
*)
Fail Fail Check Category.

(** ** CONVERSION — the opposite-functor calculus (Colimit.v 1, 2) / ** 转换 — 对偶函子演算 (Colimit.v 1, 2) *)

Section OppositeConversion.
Context {C D E : Category}.

(* NEGATIVE 1. Whole record. Stripped: `cannot unify`. / 负面 1. 整个记录。剥离：`无法统一`。 *)
Fail Definition probe_op_compose (F : D ⟶ E) (G : C ⟶ D) :
  Opposite_Functor (F ◯ G)
    = Opposite_Functor F ◯ Opposite_Functor G := eq_refl.

(*
CONTROLS 1: BOTH data actions agree on the nose, which is what localizes
   the failure to the three law fields.

--------
控制 1：两个数据操作完全一致，这就是导致故障定位到三个法律字段的原因。
*)
Definition probe_op_compose_fobj (F : D ⟶ E) (G : C ⟶ D) (x : C) :
  fobj[Opposite_Functor (F ◯ G)] x
    = fobj[Opposite_Functor F ◯ Opposite_Functor G] x := eq_refl.

Definition probe_op_compose_fmap (F : D ⟶ E) (G : C ⟶ D)
  (x y : C) (f : y ~{C}~> x) :
  fmap[Opposite_Functor (F ◯ G)] f
    = fmap[Opposite_Functor F ◯ Opposite_Functor G] f := eq_refl.

(* NEGATIVE 2. The identity. Stripped: `cannot unify`. / 负 2。身份。剥离：`无法统一`。 *)
Fail Definition probe_op_id :
  Opposite_Functor (Id[D]) = Id[Opposite D] := eq_refl.

(* CONTROL 2: its object action agrees. / 控制 2：它的对象动作一致。 *)
Definition probe_op_id_fobj (x : D) :
  fobj[Opposite_Functor (Id[D])] x = fobj[Id[Opposite D]] x := eq_refl.

End OppositeConversion.

(**
** CONVERSION — `Op`'s obligation is Qed, so nothing reduces through it

   This is the PRIOR-ART correction the `Colimit.v` header records: the
   content of `Opposite_Functor_respects` already exists as
   `Op_obligation_1`, the `fmap_respects` obligation of `Op : Cat ⟶ Cat`
   (`Instance/Cat/Opposite.v`). What survives as a reason to have the
   transparent restatement is OPACITY and universes, both pinned here.

--------
** 转换 — `Op` 的义务已经 Qed，因此没有任何东西会通过它减少

这是 `Colimit.v` 头文件记录的先前技术修正：`Opposite_Functor_respects` 的内容已经以 `Op_obligation_1` 的形式存在，即 `Op : Cat ⟶ Cat` 的 `fmap_respects` 义务（`Instance/Cat/Opposite.v`）。保留透明重述的理由是 OPACITY 和宇宙，这两者在这里都被固定。
*)

Section OpOpacity.
Context {J C : Category}.

Definition via_Op (G G' : J ⟶ C) (e : G ≈ G') :
  Opposite_Functor G ≈ Opposite_Functor G' :=
  @fmap_respects Cat Cat Op J C G G' e.

(* NEGATIVE 3. The component readback through `Op` is REJECTED (Qed). / 负面 3. 通过 `Op` 的组件回读被拒绝（Qed）。 *)
Fail Definition probe_via_Op_component (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (via_Op G G' e) x = Isomorphism_Opposite (`1 e x) := eq_refl.

(*
CONTROL 3: the SAME readback through the transparent restatement holds.
   Same statement, same arguments — only the route differs, which is what
   makes the opacity attribution discriminate.

--------
控制3：通过透明重复的方式保持相同的复述。相同的陈述，相同的论点——唯一不同的是路径，这就是使不透明性归属具有辨别性的原因。
*)
Definition probe_respects_component (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_respects e) x = Isomorphism_Opposite (`1 e x)
  := eq_refl.

End OpOpacity.

(**
** CONVERSION — the (A) round trip (Colimit.v 9, 10, 11)

   TWO INDEPENDENT OBSTRUCTIONS, and the controls are what separate them.
   The coherence component fails on its own (10); and `sigT` has no eta, so
   the pair would fail to close even had (10) not (11). Without control 10b
   "sigT eta" would have been a plausible SINGLE cause, and wrong.

--------
** 转换 —— （A）往返行程（Colimit.v 9, 10, 11）

两个独立的障碍，而控制则是它们之间的区分。  
一致性组件自身失败（10）；并且 `sigT` 没有 eta，所以即使没有（10）而有（11），这个对也无法闭合。没有控制10b，“sigT eta”本可以是一个合理的单一原因，但那是错误的。
*)

Section RoundTrip.
Context {J C : Category}.

(* NEGATIVE 4. Whole record. / 阴性 4. 整个记录。 *)
Fail Definition probe_roundtrip (G G' : J ⟶ C) (e : G ≈ G') :
  Opposite_Functor_reflects (Opposite_Functor_respects e) = e := eq_refl.

(*
CONTROL 4 (= control 10b): the ISOMORPHISM-FAMILY component IS eq_refl,
   in BOTH composition orders. So the data half is provably unaffected and
   the failure is confined to the coherence half.

--------
控制 4（= 控制 10b）：同构-族组件是 eq_refl， 在两种组合顺序中都是如此。因此数据部分可以被证明不受影响，失败仅限于一致性部分。
*)
Definition probe_roundtrip_data (G G' : J ⟶ C) (e : G ≈ G') (x : J) :
  `1 (Opposite_Functor_reflects (Opposite_Functor_respects e)) x = `1 e x
  := eq_refl.

(*
NEGATIVE 5. `sigT` eta, at an ARBITRARY e — the second, independent
   obstruction.

--------
负5。`sigT` eta，在任意 e — 第二个独立的障碍。
*)
Fail Definition probe_sigT_eta (G G' : J ⟶ C) (e : G ≈ G') :
  existT _ (`1 e) (`2 e) = e := eq_refl.

End RoundTrip.

(** ** CONVERSION — the adjunction unit/counit (Limit.v R1, R2) / ** 转换 — 附加单位/余单位 (Limit.v R1, R2) *)

Section CounitConversion.
Context {J C : Category} (L : HasLimitsOfShape J C) (F : [J, C]).

(* NEGATIVE 6. The counit component is not the limit leg ON THE NOSE. / 负6。协同元件不是正负端的极限支腿。 *)
Fail Definition probe_counit_strict (j : J) :
  transform[lim_counit L F] j = lim_leg L F j := eq_refl.

(*
CONTROL 6: with the residual identity it DOES close — which locates the
   difference at a `∘ id` and not at the leg.

--------
控制 6：通过剩余恒等，它确实闭合——这将差异定位在 `∘ id` 上，而不是在支腿上。
*)
Definition probe_counit_with_id (j : J) :
  transform[lim_counit L F] j = lim_leg L F j ∘ id := eq_refl.

End CounitConversion.

(** ** CONVERSION — the Kan comparison (Limit.v R3) / ** 转换——Kan 比较（Limit.v R3） *)

Section KanConversion.
Context {J C : Category} (c : C).

(* NEGATIVE 7. Whole records: rejected in the three Functor LAW fields. / 负 7。完整记录：在三个函数器 LAW 字段中被拒绝。 *)
Fail Definition probe_diag_induced :
  Δ[J](c)
    = fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c) := eq_refl.

(*
CONTROLS 7: BOTH actions agree on the nose (these are the target's own
   `diagonal_is_induced_obj` / `_map`), confining the failure to the laws.

--------
控件 7：两个动作在“鼻子”上完全一致（这些是目标自身的 `diagonal_is_induced_obj` / `_map`），将失败限制在定律范围内。
*)
Definition probe_diag_induced_obj (x : J) :
  fobj[Δ[J](c)] x
    = fobj[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] x := eq_refl.

Definition probe_diag_induced_map (x y : J) (f : x ~{J}~> y) :
  fmap[Δ[J](c)] f
    = fmap[fobj[@Induced J _1 (Erase J) C] (@Diagonal C _1 c)] f := eq_refl.

End KanConversion.

(**
** CONVERSION — the empty category is not its own opposite (Limit.v R4)

   This is WHY there is no colimit dual of `Terminal_Limit`, hence no
   `HasColimitsOfShape 0 C ↔ Initial C`. The target discloses that; this
   pins the blocker.

--------
** 转换 —— 空类别不是它自己的对立面（极限.v R4）

这就是为什么没有 `Terminal_Limit` 的余极限对偶，因此也没有 `HasColimitsOfShape 0 C ↔ Initial C`。目标已经透露了这一点；这锁定了阻塞因素。
*)
Fail Definition probe_zero_op : Opposite _0 = _0 := eq_refl.

(* CONTROL: `_0` is nameable and `Opposite` applies to it. / 控制：`_0` 是可命名的，并且 `Opposite` 适用于它。 *)
Check _0.
Check (Opposite _0).

(**
** FORMABILITY — universes

   No explicit universe instance is written inside any [Fail] below: such a
   [Fail] can pass for an arity reason on another Coq version, making the
   guard vacuous with nothing noticing.

--------
** 可塑性 — 宇宙

   在下面的任何 [Fail] 中都没有明确写入宇宙实例：这样的
   [Fail] 可以因为算子元数的原因在另一个 Coq 版本中通过，从而
   使守卫变得空洞而无人注意。
*)

Section FormabilityHomProof.
Universes co ch cp.
Constraint ch < cp.
Context (Cu : Category@{co ch cp}).

(*
CONTROLS: hom and object are nameable with hom and proof declared
   strictly apart, so the negatives below fire on the CONSTRAINT.

--------
控制：hom 和 object 可以命名为 hom，并且 proof 声明严格分开，因此下面的否定会在约束条件上触发。
*)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (obj[Cu]).

(* NEGATIVE 8. `Opposite` alone identifies hom with proof. / 负 8。单独使用“Opposite”就可以用证据识别 hom。 *)
Fail Check (Opposite Cu).

End FormabilityHomProof.

(**
** FORMABILITY — the OTHER reason the transparent restatement earns its
    place, which was measured in the target and guarded NOWHERE until this
    section. The `Op` route identifies the two categories' OBJECT universes;
    the restatement keeps them apart. Controls first, so the negative is
    shown to fire on the identification and not on the section's levels.

--------
** 可成形性——透明重述获得其位置的另一个原因，它在目标中被测量，但在本节之前没有任何地方进行保护。`Op` 路径识别了两类的对象宇宙；重述将它们分开。首先进行控制，因此负面作用被显示为作用于识别，而不是作用于本节的层级。
*)

Section FormabilityOpUniverses.
Universes jo jh jp co ch cp.
Constraint jo < co.
Context (Ju : Category@{jo jh jp}) (Cu : Category@{co ch cp}).

Check Ju.
Check Cu.
Check (Ju ⟶ Cu).
(*
CONTROL: the transparent restatement IS formable with the two object
   levels declared strictly apart.

--------
控制：透明的重述可以用严格分开的两个对象层级形成。
*)
Check (@Opposite_Functor_respects Ju Cu).

(*
NEGATIVE. Stripped:
     universe inconsistency: Cannot enforce co = jo because jo < co

--------
否定。剥离：
     宇宙不一致：无法强制 co = jo，因为 jo < co
*)
Fail Check (@fmap_respects Cat Cat Op Ju Cu).

End FormabilityOpUniverses.

Section FormabilitySetPin.
Universes so sh.
Constraint Set < sh.
Context (Cs : Category@{so sh sh}).

(* CONTROL: the category is nameable with its homs strictly above `Set`. / 控制：该类别可以被命名，其同态严格高于 `Set`。 *)
Check Cs.
Check (obj[Cs]).

(*
NEGATIVE 9. THE `Set` PIN, and it is the sharp one. `two_IsALimit`'s
   binder reads `∀ {C : Category@{_ Set Set}}` — the AMBIENT category's hom
   AND proof pinned to the literal `Set` — while its constraint block
   carries NO `Set =` at all. A sweep of constraint blocks for `Set =`
   returns a clean bill and is WRONG; the binder must be swept for the
   literal token. Donors: `Instance/Two.v`'s `TwoHom : ... -> Set` fixes the
   SHAPE's hom, and `IsALimit` identifies the shape's hom-and-proof with the
   ambient's. Not repaired, not claimed unavoidable.

--------
负面 9. `Set` 引脚，而且它是关键的那个。`two_IsALimit` 的绑定器读取 `∀ {C : Category@{_ Set Set}}`——AMBIENT 类别的同态和证明固定在字面量 `Set` 上——而它的约束块完全没有 `Set =`。对 `Set =` 的约束块扫描返回一份干净的结果，但这是错误的；必须对字面量标记进行绑定器扫描。来源文件：`Instance/Two.v` 中的 `TwoHom : ... -> Set` 修正了 SHAPE 的同态，而 `IsALimit` 将 shape 的同态和证明与 ambient 的同态对应起来。未修复，未声称不可避免。
*)
Fail Check (@two_IsALimit Cs).

End FormabilitySetPin.

(**
** Controls naming every constant the negatives depend on, OUTSIDE a
    [Fail], so a rename breaks a succeeding command rather than turning a
    negative vacuously green.

--------
** 控制命名每个负值依赖的常量，在 [Fail] 之外，因此重命名会破坏随后的命令，而不是使负值变为虚假的绿色。
*)

Check @Opposite_Functor.
Check @Opposite_Functor_respects.
Check @Opposite_Functor_reflects.
Check @Opposite_Functor_Proper.
Check @Op.
Check @Isomorphism_Opposite.
Check @two_IsALimit.
Check @two_IsAColimit.
Check @two_endo.
Check @two_diagrams_differ.
Check @two_transport_moves_inj.
Check @cocone_transport.
Check @isacolimit_transport.
Check @colimit_transport.
Check @cone_along.
Check @limit_induced.
Check @colimit_induced.
Check @fun_equiv_transform.
Check @cone_along_is_cone_transport.
Check @limit_transport.

Check @HasLimitsOfShape.
Check @HasColimitsOfShape.
Check @LimitFunctor.
Check @ColimitFunctor.
Check @Diagonal_Limit_Adjunction.
Check @Colimit_Diagonal_Adjunction.
Check @limits_iff_diagonal_right_adjoint.
Check @colimits_iff_diagonal_left_adjoint.
Check @lim_counit.
Check @colim_unit.
Check @lim_counit_is_limit_leg.
Check @colim_unit_is_colimit_inj.
Check @Lim_map.
Check @Colim_map.
Check @lim_leg.
Check @colim_inj.
Check @Erase_right_adjoint_iff_Terminal.
Check @Erase_left_adjoint_iff_Initial.
Check @HasLimitsOfShape_0_iff_Terminal.
Check @lim_Ran_iso.
Check @Cocone_Natural_Transform.
Check @Cone_Natural_Transform.
Check @Sets_Diagonal_Limit_Adjunction.
Check @sets_bool_lim_two_elements.
Check @Induced.
Check @Erase.
Check @Diagonal.
