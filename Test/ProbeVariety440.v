(**
* Probe for the variety development (issue #440)

    Pins the measured boundaries of Mac Lane §V.6 / Awodey §9.8 as they
    are actually delivered.  Negatives of three kinds, kept lexically
    apart, each stripped one at a time in a copy of the WHOLE file with
    the error read.

    CONVERSION (each error read as "cannot unify"): n1, ONE instance of
    the conversion step that [EqSignature]'s naturality fields demand and
    cannot take by computation — an argument bundle over the empty arity
    against the empty match.  An earlier revision of this header called
    that "the root of every [functional_extensionality] in this
    development", which is FALSE twice over and an audit refuted both
    halves by construction: the same law at the same empty arity is
    CLOSED when the bundle is spelled as a reindexing of [args], and
    associativity alone over [GroupOp] needs the axiom with no nullary
    operation in sight.  See Instance/Variety.v's header for the criterion
    that actually holds — reindexing or constant bundles convert, mixed
    ones do not.  n2, [clone_act_subst] is a genuine induction and not a
    definitional identity; n4,
    [GroupVariety] and [Grp] are not the same category, which is what
    Instance/Variety/GroupComparison.v's header says and all it says —
    that file ships a fully faithful comparison, not an isomorphism.

    TYPING (error read as "cannot satisfy constraint"): n3, the equations
    are NOT dropped — the naive [eq_refl] satisfaction proof for [AndOp],
    the booleans under conjunction, does not ascribe, because it would
    force [lhs e args] and [rhs e args] to be convertible.  That refutation
    alone would only refute ONE candidate term, so the substance is
    carried by a positive theorem beside it: [AndOp_not_group] proves
    that NO satisfaction proof exists, while the control above it shows
    [AndOp] is a perfectly good object of the equation-free [Algs].

    The import list contains the FULL union of the three target files'
    lists, plus the targets themselves.

--------
* 探查品种开发（问题 #440）

钉上 Mac Lane §V.6 / Awodey §9.8 的测量边界，按实际交付的方式。三种类型的否定，各自在词汇上保持分开，每次在包含错误读取的整个文件副本中依次剥离。

转换（每个错误读作“无法统一”）：n1，[EqSignature] 的自然性字段要求但无法通过计算执行的转换步骤的一例——一个针对空匹配的空元参数捆绑。该标题的早期版本称其为“此开发中每个 [functional_extensionality] 的根”，这是完全错误的，两次都是错误，并且审计在构造上驳回了这两部分：在相同空元的情况下，当捆绑被拼写为 [args] 的重新索引时，相同定律是封闭的；仅对 [GroupOp] 的结合律需要公理，而未见任何零元运算。请参阅 Instance/Variety.v 的头文件，以了解实际上生效的标准——重新索引或常量捆绑会转换，混合的不会。n2，[clone_act_subst] 是真正的归纳，而不是定义恒等式；n4，[GroupVariety] 和 [Grp] 不是同一类别，这正是 Instance/Variety/GroupComparison.v 的头文件所说明的内容——该文件提供完全忠实的比较，而不是同构。

输入（错误读取为“无法满足约束”）：n3，这些方程
    并没有被舍弃——对于 [AndOp] 的 [eq_refl] 原始满足性证明，在结合下的布尔值，并没有归因，因为这将强制 [lhs e args] 和 [rhs e args] 可转换。仅仅该反驳
    本身只能反驳一个候选项，因此实质内容由旁边的正定理承担：[AndOp_not_group] 证明不存在任何满足性证明，而上面的控制显示 [AndOp] 是无方程 [Algs] 的一个完全良好的对象。

导入列表包含三个目标文件列表的完整并集，以及目标文件本身。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Clone.
Require Import Category.Instance.Variety.GroupComparison.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe440_absent_name.

(** ** A: CONVERSION — the axiom root, and a genuine induction / ** A：转换——公理根本，以及真正的归纳 *)

Section BundleRoot.

Context {A B : UA.OpAlgebra UA.GroupOp}.
Context (f : UA.AlgHom A B).

(*
n1 CONVERSION: this particular empty-arity bundle is not convertible
   to the empty match.  It is ONE witness of the conversion step
   [EqSignature]'s naturality fields demand — not the root cause of the
   development's extensionality, which the header corrects.

--------
n1 转换：这个特定的空参数包不能转换为空匹配。它是转换步骤的一个见证，[EqSignature] 的自然性字段要求 —— 而不是开发扩展性的根本原因，头信息会纠正这一点。
*)
Fail Example p440_nullary_conv :
  (fun i : UA.nullary => UA.map f (match i return UA.carrier A with end))
    = (fun i : UA.nullary => match i return UA.carrier B with end) := eq_refl.

(*
control: the same equation WITH extensionality is accepted, and it is
   exactly [nullary_bundle]

--------
控制：带有扩展性的相同方程被接受，并且它正是 [nullary_bundle]
*)
Example p440_nullary_ext :
  (fun i : UA.nullary => UA.map f (match i return UA.carrier A with end))
    = (fun i : UA.nullary => match i return UA.carrier B with end).
Proof. extensionality i; destruct i. Qed.

End BundleRoot.

Section SubstIsInduction.

Context (S : UA.OpSignature).
Context (A : SetoidAction S).
Context {m n : nat}.
Context (s : Fin.t m → DerivedOperators S n).
Context (t : DerivedOperators S m).
Context (env : Fin.t n → sact_carrier A).

(*
n2 CONVERSION: substitution commutes with the action only
   propositionally — [clone_act_subst] recurses over [t], so the two
   sides are not convertible at an abstract [t].

--------
n2 转换：替换仅在命题上与作用交换——[clone_act_subst] 在 [t] 上递归，所以两边在抽象的 [t] 上不可转换。
*)
Fail Example p440_subst_conv :
  clone_act A (clone_subst s t) env
    = clone_act A t (fun i => clone_act A (s i) env) := eq_refl.

End SubstIsInduction.

(* control: the two computation rules of the action ARE definitional / 控制：该动作的两个计算规则是定义性的 *)

Example p440_act_var {S : UA.OpSignature} (A : SetoidAction S) {n}
  (i : Fin.t n) (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_var i) env = env i := eq_refl.

Example p440_act_op {S : UA.OpSignature} (A : SetoidAction S) {n}
  (o : UA.operation S) (args : UA.arity o → DerivedOperators S n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_op o args) env
    = sact_op A o (fun j => clone_act A (args j) env) := eq_refl.

(** ** B: TYPING — the equations are not dropped / ** B: 打字 — 方程式没有被丢弃 *)

(*
The booleans under conjunction: a perfectly good operation algebra for
   the group signature, and not a group.

--------
在合取下的布尔值：对于群签名来说是一个完全有效的运算代数，而不是一个群。
*)
(*
The constructor is applied explicitly rather than through record
   syntax: [UA.op]'s signature quantifies over the operation type of an
   as-yet-unresolved [?S], and record syntax does not fix it.

--------
构造函数是显式应用的，而不是通过记录语法：[UA.op] 的签名对尚未解析的 [?S] 的操作类型进行量化，而记录语法无法解决它。
*)
Definition AndOp : UA.OpAlgebra UA.GroupOp :=
  UA.Build_OpAlgebra UA.GroupOp bool
    (fun o => match o return (UA.Group_arity o → bool) → bool with
              | UA.one => fun _ => true
              | UA.mul => fun args => andb (args UA.Fst) (args UA.Snd)
              | UA.inv => fun args => args UA.Only
              end).

(* control: it IS an object of [Algs], the equation-free category / 控制：它是 [Algs] 的一个对象，一个无方程类别 *)
Example p440_and_in_algs : @UA.Algs UA.GroupOp := AndOp.

(*
the positive half of n3, stronger than any refutation: NO satisfaction
   proof exists, because [false] has no inverse under conjunction

--------
n3 的正半部分，比任何反驳都强：没有满意的证明存在，因为 [false] 在合取下没有逆元
*)
Theorem AndOp_not_group : satisfies UA.GroupEq AndOp → False.
Proof.
  intro H.
  pose proof (H UA.inv_left (fun _ => false)) as Hf.
  simpl in Hf.
  discriminate Hf.
Qed.

(* n3 TYPING: so the naive satisfaction proof does not ascribe / n3 输入：所以天真的满足证明并不归因于 *)
Fail Example p440_and_in_variety : GroupVariety :=
  (AndOp; fun e args => eq_refl).

(* control: ℤ/2 under exclusive or IS an object of the variety / 控制：ℤ/2 在异或下是该代数类的一个对象 *)
Example p440_bool_in_variety : GroupVariety := GroupVariety_Bool.

(** ** C: CONVERSION — the variety is not the category of groups / ** C: 转换 — 多样性不是群体的类别 *)

(*
n4 CONVERSION: [GroupVariety] and [Grp] are different categories.
   This is a WEAK negative and is labelled so: two unrelated
   [Definition]s that are not convertible says little, and the content
   of the claim lives in Instance/Variety/GroupComparison.v's header and
   in the full-and-faithful controls below, not here.

--------
n4 转换：[GroupVariety] 和 [Grp] 是不同类别。 这是一个弱否定，并被标注为：两个无关的 [Definition] 无法转换，几乎没有意义，并且声明的内容存在于 Instance/Variety/GroupComparison.v 的头部以及下面的完整且忠实的控制中，而不是这里。
*)
Fail Example p440_variety_is_grp : GroupVariety = Grp := eq_refl.

(* controls: the comparison exists and is full and faithful / 控制：比较存在且完整、忠实 *)
Example p440_comparison : GroupVariety ⟶ Grp := GroupVariety_to_Grp.
Example p440_comparison_faithful : Faithful GroupVariety_to_Grp :=
  GroupVariety_to_Grp_Faithful.
Example p440_comparison_full : Functor.Full GroupVariety_to_Grp :=
  GroupVariety_to_Grp_Full.

(**
** D: readbacks

    The two presentations of a variety agree on the nose, and the
    forgetful functor's carrier is the algebra's carrier.

--------
** D：回读

两个同种的呈现完全一致，并且遗忘函子（forgetful functor）的载体就是代数的载体。
*)

Example p440_pack_carrier {S : UA.OpSignature} {E : UA.EqSignature S}
  (A : UA.Algebra S E) :
  `1 (Variety_pack A) = UA.alg S E A := eq_refl.

Example p440_forget_carrier {S : UA.OpSignature} {E : UA.EqSignature S}
  (A : Variety E) :
  carrier (fobj[Variety_Forget E] A) = UA.carrier (`1 A) := eq_refl.

(** ** E: guard block / ** E：守卫块 *)

Check @satisfies.
Check @Variety_sub.
Check @Variety.
Check @Variety_Full.
Check @Variety_Incl.
Check @Variety_Incl_Faithful.
Check @Variety_Incl_Full.
Check @Variety_pack.
Check @Variety_unpack.
Check @Variety_unpack_pack.
Check @Variety_pack_unpack.
Check @Variety_Forget.
Check @Variety_Forget_Faithful.
Check @GroupVariety.
Check @GroupVariety_Bool.
Check @magma_op.
Check magma_mul.
Check @MagmaOp.
Check @comm_eq.
Check comm_law.
Check @comm_swap.
Check @CommEq.
Check @CommMagmaVariety.
Check @invinv_eq.
Check invinv.
Check @InvInvEq.
Check @InvInvVariety.
Check @DerivedOperators.
Check @clone_var.
Check @clone_op.
Check @clone_subst.
Check @clone_rename.
Check @SetoidAction.
Check @sact_carrier.
Check @sact_setoid.
Check @sact_op.
Check @sact_op_respects.
Check @sact_alg.
Check @clone_act.
Check @clone_act_var.
Check @clone_act_op.
Check @action_extends_to_clone.
Check @clone_act_subst.
Check @clone_act_rename.
Check @leibniz_action.
Check @action_extends_to_clone_leibniz.
Check @clone_act_subst_leibniz.
Check @nullary_bundle.
Check @binary_bundle.
Check @unary_bundle.
Check @alg_hom_one.
Check @alg_hom_mul.
Check @GroupVariety_obj_to_Grp.
Check @GroupVariety_hom_to_Grp.
Check @GroupVariety_to_Grp.
Check @GroupVariety_to_Grp_Faithful.
Check @GroupVariety_hom_from_Grp.
Check @GroupVariety_to_Grp_Full.
Check @GroupVariety_to_Grp_reflects_iso.
Check @UA.Algs.
Check @UA.Algebra.
Check @UA.GroupEq.
Check @Sub.
Check @Incl.
