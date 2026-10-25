(**
* Probe for the free-algebra adjunction (issue #441)

    Pins the measured boundaries of Mac Lane §V.6's free-algebra
    construction as it is actually delivered.

    THE LOAD-BEARING CLAIM is negative and is carried by a THEOREM, not
    by a refutation command: the TERM ALGEBRA does not satisfy the equations in the
    LEIBNIZ sense.  Read that for exactly what it says — an earlier
    revision of this header went on to infer that #440's [Variety CommEq]
    "has no free object on two generators", which is FALSE and was
    refuted by construction (sorting terms into normal forms builds one).
    What the theorem shows is that the NAIVE construction does not land
    in the Leibniz variety; [free_empty_eq_leibniz] below shows the
    claim needs a qualifier even for the naive one.  The reason for the
    setoid carrier is uniformity in ⟨Ω,E⟩, and Instance/Variety/Free.v's
    header states it.
    [free_magma_not_comm_leibniz] proves that no satisfaction proof
    exists, which a refutation of one candidate term could not; the
    beside it (n1) records that the obvious attempt is refused, and the
    control above it shows the shape IS inhabited at a different algebra
    (the booleans under [xorb]).

    The second negative is also a theorem: [free_comm_not_collapsed]
    shows the congruence does not identify distinct generators, so
    [Free_Variety] is not the trivial algebra at THIS presentation.  It
    is proved by mapping into a commutative magma with
    [free_alg_ext_respects] — the respectfulness lemma the universal
    property is built from, not the universal property itself; an
    earlier revision of this sentence said the latter.

    CONVERSION: n2, the free algebra's carrier is the term type but its
    `≈` is not Leibniz [=], so the two do not convert; n3, two distinct
    terms are not convertible, which is what makes n1 a statement about
    equality rather than about elaboration.

    SORT (#450): n4, the term congruence [tree_equiv] is now [Prop]-valued
    and a derivation of it is refused as the major premise of an
    elimination into a [Type]-sorted goal, against a control running the
    same script into [Prop].  [BoolCommMagma] below supplies the new
    [soa_prop] field as [eq_PropEquiv bool], which is why this file now
    requires Lib/Setoid/Propositional.v.

    The import list contains the target's in full, plus the target
    itself.  (#440's [Instance/Variety] is already one of the target's
    ten, so naming it separately would double-count.  An earlier revision
    said nine; #450 added Lib/Setoid/Propositional.v to the target's
    list, and to this file's.)

--------
* 自由代数伴随的探测（问题 #441）

固定 Mac Lane §V.6 的自由代数构造的测量边界，就其实际交付的情况而言。

承载主张是消极的，由定理支撑，而不是由反驳命令支撑：项代数在莱布尼兹意义上不满足这些方程。准确地按照字面理解——该标题的早期修订推断出 #440 的 [Variety CommEq] “在两个生成元上没有自由对象”，这是错误的，并且通过构造（将项排序成标准形式可以构造一个）已被反驳。定理所展示的是，天真的构造不会落入莱布尼兹类；下面的 [free_empty_eq_leibniz] 显示，即便是天真的构造，该主张也需要一个限定条件。setoid 载体的原因是在 ⟨Ω,E⟩ 中保持一致性，而 Instance/Variety/Free.v 的头部也说明了这一点。[free_magma_not_comm_leibniz] 证明不存在满足的证明，而单靠反驳一个候选项是无法做到的；旁边的 (n1) 记录了明显的尝试被拒绝，而它上方的控制显示该形状在不同的代数中是可居住的（[xorb] 下的布尔代数）。

第二个否定也是一个定理：[free_comm_not_collapsed] 显示这个同余关系不会将不同的生成元识别为相同，因此 [Free_Variety] 在此表示下不是平凡代数。它是通过映射到一个交换幺半群 [free_alg_ext_respects] 来证明的——这是构建通用性质的尊重引理，而不是通用性质本身；这句话的早期修订版本说的是后者。

转换：n2，自由代数的承载类型是项类型，但它的 `≈` 不是莱布尼茨 [=]，所以两者不能转换；n3，两个不同的项不可转换，这正是 n1 成为关于等式而不是关于展开的陈述的原因。

排序（#450）：n4，术语 congruence [tree_equiv] 现在为 [Prop] 值，并且其推导被拒绝作为消元到 [Type] 排序目标的主要前提，针对运行相同脚本到 [Prop] 的控制。下面的 [BoolCommMagma] 作为 [eq_PropEquiv bool] 提供了新的 [soa_prop] 字段，这就是为什么此文件现在需要 Lib/Setoid/Propositional.v。

导入列表包含目标的全部内容，以及目标本身。（#440 的 [Instance/Variety] 已经是目标的十个之一，因此单独命名它会造成重复计算。之前的修订版本说是九个；#450 将 Lib/Setoid/Propositional.v 添加到目标的列表，以及这个文件的列表。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.

Generalizable All Variables.

Module UA := Category.Instance.Comp.UniversalAlgebra.

(*
Same reason as the target's: the global [Obligation Tactic] introduces
   binders under names of its own choosing, and "o is already used" is
   what that looks like from here.

--------
原因和目标一样：全局 [Obligation Tactic] 会以其自己选择的名称引入绑定器，而“o 已经被使用”在这里看起来就是这样。
*)
#[local] Obligation Tactic := idtac.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe441_absent_name.

(** ** A: why the free object cannot live in #440's Leibniz variety / ** A: 为什么自由对象不能存在于 #440 的莱布尼茨范畴中 *)

(*
A measure that reads the leftmost generator of a term, so that the
   refutation below needs no projection out of [node]'s dependent
   argument at all.  AN EARLIER REVISION JUSTIFIED IT BY SAYING THE
   INJECTION ROUTE "would produce a dependent-pair equality and want
   [Eqdep]"; measured, that is false HERE — both sides of the equation
   carry the same literal [magma_mul], so [injection] yields a
   non-dependent hypothesis and the injection proof is closed under the
   global context too.  The measure is still the more robust route,
   because it keeps working when the two operations are only
   propositionally equal, which is when [Eqdep] would genuinely be
   wanted.

--------
一种度量，用于读取一个项的最左边生成器，因此下面的反驳完全不需要从 [node] 的依赖参数中投影出来。较早的一个修订通过说注入路径“会产生一个依赖对等式并需要 [Eqdep]”来证明它是合理的；但实际上在这里这是错误的——等式的两边都携带相同的字面 [magma_mul]，因此 [injection] 产生一个非依赖假设，并且注入证明在全局上下文下也闭合。该度量仍然是更稳健的路径，因为当两种操作仅命题上相等时，它仍然有效，而这正是 [Eqdep] 真正需要的情况。
*)
Fixpoint first_gen (t : UA.Tree MagmaOp bool) : bool :=
  match t with
  | UA.generator _ _ b => b
  | UA.node _ _ _ k    => first_gen (k UA.Fst)
  end.

Definition sep_args (i : UA.binary) : UA.Tree MagmaOp bool :=
  match i with
  | UA.Fst => UA.generator MagmaOp bool true
  | UA.Snd => UA.generator MagmaOp bool false
  end.

(*
THE THEOREM.  The term algebra over the commutative-magma signature
   does not satisfy commutativity up to Leibniz equality: [x * y] and
   [y * x] are DIFFERENT TERMS.  Hence #440's [Variety CommEq], whose
   objects are bare types with Leibniz satisfaction, has no free object
   on two generators, and the setoid carrier is forced.

--------
定理。交换幺半群签名上的项代数在莱布尼茨等价下不满足交换性：[x * y] 和 [y * x] 是不同的项。因此，#440 的 [Variety CommEq]，其对象是具有莱布尼茨满足的裸类型，没有两个生成元的自由对象，并且集合承载强制存在。
*)
Theorem free_magma_not_comm_leibniz :
  satisfies CommEq (UA.Free MagmaOp bool) → False.
Proof.
  intro H.
  pose proof (H comm_law sep_args) as Heq.
  apply (f_equal first_gen) in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
n1 TYPING ("cannot satisfy constraint"): so the obvious attempt to
   place the term algebra in #440's variety is refused.  It adds
   nothing to the theorem above; it is here because a reader reaching for
   that term should meet the refusal at the point of reaching.  Note it
   refutes THAT term — the [eq_refl] satisfaction proof — and the theorem
   above is what refutes every term.

--------
n1 TYPING（“无法满足约束”）：所以将项代数放入 #440 的范畴的明显尝试被拒绝了。它对上面的定理没有任何补充；它在这里的原因是，当读者去查找该项时，应在查找点处遇到拒绝。注意，它驳斥了那个项——[eq_refl] 满足性证明——而上面的定理则驳斥每一个项。
*)
Fail Definition term_magma_leibniz : Variety CommEq :=
  (UA.Free MagmaOp bool; fun e args => eq_refl).

(*
control: the SHAPE is inhabited — the booleans under [xorb] are a
   perfectly good object of #440's Leibniz variety, so n1 is about the
   term algebra and not about the ascription.

--------
控制：该形状是有人居住的——[xorb] 下的布尔值是 #440 的莱布尼茨类型的完全有效对象，所以 n1 关于的是项代数而不是关于归属。
*)

Definition BoolMagmaOp : UA.OpAlgebra MagmaOp :=
  UA.Build_OpAlgebra MagmaOp bool
    (fun (o : UA.operation MagmaOp) k => xorb (k UA.Fst) (k UA.Snd)).

Example p441_bool_in_leibniz_variety : Variety CommEq.
Proof.
  exists BoolMagmaOp.
  intros e args; destruct e; simpl.
  destruct (args UA.Fst), (args UA.Snd); reflexivity.
Defined.

(*
THE QUALIFIER THE CLAIM NEEDED, in tree and cheap.  With no equations
   at all the congruence is generated by nothing, the term algebra
   satisfies the (empty) law set vacuously, and it IS an object of #440's
   Leibniz variety.  So "the free object cannot live in [Variety E]" was
   false already at the degenerate presentation, before the
   normal-form construction refuted it at a real one.

--------
声明所需的限定符，在树形且廉价。由于根本没有方程，合同关系由无生成，项代数在虚空意义上满足（空）法则集，并且它确实是 #440 的莱布尼兹多样体的一个对象。因此，“自由对象不能存在于 [Variety E]”在简化表示时就已经是错误的了，在正规形式构造在真实表示中反驳它之前。
*)

Definition EmptyEq : UA.EqSignature MagmaOp.
Proof.
  unshelve refine {| UA.eq := Empty_set ; UA.eq_arity := fun e => match e with end |}.
  - intros A e; destruct e.
  - intros A e; destruct e.
  - intros A B f e; destruct e.
  - intros A B f e; destruct e.
Defined.

Example free_empty_eq_leibniz : Variety EmptyEq.
Proof. exists (UA.Free MagmaOp bool); intro e; destruct e. Defined.

(**
** B: the congruence does not collapse

    Proved through the development's own universal property: map the
    free algebra into the booleans under [xor], which IS a commutative
    magma, by the identity on generators.  If the two generators were
    congruent their images would be `≈`, i.e. equal.

--------
** B: 同余关系不会崩溃

    通过发展的自身的泛性质证明：将自由代数在 [xor] 下映射到布尔代数，它确实是一个交换半群，通过对生成元的恒等映射。如果两个生成元是同余的，它们的像将是 `≈`，即相等。
*)

Program Definition BoolCommMagma : SetoidOpAlgebra MagmaOp := {|
  soa_obj := {| carrier := bool ; is_setoid := eq_Setoid bool |};
  soa_op  := fun (o : UA.operation MagmaOp) k => xorb (k UA.Fst) (k UA.Snd);
  soa_prop := eq_PropEquiv bool
|}.
Next Obligation.
  intros o k1 k2 H; simpl.
  rewrite (H UA.Fst), (H UA.Snd); reflexivity.
Qed.

Program Definition BoolCommMagma_sat : ssatisfies CommEq BoolCommMagma.
Proof.
  intros e args; destruct e; simpl.
  destruct (args UA.Fst), (args UA.Snd); reflexivity.
Qed.

Definition BoolCommVariety : SVariety CommEq :=
  (BoolCommMagma; BoolCommMagma_sat).

(*
The generators, as a [SetoidObject] with the discrete setoid.  Named
   [BoolGens] rather than [BoolSet], which is taken four times over
   (Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v,
   Instance/Grp/EckmannHilton.v, Test/ProbeSetsQuotient.v).

--------
这些生成器，作为带有离散集合论的 [SetoidObject]。命名为 [BoolGens] 而不是 [BoolSet]，因为后者已经被使用了四次（Instance/Sets/Quotient.v, Instance/Sets/Coequalizer.v, Instance/Grp/EckmannHilton.v, Test/ProbeSetsQuotient.v）。
*)
Definition BoolGens : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

(*
No [Next Obligation] here: the identity on a discrete setoid is
   [Proper] by [Lib]'s own resolution, and adding one gets "No
   obligations remaining".

--------
这里没有 [Next Obligation]：离散集合上的恒等映射是由 [Lib] 自身的解析 [Proper]，并且加一后得到“没有剩余义务”。
*)
Definition sep_args' (i : UA.binary) : UA.Tree MagmaOp BoolGens :=
  match i with
  | UA.Fst => UA.generator MagmaOp BoolGens true
  | UA.Snd => UA.generator MagmaOp BoolGens false
  end.

Program Definition bool_generators : BoolGens ~{Sets}~> soa_obj BoolCommMagma := {|
  morphism := fun b : bool => b
|}.

Theorem free_comm_not_collapsed :
  tree_equiv CommEq BoolGens
    (UA.generator MagmaOp BoolGens true) (UA.generator MagmaOp BoolGens false) → False.
Proof.
  intro D.
  pose proof (free_alg_ext_respects CommEq BoolGens
                BoolCommVariety bool_generators _ _ D) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
Non-vacuity of the congruence, so that [free_comm_not_collapsed] is a
   sharp result rather than a statement about an empty relation: the
   commutativity law DOES identify two distinct terms.

--------
同余的非空性，因此 [free_comm_not_collapsed] 是一个明确的结果，而不是关于空关系的陈述：交换律的确识别出两个不同的项。
*)
Example p441_congruence_identifies :
  tree_equiv CommEq BoolGens
    (UA.node MagmaOp BoolGens magma_mul sep_args')
    (UA.node MagmaOp BoolGens magma_mul (fun i => sep_args' (comm_swap i)))
  := tc_law CommEq BoolGens comm_law sep_args'.

(** ** C: CONVERSION / ** C：转换 *)

(*
n2: the free algebra's carrier IS the term type, but its `≈` is the
   congruence and not Leibniz [=], so the two setoids do not convert.

--------
n2：自由代数的载体是项类型，但它的 `≈` 是合同而不是 Leibniz [=]，所以这两个集合类型不能相互转换。
*)
Fail Example p441_free_setoid_is_eq :
  Tree_Setoid CommEq BoolGens = eq_Setoid (UA.Tree MagmaOp BoolGens) := eq_refl.

(* control: the CARRIER does agree on the nose / 控制：承运人确实同意在鼻子上 *)
Example p441_free_carrier :
  carrier (soa_obj (`1 (Free_Variety CommEq BoolGens)))
    = UA.Tree MagmaOp BoolGens := eq_refl.

(*
n3: the two terms n1 is about are not CONVERTIBLE.  That is weaker
   than "distinct" — non-convertibility is not disprovability — and an
   earlier revision of this comment claimed the stronger thing.  What
   establishes distinctness is [free_magma_not_comm_leibniz] above.

--------
n3: n1 涉及的两个术语是不可互换的。这比“不同”要弱——不可互换性并不等于可反驳性——而该评论的早期修订版本声称的是更强的内容。确定不同之处的是上文的 [free_magma_not_comm_leibniz]。
*)
Fail Example p441_terms_convert :
  UA.node MagmaOp bool magma_mul sep_args
    = UA.node MagmaOp bool magma_mul (fun i => sep_args (comm_swap i)) := eq_refl.

(**
** C2 (#450): the congruence is a [Prop] and eliminates only into [Prop]

    Since #450 [tree_equiv] is [Prop]-valued (Instance/Variety/Free.v's
    header records the correction).  n4 pins that a derivation cannot be
    eliminated into a [Type]-sorted goal; the control below it runs the
    SAME script into a [Prop]-sorted goal and is accepted, so the refusal
    is about the sort of the goal and nothing else.  With the refutation
    keyword stripped in a copy of this whole file the refusal reads
    "Cannot find the elimination combinator tree_equiv_rec, the
    elimination of the inductive definition tree_equiv on sort Set is
    probably not allowed".
    Refuting a [Lemma] with the statement alone would pass vacuously -- the
    statement is well typed -- so the pin is a [Definition] whose body is
    the elimination.  The goal is [bool] rather than [nat] on purpose:
    numerals have no interpretation under this file's scopes, so an
    [exact 0] body is refused for that reason and its refutation would
    pass without testing the sort (measured).

--------
** C2 (#450)：该同余是 [Prop]，并且只消除到 [Prop]

由于 #450 [tree_equiv] 是 [Prop] 值（Instance/Variety/Free.v 的头部记录了修正）。n4 指出一个推导不能被消去到 [Type] 排序的目标；其下的控制将相同的脚本运行到 [Prop] 排序的目标并被接受，因此拒绝是关于目标的排序，而不是其他问题。在这整个文件的副本中去掉反驳关键字后，拒绝信息显示为“找不到消去组合器 tree_equiv_rec，归纳定义 tree_equiv 在集合类型上的消去可能不被允许”。仅凭这一声明驳斥 [Lemma] 将会空泛地通过——该声明类型正确——因此该引脚是一个 [Definition]，其主体是消解。目标故意是 [bool] 而不是 [nat]：在此文件的作用域下，数字没有解释，因此 [exact 0] 主体因此会被拒绝，其驳斥将无需测试类型（已测量）就通过。
*)

Fail Definition p450_tree_equiv_elim_Type (X : Sets) (t u : UA.Tree MagmaOp X)
  (H : tree_equiv CommEq X t u) : bool := ltac:(induction H; exact true).

(* control: the identical script into a [Prop] goal / 控制：将相同的脚本置入 [Prop] 目标 *)
Definition p450_tree_equiv_elim_Prop (X : Sets) (t u : UA.Tree MagmaOp X)
  (H : tree_equiv CommEq X t u) : True := ltac:(induction H; exact I).

(**
** D: readbacks

    The unit is the generator embedding on the nose, and the extension
    of a map along it IS Instance/Comp.v's [induced_map] — nothing is
    re-recursed.

--------
** D: 回读

该单元是安装在机鼻上的发电机，以及沿其扩展的地图是 Instance/Comp.v 的 [induced_map] —— 没有重复递归。
*)

Example p441_unit_is_generator (X : Sets) (x : X) :
  free_unit CommEq X x = UA.generator MagmaOp X x := eq_refl.

(*
This one pins TRANSPARENCY and nothing else: [free_alg_ext]'s body IS
   the right-hand side, so it is discharged by delta and holds for as
   long as that body stands.  An earlier revision offered it as evidence
   that "nothing is re-recursed", which it is not — an independently
   written [Fixpoint] with the same clauses also converts.

--------
这个只针对于透明性，而不涉及其他：[free_alg_ext] 的主体在右侧，因此它由 delta 放电，并在该主体存在期间有效。一个早期的版本将其作为“没有被重新递归”的证据，但事实并非如此——一个独立编写的、具有相同条款的 [Fixpoint] 也会转换。
*)
Example p441_ext_is_induced_map (X : Sets) (A : SVariety CommEq)
  (h : X ~{Sets}~> soa_obj (`1 A)) (t : UA.Tree MagmaOp X) :
  free_alg_ext A h t = UA.induced_map MagmaOp X (soa_alg (`1 A)) h t := eq_refl.

(*
This one pins the RECURSION STEP, which is what the prose was reaching
   for: the extension of a map at a node is the algebra's operation
   applied to the extensions of the arguments.

--------
这一点钉住了递归步骤，这正是散文所追求的：在一个节点上映射的扩展就是代数的运算作用于参数的扩展。
*)
Example p441_ext_step (X : Sets) (A : SVariety CommEq)
  (h : X ~{Sets}~> soa_obj (`1 A)) (o : UA.operation MagmaOp)
  (k : UA.arity o → UA.Tree MagmaOp X) :
  free_alg_ext A h (UA.node MagmaOp X o k)
    = soa_op (`1 A) o (fun i => free_alg_ext A h (k i)) := eq_refl.

(*
And the left adjoint's action on OBJECTS, which nothing else pinned:
   the functor built from the universal arrows really is [Free_Variety].

--------
以及左伴随作用于对象的情形，没有其他东西能固定它：由泛化箭头构建的函子确实是 [Free_Variety]。
*)
Example p441_left_adjoint_obj (X : Sets) :
  Free_Variety_Functor CommEq X = Free_Variety CommEq X := eq_refl.

Example p441_free_op_is_node (X : Sets) (o : UA.operation MagmaOp)
  (k : UA.arity o → UA.Tree MagmaOp X) :
  soa_op (FreeSOA CommEq X) o k = UA.node MagmaOp X o k := eq_refl.

(** ** E: guard block / ** E：守卫块 *)

Check @SetoidOpAlgebra.
Check @soa_obj.
Check @soa_op.
Check @soa_op_respects.
Check @soa_prop.
Check @soa_alg.
Check @SAlgHom.
Check @salg_map.
Check @salg_respects.
Check @salg_commute.
Check @SAlgHom_Setoid.
Check @SAlg_id.
Check @SAlg_comp.
Check @SetoidAlgs.
Check @ssatisfies.
Check @SVariety_sub.
Check @SVariety.
Check @SVariety_Full.
Check @SVariety_Incl.
Check @SVariety_Forget.
Check @SVariety_Forget_Faithful.
Check @tree_equiv.
Check @tc_gen.
Check @tc_op.
Check @tc_law.
Check @tc_sym.
Check @tc_trans.
Check @tc_refl.
Check @Tree_Setoid.
Check @FreeSOA.
Check @FreeSOA_satisfies.
Check @Free_Variety.
Check @free_alg_ext.
Check @free_alg_ext_respects.
Check @free_alg_hom.
Check @free_alg_hom_unique.
Check @free_unit.
Check @FreeUA.
Check @Free_Variety_Functor.
Check @Free_Variety_adjunction.
Check @soa_prod_setoid.
Check @soa_prod.
Check @soa_prod_exl.
Check @soa_prod_exr.
Check @soa_prod_satisfies.
Check @not_equationally_definable.
Check @CommMagmaFree.
Check @CommMagmaFree_adjunction.
Check @SGroupVariety.
Check @FreeGroupOn.
Check @FreeGroup_adjunction.
Check @leibniz_soa.
Check @ring_op.
Check @RingOp.
Check rzero.
Check rone.
Check radd.
Check rmul.
Check @F2_op.
Check @F2.
Check @r_zero.
Check @r_one.
Check @r_mul.
Check @HasDivision.
Check @IsField.
Check @r_add.
Check @F2_HasDivision.
Check @F2_IsField.
Check @F2xF2_no_division.
Check @F2xF2_not_field.
Check @division_is_not_equationally_definable.
Check @fields_are_not_a_variety.
Check @Variety.
Check @CommEq.
Check @MagmaOp.
Check @BoolGens.
Check @EmptyEq.
Check @free_empty_eq_leibniz.
Check @BoolMagmaOp.
Check @BoolCommMagma.
Check @BoolCommVariety.
Check @bool_generators.
Check @first_gen.
Check @sep_args.
Check @sep_args'.
Check @p441_congruence_identifies.
Check @free_magma_not_comm_leibniz.
Check @free_comm_not_collapsed.
