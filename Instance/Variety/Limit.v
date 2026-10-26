Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.

Generalizable All Variables.

(* * * Limits in the setoid variety are computed on underlying sets / * * 在等价关系类型中，极限是在其底层集合上计算的 *)

(*
 nLab:      https://ncatlab.org/nlab/show/created+limit
 nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
 Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)
 Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)

 A limit of algebras is computed on the underlying sets: its carrier is
 the limit of the carriers, its operations act coordinatewise, and it
 satisfies every equation the components satisfy because each
 coordinate does.  Mac Lane's §V.1 proves this for groups (the forgetful
 functor creates limits, Theorem 2, so the category is complete,
 Theorem 3); Instance/Grp/Limit.v formalises that case.  This file does
 the same for the SETOID VARIETY [SVariety E] of
 Instance/Variety/Free.v, uniformly in the operation signature and the
 set of equations.  It supplies completeness, which every application
 of the adjoint functor theorem (Adjunction/GAFT.v's [GAFT]) at this
 category takes, and the continuity of the forgetful functor, which the
 application at that functor takes.  Instance/Variety/Colimit.v makes
 both applications: at the diagonal, for Mac Lane's colimits of
 algebras (§V.7 Exercise 4, §IX.1 Exercise 2), where the preservation
 input is Adjunction/Diagonal/Limit.v's [Diagonal_continuous]; and at
 the forgetful functor, for Mac Lane's own route to the free algebra
 (§V.6), where it is [SVariety_Forget_continuous] below.

 CONSUMED, not rebuilt: Instance/Sets/Complete.v's compatible families
 ([Sets_limit_obj], [Sets_limit_carrier]); Instance/Sets/Propositional.v's
 [limit_PropEquiv], the propositional mirror of a limit of setoids,
 which supplies the [soa_prop] field Instance/Variety/Free.v's record
 carries since #450 with no hypothesis on the limit; and
 Instance/Comp.v's [lhs_natural] and [rhs_natural], CONSUMED along
 evaluation at a coordinate exactly as Free.v's [soa_prod_satisfies]
 consumes them along a projection -- never proved, so nothing here pays
 the functional extensionality some [EqSignature]s cost to BUILD.

 BUILT:

 - [svlim_soa]/[svlim_alg], the limit algebra over any shape and any
 diagram; [svlim_eval d], evaluation at a coordinate as a LEIBNIZ
 homomorphism of Instance/Comp.v, whose [op_commute] is
 [reflexivity]; [svlim_satisfies], the equations coordinatewise.
 - [svlim_cone], [svlim_med] and [SVariety_Limit : Limit F], the cone
 with its mediator and uniqueness read off pointwise, as
 [Sets_Limit] does; [SVariety_Complete : @Complete (SVariety E)].
 - [SVariety_Forget_continuous : ContinuousFunctor (SVariety_Forget
 E)], cone-level preservation of EVERY limit, not only of the
 computed one: for a limiting cone [N] the comparison [svf_to] from
 the computed limit is a retraction of [svlim_med] ([svf_to_med]),
 both composites being mediators out of [N] into itself, and the
 mediator out of a cone of setoids is the compatible family of its
 legs followed by [svf_to].

 STRENGTH, STRICTEST FIRST.  At the limit [SVariety_Complete] chooses,
 the carrier IS the compatible families, the operation at coordinate [d]
 IS the component's operation, and the leg at [d] IS evaluation:
 [svariety_complete_carrier], [svariety_complete_op] and
 [svariety_complete_leg] are three [eq_refl] Examples at an arbitrary
 signature, set of equations, shape and diagram.  They compare carriers
 and elements, the sanctioned exception to comparing morphisms by `≈`;
 every law, mediator and uniqueness clause is stated with `≈`.  NOT
 delivered at any strength is CREATION in the sense of
 Structure/Limit/Creation.v -- no [CreatesLimits] or
 [StrictlyCreatesLimit] instance, and no statement that the algebra
 structure on a limit of carriers is UNIQUE (Mac Lane's Theorem 2 has
 that clause; Instance/Grp/Limit.v's [glim_structure_unique] states it
 for groups).  What is delivered is computation plus continuity, which
 is exactly what [GAFT] consumes.

 UNIVERSES, measured with [About] under [Set Printing Universes], the
 stdlib-global bounds ([Projections], [compose], [eq_rect_r], [ID])
 dropped:

 SVariety_Complete@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} :
 ∀ {S : UA.OpSignature@{u0 u1}} (E : UA.EqSignature@{u2 u3 u u u0 u1} S),
 Complete@{u u4 u u5}
 ( * Set < u6 / u < u6 / u < u9 / u <= u7 / u0 <= u / u1 <= u /
 u2 <= u7 / u3 <= u7 / u4 <= u / u6 <= u5 / u7 <= u5 / u8 <= u * )

 So the result and hom universes of [Complete@{r so h o}] are the
 carrier universe [u], shapes may have objects at or below it
 ([u4 <= u]), and the category's objects sit strictly above it -- more
 permissive than [Sets_Complete@{u u0} : Complete@{u u u u0}], whose
 shapes have their objects AT the carrier universe ([Category] is not
 cumulative), and at [u4 := u] exactly the [Complete@{h h h cobj}]
 instance [GAFT] needs with [h] the carrier.
 No universe is instantiated at [Set]; the one [Set] is the lower bound
 [Set < u6] that [soa_prop] puts on the object universe
 (Instance/Variety/Free.v's header).  No binder is annotated by hand:
 minimization collapsed nothing, measured by the readback above.

 NON-VACUITY.  Nothing here is specific to a witness category: the
 three readbacks hold for every diagram, and
 Instance/Variety/Colimit.v instantiates [SVariety_Complete] at #440's
 [CommEq], whose [EqSignature] is built without extensionality, in
 closed constants of its own.

 TRANSPARENCY, measured by flipping each of the four [Defined] to [Qed]
 in a scratch copy of this file: all four are load-bearing.  [svlim_op]
 opaque stops [svlim_soa], whose respect field needs the operation to
 reduce at a coordinate; [svlim_eval] opaque stops [svlim_satisfies],
 which needs its map to reduce to evaluation; [svlim_med_map] opaque
 stops the respect obligation of [svlim_med], and [svf_family] opaque
 stops that of [svf_med], each needing the family to reduce at a
 coordinate.  The [Program] obligations and the lemmas end in [Qed].

 PORTABILITY.  [svlim_op], [svlim_med_map] and [svf_family] are
 written as tactic proofs, the first component given by [exists] and
 the second proved by tactics against the goal it leaves, not as
 anonymous-constructor terms [(a; b)]: measured by a Nix build
 on Coq 8.20.1 of the first revision of this file, the term form of
 [svlim_med_map] is refused there although Rocq 9.1 accepts it (the
 comment above that definition quotes the refusal).

 ASSUMPTIONS, measured: [Print Assumptions] on every constant of the
 module, enumerated by [Print Module] (heads and [Program] obligations,
 which [.glob] heads omit) returns “Closed under the global context”
 for each.

 NOT delivered: creation and uniqueness of the lifted structure, as
 above; no identification of [soa_prod] (Instance/Variety/Free.v) with
 the binary product computed here; no colimits (Instance/Variety/Colimit.v);
 and nothing about #440's Leibniz [Variety E], whose limits are not
 touched. 

 --------
 nLab:       https://ncatlab.org/nlab/show/created+limit 
 nLab:       https://ncatlab.org/nlab/show/variety+of+algebras 
 维基百科:  https://en.wikipedia.org/wiki/Variety_(universal_algebra) 
 Mac Lane:  《为在职数学家而作的范畴论》，第2版（GTM 5），
 §V.1 定理 2 和 3，书籍页码 111-112（PDF 页码 120-121）代数的极限是在底层集合上计算的：其载体是载体的极限，其运算按坐标作用，并且它满足每个分量满足的所有方程，因为每个坐标都满足这些方程。Mac Lane 的 §V.1 证明了群的情况（遗忘函子产生极限，定理 2，因此范畴是完备的，定理 3）；Instance/Grp/Limit.v 对该情况进行了形式化。该文件对 Instance/Variety/Free.v 的集合等价类 VARIETY [SVariety E] 做了同样的处理，在运算符号和方程集合上是统一的。它提供了完备性，这是在该范畴中应用伴随函子定理（Adjunction/GAFT.v 的 [GAFT]）所需的，并且提供了遗忘函子的连续性，这是在该函子上应用时所需的。Instance/Variety/Colimit.v 同时用于两种应用：在对角线上，用于 Mac Lane 的代数余极限（§V.7 练习 4，§IX.1 练习 2），其中的保持输入是 Adjunction/Diagonal/Limit.v 的 [Diagonal_continuous]；以及在遗忘函子上，用于 Mac Lane 自己通向自由代数的路径（§V.6），其中它是下面的 [SVariety_Forget_continuous]。已消耗，而非重建：Instance/Sets/Complete.v 的兼容族
 ([Sets_limit_obj], [Sets_limit_carrier])；Instance/Sets/Propositional.v 的
 [limit_PropEquiv]，一个集合论极限的命题镜像，
 它提供了 Instance/Variety/Free.v 的记录的 [soa_prop] 字段，
 自 #450 起在极限上没有假设；以及
 Instance/Comp.v 的 [lhs_natural] 和 [rhs_natural]，在坐标上的求值时被消耗，
 就像 Free.v 的 [soa_prod_satisfies] 在投影上消耗它们一样——从未被证明，因此这里没有任何东西承担某些 [EqSignature] 构建功能外延所需的代价。

 已构建:- [svlim_soa] / [svlim_alg]，任意形状和任意图上的极限代数；[svlim_eval d]，作为Instance/Comp.v的LEIBNIZ同态在坐标处的评估，其[op_commute]是[reflexivity]；[svlim_satisfies]，按坐标的方程。 - [svlim_cone]，[svlim_med]和[SVariety_Limit : Limit F]，带有其中介和唯一性按点读取的圆锥，正如[Sets_Limit]所做；[SVariety_Complete : @Complete (SVariety E)]。- [SVariety_Forget_continuous : ContinuousFunctor (SVariety_Forget E)]，保持每一个极限的锥层面，而不仅仅是已计算的极限：对于一个极限锥 [N]，从已计算极限得到的比较 [svf_to] 是 [svlim_med] ([svf_to_med]) 的一个重traction，两个复合都是从 [N] 到其自身的中介，而从集合体锥出的中介是其各条腿的兼容族，随后是 [svf_to]。强度，最严格优先。在极限 [SVariety_Complete] 选择时，载体是兼容的族，坐标 [d] 处的运算是组件的运算，[d] 处的腿是评估：[svariety_complete_carrier]、[svariety_complete_op] 和 [svariety_complete_leg] 是在任意签名、方程集、形状和图表下的三个 [eq_refl] 示例。它们比较载体和元素，由 `≈` 批准的比较态射的例外；每条定律、中介和唯一性条款都用 `≈` 陈述。未以任何强度交付的是结构/极限/创建.v 意义上的创造——没有 [CreatesLimits] 或 [StrictlyCreatesLimit] 实例，也没有关于载体的极限上的代数结构是唯一的声明（Mac Lane 的定理 2 有该条款；Instance/Grp/Limit.v 的 [glim_structure_unique] 为群体陈述了它）。所提供的是计算加连续性，这正是 [GAFT] 所消耗的。

 在 [Set Printing Universes] 下，用 [About] 测量的宇宙，stdlib-全局边界（[Projections]、[compose]、[eq_rect_r]、[ID]）下降：

 SVariety_Complete@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9} ：
 ∀ {S : UA.OpSignature@{u0 u1}} (E : UA.EqSignature@{u2 u3 u u u0 u1} S)，
 Complete@{u u4 u u5}
 ( * 集合 < u6 / u < u6 / u < u9 / u <= u7 / u0 <= u / u1 <= u /
 u2 <= u7 / u3 <= u7 / u4 <= u / u6 <= u5 / u7 <= u5 / u8 <= u * )因此 [Complete@{r so h o}] 的结果和同态宇宙是承载宇宙 [u]，形状的对象可以位于其上或其下（[u4 <= u]），并且该范畴的对象严格位于其上——比 [Sets_Complete@{u u0} : Complete@{u u u u0}] 更宽松，后者的形状的对象位于承载宇宙（[Category] 不是累积的），而在 [u4 := u] 中正好是 [Complete@{h h h cobj}] 实例 [GAFT] 需要 [h] 承载。没有宇宙在 [Set] 实例化；[Set] 是 [soa_prop] 对对象宇宙施加的下界 [Set < u6]（Instance/Variety/Free.v 的头部）。没有绑定器是手动标注的：最小化没有折叠任何内容，以上述回读衡量。非空性。这里没有特定于见证类别的内容：这三个回读适用于每个图，并且 Instance/Variety/Colimit.v 在 #440 的 [CommEq] 处实例化 [SVariety_Complete]，其 [EqSignature] 在自身闭合常量中构建时没有使用外延性。

 透明性，通过在此文件的一个临时副本中将四个 [Defined] 翻转为 [Qed] 来衡量：四个都是承重的。[svlim_op] 不透明地阻止 [svlim_soa]，其 respect 字段需要操作在一个坐标上化简；[svlim_eval] 不透明地阻止 [svlim_satisfies]，需要其映射化简为求值；[svlim_med_map] 不透明地阻止 [svlim_med] 的 respect 义务，[svf_family] 不透明地阻止 [svf_med] 的义务，每个都需要族在一个坐标上化简。[Program] 的义务和引理最终结束于 [Qed] 。可移植性。[svlim_op]、[svlim_med_map] 和 [svf_family] 被写成战术证明，第一部分由 [exists] 给出，第二部分通过针对它留下的目标的战术来证明，而不是作为匿名构造子项 [(a; b)]：根据在 Coq 8.20.1 上使用 Nix 构建的本文件第一个修订版进行测量，[svlim_med_map] 的项形式在那里被拒绝，尽管 Rocq 9.1 接受它（该定义上方的注释引用了拒绝信息）。

 假设，测量：[Print Assumptions] 对模块的每个常量进行测量，由 [Print Module] 枚举（头和 [Program] 义务，[.glob] 的头部省略了），每个都返回“在全局上下文下封闭”。未完成：提升结构的创建和唯一性，如上所述；未将 [soa_prod]（实例/种类/自由.v）与此处计算的二元积识别；没有余极限（实例/种类/余极限.v）；且没有涉及 #440 的 Leibniz [Variety E]，其极限未被触及。
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

#[local] Obligation Tactic := idtac.

Section SVarietyLimit.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (F : J ⟶ SVariety E).

(* The underlying diagram of setoids. / 集合类的基础图示。 *)
Definition svlim_UF : J ⟶ Sets := SVariety_Forget E ◯ F.

(* The carrier: the compatible families of Instance/Sets/Complete.v. / 载体：Instance/Sets/Complete.v 的兼容族。 *)
Definition svlim_obj : SetoidObject := Sets_limit_obj svlim_UF.

(*
 The operations, pointwise in the shape.  Compatibility of the result is
 the homomorphism law of each [fmap[F] f] followed by respect for `≈`
 of the target's operation, applied to the compatibility of each
 argument. 

 --------
 运算在形状上逐点进行。结果的兼容性是每个 [fmap[F] f] 的同态律，随后尊重目标运算的 `≈`，对每个参数的兼容性应用。
*)
Definition svlim_op (o : UA.operation S)
  (k : UA.arity o → carrier svlim_obj) : carrier svlim_obj.
Proof.
  exists (fun d => soa_op (`1 (F d)) o (fun i => `1 (k i) d)).
  intros d d' f; simpl.
  transitivity (soa_op (`1 (F d')) o
                  (fun i => salg_map (`1 (fmap[F] f)) (`1 (k i) d))).
  - exact (salg_commute (`1 (fmap[F] f)) o (fun i => `1 (k i) d)).
  - apply (soa_op_respects (`1 (F d')) o); intro i.
    exact (`2 (k i) d d' f).
Defined.

(*
 The propositional equality is Instance/Sets/Propositional.v's limit
 transport, supplied from the components' own [soa_prop] with no
 hypothesis on the limit. 

 --------
 命题等式是 Instance/Sets/Propositional.v 的极限传输，它来自组件自身的 [soa_prop]，且对极限没有任何假设。
*)
Definition svlim_soa : SetoidOpAlgebra S := {|
  soa_obj := svlim_obj;
  soa_op := svlim_op;
  soa_op_respects := fun o k1 k2 H d =>
    soa_op_respects (`1 (F d)) o _ _ (fun i => H i d);
  soa_prop := limit_PropEquiv svlim_UF (fun d => soa_prop (`1 (F d)))
|}.

(* Evaluation at [d] is a LEIBNIZ homomorphism of Instance/Comp.v: the limit's operation at [d] is the component's operation on the nose, so [op_commute] is [eq_refl]. / 在 [d] 上的评估是 Instance/Comp.v 的 LEIBNIZ 同态：在 [d] 上的极限操作正是组件的操作，因此 [op_commute] 就是 [eq_refl]。 *)
Definition svlim_eval (d : J) :
  UA.AlgHom (soa_alg svlim_soa) (soa_alg (`1 (F d))).
Proof. exists (fun p => `1 p d). intros o args; reflexivity. Defined.

(* The equations hold pointwise: each component is [F d]'s own satisfaction transported along [svlim_eval d] by [lhs_natural] and [rhs_natural], consuming those fields and never proving one. / 这些方程在每一点上都成立：每个分量都是 [F d] 自身的满足，通过 [lhs_natural] 和 [rhs_natural] 沿 [svlim_eval d] 传递，消耗那些场而从不证明其中任何一个。 *)
Lemma svlim_satisfies : ssatisfies E svlim_soa.
Proof.
  intros e args d.
  assert (HL : `1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
               = @UA.lhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.lhs_natural S E _ _ (svlim_eval d) e args).
  assert (HR : `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d
               = @UA.rhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.rhs_natural S E _ _ (svlim_eval d) e args).
  change (`1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
          ≈ `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d).
  rewrite HL, HR.
  exact (`2 (F d) e (fun i => `1 (args i) d)).
Qed.

Definition svlim_alg : SVariety E := (svlim_soa; svlim_satisfies).

Program Definition svlim_leg (d : J) : svlim_alg ~{SVariety E}~> F d :=
  ({| salg_map := fun p : carrier svlim_obj => `1 p d |}; I).
Next Obligation. intros d p q H; exact (H d). Qed.
Next Obligation. intros d o args; simpl; reflexivity. Qed.

Program Definition svlim_cone : Cone F := {|
  vertex_obj := svlim_alg;
  coneFrom := {| vertex_map := svlim_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(*
 Written as a tactic proof, the coherence component closed by [exact],
 and NOT as an anonymous-constructor term: its expected type states
 compatibility with [fmap[SVariety_Forget E ◯ F]], which [cone_coherence]
 matches only after unfolding the composite.  Measured by a Nix build
 of this file's first revision on Coq 8.20.1, the term form
 [(fun d => … ; fun d d' f => @cone_coherence … x)] is refused there
 with “The term … has type ”∃ _ : ∀ x0 : obj[J], soa_obj (projT1
 (fobj[F] x0)), …“ while it is expected to have type ”carrier
 svlim_obj“”, although Rocq 9.1 accepts it. 

 --------
 以战术证明的形式书写时，连贯性组件由 [exact] 闭合，而不是作为匿名构造子项：它的预期类型声明与 [fmap[SVariety_Forget E ◯ F] 兼容，[cone_coherence] 只有在展开复合后才匹配。根据在 Coq 8.20.1 上对该文件首次修订的 Nix 构建测量，项形式 [(fun d => … ; fun d d' f => @cone_coherence … x)] 在那里被拒绝，提示“该项 … 的类型为 ‘∃ _ : ∀ x0 : obj [J] , soa_obj (projT1 (fobj [F] x0)), …’，而预期类型为 ‘carrier svlim_obj’”，尽管 Rocq 9.1 可以接受它。
*)
Definition svlim_med_map (N : Cone F)
  (x : carrier (soa_obj (`1 (vertex_obj[N])))) : carrier svlim_obj.
Proof.
  exists (fun d => salg_map (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f x).
Defined.

Program Definition svlim_med (N : Cone F) :
  vertex_obj[N] ~{SVariety E}~> svlim_alg :=
  ({| salg_map := svlim_med_map N |}; I).
Next Obligation.
  intros N x y H d; simpl.
  exact (salg_respects (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x y H).
Qed.
Next Obligation.
  intros N o args d; simpl.
  exact (salg_commute (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) o args).
Qed.

Program Definition SVariety_Limit : Limit F := {|
  limit_cone := svlim_cone;
  ump_limits := fun N => {| unique_obj := svlim_med N |}
|}.
Next Obligation. intros N d x; simpl; reflexivity. Qed.
Next Obligation. intros N v Hv x d; simpl; symmetry; exact (Hv d x). Qed.

End SVarietyLimit.

Arguments svlim_UF {_} _ {_} _.
Arguments svlim_obj {_} _ {_} _.
Arguments svlim_op {_} _ {_} _ _ _.
Arguments svlim_soa {_} _ {_} _.
Arguments svlim_eval {_} _ {_} _ _.
Arguments svlim_satisfies {_} _ {_} _ _ _ _.
Arguments svlim_alg {_} _ {_} _.
Arguments svlim_leg {_} _ {_} _ _.
Arguments svlim_cone {_} _ {_} _.
Arguments svlim_med_map {_} _ {_} _ _ _.
Arguments svlim_med {_} _ {_} _ _.
Arguments SVariety_Limit {_} _ {_} _.

Definition SVariety_Complete {S : UA.OpSignature} (E : UA.EqSignature S) :
  @Complete (SVariety E) := fun J F => SVariety_Limit E F.

(*
 The limit [SVariety_Complete] chooses IS the computed one on the nose:
 its carrier is the compatible families of Instance/Sets/Complete.v,
 its operation at a coordinate is the component's operation, and its
 legs are evaluation. 

 --------
 极限 [SVariety_Complete] 选择的正是精确计算出来的那个：
 它的承载体是 Instance/Sets/Complete.v 的兼容族，
 它在某坐标处的运算是该分量的运算，而它的腿是评估。
*)

Example svariety_complete_carrier {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) :
  carrier (soa_obj (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])))
    = Sets_limit_carrier (svlim_UF E F) := eq_refl.

Example svariety_complete_op {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (o : UA.operation S)
  (k : UA.arity o → carrier (svlim_obj E F)) (d : J) :
  `1 (soa_op (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])) o k) d
    = soa_op (`1 (F d)) o (fun i => `1 (k i) d) := eq_refl.

Example svariety_complete_leg {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (d : J) (p : carrier (svlim_obj E F)) :
  salg_map (`1 (@vertex_map _ _ _ _
                 (@coneFrom _ _ _ (@limit_cone _ _ _ (SVariety_Complete E J F))) d)) p
    = `1 p d := eq_refl.

(*
   * ** The forgetful functor is continuous

   The image under [SVariety_Forget] of ANY limiting cone -- not only
   of [svlim_cone] -- is limiting in [Sets].  Given a limiting [N] and a
   cone [M] of setoids, the mediator is the compatible family of [M]'s
   legs followed by the comparison [svf_to] from the computed limit to
   [N]; uniqueness goes back through the comparison [svlim_med] the
   other way, which composes with [svf_to] to the identity by [N]'s own
   uniqueness clause. 

   --------
   * ** 忘记函子是连续的

   任何极限锥在 [SVariety_Forget] 下的像——不仅仅是 [svlim_cone] 的像——在 [Sets] 中是极限的。给定一个极限 [N] 和一个集合论对象的锥 [M]，调解子是由 [M] 的各条腿组成的兼容族，然后是从计算出的极限到 [N] 的比较 [svf_to]；唯一性通过比较 [svlim_med] 反向回溯，它与 [svf_to] 组成恒等映射，根据 [N] 自身的唯一性条款。
*)

Section ForgetContinuous.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (G : J ⟶ SVariety E).
Context (N : Cone G) (HN : IsLimitCone N).
Context (M : Cone (SVariety_Forget E ◯ G)).

(* The comparison from the computed limit to [N]. / 从计算极限到 [N] 的比较。 *)
Definition svf_to : svlim_alg E G ~{SVariety E}~> vertex_obj[N] :=
  unique_obj (HN (svlim_cone E G)).

Lemma svf_to_legs (d : J) (p : carrier (svlim_obj E G)) :
  salg_map (`1 (cone_leg N d)) (salg_map (`1 svf_to) p) ≈ `1 p d.
Proof. exact (unique_property (HN (svlim_cone E G)) d p). Qed.

(*
 It is a retraction of [svlim_med]: [svf_to ∘ svlim_med N] and the
 identity are both mediators from [N] to itself. 

 --------
 这是对 [svlim_med] 的撤回：[svf_to ∘ svlim_med N] 和恒等映射都是从 [N] 到其自身的中介者。
*)
Lemma svf_to_med (y : carrier (soa_obj (`1 (vertex_obj[N])))) :
  salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) y) ≈ y.
Proof.
  assert (Hid : unique_obj (HN N) ≈ id[vertex_obj[N]]).
  { apply (uniqueness (HN N)); intros d x; reflexivity. }
  assert (Hcomp : unique_obj (HN N) ≈ svf_to ∘ svlim_med E G N).
  { apply (uniqueness (HN N)); intros d x; simpl.
    exact (svf_to_legs d (svlim_med_map E G N x)). }
  exact (transitivity (symmetry (Hcomp y)) (Hid y)).
Qed.

(* The compatible family of the legs of [M]. / [M] 的腿的兼容系列。 *)
Definition svf_family (x : carrier (vertex_obj[M])) : carrier (svlim_obj E G).
Proof.
  (* Tactic form for the reason given at [svlim_med_map]. / 针对 [svlim_med_map] 提供的理由的策略形式。 *)
  exists (fun d => cone_leg M d x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) d d' f x).
Defined.

Program Definition svf_med :
  vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N]) := {|
  morphism := fun x => salg_map (`1 svf_to) (svf_family x)
|}.
Next Obligation.
  intros x y Hxy.
  apply (salg_respects (`1 svf_to)).
  intro d; simpl.
  exact (proper_morphism (cone_leg M d) x y Hxy).
Qed.

Lemma svf_med_legs (d : J) :
  cone_leg (FCone (SVariety_Forget E) N) d ∘ svf_med ≈ cone_leg M d.
Proof. intro x; exact (svf_to_legs d (svf_family x)). Qed.

Lemma svf_med_unique
  (v : vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N])) :
  (∀ d : J, cone_leg (FCone (SVariety_Forget E) N) d ∘ v ≈ cone_leg M d) →
  svf_med ≈ v.
Proof.
  intros Hv x; simpl.
  transitivity (salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) (v x))).
  - apply (salg_respects (`1 svf_to)).
    intro d; simpl; symmetry; exact (Hv d x).
  - exact (svf_to_med (v x)).
Qed.

End ForgetContinuous.

Arguments svf_to {_} _ {_} _ _ _.
Arguments svf_to_legs {_} _ {_} _ _ _ _ _.
Arguments svf_to_med {_} _ {_} _ _ _ _.
Arguments svf_family {_} _ {_} _ _ _.
Arguments svf_med {_} _ {_} _ _ _ _.
Arguments svf_med_legs {_} _ {_} _ _ _ _ _ _.
Arguments svf_med_unique {_} _ {_} _ _ _ _ _ _ _.

Definition SVariety_Forget_continuous {S : UA.OpSignature}
  (E : UA.EqSignature S) : ContinuousFunctor (SVariety_Forget E) :=
  fun J G N HN M =>
    {| unique_obj := svf_med E G N HN M
     ; unique_property := svf_med_legs E G N HN M
     ; uniqueness := svf_med_unique E G N HN M |}.
