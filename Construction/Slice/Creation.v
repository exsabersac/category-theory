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
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Set Universe Polymorphism.

Generalizable All Variables.

(* * * The coslice projection creates limits / * * 余切投影创建了极限 *)

(*
 nLab: https://ncatlab.org/nlab/show/over+category#limits_and_colimits
 nLab: https://ncatlab.org/nlab/show/created+limit

 Mac Lane §V.1 Exercise 1 (book p. 112) asks for the coslice case of the
 comma lemma: the projection [c ̸co C ⟶ C] creates every limit [C] has.
 Riehl states the same as the limit half of §3.4 Proposition 8 (printed
 p. 106) and again as §4.7 Lemma 2 (printed p. 174), whose Exercise
 (printed p. 180) asks for the direct argument.

 The comma side of that is Construction/Comma/Creation.v, which needs no
 hypothesis here beyond one this library already supplies: [Id] is a right
 adjoint ([adj_id], Instance/Adjoints.v, re-exported as
 [Adjunction_Id], Adjunction/Compose.v), and
 [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v)
 turns any adjunction into the preservation witness.  So
 [@PreservesImageLimit C C Id] is inhabited for EVERY category, with no
 premise at all, and every statement in this file is unconditional in that
 sense — the only hypothesis anywhere below is a [Complete C] where
 completeness is the conclusion's subject.

 What transports and what does not.  [Comma_Coslice] (Construction/Slice.v —
 issue #438 and five in-tree sites cite the [#[export]]
 attribute heading that same declaration, one line above it)
 is an isomorphism [c ̸co C ≅ =(c) ↓ Id] in [Cat], hence an equivalence,
 hence a creator of all limits (Theory/Equivalence/Creation.v), so
 completeness and CreatesLimit both cross over.  STRICT creation is not
 carried across by that argument, and no strict statement about the
 transported projection is claimed here either way: the transported
 projection [comma_proj2 ◯ Coslice_to_Comma] has an object action that
 does not reduce to the first projection —
 [Comma_Coslice] is a [Program Instance] whose [fobj] is an obligation —
 and there is no [StrictlyCreatesLimit_compose] to compose strictness
 through.  Test/ProbeCommaCreation438.v's negatives n3 and n4 pin both
 halves: the object action is refused against [`1 x], and the coslice is
 not the comma category on the nose.  Both close the [eq_refl] route to
 [slift_eq], which is what "there is no [StrictlyCreatesLimit_compose]"
 leaves without an alternative; neither REFUTES the existence of a
 [StrictlyCreatesLimit K (comma_proj2 ◯ Coslice_to_Comma)], whose
 [slift_eq] is a Leibniz [=] that need not be [eq_refl], and no such lift
 was attempted.

 That is a fact about the TRANSPORT, not about coslice projections.  An
 earlier revision of this header drew the wrong conclusion from it — that
 a plain unconditioned projection [c ̸co C ⟶ C] would have to be built
 from scratch, all three in-tree coslice projections carrying an extra
 hypothesis on [C].  Measured, that is false for two of the three:
 [Coslice_Proj] (Construction/Slice/Adjunction.v) prints as
 [∀ {C : Category} (a : obj[C]), (a ̸co C) ⟶ C] and [Coslice_proj]
 (Instance/Cat/Pullback.v) as the same, because the [Cocartesian] and
 [ObjUIP] variables of the sections they sit in are never discharged into
 them — their bodies do not use them.  Only [Coslice_Forget]
 (Construction/Slice/Terminal.v) genuinely carries one, an [Initial].
 So the second half of this file does the direct argument for
 [Coslice_Proj] itself, and n6 records that the plain and the transported
 projection are nevertheless different functors, so neither result
 transfers to the other by conversion. 

 --------
 nLab: https://ncatlab.org/nlab/show/over+category#limits_and_colimits
 nLab: https://ncatlab.org/nlab/show/created+limit

 Mac Lane §V.1 练习1（书第112页）要求对于逗号引理的余切情况：投影 [c ̸co C ⟶ C] 能创建每个极限 [C]。Riehl 在 §3.4 命题8（印刷第106页）的极限部分以及 §4.7 引理2（印刷第174页）中也表述了相同的内容，其练习（印刷第180页）要求直接论证。其逗号部分是 Construction/Comma/Creation.v，这里不需要任何假设，除了本库已经提供的一个：[Id] 是一个右伴随 ([adj_id], Instance/Adjoints.v, 重新导出为 [Adjunction_Id], Adjunction/Compose.v)，并且 [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v) 将任何伴随转换为保持见证。因此 [@PreservesImageLimit C C Id] 对每个范畴都是可用的，根本不需要前提，并且本文件中的每个陈述在这种意义上都是无条件的——下面任何地方的唯一假设是一个 [Complete C]，其中完全性是结论的主题。什么可以传输，什么不能传输。[Comma_Coslice]（Construction/Slice.v — 问题 #438 以及五个内置站点引用了 [#[export]）属性标题在其上一行声明，是 [c ̸co C ≅ =(c) ↓ Id] 在 [Cat] 中的同构，因此是等价的，因此是所有极限的创造者（Theory/Equivalence/Creation.v），所以 completeness 和 CreatesLimit 都可以交叉。严格创建并未通过该论证被传递，并且这里也没有对传输的投影做出严格声明：传输的投影 [comma_proj2 ◯ Coslice_to_Comma] 有一个对象动作，该动作不能归约为第一个投影 — [Comma_Coslice] 是一个 [Program Instance]，其 [fobj] 是一个义务 — 并且没有 [StrictlyCreatesLimit_compose] 可以通过组成严格性。Test/ProbeCommaCreation438.v 的负极 n3 和 n4 引脚同时阻止两半部分：对象操作被拒绝针对 [`1 x]，并且切片并不是逗号类别的正好。两者都关闭了 [eq_refl] 到 [slift_eq] 的路径，这就是“没有 [StrictlyCreatesLimit_compose]”所没有替代方案的原因；两者都没有反驳 [StrictlyCreatesLimit K (comma_proj2 ◯ Coslice_to_Comma)] 的存在，其 [slift_eq] 是一个莱布尼茨 [=]，不需要是 [eq_refl]，并且没有尝试进行这样的提升。这是关于运输（TRANSPORT）的事实，而不是关于余切片投影（coslice projections）的事实。这个头文件的早期版本从中得出了错误的结论——认为一个普通无条件的投影 [c ̸co C ⟶ C] 必须从零开始构建，即所有三个树内余切片投影都带有 [C] 上的额外假设。经测量，对于三个中的两个来说，这是错误的：[Coslice_Proj]（Construction/Slice/Adjunction.v）打印为 [∀ {C : Category} (a : obj[C] ), (a ̸co C) ⟶ C] 和 [Coslice_proj] （Instance/Cat/Pullback.v）也一样，因为它们所在段落的 [Cocartesian] 和 [ObjUIP] 变量从未被传递给它们——它们的主体并未使用它们。只有 [Coslice_Forget]（Construction/Slice/Terminal.v）真正携带了一个假设，即 [Initial]。所以这个文件的下半部分直接论证了 [Coslice_Proj] 本身，而 n6 记录表明普通投影和传递投影仍然是不同的函子，因此任何结果都不能通过转换传递给另一个。
*)

(*
   * ** The identity is its own right adjoint, so the comma side is free 

   --------
   * ** 恒等函子本身是它自己的右伴随函子，因此逗号侧是自由的
*)

Definition Id_PreservesImageLimit {C : Category} : @PreservesImageLimit C C Id
  := right_adjoint_PreservesImageLimit (@Adjunction_Id C).

Section CosliceComma.

Context {C : Category}.
Context (c : C).

(*
 Strict creation for the coslice READ AS A COMMA.  Here the projection is
 [comma_proj2] itself, so the strictness of Construction/Comma/Creation.v
 survives: apex by [eq_refl], legs by [reflexivity], at every limiting
 cone downstairs. 

 --------
 对余切片的严格创建读作逗号。这里的投影是[comma_proj2]本身，所以Construction/Comma/Creation.v的严格性得以保留：顶点由[eq_refl]表示，底部的每个极限锥由[reflexivity]表示。
*)

Definition coslice_comma_StrictlyCreatesLimit
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  StrictlyCreatesLimit K comma_proj2 :=
  comma_StrictlyCreatesLimit K
    (fun N HN => Id_PreservesImageLimit J (Gdiag K)
                   (@Build_Limit J C (Gdiag K) N HN)).

Definition coslice_comma_CreatesAllLimits :
  CreatesAllLimits (@comma_proj2 _ _ _ (=(c)) (Id[C])) :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (coslice_comma_StrictlyCreatesLimit K).

(*
 Completeness of the coslice-as-comma, obtained THROUGH creation rather
 than through [Comma_Complete]. 

 --------
 通过创造而获得的余片作为逗号的完整性，而不是通过 [Comma_Complete]。
*)

Definition coslice_comma_Complete (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  creates_limits_Complete comma_proj2 HC coslice_comma_CreatesAllLimits.

(*
 The same completeness by the route the issue names, kept as a
 cross-check: [Comma_Complete_right_adjoint] at [Adjunction_Id] does
 type-check, exactly as the issue's "Also covered by" section claims.  It
 is a different term from the one above — that one goes through creation,
 this one through Construction/Comma/Limit.v's [Comma_Complete]. 

 --------
 通过问题名称的路线保持相同的完整性，作为交叉检查：[Comma_Complete_right_adjoint] 在 [Adjunction_Id] 处进行了类型检查，完全如问题的“也涵盖于”部分所声明的。它与上面的那个术语不同——那个通过创建，这个通过 Construction/Comma/Limit.v 的 [Comma_Complete]。
*)

Definition coslice_comma_Complete_via_adjoint (HC : @Complete C) :
  @Complete (=(c) ↓ Id) :=
  Comma_Complete_right_adjoint (@Adjunction_Id C) c HC.

(* * ** Transporting along [Comma_Coslice] / * ** 沿 [Comma_Coslice] 运输 *)

Definition Coslice_to_Comma : (c ̸co C) ⟶ (=(c) ↓ Id) :=
  to (Comma_Coslice C c).

Definition Coslice_Comma_Equivalence :
  @EquivalenceOfCategories (c ̸co C) (=(c) ↓ Id) Coslice_to_Comma :=
  Cat_Iso_to_Equivalence (Comma_Coslice C c).

Definition Coslice_to_Comma_CreatesAllLimits :
  CreatesAllLimits Coslice_to_Comma :=
  equivalence_CreatesAllLimits Coslice_Comma_Equivalence.

Definition Coslice_Complete (HC : @Complete C) : @Complete (c ̸co C) :=
  creates_limits_Complete Coslice_to_Comma (coslice_comma_Complete HC)
    Coslice_to_Comma_CreatesAllLimits.

(* The coslice projection, as the transported comma projection. / 余切投影，作为被传送的逗号投影。 *)

Definition coslice_comma_proj : (c ̸co C) ⟶ C := comma_proj2 ◯ Coslice_to_Comma.

Definition coslice_comma_proj_CreatesLimit {J : Category} (K : J ⟶ (c ̸co C)) :
  CreatesLimit K coslice_comma_proj :=
  CreatesLimit_compose (Coslice_to_Comma_CreatesAllLimits J K)
    (coslice_comma_CreatesAllLimits J (Coslice_to_Comma ◯ K)).

Definition coslice_comma_proj_CreatesAllLimits :
  CreatesAllLimits coslice_comma_proj :=
  fun J K => coslice_comma_proj_CreatesLimit K.

End CosliceComma.

(*
   * ** Strict creation for the PLAIN coslice projection 

   --------
   * ** 针对 PLAIN coslice 投影的严格创建
*)

(*
 Everything above goes through [Comma_Coslice], and strictness does not
 survive that transport.  It does not have to: [Coslice_Proj]
 (Construction/Slice/Adjunction.v) is an unconditioned functor
 [c ̸co C ⟶ C] — the [Cocartesian] variable of the section it sits in is
 not discharged into it, because its body does not use it — and both its
 data fields reduce, [fobj] to [`1 x] and [fmap] to [`1 f] by [eq_refl].
 So the [StrictLift] apex clause is definitional for it.  Riehl's §4.7
 exercise asks for the direct argument for the COMMA projection "along the
 lines of the argument for the analogous statement about slice/coslice
 projections": the exercise proper is
 Construction/Comma/Creation.v's [comma_StrictlyCreatesLimit], and what is
 built below is the slice/coslice statement the exercise names as its
 model, which the tree did not have either.

 It is carried out below, and it needs NO hypothesis whatever: the step
 that consumes preservation in the comma case is the passage from the
 limit downstairs to a limit of its [U]-image, and with [U] the identity
 that passage is the given limiting cone itself.  The structure maps
 [`2 (K j) : c ~> `1 (K j)] of the diagram's objects form a cone with apex
 [c] over the projected diagram, whose mediator into the given limiting
 cone is the lifted object's own structure map; the lifted legs are the
 given legs, so the projection returns them on the nose.

 [Instance/Cat/Pullback.v]'s [Coslice_proj] is a second unconditioned
 projection with the same two data fields, and it reduces the same way;
 it is not used here, since importing that file would cost twelve modules
 of closure against this file's five for Construction/Slice/Adjunction.v,
 and the two functors are distinct records. 

 --------
 以上所有内容都通过 [Comma_Coslice]，而严格性无法在该传输中存活。它没有必要这样：[Coslice_Proj]（Construction/Slice/Adjunction.v）是一个无条件函子 [c ̸co C ⟶ C]——它所处部分的 [Cocartesian] 变量未被释放到其中，因为其主体未使用它——并且它的两个数据字段通过 [eq_refl] 分别简化为 [`1 x] 和 [`1 f]。因此 [StrictLift] 顶点子句是其定义性的。Riehl §4.7 的练习要求直接给出 COMMA 投影的参数，“沿着对 slice/coslice 投影的类似命题的论证路线”：实际练习是 Construction/Comma/Creation.v 的 [comma_StrictlyCreatesLimit]，下面构建的内容是该练习命名为其模型的 slice/coslice 命题，原来的树中也没有。它在下面进行，并且根本不需要任何假设：在逗号情况中消耗保结构的步骤是从下方的极限到其 [U] 像的极限的过程，对于 [U] 身份而言，这个过程就是给定的极限锥本身。图对象的结构映射 [`2 (K j) : c ~> `1 (K j)] 形成一个以 [c] 为顶点的投影图锥，其到给定极限锥的中介是提升对象自身的结构映射；提升的边是给定的边，因此投影会精确返回它们。[Instance/Cat/Pullback.v] 的 [Coslice_proj] 是第二个无条件投影，具有相同的两个数据字段，并且它的缩减方式相同；这里没有使用它，因为导入该文件将对 Construction/Slice/Adjunction.v 产生十二个闭包模块的开销，而该文件只有五个，而且这两个函子是不同的记录。
*)

Section CosliceCreate.

Context {C : Category}.
Context (c : C).
Context {J : Category}.
Context (K : J ⟶ (c ̸co C)).

Lemma coslice_structure_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Coslice_Proj c ◯ K] f ∘ `2 (K x) ≈ `2 (K y).
Proof.
  symmetry.
  exact (`2 (fmap[K] f)).
Qed.

Definition coslice_structure_cone : Cone (Coslice_Proj c ◯ K) :=
  @Build_Cone J C (Coslice_Proj c ◯ K) c
    (@Build_ACone J C c (Coslice_Proj c ◯ K)
       (fun j => `2 (K j)) (@coslice_structure_coherence)).

(*
 Reflection needs no chosen cone downstairs, so it sits outside the
 section that fixes one. 

 --------
 反射不需要楼下选择的圆锥，所以它位于固定某物的部分之外。
*)

Definition coslice_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone (Coslice_Proj c) M)) : IsLimitCone M.
Proof.
  intro N.
  destruct (HM (FCone (Coslice_Proj c) N)) as [w Hw Hwu].
  assert (Hsq : `2 (vertex_obj[M]) ≈ w ∘ `2 (vertex_obj[N])).
  { transitivity (unique_obj (HM coslice_structure_cone)).
    - symmetry.
      apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      symmetry.
      exact (`2 (cone_leg M j)).
    - apply (uniqueness (HM coslice_structure_cone)).
      intro j.
      rewrite comp_assoc.
      rewrite (Hw j).
      symmetry.
      exact (`2 (cone_leg N j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Section CosliceLift.

Context (N : Cone (Coslice_Proj c ◯ K)).
Context (HN : IsLimitCone N).

Definition coslice_med : c ~{C}~> vertex_obj[N] :=
  unique_obj (HN coslice_structure_cone).

Lemma coslice_med_commutes (j : J) :
  cone_leg N j ∘ coslice_med ≈ `2 (K j).
Proof.
  exact (unique_property (HN coslice_structure_cone) j).
Qed.

Definition coslice_lift_obj : c ̸co C := (vertex_obj[N]; coslice_med).

Definition coslice_lift_leg (j : J) : coslice_lift_obj ~{c ̸co C}~> K j.
Proof.
  unshelve refine (cone_leg N j; _).
  symmetry.
  exact (coslice_med_commutes j).
Defined.

Lemma coslice_lift_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ coslice_lift_leg x ≈ coslice_lift_leg y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f).
Qed.

Definition coslice_lift_cone : Cone K :=
  @Build_Cone J (c ̸co C) K coslice_lift_obj
    (@Build_ACone J (c ̸co C) coslice_lift_obj K
       coslice_lift_leg (@coslice_lift_coherence)).

Definition coslice_lift_ump (M : Cone K) :
  ∃! u : vertex_obj[M] ~{c ̸co C}~> coslice_lift_obj,
    ∀ j : J, coslice_lift_leg j ∘ u ≈ cone_leg M j.
Proof.
  destruct (HN (FCone (Coslice_Proj c) M)) as [w Hw Hwu].
  assert (Hsq : coslice_med ≈ w ∘ `2 (vertex_obj[M])).
  { unfold coslice_med.
    apply (uniqueness (HN coslice_structure_cone)).
    intro j.
    rewrite comp_assoc.
    rewrite (Hw j).
    symmetry.
    exact (`2 (cone_leg M j)). }
  unshelve refine {| unique_obj := (w; Hsq) |}.
  - intro j.
    exact (Hw j).
  - intros v Hv.
    apply Hwu.
    intro j.
    exact (Hv j).
Defined.

Definition coslice_limit_at : Limit K :=
  @Build_Limit J (c ̸co C) K coslice_lift_cone coslice_lift_ump.

(*
 Mac Lane's [F a = x] and [F σ = τ], at the GIVEN limiting cone. 

 --------
 在给定的极限圆锥处，Mac Lane 的 [F a = x] 和 [F σ = τ]。
*)

Definition coslice_strict_lift : StrictLift K (Coslice_Proj c) N :=
  @Build_StrictLift J (c ̸co C) C K (Coslice_Proj c) N
    coslice_lift_cone eq_refl (fun x => reflexivity _).

Definition coslice_lift_apex :
  fobj[Coslice_Proj c] (vertex_obj[coslice_lift_cone]) = vertex_obj[N]
  := eq_refl.

Definition coslice_lift_legs (j : J) :
  fmap[Coslice_Proj c] (cone_leg coslice_lift_cone j) = cone_leg N j
  := eq_refl.

End CosliceLift.

Definition Coslice_Proj_StrictlyCreatesLimit :
  StrictlyCreatesLimit K (Coslice_Proj c).
Proof.
  unshelve refine {| screates := coslice_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone (coslice_limit_at N HN)).
  - exact coslice_reflect_at.
Defined.

Definition Coslice_Proj_CreatesLimit : CreatesLimit K (Coslice_Proj c) :=
  StrictlyCreatesLimit_CreatesLimit Coslice_Proj_StrictlyCreatesLimit.

End CosliceCreate.

Definition Coslice_Proj_CreatesAllLimits {C : Category} (c : C) :
  CreatesAllLimits (Coslice_Proj c) :=
  fun J K => Coslice_Proj_CreatesLimit c K.

(*
 Completeness of the coslice without any transport at all.  [Coslice_Complete]
 above reaches the same conclusion through [Comma_Coslice]; the two are
 kept side by side because the transported one is what an equivalence
 gives in general, and this one is what the direct argument gives. 

 --------
 余切片的完整性完全没有任何传输。[Coslice_Complete] 上述通过 [Comma_Coslice] 达到相同的结论；两者被并列放置，因为传输的那个是一般等价所给出的，而这个则是直接论证所给出的。
*)

Definition Coslice_Complete_direct {C : Category} (c : C) (HC : @Complete C) :
  @Complete (c ̸co C) :=
  creates_limits_Complete (Coslice_Proj c) HC (Coslice_Proj_CreatesAllLimits c).
