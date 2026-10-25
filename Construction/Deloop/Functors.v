Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Opposite.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Functors out of a delooping: homomorphisms, actions, representations

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.3
   (printed p. 15), Exercise 3(b,c) [maclane:I.3:ex3]: a functor between
   two groups regarded as one-object categories is a group homomorphism;
   a functor from a group to Set is a permutation representation, and to
   [Matr_K] a matrix representation.
   Awodey, "Category Theory", §4.3 (printed p. 86)
   [awodey:4.3:remark-functor-group-hom, awodey:4.3:def-representation]:
   the same identification, and representations as functors out of the
   delooping; §7.1 (printed p. 154)
   [awodey:7.1:construction-poset-to-group]: a functor from a poset to a
   group is exactly a unit-and-composition-respecting family g_{p,q} —
   a cocycle.
   Riehl, "Category Theory in Context", §1.3: Example 1.3.9
   [riehl:1.3:example9] (actions as functors, with the left/right
   convention), Corollary 1.3.10 [riehl:1.3:cor10] (each group element
   acts by an automorphism, inverses mapping to inverses), Exercise
   1.3.i [riehl:1.3:exi] (functors between groups).

   Everything is developed over Construction/Deloop.v's [MonObject] and
   [GrpObject] and its delooping [Deloop M].  The homomorphism record
   is Structure/Groupoid.v's [MonHom] (with [MonIso] for isomorphisms),
   and group statements are the monoid statements read at a
   [GrpObject]: the extra content — homomorphisms preserve inverses —
   is that file's THEOREM [MonHom_grp_inv], by uniqueness of inverses,
   the same derivation pattern as Instance/Ab.v's and
   Theory/Algebra/Rig.v's negation-preservations.  Part (b) itself is
   likewise already in tree: Construction/Deloop/Transform.v's
   [Deloop_map]/[Deloop_unmap], whose homomorphism-side round trip
   [Deloop_unmap_map] holds as an EQUALITY OF RECORDS — nothing here
   re-proves either.

   THE SPINE is one general correspondence: functors [Deloop M ⟶ C]
   are the same as a choice of object c : C together with a monoid
   homomorphism [M → hom_monoid C c] into Deloop.v's endomorphism
   monoid ([functor_of_hom_monoid] / [hom_monoid_of_functor], with
   round trips).  Every part of the exercise specializes it:

   - C := Deloop N (part b): the object choice is forced, and
   Transform.v's [Deloop_map] IS the spine at that single object
   ([Deloop_map_spine]; the types agree definitionally by
   Deloop.v's [hom_monoid_Deloop]); what Transform.v states only
   pointwise — its functor-side round trip is [eq_refl] on [fmap]
   and propositional on [fobj] — is completed here to a full
   [Functor_Setoid] natural isomorphism ([Deloop_functor_round]);
   - C := Sets (part c, permutation representations): unfolded into
   the friendlier [MSetoidAction] record — a monoid acting on a
   setoid — with the correspondence both ways
   ([action_of_functor] / [functor_of_action]); at a [GrpObject]
   this is Riehl's Example 1.3.9, the LEFT-action convention (a
   left action is a functor out of B G);
   - C := Matr R (part c, matrix representations): [MatrixRep], a
   dimension n together with a homomorphism into the multiplicative
   monoid of n × n matrices — the dimension IS the chosen object
   ([matrix_rep_of_functor] / [functor_of_matrix_rep]).

   RIGHT ACTIONS (Riehl's convention note): a right action is a functor
   out of [(Deloop G)^op], and Construction/Deloop/Opposite.v's
   [Deloop_op] identifies that source with [Deloop (MonObject_op G)],
   so the two translations [right_action_of_op_functor] and
   [op_functor_of_right_action] carry right actions to and from LEFT
   actions of the opposite monoid — the classical statement.  Their
   mutual inversion is NOT stated here: it would combine
   [action_functor_round] with [Deloop_op]'s isomorphism laws and the
   functoriality of [◯] over [Functor_Setoid].

   THE AUTOMORPHISM COROLLARY (Riehl 1.3.10): at a [GrpObject] every
   [fmap] lands in isomorphisms.  Per the issue this is delivered as a
   NAMED INSTANTIATION of Theory/Functor.v's [fobj_iso] at
   [Deloop_group_iso] ([action_automorphism]), with the inverse of the
   action of g being the action of the inverse of g, recorded
   definitionally ([action_automorphism_from]).  As with Deloop.v's
   [Deloop_group_iso], the TYPE [F ttt ≅ F ttt] is inhabited by
   [iso_id] alone; the corollary's content is WHICH isomorphism, i.e.
   the two definitional readings [action_automorphism_to]/[_from].

   THE COCYCLE CHARACTERIZATION (Awodey §7.1): functors from a proset
   into a delooping are exactly proof-irrelevant families g_{p,q}
   satisfying the unit and composition conditions ([Cocycle],
   [cocycle_of_functor] / [functor_of_cocycle], with round trips on
   BOTH sides — [cocycle_round] pointwise, [cocycle_functor_round] up
   to [Functor_Setoid] isomorphism).  The worked witness is
   Awodey's, transposed from ℝ to ℤ to keep the instance layer
   axiom-free (the same substitution Theory/Algebra/Rig.v makes for its
   ring witness): P = (ℤ, ≤), G = (ℤ, +), g_{x,y} = y − x
   ([translation_cocycle]). 

   --------
   * * 从去圈化出的函子：同态、作用、表示麦克莱恩，《为工作的数学家准备的范畴论》，第2版，第I.3节（印刷第15页），练习3(b,c) [maclane:I.3:ex3]：两个被视为单对象范畴的群之间的函子是群同态；一个从群到集合的函子是置换表示，而到 [Matr_K] 是矩阵表示。Awodey，《范畴论》，第4.3节（印刷第86页）[awodey:4.3:remark-functor-group-hom, awodey:4.3:def-representation]：相同的识别，以及作为从去环绕函子的表示；第7.1节（印刷第154页）[awodey:7.1:construction-poset-to-group]：从偏序集合到群的函子正好是遵循单位和组合的族 g_{p,q}——一个上同调。Riehl，《语境中的范畴论》，§1.3：例 1.3.9 [riehl:1.3:example9]（作为函子作用，遵循左/右约定），推论 1.3.10 [riehl:1.3:cor10]（每个群元素通过自同构作用，逆元素映射为逆元素），练习 1.3.i [riehl:1.3:exi]（群之间的函子）。一切都是在 Construction/Deloop.v 的 [MonObject] 和 [GrpObject] 及其去环 [Deloop M] 上开发的。同态记录是 Structure/Groupoid.v 的 [MonHom]（对于同构为 [MonIso]），而群论陈述是单子陈述在 [GrpObject] 上的读取：额外内容——同态保持逆元——是该文件的 THEOREM [MonHom_grp_inv]，由逆元的唯一性得出，与 Instance/Ab.v 和 Theory/Algebra/Rig.v 的负保持相同的推导模式。部分 (b) 本身同样已经在树中：Construction/Deloop/Transform.v 的 [Deloop_map] / [Deloop_unmap]，其同态侧的循环往复 [Deloop_unmap_map] 作为记录的等式成立——这里没有重新证明任何内容。脊柱是一个一般的对应关系：函子 [Deloop M ⟶ C] 与选择一个对象 c : C 以及一个单子同态 [M → hom_monoid C c] 到 Deloop.v 的自同态单子 ([functor_of_hom_monoid] / [hom_monoid_of_functor]，带有往返) 是相同的。练习的每一部分都对其进行了专门化：- C := Deloop N（部分 b）：对象的选择是强制性的，而 Transform.v 的 [Deloop_map] 是该单一对象上的 spine（[Deloop_map_spine]；其类型根据 Deloop.v 的 [hom_monoid_Deloop] 在定义上是一致的）；Transform.v 仅以点态方式声明 —— 其函子方向的往返是 [eq_refl] 于 [fmap] 上，并且在 [fobj] 上是命题性的 —— 在这里被完成为一个完整的 [Functor_Setoid] 自然同构（[Deloop_functor_round]）；
   - C := Sets（部分 c，置换表示）：展开为更友好的 [MSetoidAction] 记录 —— 一个半群作用于一个集合型对象 —— 并且存在双向对应（[action_of_functor] / [functor_of_action]）；在 [GrpObject]，这对应于 Riehl 的示例 1.3.9，采用左作用约定（左作用是从 B G 出发的函子）；
   - C := Matr R（部分 c，矩阵表示）s)：[MatrixRep]，维数 n 以及一个映射到 n × n 矩阵乘法幺半群的同态——维数是所选择的对象（[matrix_rep_of_functor] / [functor_of_matrix_rep]）。正确的作用（Riehl的惯例注释）：一个正确的作用是从 [(Deloop G)^op] 出发的函子，而 Construction/Deloop/Opposite.v 的 [Deloop_op] 将该源与 [Deloop (MonObject_op G)] 识别，因此两个翻译 [right_action_of_op_functor] 和 [op_functor_of_right_action] 将正确作用与对偶幺半群的左作用相互传递——这是经典陈述。这里没有说明它们的相互逆：它将结合 [action_functor_round] 与 [Deloop_op] 的同构律以及 [◯] 在 [Functor_Setoid] 上的函子性。自同构推论（Riehl 1.3.10）：在每个 [GrpObject] 上，[fmap] 的每个元素都是同构。根据问题，这作为 Theory/Functor.v 的 [fobj_iso] 在 [Deloop_group_iso]（[action_automorphism]）处的命名实例给出，g 的作用的逆是 g 的逆作用，以定义方式记录（[action_automorphism_from]）。与 Deloop.v 的 [Deloop_group_iso] 类似，类型 [F ttt ≅ F ttt] 仅由 [iso_id] 构成；该推论的内容是哪个同构，即两个定义性读法 [action_automorphism_to] / [_from]。余圈表征 (Awodey §7.1)：从一个前序集合到一个 delooping 的函子，正好是满足单位和组合条件的证明无关族 g_{p,q}（[Cocycle], [cocycle_of_functor] / [functor_of_cocycle]，两边都有往返——[cocycle_round] 点态地，[cocycle_functor_round] 至 [Functor_Setoid] 同构）。具体的实例见 Awodey，将 ℝ 转置到 ℤ 以保持实例层无公理性（与其环实例的替代 Theory/Algebra/Rig.v 相同）：P = (ℤ, ≤), G = (ℤ, +), g_{x,y} = y − x ([translation_cocycle]) 。
*)

(*
   * ** Monoid homomorphisms: Structure/Groupoid.v's [MonHom]

   The homomorphism record and its inverse-preservation theorem are
   imported, not redefined: Structure/Groupoid.v's [MonHom_grp_inv]
   already proves (via [mon_inverse_unique]) that a monoid
   homomorphism between groups preserves inverses, which is why
   neither that file nor this one defines a separate class of group
   homomorphisms. 

   --------
   * ** 幺半群同态：Structure/Groupoid.v 的 [MonHom] 

   同态记录及其逆保持定理是被导入的，而非重新定义：Structure/Groupoid.v 的 [MonHom_grp_inv] 
   已经通过 [mon_inverse_unique] 证明了群之间的幺半群同态保持逆元，这也是为什么
   该文件和这个文件都没有定义单独的群同态类的原因。
*)

(*
   * ** The spine: functors out of a delooping pick an endomorphism
   monoid 

   --------
   * ** 脊柱：来自去环的函子选择一个自同态幺半群
*)

Section Spine.

Context {M : MonObject}.
Context {C : Category}.

Program Definition functor_of_hom_monoid (c : C)
  (h : MonHom M (hom_monoid C c)) : Deloop M ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ (g : carrier M) => mon_map h g
|}.
Next Obligation.
  intros c h x y f g Hfg; exact (mon_map_respects h _ _ Hfg).
Qed.
Next Obligation. intros c h x; exact (mon_map_unit h). Qed.
Next Obligation. intros c h x y z f g; exact (mon_map_op h f g). Qed.

(*
 The reverse leg needs no obligations: every homomorphism law is a
 functor law by projection, exactly as in Transform.v's
 [Deloop_unmap] (of which this is the general-codomain form).
 ([Build_MonHom] is applied to explicit arguments for the same reason
 Transform.v's [Deloop_map] applies [Build_Functor] so: the fields
 alone do not determine the record's parameters.) 

 --------
 反向引理不需要任何约束：每个同态律通过投影都是函子律，正如 Transform.v 中的 [Deloop_unmap]（这是通用余域形式）一样。
 （出于同样的原因，[Build_MonHom] 被应用于显式参数，正如 Transform.v 中的 [Deloop_map] 这样应用 [Build_Functor] 一样：仅凭字段无法确定记录的参数。）
*)
Definition hom_monoid_of_functor (F : Deloop M ⟶ C) :
  MonHom M (hom_monoid C (F ttt)) :=
  @Build_MonHom M (hom_monoid C (F ttt))
    (fun g : carrier M => @fmap _ _ F ttt ttt g)
    (@fmap_respects _ _ F ttt ttt)
    (@fmap_id _ _ F ttt)
    (fun a b => @fmap_comp _ _ F ttt ttt ttt a b).

(*
 Round trip on the homomorphism side: the same map, pointwise. 

 --------
 同态一边的往返：相同的映射，逐点地。
*)
Lemma hom_monoid_round (c : C) (h : MonHom M (hom_monoid C c))
  (g : carrier M) :
  mon_map (hom_monoid_of_functor (functor_of_hom_monoid c h)) g
    ≈ mon_map h g.
Proof. reflexivity. Qed.

(*
 Round trip on the functor side: the same functor up to natural
 isomorphism, with identity components. 

 --------
 函子端的往返：相同的函子，直到自然同构，带有单位分量。
*)
Lemma functor_round (F : Deloop M ⟶ C) :
  functor_of_hom_monoid (F ttt) (hom_monoid_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End Spine.

(*
   * ** Part (b): functors between deloopings are homomorphisms 

   --------
   * ** 部分 (b)：去环化之间的函子是同态
*)

(*
 Construction/Deloop/Transform.v already proves the dictionary:
 [Deloop_map] / [Deloop_unmap], with the homomorphism-side round trip
 an EQUALITY OF RECORDS ([Deloop_unmap_map], by [eq_refl]) — stronger
 than the pointwise form the spine yields, so nothing is re-proved
 here.  What is added is the two statements Transform.v does not
 make: [Deloop_map] IS the spine at the delooping's single object
 (the types agreeing definitionally by Deloop.v's
 [hom_monoid_Deloop]), and the functor-side round trip in full
 [Functor_Setoid] strength — Transform.v states it only as [eq_refl]
 on [fmap] and a propositional case split on [fobj]
 ([Deloop_map_unmap_fmap]/[_fobj]). 

 --------
 Construction/Deloop/Transform.v 已经证明了字典：
 [Deloop_map] / [Deloop_unmap]，并通过同态端的往返
 证明了记录的相等性 ([Deloop_unmap_map]，由 [eq_refl]) — 比脊柱产生的逐点形式更强，因此这里没有重新证明任何内容。
 新增的是 Transform.v 未作出的两个陈述：[Deloop_map] 是去环绕单对象处的脊柱（类型在 Deloop.v 的 [hom_monoid_Deloop] 定义上是一致的），以及函子端往返的完整 [Functor_Setoid] 强度 — Transform.v 仅在 [fmap] 上以 [eq_refl] 形式陈述，并对 [fobj] 进行了命题划分 ([Deloop_map_unmap_fmap] / [_fobj])。
*)

Section PartB.

Context {M N : MonObject}.

(*
 [Deloop_map] is the spine specialized at the single object; the
 homomorphism argument is accepted UNCHANGED, [MonHom M N] and
 [MonHom M (hom_monoid (Deloop N) ttt)] being definitionally the
 same type. 

 --------
 [Deloop_map] 是专注于单一对象的脊柱；同态论证被保持不变地接受，[MonHom M N] 和 [MonHom M (hom_monoid (Deloop N) ttt)] 在定义上是相同的类型。
*)
Lemma Deloop_map_spine (h : MonHom M N) :
  Deloop_map h ≈ functor_of_hom_monoid (C := Deloop N) ttt h.
Proof.
  exists (fun x => iso_id).
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

(*
 The functor-side round trip, at [Functor_Setoid] strength. 

 --------
 函子端往返，在 [Functor_Setoid] 强度下。
*)
Lemma Deloop_functor_round (F : Deloop M ⟶ Deloop N) :
  Deloop_map (Deloop_unmap F) ≈ F.
Proof.
  unshelve eexists.
  { intro x.
    exact (@Build_Isomorphism (Deloop N) _ _
             (mon_unit : carrier N) (mon_unit : carrier N)
             (mon_op_unit_l mon_unit) (mon_op_unit_l mon_unit)). }
  intros [] [] g; simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End PartB.

(*
   * ** Part (c): permutation representations — actions on setoids 

   --------
   * ** 第（c）部分：排列表示——在集合类上的作用
*)

(*
 A monoid acting on a setoid; at a [GrpObject] this is a permutation
 representation / G-set (Riehl 1.3.9, left convention: the action law
 is act (g · h) = act g ∘ act h, matching Deloop's composition). 

 --------
 一个幺半群作用于一个集合上；在一个 [GrpObject] 上，这是一种置换表示 / G-集（Riehl 1.3.9，左侧约定：作用律为 act (g · h) = act g ∘ act h，与 Deloop 的组合相匹配）。
*)
Record MSetoidAction (M : MonObject) := {
  act_setoid :> SetoidObject;
  act : carrier M → carrier act_setoid → carrier act_setoid;
  act_respects : Proper (equiv ==> equiv ==> equiv) act;
  act_unit : ∀ x, act mon_unit x ≈ x;
  act_op : ∀ g h x, act (mon_op g h) x ≈ act g (act h x)
}.

Arguments act_setoid {M} _.
Arguments act {M} _ _ _.
Arguments act_respects {M} _.
Arguments act_unit {M} _ _.
Arguments act_op {M} _ _ _ _.

#[export] Existing Instance act_respects.

Section PartC.

Context {M : MonObject}.

Program Definition action_of_functor (F : Deloop M ⟶ Sets) :
  MSetoidAction M := {|
  act_setoid := F ttt;
  act := fun g x => @fmap _ _ F ttt ttt g x;
  act_unit := fun x => @fmap_id _ _ F ttt x;
  act_op := fun g h x => @fmap_comp _ _ F ttt ttt ttt g h x
|}.
Next Obligation.
  intros F g g' Hg x x' Hx.
  rewrite (@fmap_respects _ _ F ttt ttt g g' Hg x).
  exact (proper_morphism (@fmap _ _ F ttt ttt g') _ _ Hx).
Qed.

Program Definition functor_of_action (A : MSetoidAction M) :
  Deloop M ⟶ Sets := {|
  fobj := fun _ => act_setoid A;
  fmap := fun _ _ (g : carrier M) =>
    {| morphism := act A g
     ; proper_morphism := act_respects A g g (Equivalence_Reflexive g) |}
|}.
Next Obligation.
  intros A0 x y f g Hfg p; simpl.
  exact (act_respects A0 f g Hfg p p (Equivalence_Reflexive p)).
Qed.
Next Obligation. intros A0 x p; apply act_unit. Qed.
Next Obligation. intros A0 x y z f g p; apply act_op. Qed.

Lemma action_round (A : MSetoidAction M) (g : carrier M)
  (x : carrier (act_setoid A)) :
  act (action_of_functor (functor_of_action A)) g x ≈ act A g x.
Proof. reflexivity. Qed.

Lemma action_functor_round (F : Deloop M ⟶ Sets) :
  functor_of_action (action_of_functor F) ≈ F.
Proof.
  exists (fun x => match x as x0 return (F ttt ≅ F x0) with
                   | ttt => iso_id
                   end).
  intros [] [] g x; simpl.
  reflexivity.
Qed.

End PartC.

(* * ** Part (c): matrix representations / * ** 第(c)部分：矩阵表示 *)

(*
 A matrix representation: a dimension together with a homomorphism
 into the multiplicative monoid of n × n matrices — the endomorphism
 monoid of n in Matr R.  The dimension IS the chosen object of the
 spine correspondence. 

 --------
 矩阵表示：一个维度以及一个同态映射到 n × n 矩阵的乘法幺半群——在 Matr R 中 n 的自同态幺半群。维度即是脊对应中的选定对象。
*)
Definition MatrixRep (M : MonObject) (R : RigObject) : Type :=
  { n : nat & MonHom M (hom_monoid (Matr R) n) }.

Definition functor_of_matrix_rep {M : MonObject} {R : RigObject}
  (ρ : MatrixRep M R) : Deloop M ⟶ Matr R :=
  functor_of_hom_monoid (C := Matr R) (`1 ρ) (`2 ρ).

(*
 The sigma's family is supplied explicitly rather than left to
 unification: inferring it requires unfolding [obj] at [Matr R],
 which Coq 8.19/8.20's unifier declines in evar problems (the same
 version split as Monotone.v's [nondecreasing_of_endo]). 

 --------
 sigma 的族是显式提供的，而不是留给统一：推断它需要在 [Matr R] 处展开 [obj]，Coq 8.19/8.20 的统一器在 evar 问题中拒绝这样做（相同版本分裂如 Monotone.v 的 [nondecreasing_of_endo]）。
*)
Definition matrix_rep_of_functor {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) : MatrixRep M R :=
  existT (fun n : nat => MonHom M (hom_monoid (Matr R) n))
    (F ttt : nat) (hom_monoid_of_functor (C := Matr R) F).

Lemma matrix_rep_dimension {M : MonObject} {R : RigObject}
  (F : Deloop M ⟶ Matr R) :
  `1 (matrix_rep_of_functor F) = F ttt.
Proof. reflexivity. Qed.

(*
   * ** Right actions, along the opposite-monoid identification 

   --------
   * ** 正确的行为，沿着相反幺半群的识别
*)

Section RightActions.

Context {G : MonObject}.

(*
 Riehl's convention: a right action is a functor out of the OPPOSITE
 of the delooping; [Deloop_op] carries that source to the delooping of
 the opposite monoid, so right actions of G are left actions of
 [MonObject_op G]. 

 --------
 Riehl 的公理：右作用是从去循环的对偶出来的函子；[Deloop_op] 将该源映射到对偶幺半群的去循环，因此 G 的右作用是 [MonObject_op G] 的左作用。
*)
Definition right_action_of_op_functor
  (F : (Deloop G)^op ⟶ Sets) : MSetoidAction (MonObject_op G) :=
  action_of_functor (F ◯ from (Deloop_op G)).

Definition op_functor_of_right_action
  (A : MSetoidAction (MonObject_op G)) : (Deloop G)^op ⟶ Sets :=
  functor_of_action A ◯ to (Deloop_op G).

End RightActions.

(*
   * ** Riehl 1.3.10: each group element acts by an automorphism 

   --------
   * ** Riehl 1.3.10：每个群元素通过自同构作用
*)

Section Automorphism.

Context {G : GrpObject}.
Context {C : Category}.

(*
 The named instantiation of [fobj_iso] at the delooped group's
 isomorphisms: the action of g, as an isomorphism of the underlying
 object. 

 --------
 在去环的群同构处 [fobj_iso] 的命名实例化：g 的作用，作为底层对象的同构。
*)
Definition action_automorphism (F : Deloop G ⟶ C) (g : carrier G) :
  F ttt ≅ F ttt :=
  fobj_iso F ttt ttt (Deloop_group_iso G ttt ttt g).

(* Its forward leg is the action of g... / 它的前腿是g的动作... *)
Lemma action_automorphism_to (F : Deloop G ⟶ C) (g : carrier G) :
  to (action_automorphism F g) ≈ fmap[F] g.
Proof. reflexivity. Qed.

(* ...and its inverse is the action of the inverse of g. / ...而它的逆是 g 的逆的作用。 *)
Lemma action_automorphism_from (F : Deloop G ⟶ C) (g : carrier G) :
  from (action_automorphism F g) ≈ fmap[F] (grp_inv g).
Proof. reflexivity. Qed.

End Automorphism.

(* * ** Awodey §7.1: the cocycle characterization / * ** Awodey §7.1：群环特征 *)

Section Cocycle.

Context {A : Type} {R : relation A} (P : RelationClasses.PreOrder R).
#[local] Existing Instance P.
Context (M : MonObject).

(*
 A cocycle: an element g_{p,q} for each related pair, independent of
 the witnessing proof (Awodey indexes by the PAIR, and a functor's
 [fmap_respects] forces exactly this over the proset's all-True
 hom-equivalence), with the unit and composition conditions. 

 --------
 一个群圈：对于每个相关对都有一个元素 g_{p,q}，独立于证明的具体过程（Awodey 按对索引，而函子 [fmap_respects] 恰好在前序集合的全真同构等价上强制了这一点），并满足单位和组合条件。
*)
Record Cocycle := {
  cocycle : ∀ p q : A, R p q → carrier M;
  cocycle_irrel : ∀ p q (h h' : R p q), cocycle p q h ≈ cocycle p q h';
  cocycle_refl : ∀ p,
    cocycle p p (@RelationClasses.PreOrder_Reflexive A R P p) ≈ mon_unit;
  cocycle_trans : ∀ p q r (h : R p q) (k : R q r),
    mon_op (cocycle q r k) (cocycle p q h)
      ≈ cocycle p r
          (@RelationClasses.PreOrder_Transitive A R P p q r h k)
}.

Program Definition functor_of_cocycle (γ : Cocycle) :
  Proset P ⟶ Deloop M := {|
  fobj := fun _ => ttt;
  fmap := fun p q (h : R p q) => cocycle γ p q h
|}.
Next Obligation.
  intros γ p q f g T; exact (cocycle_irrel γ p q f g).
Qed.
Next Obligation. intros γ p; exact (cocycle_refl γ p). Qed.
Next Obligation.
  intros γ x y z g f; symmetry; exact (cocycle_trans γ x y z f g).
Qed.

Program Definition cocycle_of_functor (F : Proset P ⟶ Deloop M) :
  Cocycle := {|
  cocycle := fun p q (h : R p q) => @fmap _ _ F p q h
|}.
Next Obligation.
  intros F p q h h'; exact (@fmap_respects _ _ F p q h h' I).
Qed.
Next Obligation. intros F p; exact (@fmap_id _ _ F p). Qed.
Next Obligation.
  intros F p q r h k; symmetry; exact (@fmap_comp _ _ F p q r k h).
Qed.

Lemma cocycle_round (γ : Cocycle) (p q : A) (h : R p q) :
  cocycle (cocycle_of_functor (functor_of_cocycle γ)) p q h
    ≈ cocycle γ p q h.
Proof. reflexivity. Qed.

(*
 The functor side, at [Functor_Setoid] strength: the components sit
 over the target's single object, so each is found by case analysis
 on [fobj F x] (a [poly_unit] has no definitional eta, so the match
 is genuine — compare Transform.v's [Deloop_map_unmap_fobj]). 

 --------
 函子侧，在[Functor_Setoid]强度下：分量坐着
 对目标的单一对象，因此每个对象都通过案例分析被找到
 在 [fobj F x]（一个[poly_unit]没有定义的预计时间，因此匹配
 是真实的——可与Transform.v的 [Deloop_map_unmap_fobj] 对比）。
*)
Lemma cocycle_functor_round (F : Proset P ⟶ Deloop M) :
  functor_of_cocycle (cocycle_of_functor F) ≈ F.
Proof.
  exists (fun x =>
            match fobj[F] x as u
                  return (@Isomorphism (Deloop M) ttt u) with
            | ttt => iso_id
            end).
  intros p q h; simpl.
  destruct (fobj[F] p), (fobj[F] q); simpl.
  now rewrite mon_op_unit_l, mon_op_unit_r.
Qed.

End Cocycle.

(*
   * ** The worked witness: (ℤ, ≤) into (ℤ, +) by differences 

   --------
   * ** 已处理的证人: (ℤ, ≤) 映射到 (ℤ, +) 通过差值
*)

(*
 The additive group of the integers, as a [GrpObject] — Awodey's ℝ
 transposed to ℤ so the instance layer stays axiom-free (the same
 substitution Theory/Algebra/Rig.v makes for [Int_Ring]). 

 --------
 整数的加法群，作为一个 [GrpObject] — Awodey 的 ℝ 转置到 ℤ，这样实例层保持无公理（同样的替代 Theory/Algebra/Rig.v 对 [Int_Ring] 所做的）。
*)
Program Definition Int_Plus : MonObject := {|
  mon_setoid := {| carrier := Z
                 ; is_setoid := {| Setoid.equiv := @eq Z |} |};
  mon_unit := 0%Z;
  mon_op := Z.add
|}.
Next Obligation. intros a b c; simpl; now rewrite Z.add_assoc. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_l. Qed.
Next Obligation. intros a; simpl; apply Z.add_0_r. Qed.

Program Definition Int_Plus_Grp : GrpObject := {|
  grp_monoid := Int_Plus;
  grp_inv := Z.opp
|}.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_l. Qed.
Next Obligation. intros a; simpl; now rewrite Z.add_opp_diag_r. Qed.

(*
 Awodey's cocycle: g_{x,y} = y − x, with the unit condition x − x = 0
 and the composition condition (z − y) + (y − x) = z − x. 

 --------
 Awodey 的 1-环：g_{x,y} = y − x，满足单位条件 x − x = 0 和组合条件 (z − y) + (y − x) = z − x。
*)
Program Definition translation_cocycle :
  Cocycle Z.le_preorder Int_Plus := {|
  cocycle := fun x y _ => (y - x)%Z
|}.
Next Obligation. intros p q h h'; reflexivity. Qed.
Next Obligation. intros p; simpl; now rewrite Z.sub_diag. Qed.
Next Obligation. intros p q r h k; simpl; lia. Qed.

Definition translation_functor :
  Proset Z.le_preorder ⟶ Deloop Int_Plus :=
  functor_of_cocycle Z.le_preorder Int_Plus translation_cocycle.

Example five_le_twelve : (5 <= 12)%Z.
Proof. lia. Qed.

Example translation_5_12 :
  @fmap _ _ translation_functor 5%Z 12%Z five_le_twelve = 7%Z
  := eq_refl.
