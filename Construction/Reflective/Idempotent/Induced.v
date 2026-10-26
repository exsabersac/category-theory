Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Construction.Reflective.FixedPoints.

Generalizable All Variables.

(*
   * * The reflection of an idempotent monad induces that monad 

   --------
   * * 幂等单子（Monad）的反射会诱导该单子
*)

(*
 nLab: https://ncatlab.org/nlab/show/idempotent+monad
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, SS VI.2, Theorem 1, printed pp. 140-141
 Book: Awodey, “Category Theory” (1st ed., CMU pre-print, Sept 2005),
 SS 10.2, printed p. 271

 Construction/Reflective/Idempotent.v proves that an idempotent monad M
 reflects C onto its M-local objects, those x at which ret x is
 invertible: [idem_reflective_adj] is the adjunction
 [idem_reflector ⊣ Incl C MLocal_Subcategory].  Its converse there,
 [Reflective_Monad] with [Reflective_IdempotentMonad], goes from a
 reflection to a monad.  What it does not state is that the two meet:
 that the monad induced by the reflection BUILT FROM M is M again.
 This file states it, as the triple the tree already uses for the other
 two resolutions of a monad, Monad/Eilenberg/Moore/Adjunction.v's
 [EM_unit_agrees], [EM_join_agrees], [EM_Monad_agrees] and
 Monad/Kleisli/Adjunction.v's [Kleisli_*_agrees]:
 - [idem_unit_agrees]: the induced unit is ret;
 - [idem_join_agrees]: the induced multiplication is join;
 - [idem_Monad_agrees]: the composite [Incl ◯ idem_reflector] is M,
 as functors, with identity components.
 The dual is the same three lemmas at C^op, the tree's duality
 discipline: the coreflection of an idempotent comonad, the adjunction
 of Construction/Reflective/FixedPoints.v's [Idempotent_Coreflective],
 induces that comonad ([idem_counit_agrees], [idem_comult_agrees],
 [idem_Comonad_agrees]), with no law proved again.
 The induced monad is Monad/Comparison.v's [Adjunction_Induced_Monad],
 whose ret and join are the adjunction's unit and the image of its
 counit, transparently.

 For the Eilenberg-Moore resolution Mac Lane states this as part of
 Theorem 1 (p. 140): “The monad defined in X by this adjunction is the
 given monad”, checked on p. 141 as “The endofunctor G^T F^T is the
 original T, its unit η^T is the original unit, and its multiplication
 ... is the original multiplication of T.”  For the fixed-point reflection
 of a monad on a poset Awodey builds the adjunction on p. 271 (with
 T = i ∘ t and t ⊣ i) without saying in words that it induces T; the
 order-theoretic instance of this file, where that is read back, is
 Instance/Proset/Monad/Awodey.v, and the instance at a preorder is
 Instance/Proset/Monad.v's [proset_fixed_adj].  This file is a
 satellite rather than an addition to Idempotent.v so that the donor,
 whose closure the index records, is not edited.

 STRENGTHS, measured.  On objects and on arrows the composite IS M by
 [eq_refl] ([idem_factorisation_obj], [idem_factorisation_fmap]).  The
 unit and multiplication agree at ≈
 and not by conversion: [cbn] and [cbv] both reduce the induced unit at
 x to [id ∘ ret x] and the induced multiplication at x to
 [join x ∘ fmap[M] id], with no opaque constant left in the normal
 form.  The identities are Theory/Adjunction.v's definitions of the
 unit and counit as transposes of identities ([unit := ⌊id⌋]), read
 through the bijection of [Adjunction_from_Transform]
 (Adjunction/Natural/Transformation/Universal.v), whose transpose of f
 is [fmap f ∘ unit].  So no [Qed] in the donors is what stands in the way;
 the gap is exactly the laws [id_left] and [fmap_id], which in an
 arbitrary C hold at ≈ only.  [eq_refl] for either component is
 refused by conversion ([cannot unify]), and so is the functor
 equation [Incl ◯ idem_reflector = M].  For the functor equation, fobj
 and fmap agree by eq_refl and the refusal is in the law fields alone,
 stuck projections of a variable M.  In a thin category every one
 of these ≈ is trivial, which is the situation of
 Instance/Proset/Monad.v.

 UNIVERSES, read off [About].  [idem_unit_agrees], [idem_join_agrees]
 and their duals [idem_counit_agrees], [idem_comult_agrees] bind
 [@{o h d s a}], the others [@{o h d s}], with [C : Category@{o h h}]
 as in every constant of Idempotent.v.
 [d] is the object level of the subcategory [Sub] ([o <= d],
 [h <= d]); [s] carries the one strict bound [h < s].  Its first
 carrier in dependency order is Theory/Functor.v's [Compose]
 ([u3 < u2]), through the composite [Incl ◯ idem_reflector] that every
 statement mentions; Construction/Subcategory.v's [Sub] introduces the
 same kind of bound in its own block (while [Setoid] and [Category]
 carry none), and for the unit and the multiplication so does
 Instance/Sets.v's [Sets] ([o < so]), where the hom-setoid isomorphism
 of [Adjunction] lives.  All are unified into [s].  [a] is a level of
 [idem_reflective_adj] that is free in that constant's block and
 occurs in the statement through its instance.  The stdlib caps
 [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1] come
 from [Sub] and [Incl], and the unit and multiplication lemmas and
 their duals add [h <= compose.u0, compose.u1, compose.u2, ID.u0],
 first carried by [Sets] through [Adjunction] ([Sets@{o so}] has them
 at its level o).  In the duals the type level of FixedPoints.v's
 [IdempotentComonad] is unified with [d].  No constant carries [Set].

 NOT DELIVERED.  The three facts are not packaged as one isomorphism
 of monads; the tree has no record of monad morphisms to package them
 in.  The dual is stated only as the C^op instance of the three
 lemmas: [idem_Comonad_agrees] compares functors on C^op, as
 FixedPoints.v's [Coreflective_IdempotentMonad_op] does, and is not
 transported to C; and it is not stated through Comonad/Duality.v's
 [Adjunction_Comonad], which is built through the opaque
 [Adjunction_Monad], so that its extract does not reduce
 (Construction/Reflective/FixedPoints.v records the same obstacle).

 CORRECTION (#468).  The record exists now: Monad/Morphism.v's [MonadHom]
 and its category [Monads C], in which an isomorphism of monads is an
 [Isomorphism] of [Monads C].  The three facts are still not packaged as
 one: no isomorphism in [Monads C] between the monad induced by
 [idem_reflective_adj] and M is stated. 

 --------
 nLab：https://ncatlab.org/nlab/show/idempotent+monad
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，Springer GTM 5, 1998，第VI.2节，定理1，印刷页140-141
 书籍：Awodey，《范畴论》（第1版，CMU预印本, 2005年9月），第10.2节，印刷页271Construction/Reflective/Idempotent.v 证明了幂等单子 M 会将 C 反映到它的 M-局部对象上，即那些使 ret x 可逆的 x：[idem_reflective_adj] 是伴随关系 [idem_reflector ⊣ Incl C MLocal_Subcategory] 。它的逆过程 [Reflective_Monad] 与 [Reflective_IdempotentMonad] 从一个反射出发到一个单子。它没有说明的是两者的相遇：即由反射（由 M 构建）所诱导的单子再次是 M。该文件说明了这一点，作为树已用于单子其他两种分解的三元组，Monad/Eilenberg/Moore/Adjunction.v 的 [EM_unit_agrees]、[EM_join_agrees]、[EM_Monad_agrees] 以及 Monad/Kleisli/Adjunction.v 的 [Kleisli_*_agrees]：
 - [idem_unit_agrees]：诱导的单位是 ret；
 - [idem_join_agrees]：诱导的乘法是 join；
 - [idem_Monad_agrees]：复合 [Incl ◯ idem_reflector] 是 M，作为函子，具有相应的恒等组件。对偶是在 C^op 上的相同三个引理，树的对偶性学科：幂等余单子（comonad）的余反映，Construction/Reflective/FixedPoints.v 的 [Idempotent_Coreflective] 的伴随，引出该余单子（[idem_counit_agrees]、[idem_comult_agrees]、[idem_Comonad_agrees]），没有再次证明定律。所引出的单子是 Monad/Comparison.v 的 [Adjunction_Induced_Monad]，其 ret 和 join 分别是伴随的单位和其余单位的像，透明地。对于 Eilenberg-Moore 分解，Mac Lane 在定理 1（第 140 页）中陈述了这一点：“由该伴随关系在 X 中定义的单子是给定的单子”，并在第 141 页进行了验证：“函子 G^T F^T 是原始的 T，其单位 η^T 是原始单位，其乘法 ... 是 T 的原始乘法。” 对于偏序集上的单子不动点反射，Awodey 在第 271 页构建了伴随关系（其中 T = i ∘ t 且 t ⊣ i），但并未用文字说明它会诱导 T；该文件的序理论实例（在那里可读回）是 Instance/Proset/Monad/Awodey.v，而在预序集上的实例是 Instance/Proset/Monad.v 的 [proset_fixed_adj]。这个文件是一个卫星文件，而不是 Idempotent.v 的补充，因此捐赠者（其索引记录了闭包）未被编辑。优势，已测量。在对象和箭头上，复合体由 [eq_refl]（[idem_factorisation_obj], [idem_factorisation_fmap]）表示为 IS M。单位和乘法在 ≈ 处一致，而非通过转换：[cbn] 和 [cbv] 都将 x 处的诱导单位化简为 [id ∘ ret x]，并将 x 处的诱导乘法化简为 [join x ∘ fmap[M] id，正规形式中没有遗留不透明常数。恒等式是 Theory/Adjunction.v 中对单位和余单位的定义，作为恒等式（[unit := ⌊id⌋]）的转置，通过 [Adjunction_from_Transform]（Adjunction/Natural/Transformation/Universal.v）的双射读取，其 f 的转置是 [fmap f ∘ unit]。因此，donors 中没有 [Qed] 是阻碍因素；差距正是定律 [id_left] 和 [fmap_id]，在任意 C 中只能在 ≈ 处成立。对于任意一个组件，[eq_refl] 都被转换（[cannot unify]）拒绝，同样，函子方程 [Incl ◯ idem_reflector = M] 也被拒绝。对于函子方程，fobj 和 fmap 通过 eq_refl 一致，而拒绝仅出现在定律字段中，即变量 M 的卡住投影。在一个薄范畴中，这些 ≈ 每一个都是平凡的，这就是 Instance/Proset/Monad.v 的情况。UNIVERSES，读出 [About]、[idem_unit_agrees]、[idem_join_agrees] 及其对偶 [idem_counit_agrees]、[idem_comult_agrees] 绑定 [@{o h d s a}]，其他 [@{o h d s}] 与 [C : Category@{o h h}]，如同 Idempotent.v 的每个常量一样。[d] 是子范畴 [Sub]（[o <= d]、[h <= d]）的对象层级；[s] 携带一个严格的绑定 [h < s]。其依赖顺序中的第一个承载者是 Theory/Functor.v 的 [Compose]（[u3 < u2]），通过每个语句中提到的复合 [Incl ◯ idem_reflector]；Construction/Subcategory.v 的 [Sub] 在其自身模块中引入相同类型的绑定（而 [Setoid] 和 [Category] 则没有），对于单位和乘法，Instance/Sets.v 的 [Sets]（[o < so]）也如此，其中 [Adjunction] 的 Hom-集合同构存在。所有这些统一成 [s]。[a] 是 [idem_reflective_adj] 的一个级别，它在该常量的块中是自由的，并且通过其实例出现在语句中。stdlib 限制 [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1] 来自 [Sub] 和 [Incl]，而单位和乘法引理及其对偶增加了 [h <= compose.u0, compose.u1, compose.u2, ID.u0]，最初由 [Sets] 通过 [Adjunction] 携带（[Sets@{o so}] 在其级别 o 上拥有它们）。在对偶中，FixedPoints.v 的 [IdempotentComonad] 的类型级别与 [d] 统一。没有常量携带 [Set]。未交付。三个事实没有被打包为单一的单子同构；树中没有记录单子态射以便打包它们。其对偶只是作为三个引理的 C^op 实例来陈述：[idem_Comonad_agrees] 比较 C^op 上的函子，就像 FixedPoints.v 的 [Coreflective_IdempotentMonad_op] 一样，并未传递到 C；并且它没有通过 Comonad/Duality.v 的 [Adjunction_Comonad] 来陈述，该 [Adjunction_Comonad] 是通过不透明的 [Adjunction_Monad] 构建的，因此其提取不简化（Construction/Reflective/FixedPoints.v 记录了同样的障碍）。更正（#468）。记录现在存在：Monad/Morphism.v 的 [MonadHom] 及其类别 [Monads C]，其中单子同构是 [Isomorphism] 的 [Monads C]。这三个事实仍然没有打包为一个：没有在 [Monads C] 中声明由 [idem_reflective_adj] 引入的单子与 M 之间的同构。
*)

(*
 The unit of the induced monad is ret.  It reduces to [id ∘ ret x]. 

 --------
 诱导单子的单元是 ret。它化简为 [id ∘ ret x]。
*)
Lemma idem_unit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @ret C _ (Adjunction_Induced_Monad
              (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @ret C M MM x.
Proof. cbn. apply id_left. Qed.

(*
 The multiplication of the induced monad is join.  It reduces to
 [join x ∘ fmap[M] id]. 

 --------
 诱导莫纳德的乘法是 join。 它化简为 [join x ∘ fmap[M]  id]。
*)
Lemma idem_join_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  @join C _ (Adjunction_Induced_Monad
               (@idem_reflective_adj@{o h d a h s} C M MM IM)) x
    ≈ @join C M MM x.
Proof. cbn. rewrite fmap_id. apply id_right. Qed.

(*
 The composite of the reflection is M, with identity components. 

 --------
 反射的复合是 M，具有单位分量。
*)
Theorem idem_Monad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} :
  Incl C (@MLocal_Subcategory C M MM)
    ◯ @idem_reflector@{o h d h h s} C M MM IM ≈ M.
Proof. exists (fun x => iso_id). intros x y f; cbn. cat. Qed.

(* ...and on objects it is M on the nose. / ...而在物体上，它正好是 M。 *)
Example idem_factorisation_obj@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} (x : C) :
  fobj[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] x = M x := eq_refl.

(*
 ...and on arrows: the functor equation is refused in the law fields
 alone. 

 --------
 ...而在箭头上：函子方程仅在法域中被拒绝。
*)
Example idem_factorisation_fmap@{o h d s | h < s +} {C : Category@{o h h}}
  {M : C ⟶ C} {MM : @Monad C M} {IM : @IdempotentMonad C M MM} {x y : C}
  (f : x ~> y) :
  fmap[Incl C (@MLocal_Subcategory C M MM)
         ◯ @idem_reflector@{o h d h h s} C M MM IM] f = fmap[M] f := eq_refl.

(* * ** The dual, as the three lemmas at C^op / * ** 对偶，作为 C^op 的三个引理 *)

(*
 The counit of the comonad induced by the coreflection is extract. 

 --------
 由余反射引起的余单子函子（comonad）的余单位是 extract。
*)
Definition idem_counit_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @ret (C^op) _ (Adjunction_Induced_Monad
                   (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @extract C W H x :=
  @idem_unit_agrees@{o h d s a} (C^op) (W^op) H IH x.

(* Its comultiplication is duplicate. / 它的余乘是重复的。 *)
Definition idem_comult_agrees@{o h d s a | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} (x : C) :
  @join (C^op) _ (Adjunction_Induced_Monad
                    (@idem_reflective_adj@{o h d a h s} (C^op) (W^op) H IH)) x
    ≈ @duplicate C W H x :=
  @idem_join_agrees@{o h d s a} (C^op) (W^op) H IH x.

(*
 The composite of the coreflection is W^op, with identity components. 

 --------
 核心反射的复合是 W^op，具有单位分量。
*)
Definition idem_Comonad_agrees@{o h d s | h < s +} {C : Category@{o h h}}
  {W : C ⟶ C} {H : @Comonad C W} {IH : IdempotentComonad W H} :
  Incl (C^op) (@MLocal_Subcategory (C^op) (W^op) H)
    ◯ @idem_reflector@{o h d h h s} (C^op) (W^op) H IH ≈ W^op :=
  @idem_Monad_agrees@{o h d s} (C^op) (W^op) H IH.
