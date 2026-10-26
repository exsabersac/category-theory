(*
   * * The inclusion of a reflective subcategory is monadic

   Riehl, “Category Theory in Context”, §5.3, printed p. 196 (PDF
   p. 216), read from the page image.  Definition 5.3.1: an adjunction
   “is monadic if the canonical comparison functor of Proposition
   5.2.13 from D to the category of algebras for the underlying monad
   on C defines an equivalence of categories”, and a functor is monadic
   when it has a left adjoint whose adjunction is monadic (the second
   sentence of the definition, paraphrased).  Proposition 5.3.3 (ii):
   “The inclusion D ↪ C of a reflective subcategory is monadic: that
   is, the functor K from D to the category of algebras C^L for the
   induced idempotent monad L is an equivalence of categories.”
   Exercise 5.3.ii, printed p. 197 (PDF p. 217), catalog item
   riehl:5.3:exii: “Revisit your favorite example of an reflective
   subcategory from Examples 4.6.13 and use Proposition 5.3.3 to give
   an equivalent presentation of this subcategory as the category of
   algebras for an idempotent monad.”
   Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   §IV.3, printed p. 91 (PDF p. 100), read from the page image, for
   the notion itself: “A subcategory A of B is called reflective in B
   when the inclusion functor K: A → B has a left adjoint F: B → A.”
   nLab: https://ncatlab.org/nlab/show/reflective+subcategory
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/idempotent+monad

   BACKGROUND.  nLab's reflective-subcategory page states the fact as a
   proposition -- “Every reflective subcategory inclusion is a monadic
   functor, exhibiting the reflective subcategory as the
   Eilenberg-Moore category of modules for its induced idempotent
   monad” -- with the converse, and points to Borceux's Handbook,
   vol. 2, Cor. 4.2.4, for a proof.  Riehl proves the essential
   surjectivity of K from the characterization of the algebras of an
   idempotent monad (an object carries an algebra structure exactly
   when its unit is invertible, the structure map being the inverse)
   and concludes by her Theorem 1.5.9.  The route here is the same in
   outline: full, faithful and essentially surjective, then
   Theory/Equivalence/FullFaithful.v's [FF_ESO_Equivalence].

   WHAT THIS ADDS TO Construction/Reflective/Idempotent.v.  That file
   already has both directions of the correspondence and the
   Eilenberg–Moore reading, but its [Idempotent_EM_Equivalence] is an
   equivalence between the algebras of an idempotent monad and that
   monad's M-LOCAL subcategory [MLocal_Subcategory], not the subcategory
   a reflection started from.  Fed a reflection, it lands on the
   objects at which the unit is invertible, which is a different
   [Subcategory] record.  This file instead takes Monad/Comparison.v's
   [EM_Comparison] of the reflection itself, [reflective_comparison R :
   Sub C S ⟶ EilenbergMoore (Incl ◯ reflector R)], and proves THAT an
   equivalence, so the subcategory S is itself presented as the
   algebras ([Reflective_EM_Equivalence]) and its inclusion is monadic
   in Monad/Comparison.v's own sense ([Reflective_Monadic]).  The monad
   is Idempotent.v's [Reflective_Monad R], which is
   [Adjunction_Induced_Monad (reflective_adj R)] by definition, so the
   two developments speak about one category of algebras.

   THE PROOF.  Faithful: morphisms of algebras are compared on their
   underlying arrows.  Full: an algebra morphism between comparison
   algebras is an arrow of C between objects of S, lifted by the
   record's fullness field ([reflective_comparison_prefmap]).
   Essentially surjective: the chosen preimage of an algebra (a, α) is
   the reflection of a ([reflective_eso_obj]); the isomorphism has α
   as its forward leg and the unit as its backward leg, with the
   algebra laws [t_id] and [t_action] and Idempotent.v's
   [algebra_ret_iso] as the four obligations.  The witness of
   [algebra_ret_iso] is bound with [pose] rather than [pose proof], and
   that is load-bearing: in a copy using [pose proof] the step
   [exact (is_right_inverse Hret)] is refused, its type reading
   [ret ∘ two_sided_inverse ≈ id] where [unit ∘ t_alg[alg] ≈ id] is
   wanted.

   STRENGTHS.  The five [Example]s hold at [eq_refl]: the comparison
   sends an object of S to its own carrier ([reflective_comparison_obj])
   with the counit, read through the inclusion, as the structure map
   ([reflective_comparison_alg]); the chosen preimage IS the reflection
   of the carrier ([reflective_eso_obj_is_reflector]); the forward leg
   of the isomorphism IS the algebra's structure map
   ([reflective_eso_iso_to]); and the left adjoint of the monadic
   witness IS the reflector ([Reflective_Monadic_left]).  No constant
   is closed with [Qed].  Concrete instances: Instance/Ab/Torsion.v
   ([TorsionFree_EM_Equivalence], [TorsionFree_Incl_Monadic], at #371's
   torsion-free reflection) and Instance/Grp/Abelianize/Reflective.v
   ([AbGrp_Incl_Monadic]).

   UNIVERSES, read by [About] under [Set Printing Universes] on all
   fourteen constants.  Each carries the binder [@{o h +}] with
   [C : Category@{o h h}] and binds S at [Subcategory@{o h s h}] for a
   level s of its own: the hom-with-proof identification is
   [Subcategory]'s, and the fourth level's identification with h is
   [Reflective]'s own binder ([Subcategory@{u3 u5 u4 u5}]).  No
   constraint block carries an equation or mentions [Set], and every
   global universe in them ([Basics.compose.u0]-[u2], [ID.u0],
   [Projections.u0]/[u1]) is an upper bound.  Against a copy with
   every binder removed, compared under [Set Printing All], every
   constant has the same number of universes and the same
   identifications.

   NOT DELIVERED.
   - No comparison between [reflective_comparison R] and
   Idempotent.v's [idem_G], and no equivalence between S and the
   M-local subcategory of its monad.
   - No strict monadicity: the comparison is an equivalence, not an
   isomorphism of categories.
   - No comonadic statement for a coreflection, although
   [Reflective_Monadic] applies to a [Coreflective] record (which
   is a [Reflective] one in the opposite category) as it stands.
   - The monadicity here is proved directly; Beck's theorem
   (Monad/Monadicity/Beck.v) is not used. 

   --------
   * * 反思子类别的包含是单一的Riehl，《上下文中的范畴论》，§5.3，第196页（PDF 第216页），根据页面图像阅读。定义 5.3.1：一个伴随函子“如果命题 5.2.13 中从 D 到 C 上下单子代数范畴的典型比较函子定义了范畴的等价，则称该伴随函子为单态的”，并且一个函子是单态的，当它有一个左伴随且该伴随是单态的（定义的第二句话，意译）。命题 5.3.3 (ii)：“反射子范畴 D ↪ C 的包含函子是单态的：也就是说，从 D 到所诱导的幂等单子 L 的代数范畴 C^L 的函子 K 是范畴的等价。” 练习 5.3.ii，第197页（PDF 第217)，目录项
   riehl:5.3:exii: “回顾你在例 4.6.13 中最喜欢的反射子范畴的例子，并使用命题 5.3.3 给出该子范畴作为幂等幺函子代数的范畴的等价表示。”
   Mac Lane，《为工作中的数学家准备的范畴论》，第二版，§IV.3，第 91 页（PDF 第 100 页），根据页面图像阅读，关于概念本身：“B 的子范畴 A 称为 B 中的反射子范畴，当且仅当包含函子 K: A → B 存在左伴随 F: B → A。”
   nLab: https://ncatlab.org/nlab/show/reflective+subcategory 
   nLab: https://ncatlab.org/nlab/show/monadic+functor 
   nLab: https://ncatlab.org/nlab/show/idempotent+monad背景。nLab 的反射子范畴页面将该事实以命题形式陈述——“每个反射子范畴的包含函子都是一个单子函子，将反射子范畴展示为其诱导幂等单子的模块的 Eilenberg-Moore 范畴”——并指出其逆命题，并指向 Borceux 的《Handbook》第 2 卷，推论 4.2.4 以获取证明。Riehl 从幂等单子代数的特征（一个对象恰好在其单位可逆时携带代数结构，结构映射为逆映射）证明了 K 的本质满射性，并通过她的定理 1.5.9 得出结论。这里的路线在大纲上是相同的：先证明满、忠实且本质上满射，然后参考 Theory/Equivalence/FullFaithful.v 的 [FF_ESO_Equivalence]。这为 Construction/Reflective/Idempotent.v 文件增加了什么。该文件已经包含了对应的两个方向以及 Eilenberg–Moore 解析，但其 [Idempotent_EM_Equivalence] 是幂等单子代数与该单子的 M-LOCAL 子范畴 [MLocal_Subcategory] 之间的等价，而不是从反射开始的子范畴。给定一个反射，它会落在单位可逆的对象上，这是一个不同的 [Subcategory] 记录。相反，该文件采用了 Monad/Comparison.v 中反射本身的 [EM_Comparison]，[reflective_comparison R : Sub C S ⟶ EilenbergMoore (Incl ◯ reflector R)]，并证明了这是一个等价，因此子范畴 S 本身呈现为代数 ([Reflective_EM_Equivalence])，且其包含是 Monad/Comparison.v 自身意义下的单子性 ([Reflective_Monadic])。该单子是 Idempotent.v 的 [Reflective_Monad R]，根据定义它是 [Adjunction_Induced_Monad (reflective_adj R)]，所以这两个发展讨论的是同一类代数。证明。忠实：代数的态射在其底层箭头上进行比较。满：比较代数之间的代数态射是对象 S 之间 C 的箭头，由记录的 fullness 字段提升（[reflective_comparison_prefmap]）。本质上可满：代数 (a, α) 的选定原像是 a 的反射（[reflective_eso_obj]）；同构的前向边是 α，反向边是单位，代数定律 [t_id] 和 [t_action] 以及 Idempotent.v 的 [algebra_ret_iso] 作为四个义务。[algebra_ret_iso] 的证人绑定于 [pose] 而不是 [pose proof]，这一点是关键：在使用 [pose proof] 的副本中，步骤 [exact (is_right_inverse Hret)] 被拒绝，其类型读取 [ret ∘ two_sided_inverse ≈ id]，其中 [unit ∘ t_alg[alg] ≈ id 是所需的。优点。五个 [Example] 在 [eq_refl] 上成立：比较将 S 的一个对象送到其自身的承载体（[reflective_comparison_obj]），通过包含映射读取余单位，作为结构映射（[reflective_comparison_alg]）；选择的原像是承载体的反射（[reflective_eso_obj_is_reflector]）；同构的前向分支是代数的结构映射（[reflective_eso_iso_to]）；单子见证的左伴随是反射器（[Reflective_Monadic_left]）。没有常量与 [Qed] 封闭。具体实例：Instance/Ab/Torsion.v（[TorsionFree_EM_Equivalence], [TorsionFree_Incl_Monadic], 在 #371 的无挠反射）以及 Instance/Grp/Abelianize/Reflective.v（[AbGrp_Incl_Monadic]）。宇宙，由 [About] 在 [Set Printing Universes] 下读取，针对所有十四个常量。每一个都带有绑定器 [@{o h +}] 和 [C : Category@{o h h}]，并在 [Subcategory@{o h s h}] 对其自身的某一级 s 绑定 S：带证明的同一性是 [Subcategory] 的，而第四级与 h 的同一性是 [Reflective] 自己的绑定器 ([Subcategory@{u3 u5 u4 u5}])。没有约束块携带方程或提到 [Set]，并且其中的每个全局宇宙 ([Basics.compose.u0] - [u2]，[ID.u0]，[Projections.u0] / [u1]) 都是上界。与移除每个绑定器的副本相比，在 [Set Printing All] 下比较，每个常量的宇宙数量相同，认同也相同。未交付。
   - 没有比较 [reflective_comparison R] 与 Idempotent.v 的 [idem_G]，也没有 S 与其单子 M-局部子范畴之间的等价。
   - 没有严格的单子性：比较是等价的，而不是范畴的同构。
   - 对于一个共反射没有共单子性声明，尽管 [Reflective_Monadic] 对 [Coreflective] 记录（在对偶范畴中为 [Reflective] 记录）如原样适用。
   - 这里的单子性是直接证明的；没有使用 Beck 定理（Monad/Monadicity/Beck.v）。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.

Generalizable All Variables.

(* * ** The comparison functor of a reflection / * ** 反射的比较函子 *)

(*
 [Reflective_Monad R] is [Adjunction_Induced_Monad (reflective_adj R)]
 by definition, so the Eilenberg–Moore comparison of the reflection
 lands in the category of algebras for the idempotent monad
 Construction/Reflective/Idempotent.v attaches to [R]. 

 --------
 [Reflective_Monad R] 根据定义是 [Adjunction_Induced_Monad (reflective_adj R)]，因此 Eilenberg–Moore 的反射比较落在幂等单子代数的范畴中。Construction/Reflective/Idempotent.v 附加到 [R]。
*)
Definition reflective_comparison@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Sub C S ⟶ @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)
  := EM_Comparison (reflective_adj R).

Definition reflective_comparison_Faithful@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Faithful (reflective_comparison R).
Proof. constructor; intros x y f g H; exact H. Defined.

(*
 A morphism of algebras between two comparison algebras is an arrow of
 C between objects of the subcategory; fullness of the subcategory puts
 it back in [Sub C S]. 

 --------
 两个比较代数之间的代数态射是 C 中的一个箭头，连接子类中的对象；子类的充满性将其放回 [Sub C S]。
*)
Definition reflective_comparison_prefmap@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) {s t : Sub C S}
  (h : reflective_comparison R s ~> reflective_comparison R t) : s ~> t :=
  (t_alg_hom[h]; reflective_full R _ _ `2 s `2 t t_alg_hom[h]).

Definition reflective_comparison_Full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  Functor.Full (reflective_comparison R).
Proof.
  refine {| prefmap := @reflective_comparison_prefmap C S R |}.
  intros s t h; simpl; reflexivity.
Defined.

(*
 The chosen preimage of an algebra (a, α) is the reflection of [a]. 

 --------
 代数 (a, α) 的选定原像是 [a] 的反射。
*)
Definition reflective_eso_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  Sub C S := reflector R ``z.

(*
 The comparison algebra at the reflection of [a] is isomorphic to
 (a, α): forward the structure map α, backward the unit.  That the unit
 is inverse to α is Idempotent.v's [algebra_ret_iso]; the witness is
 bound with [pose] so that its inverse stays a reduct of α. 

 --------
 在 [a] 的反射处的比较代数同构于 (a, α)：前向为结构映射 α，后向为单位。单位与 α 的逆是 Idempotent.v 的 [algebra_ret_iso]；见证与 [pose] 绑定，以便其逆保持 α 的约简。
*)
Definition reflective_eso_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_comparison R (reflective_eso_obj R z) ≅ z.
Proof.
  destruct z as [a alg].
  pose (Hret := @algebra_ret_iso C _ (Reflective_Monad R)
                  (Reflective_IdempotentMonad R) a alg).
  unshelve refine
    (@Build_Isomorphism
       (@EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R))
       (reflective_comparison R (reflective_eso_obj R (a; alg))) (a; alg)
       _ _ _ _).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (t_alg[alg]) _).
    simpl. symmetry. exact (@t_action C _ (Reflective_Monad R) a alg).
  - refine (@Build_TAlgebraHom C _ (Reflective_Monad R) _ _ _ _
              (@ret C _ (Reflective_Monad R) a) _).
    simpl.
    transitivity (@id C (fobj[Incl C S ◯ reflector R] a)).
    + exact (@is_right_inverse C _ _ _ Hret).
    + symmetry. exact (@join_fmap_ret C _ (Reflective_Monad R) a).
  - simpl. exact (@t_id C _ (Reflective_Monad R) a alg).
  - simpl. exact (@is_right_inverse C _ _ _ Hret).
Defined.

Definition reflective_comparison_ESO@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EssentiallySurjective (reflective_comparison R) :=
  @Build_EssentiallySurjective _ _ (reflective_comparison R)
    (reflective_eso_obj R) (reflective_eso_iso R).

(** ** Riehl, Proposition 5.3.3 (ii) / ** Riehl，第 5.3.3 命题 (ii) *)

(*
 The subcategory ITSELF is equivalent to the algebras of the induced
 idempotent monad, by the comparison functor. 

 --------
 子范畴本身等价于通过比较函子得到的诱导幂等幺半群代数。
*)
Definition Reflective_EM_Equivalence@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  EquivalenceOfCategories (reflective_comparison R) :=
  @FF_ESO_Equivalence _ _ (reflective_comparison R)
    (reflective_comparison_Full R) (reflective_comparison_Faithful R)
    (reflective_comparison_ESO R).

(*
 The inclusion of a reflective subcategory is monadic, in
 Monad/Comparison.v's sense: the reflector, the reflection, and the
 equivalence above. 

 --------
 反射子类别的包含在 Monad/Comparison.v 的意义上是单子性的：反射器、反射以及上述等价。
*)
Definition Reflective_Monadic@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) : Monadic (Incl C S) :=
  (reflector R; (reflective_adj R; Reflective_EM_Equivalence R)).

(** ** Readbacks / ** 回读 *)

(*
 The comparison sends an object of the subcategory to its own carrier,
 with the counit read through the inclusion as the structure map. 

 --------
 这个比较将子类别的一个对象发送到它自己的承载器，并通过包含读取余单位作为结构映射。
*)
Example reflective_comparison_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  ``(reflective_comparison R s) = `1 s := eq_refl.

Example reflective_comparison_alg@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (s : Sub C S) :
  t_alg[projT2 (reflective_comparison R s)]
    = fmap[Incl C S] (@counit _ _ _ _ (reflective_adj R) s) := eq_refl.

(*
 The chosen preimage of an algebra is the reflection of its carrier. 

 --------
 一个代数的选定原像是其载体的反映。
*)
Example reflective_eso_obj_is_reflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S)
  (z : @EilenbergMoore C (Incl C S ◯ reflector R) (Reflective_Monad R)) :
  reflective_eso_obj R z = fobj[reflector R] ``z := eq_refl.

(*
 The isomorphism's forward leg IS the algebra's structure map. 

 --------
 同构的正向部分就是代数的结构映射。
*)
Example reflective_eso_iso_to@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) (a : C)
  (alg : @TAlgebra C _ (Reflective_Monad R) a) :
  t_alg_hom[to (reflective_eso_iso R (a; alg))] = t_alg[alg] := eq_refl.

(* The monadic witness's left adjoint is the reflector itself. / 单子见证者的左伴随是反射器本身。 *)
Example Reflective_Monadic_left@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Reflective S) :
  `1 (Reflective_Monadic R) = reflector R := eq_refl.
