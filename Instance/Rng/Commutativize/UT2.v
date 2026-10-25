(*
   * * The commutator-ideal reflection is not trivial: upper-triangular UT2

   Riehl, "Category Theory in Context", §4.6, Example 4.6.13 (ii),
   printed p. 170 (PDF p. 190), read from the page image: "A similar
   construction defines a left adjoint to the inclusion CRing ↪ Ring
   of commutative rings into the category of all rings."  The
   reflection is Instance/Rng/Commutativize.v; this satellite shows at
   one ring that it does something.
   nLab: https://ncatlab.org/nlab/show/reflective+subcategory

   BACKGROUND.  A reflection is visibly non-trivial at an object outside
   the subcategory whose unit is not invertible and whose reflection is
   not the terminal object.  The witness is [UT2], the ring of
   upper-triangular 2×2 integer matrices [[a, b], [0, c]] carried as
   triples (a, b, c), built in Instance/Rng/Algebras/Associative.v
   together with the matrix units [ut2_e11] = E11 and
   [ut2_e12] = E12 and [UT2_not_commutative] (E11·E12 = E12 while
   E12·E11 = 0).  Instance/Rng/Quotient/OneSided.v uses the same ring
   for its one-sided ideals, and isolates it in a satellite for the
   same reason: [UT2]'s file brings modules the reflection does not
   need (Commutativize.v's header gives the closure counts).

   WHAT IS SHOWN.
   - UT2 is not an object of the subcategory
   ([UT2_not_commutative_ring]).
   - E12 is itself a commutator, E11·E12 − E12·E11, on the nose
   ([ut2_e12_commutator], [eq_refl]), so it lies in the commutator
   ideal ([ut2_e12_in_CommIdeal]) and the unit at UT2 identifies it
   with zero ([crng_unit_UT2_merges]).  E12 is not zero in UT2
   ([ut2_e12_nonzero]), so the unit is not invertible
   ([crng_unit_UT2_not_iso]).
   - The reflection is not the zero ring: the top-left entry
   (a, b, c) ↦ a is a ring map into ℤ ([ut2_diag1_hom]); exercising
   [crng_universal] on it, the mediator sends one to 1
   ([crng_UT2_med_one], [eq_refl]) and zero to 0, so one and zero
   stay apart in the quotient ([Commutativize_UT2_nonzero]).

   UNIVERSES, read by [About] under [Set Printing Universes] on all
   eleven named constants.  The binders name [a c p] where the
   statement is about the ring [UT2 : RingObject@{a c p}], [u p] where
   it is about [Rng@{u p}], [c] for [ut2_diag1 : ut2@{c} → Z], and
   nothing ([@{+}]) for the respectfulness witness [ut2_diag1_proper],
   whose levels are the setoids'.  THE BINDERS LIFT A [Set] PIN,
   measured: in an unannotated draft of this file [crng_unit_UT2_not_iso]
   read [IsIsomorphism@{u Set Set} (crng_unit@{…} UT2@{Set Set Set}) →
   False], [ut2_diag1_hom] was a map [UT2@{Set Set Set} →
   Int_Ring@{Set Set Set}], and [crng_UT2_med_one] and
   [Commutativize_UT2_nonzero] were at [Set] too.  The bare statement
   [IsIsomorphism (crng_unit UT2) → False], elaborated alone as a
   [Definition], is general, and the same proof under [@{p +}] is
   accepted, so the pin was an artefact of elaborating the unannotated
   theorem.  Here all four read [UT2@{p p p}] at a general [p]; no
   constant of this file prints [Set] in an instance.  No block carries
   an equation.  Five blocks carry [Set < u] on [Rng]'s object level,
   [Rng]'s own bound; the six ring-level constants carry none.  [UT2]'s
   carrier level is capped by the standard library's monomorphic
   [Logic_lemmas.equality.u0] in [UT2]'s own block ([About UT2]), and
   that cap, like every global universe here, is an upper bound.

   AXIOMS.  All fifteen constants of this module, the eleven above and
   the four [Program] obligations of [ut2_diag1_hom], are closed under
   the global context.

   NOT DELIVERED.
   - No computation of the whole quotient: that UT2/[UT2, UT2] is
   ℤ × ℤ through the two diagonal entries is not proved here; only
   E12 ↦ 0 and 1 ≉ 0 are.
   - No second witness, and no statement at a ring whose reflection
   collapses. 

   --------
   * * 交换子理想反射并非平凡：上三角 UT2

   Riehl，《语境中的范畴论》，§4.6，例 4.6.13 (ii)，
   印刷版第 170 页（PDF 第 190 页），从页面图像读取：“类似的构造定义了一个左伴随于包含 CRing ↪ Ring 的函子，将交换环包含到所有环的范畴中。”
   该反射对应于 Instance/Rng/Commutativize.v；这个卫星展示了在一个环上它确实起作用。
   nLab: https://ncatlab.org/nlab/show/reflective+subcategory背景。对于子范畴之外的对象，其单位不可逆且其反射不是终对象时，反射显然是非平凡的。证据是 [UT2]，即由上三角 2×2 整数矩阵 [[a, b]、[0, c] 构成的环，以三元组 (a, b, c) 的形式表示，在 Instance/Rng/Algebras/Associative.v 中构建，同时包含矩阵单位 [ut2_e11] = E11 和 [ut2_e12] = E12 以及 [UT2_not_commutative]（E11·E12 = E12 而 E12·E11 = 0）。Instance/Rng/Quotient/OneSided.v 对其一边理想使用相同的环，并出于相同原因在一个卫星中将其隔离：[UT2] 的文件引入了反射不需要的模（Commutativize.v 的头部给出了闭包计数）。显示的内容。
   - UT2 不是子类别的对象
   ( [UT2_not_commutative_ring] )。
   - E12 本身是一个换位子，即 E11·E12 − E12·E11，正如所示
   ( [ut2_e12_commutator] ,  [eq_refl] )，因此它位于换位理想中
   ( [ut2_e12_in_CommIdeal] )，UT2 处的单位将其识别为零
   ( [crng_unit_UT2_merges] )。E12 在 UT2 中不为零
   ( [ut2_e12_nonzero] )，所以该单位不可逆
   ( [crng_unit_UT2_not_iso] )。
   - 反射不是零环：左上角的条目
   (a, b, c) ↦ a 是映射到 ℤ 的环映射 ( [ut2_diag1_hom] )；在其上使用
   [crng_universal] ，中介元将 1 发给 1
   ( [crng_UT2_med_one] ,  [eq_refl] )，将 0 发给 0，因此 1 和 0
   在商中保持不同 ( [Commutativize_UT2_nonzero] )。宇宙，由 [About] 在 [Set Printing Universes] 下读取，作用于所有十一命名常数。绑定器命名 [a c p] 表示关于环 [UT2 : RingObject@{a c p}] 的语句，[u p] 表示关于 [Rng@{u p}] 的，[c] 表示 [ut2_diag1 : ut2@{c} → Z]，而尊重见证 [ut2_diag1_proper] 没有绑定（[@{+}]），其级别是集合族。绑定器提升了一个 [Set] 引脚，测量值：在该文件的未标注草稿中 [crng_unit_UT2_not_iso] 读取 [IsIsomorphism@{u Set Set} (crng_unit@{…} UT2@{Set Set Set}) → False]，[ut2_diag1_hom] 是一个映射 [UT2@{Set Set Set} → Int_Ring@{Set Set Set}]，[crng_UT2_med_one] 和 [Commutativize_UT2_nonzero] 也位于 [Set]。简单陈述 [IsIsomorphism (crng_unit UT2) → False] ，单独展开为 [Definition] ，是一般性的，并且在 [@{p +}] 下的相同证明是被接受的，因此这个引脚是展开未注释定理的一个人工产物。在这里，所有四个在一般 [p] 下读取 [UT2@{p p p}] ；此文件中没有常量在实例中打印 [Set] 。没有区块携带等式。五个区块在 [Rng] 的对象级别上携带 [Set < u] ，即 [Rng] 自身的界限；六个环级常量均不携带。[UT2] 的承载级别被标准库在 [UT2] 自身区块 ([About UT2]) 中的单态 [Logic_lemmas.equality.u0] 限制，而这个上限，就像这里的每个全局宇宙一样，是一个上界。公理。本模块的所有十五个常量，上述十一项以及 [Program] 的四个 [ut2_diag1_hom] 义务，在全局上下文中都是封闭的。

   未完成。
   - 未计算整个商：UT2/ [UT2, UT2] 通过两个对角线元素是 ℤ × ℤ，这里没有证明；仅证明了 E12 ↦ 0 和 1 ≉ 0。
   - 没有第二个见证，并且没有关于其反射会塌缩的环的陈述。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Commutativize.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* * ** UT2 is not an object of the subcategory / * ** UT2 不是子类别的对象 *)

Lemma UT2_not_commutative_ring@{a c p +} :
  IsCommutative (UT2 : RingObject@{a c p}) → False.
Proof. intro H; exact (UT2_not_commutative (H ut2_e11 ut2_e12)). Qed.

(* * ** The unit at UT2 merges E12 with zero / * ** UT2 单元将 E12 与零合并 *)

(* E12 = E11·E12 − E12·E11 is itself a commutator. / E12 = E11·E12 − E12·E11 本身就是一个对易子。 *)
Example ut2_e12_commutator@{a c p +} :
  rcomm (UT2 : RingObject@{a c p}) ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Lemma ut2_e12_in_CommIdeal@{a c p +} :
  InCommIdeal (UT2 : RingObject@{a c p}) ut2_e12.
Proof. exact (@ici_gen UT2 ut2_e11 ut2_e12). Defined.

Lemma crng_unit_UT2_merges@{u p +} :
  rig_map (crng_unit (UT2 : Rng@{u p})) ut2_e12
    ≈ rig_map (crng_unit (UT2 : Rng@{u p})) ut2_zero.
Proof.
  simpl; unfold rquot_rel; constructor.
  exact (@ici_resp UT2 ut2_e12 _ eq_refl ut2_e12_in_CommIdeal).
Qed.

Lemma ut2_e12_nonzero@{a c p +} :
  @equiv (carrier (rig_setoid (UT2 : RingObject@{a c p}))) _ ut2_e12 ut2_zero
    → False.
Proof. unfold ut2_e12, ut2_zero; simpl; unfold ut2_eqT; discriminate. Qed.

(* So the unit at UT2 is not invertible: the reflection is a proper quotient there. / 所以 UT2 的单位不可逆：在那里反射是一个真商。 *)
Theorem crng_unit_UT2_not_iso@{u p +} :
  IsIsomorphism (crng_unit (UT2 : Rng@{u p})) → False.
Proof.
  intros [g _ Hgf].
  apply ut2_e12_nonzero.
  refine (transitivity (symmetry (Hgf ut2_e12)) _).
  refine (transitivity _ (Hgf ut2_zero)).
  exact (proper_morphism (rig_map g) _ _ crng_unit_UT2_merges).
Qed.

(* * ** The reflection of UT2 is not the zero ring / * ** UT2的反射不是零环 *)

(* The top-left entry is a ring map into ℤ, which is commutative. / 左上角的条目是一个映射到 ℤ 的环映射，它是交换的。 *)
Definition ut2_diag1@{c +} (x : ut2@{c}) : Z := fst (fst x).

#[local] Obligation Tactic := idtac.

(* The respectfulness witness is written out rather than left to instance resolution, as Associative.v does for [ut2_scal_proper]. / 尊重性见证是被显式写出的，而不是像 Associative.v 对 [ut2_scal_proper] 所做的那样留给实例解析。 *)
Definition ut2_diag1_proper@{+}
  : Proper (@equiv _ (is_setoid ut2_setoid_object)
              ==> @equiv _ (is_setoid Z_setoid_object)) ut2_diag1 :=
  fun x y H => f_equal ut2_diag1 H.

Program Definition ut2_diag1_hom@{u p +} :
  (UT2 : Rng@{u p}) ~{Rng@{u p}}~> Int_Ring := {|
  rig_map := {| morphism := ut2_diag1; proper_morphism := ut2_diag1_proper |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros [[a b] c] [[a' b'] c']; reflexivity. Qed.

(*
 Exercising the universal property on it separates one from zero in
 the quotient. 

 --------
 在商中运用其泛性质把一与零分开。
*)
Example crng_UT2_med_one@{u p +} :
  rig_map `1 (unique_obj (crng_universal (UT2 : Rng@{u p}) Int_CRng
                            ut2_diag1_hom))
    (rig_one UT2) = 1%Z := eq_refl.

Theorem Commutativize_UT2_nonzero@{u p +} :
  @equiv (carrier (rig_setoid (Commutativize (UT2 : Rng@{u p})))) _
    (rig_one UT2) (rig_zero UT2) → False.
Proof.
  intro H.
  pose proof (proper_morphism
                (rig_map `1 (unique_obj
                               (crng_universal UT2 Int_CRng ut2_diag1_hom)))
                _ _ H) as E.
  simpl in E; discriminate E.
Qed.
