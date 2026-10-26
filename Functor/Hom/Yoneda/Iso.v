Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Theory.Sheaf.
Require Import Category.Functor.Hom.Yoneda.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(**
* Representably isomorphic objects

    Riehl, “Category Theory in Context”, 2nd ed., §2.3 (printed p. 67):
    the opening definition — two objects are REPRESENTABLY ISOMORPHIC
    when their represented functors are naturally isomorphic, in either
    variance — and Proposition 2.3.1
    [riehl:2.3:def-representable-isomorphism, riehl:2.3:prop1]: the
    three kinds of data
      (i)   an isomorphism x ≅ y,
      (ii)  a natural isomorphism C(−,x) ≅ C(−,y),
      (iii) a natural isomorphism C(y,−) ≅ C(x,−)
    correspond, because the Yoneda embeddings are fully faithful and so
    preserve, reflect, and CREATE isomorphisms — the explicit mutually
    inverse pair underlying an α as in (ii) being α_x(id_x) and
    (α⁻¹)_y(id_y).
    nLab: https://ncatlab.org/nlab/show/Yoneda+embedding

    Everything here is assembly of parts long in tree, composed for the
    first time: [FullyFaithful] (Theory/Functor.v) instantiated at the
    embeddings [Curried_CoHom]/[Curried_Hom] via [Yoneda_Full] and
    [Yoneda_Faithful] (Functor/Hom.v) gives reflection; [fobj_iso]
    (Theory/Functor.v) gives preservation; and the CREATION strength —
    Riehl's actual proposition, a bijection of DATA and not merely a
    pair of implications — is the setoid isomorphism
    [representable_iso_setoid] between isomorphisms x ≅ y and natural
    isomorphisms [Hom ─,x] ≅ [Hom ─,y] — proved for the contravariant
    variance, which is the bijection Riehl's proposition names (the
    covariant leg is delivered as the biconditional
    [iso_iff_corepresentably_iso] only).  One round trip is
    [Yoneda_Embedding]'s [iso_from_to] leg read pointwise at each of
    the two legs; the other is the identity laws.

    The file also exports [repr_pair_iso] — the explicit-inverse-pair
    construction that Structure/UniversalProperty.v had inlined at its
    [univ_property_unique] since that file's beginning (the issue's
    “library defect”): given isomorphisms of both [Hom c,─] and
    [Hom v,─] with one and the same F, the objects c and v are
    isomorphic, by evaluating the composite transformations at the
    identity.  Structure/UniversalProperty.v now consumes it. 

--------
* 可表示的同构对象

Riehl，“语境中的范畴论”，第二版，§2.3（印刷第 67 页）：
 开放定义——两个对象是可表示同构的
 当它们所代表的函子自然同构时，无论是
 方差——以及命题 2.3.1
 [riehl:2.3:def-representable-isomorphism, riehl:2.3:prop1]：
 三种数据
 (i) 同构 x ≅ y，
 (ii) 自然同构 C(−,x) ≅ C(−,y)，
 (iii) 自然同构 C(y,−) ≅ C(x,−)
 对应，因为米田嵌入是完全忠实的，所以
 保留、反映和创建同构——显式的相互
 α 下的逆对，如 (ii) 中的 α_x(id_x) 和
 (α⁻1)_y(id_y)。 
nLab：https://ncatlab.org/nlab/show/Yoneda+embedding

这里的一切都是长在树上的部件的组装，为
 第一次：[FullyFaithful]（Theory/Functor.v）在
 通过 [Yoneda_Full] 嵌入 [Curried_CoHom]/[Curried_Hom] 和
 [Yoneda_Faithful] (Functor/Hom.v) 给出反射； 保护6X
 (Theory/Functor.v) 给出保存； 以及创造的力量——
 Riehl 的实际命题是 DATA 的双射而不仅仅是
 一对含义 — 是 setoid 同构
 同构 x ≅ y 和自然之间的 [representable_iso_setoid]
 同构 [Hom ─,x] ≅ [Hom ─,y] — 证明逆变
 方差，这是双射 Riehl 的命题名称（
 协变腿作为双条件传递
 仅限 [iso_iff_corepresentably_iso]）。 一个往返行程是
 [Yoneda_Embedding] 的 [iso_from_to] 腿在每个点逐点读取
 两条腿； 另一个是身份法。

该文件还导出 [repr_pair_iso] — 显式逆对
 Structure/UniversalProperty.v 已内联在其
 [univ_property_unique] 自该文件开始以来（问题是
 “库缺陷”）：给出 [Hom c,─] 和 [Hom c,─] 的同构
 [Hom v,─] 具有一个和 F 相同的对象 c 和 v 是
 同构，通过评估复合变换
 身份。 Structure/UniversalProperty.v 现在使用它。 
*)

(** ** The Yoneda embeddings are fully faithful, in both variances  / ** 米田嵌入在两个方差中都是完全忠实的*)

Section RepresentablyIso.

Context {C : Category}.

(*
[Curried_CoHom C] is [Curried_Hom C^op] by definition, but typeclass
   resolution does not unfold definitions; these instances make the
   contravariant embedding's full faithfulness available by name. 

--------
根据定义，[Curried_CoHom C] 是 [Curried_Hom C^op]，但是类型类
 决议没有展开定义； 这些实例使得
 逆变嵌入的完全忠实性可通过名称获得。 
*)
#[export] Instance CoYoneda_Faithful : Faithful (Curried_CoHom C) :=
  Yoneda_Faithful C^op.

#[export] Instance CoYoneda_Full : Full (Curried_CoHom C) :=
  Yoneda_Full C^op.

(*
An isomorphism read in the opposite category, with the two triangle
   laws exchanged. 

--------
同构读入相反的范畴，用两个三角形
 交换了法律。 
*)
Definition iso_op {x y : C} (i : x ≅ y) : @Isomorphism C^op y x := {|
  to := to i : @hom C^op y x;
  from := from i;
  iso_to_from := iso_from_to i;
  iso_from_to := iso_to_from i
|}.

(** ** The predicate, in Riehl's orientations  / ** 谓词，在里尔的取向中*)

(*
Two objects are representably isomorphic when both represented
   functors agree up to natural isomorphism: C(−,x) ≅ C(−,y) in
   presheaves AND C(y,−) ≅ C(x,−) in copresheaves (Riehl's directions;
   either component determines the other through x ≅ y below). 

--------
当两个对象都表示时，它们是可表示同构的
 函子符合自然同构： C(−,x) ≅ C(−,y) 中
 预滑轮 AND C(y,−) ≅ C(x,−) 位于预滑轮中（Riehl 方向；
 任一分量通过下面的 x ≅ y 决定另一个分量）。 
*)
Definition ContravariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y].

Definition CovariantRepresentableIso (x y : C) : Type :=
  @Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─].

Definition RepresentablyIsomorphic (x y : C) : Type :=
  ContravariantRepresentableIso x y * CovariantRepresentableIso x y.

(** ** The two biconditionals: reflection composed with preservation  / ** 两个双条件：反射与保留组合*)

(*
Contravariant: x ≅ y exactly when [Hom ─,x] ≅ [Hom ─,y].  The
   forward map is the embedding's action on isomorphisms; the backward
   map is [FullyFaithful] at [Curried_CoHom] — the instantiation issue
   #942 records as never before taken. 

--------
逆变：当 [Hom ─,x] ≅ [Hom ─,y] 时 x ≅ y。 的
 前向映射是嵌入对同构的作用； 落后的
 地图是 [FullyFaithful] 和 [Curried_CoHom] — 实例化问题
 第942章 前所未有的记录 
*)
Definition iso_iff_representably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]).
Proof.
  split.
  - exact (@fobj_iso _ _ (Curried_CoHom C) x y).
  - exact (@FullyFaithful _ _ (Curried_CoHom C) _ _ x y).
Defined.

(*
Covariant twin: x ≅ y exactly when [Hom y,─] ≅ [Hom x,─], through
   the opposite category. 

--------
协变孪生：x ≅ y 恰好当 [Hom y,─] ≅ [Hom x,─] 时，通过
 相反的类别。 
*)
Definition iso_iff_corepresentably_iso (x y : C) :
  iffT (x ≅ y) (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split.
  - intros i.
    exact (@fobj_iso _ _ (Curried_Hom C) y x (iso_op i)).
  - intros α.
    pose (i := @FullyFaithful _ _ (Curried_Hom C) _ _ y x α).
    exact {| to := to i : x ~{C}~> y
           ; from := from i
           ; iso_to_from := iso_from_to i
           ; iso_from_to := iso_to_from i |}.
Defined.

(*
Isomorphic objects are representably isomorphic in both variances at
   once, and the two variances agree with each other. 

--------
同构对象在两个方差中都具有同构性
 一次，并且两个方差一致。 
*)
Definition representably_isomorphic_of_iso {x y : C} (i : x ≅ y) :
  RepresentablyIsomorphic x y :=
  (fst (iso_iff_representably_iso x y) i,
   fst (iso_iff_corepresentably_iso x y) i).

(*
...and conversely, either representable isomorphism recovers the
   isomorphism of objects. 

--------
...相反，任一可表示的同构都恢复了
 对象的同构。 
*)
Definition iso_of_representably_isomorphic {x y : C}
  (r : RepresentablyIsomorphic x y) : x ≅ y :=
  snd (iso_iff_representably_iso x y) (fst r).

Definition representably_iso_variances_agree (x y : C) :
  iffT (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y])
       (@Isomorphism (@Copresheaves C Sets) [Hom y,─] [Hom x,─]).
Proof.
  split; intros α.
  - exact (fst (iso_iff_corepresentably_iso x y)
             (snd (iso_iff_representably_iso x y) α)).
  - exact (fst (iso_iff_representably_iso x y)
             (snd (iso_iff_corepresentably_iso x y) α)).
Defined.

End RepresentablyIso.

(**
** The reusable inverse pair for representability arguments

    Two representations of one functor have isomorphic representing
    objects, by the explicit inverse pair: compose the legs, pull each
    composite back through [Yoneda_Embedding']'s two-sided inverse —
    evaluation at the identity — and the triangle laws follow from the
    isomorphisms' own round trips.  This is verbatim the construction
    Structure/UniversalProperty.v's [univ_property_unique] had inlined;
    it now lives here, generalized over the represented functor, and
    that file consumes it. 

--------
** 可重复使用的可表示性参数的逆对

 一个函子的两个表示具有同构表示
 对象，通过显式逆对：组成腿，拉动每条腿
 通过 [Yoneda_Embedding'] 的双面反转复合背面 —
 恒等式的评估——三角定律遵循
 同构自身的往返行程。 这是逐字构造
 Structure/UniversalProperty.v 的 [univ_property_unique] 已内联；
 它现在住在这里，泛化到所代表的函子上，并且
 该文件消耗它。 
*)

Definition repr_pair_iso {C : Category} {F : C ⟶ Sets} {c v : C}
  (b1 : @Isomorphism (@Copresheaves C Sets) [Hom c,─] F)
  (b2 : @Isomorphism (@Copresheaves C Sets) [Hom v,─] F) : c ≅ v.
Proof.
  unshelve econstructor.
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C v c)
             (from b1 ∘ to b2)).
  - exact (@two_sided_inverse _ _ _ _ (Yoneda_Embedding' C c v)
             (from b2 ∘ to b1)).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C v c v (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b1));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b2 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b2));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
  - abstract(apply (@fmap_inj _ _ (Curried_Hom C) _);
    set (j := ( _ ( compose  _ _)));
    set (j' := ( _ ( compose  _ _)));
    change j with (op j);
    change j' with (op j');
    set (m := @fmap_comp _ _ C c v c (op j') (op j));
    rewrite m;
    unfold op, j, j';
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C v c) (from b1 ∘ b2));
    rewrite (@is_right_inverse  _ _ _ _ (Yoneda_Embedding' C c v) (from b2 ∘ b1));
    simpl; intros x f; unfold op; rewrite id_right;
    set (ab := (iso_to_from b2));
    simpl in ab; rewrite ab;
    rewrite (@fmap_id _ _ F x (to b1 x f));
    simpl; clear ab;
    set (ab' := (iso_from_to b1));
    simpl in ab'; rewrite ab'; rewrite id_left;
    reflexivity).
Defined.

(** ** Creation: the bijection of data (Riehl's Proposition 2.3.1)  / ** 创建：数据的双射（Riehl 命题 2.3.1）*)

(* An isomorphism read back from the opposite category.  / 同构从相反的范畴读回。*)
Definition iso_unop {C : Category} {x y : C}
  (i : @Isomorphism C^op x y) : x ≅ y := {|
  to := from i : x ~{C}~> y;
  from := to i;
  iso_to_from := iso_to_from i;
  iso_from_to := iso_from_to i
|}.

(*
The explicit inverse pair carried by a natural isomorphism
   α : [Hom ─,x] ≅ [Hom ─,y] — Riehl's α_x(id_x) and (α⁻¹)_y(id_y) —
   obtained with NO new proof content: [repr_pair_iso] at C^op, with
   the second representation the identity.  [eval_iso_to] and
   [eval_iso_from] record that the components are the evaluations at
   the identity, up to the identity laws. 

--------
自然同构所携带的显式逆对
 α : [Hom ─,x] ≅ [Hom ─,y] — Riehl 的 α_x(id_x) 和 (α⁻1)_y(id_y) —
 在没有新证明内容的情况下获得：[repr_pair_iso] at C^op，
 第二个代表身份。 [eval_iso_to] 和
 [eval_iso_from] 记录组件的评估结果为
 身份，直至身份法。 
*)
Definition eval_iso {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) : x ≅ y :=
  iso_unop (@repr_pair_iso C^op (fobj[Curried_CoHom C] y) x y α iso_id).

Lemma eval_iso_to {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  to (eval_iso α) ≈ transform[to α] x id.
Proof. simpl; cat. Qed.

Lemma eval_iso_from {C : Category} {x y : C}
  (α : @Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) :
  from (eval_iso α) ≈ transform[from α] y id.
Proof. simpl; cat. Qed.

(*
The setoid of isomorphisms x ≅ y is isomorphic IN Sets to the setoid
   of natural isomorphisms [Hom ─,x] ≅ [Hom ─,y]: the embedding
   CREATES isomorphisms, as a bijection of data with both round trips.
   Forward: the embedding's action.  Backward: evaluation at the
   identity ([eval_iso]). 

--------
同构 x ≅ y 的集合是同构 IN 集合为集合
 自然同构 [Hom ─,x] ≅ [Hom ─,y]：嵌入
 创建同构，作为具有两次往返的数据双射。 
前向：嵌入的动作。 向后：评估
 身份（[eval_iso]）。 
*)
Program Definition representable_iso_setoid {C : Category} (x y : C) :
  (x ≅ y) ≊ (@Isomorphism (@Presheaves C Sets) [Hom ─,x] [Hom ─,y]) := {|
  to := {| morphism := fst (iso_iff_representably_iso x y) |};
  from := {| morphism := eval_iso |}
|}.
Next Obligation.
  intros C x y i j [Ht Hf]; split; simpl.
  - intros c g; unfold op; now rewrite Ht.
  - intros c g; unfold op; now rewrite Hf.
Qed.
Next Obligation.
  intros C x y α β [Ht Hf]; split; simpl.
  - now rewrite (Ht x id).
  - exact (Hf y (id ∘ id)).
Qed.
Next Obligation.
  intros C x y α; split; simpl.
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C x y) (to α) c g).
  - intros c g; unfold op; rewrite id_right.
    exact (iso_from_to (Yoneda_Embedding C y x) (from α) c g).
Qed.
Next Obligation.
  intros C x y i; split; simpl; cat.
Qed.
