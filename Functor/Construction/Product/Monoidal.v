Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Product.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** Monoidal structure on a product of functors.  / 函子乘积的幺半群结构。*)

(*
nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   Given (lax/strong) monoidal functors F : C ⟶ J and G : D ⟶ K between
   monoidal categories, the pointwise product functor

       F ∏⟶ G : C ∏ D ⟶ J ∏ K

   is again (lax/strong) monoidal for the product monoidal structures on
   C ∏ D and J ∏ K (see Structure.Monoidal.Product). The unit comparison is
   the pair of the unit comparisons of F and G, and the tensor comparison is
   the componentwise pair of their tensor comparisons,

       η      = (η_F, η_G)        : I ~> (F ∏⟶ G) I,
       μ_{..} = (μ^F_{..}, μ^G_{..}).

   Because equivalence in a product category is the componentwise conjunction
   (see Construction.Product), each coherence square in J ∏ K splits into the
   corresponding squares in J and in K, so the laws hold whenever they hold
   for F and G; if both are strong (resp. strict) so is the product.

   Conversely, monoidality of F ∏⟶ G can be projected back onto each factor
   by feeding the unit I into the unused slot: the [_proj1]/[_proj2]
   definitions recover monoidality of F and of G. This is the product (in the
   2-category MonCat / its lax variant) acting on monoidal functors. 

--------
nLab：https://ncatlab.org/nlab/show/monoidal+functor
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

给定（松/强）幺半群函子 F : C ⟶ J 和 G : D ⟶ K 之间
 幺半群范畴，点积函子

F ∏⟶ G : C ∏ D ⟶ J ∏ K

又是（松/强）幺半群的乘积幺半群结构
 C ∏ D 和 J ∏ K（请参见结构.Monoidal.Product）。 比较单位为
 F 和 G 的单位比较对，张量比较为
 它们的张量比较的分量对，

η = (η_F, η_G) : I ~> (F ∏⟶ G) I,
 μ_{..} = (μ^F_{..}, μ^G_{..})。

因为产品类别中的等价是组件方面的合取
 （参见 Construction.Product），J ∏ K 中的每个相干平方都分裂为
 J 和 K 中对应的平方，因此只要定律成立，它们就成立
 对于F和G； 如果两者都很强（或严格），那么产品也一样。

相反，F ∏⟶ G 的单态性可以投影回每个因子
 将单元 I 插入未使用的插槽：[_proj1]/[_proj2]
 定义恢复了 F 和 G 的单一性。这是乘积（在
 作用于幺半群函子的 2 类 MonCat/其松散变体。 
*)

Section ProductMonoidal.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {J : Category}.
Context `{@Monoidal J}.
Context {K : Category}.
Context `{@Monoidal K}.

Context {F : C ⟶ J}.
Context {G : D ⟶ K}.

#[local] Obligation Tactic := program_simpl.

(*
The tensor comparison μ for F ∏⟶ G as a natural isomorphism, built
   componentwise from the tensor comparisons of F (via O) and of G (via P). 

--------
F ∏⟶ G 作为自然同构的张量比较 μ，构建
 来自 F（通过 O）和 G（通过 P）的张量比较的分量。 
*)
Program Definition ProductFunctor_Monoidal_ap_functor_iso
  (O : MonoidalFunctor F) (P : MonoidalFunctor G) :
    (⨂) ◯ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ≅[[(C ∏ D) ∏ (C ∏ D), J ∏ K]] F ∏⟶ G ◯ (⨂) :=
  {|
    to := {| transform := _; naturality := _; naturality_sym := _ |};
    from := {| transform := _; naturality := _; naturality_sym := _ |};
    iso_to_from := _;
    iso_from_to := _;
  |}.
Next Obligation.
  simpl. split;
    exact (transform[to ap_functor_iso] (_, _)).
Defined.
Next Obligation.
  simpl. split;
    apply (naturality (to ap_functor_iso) (_, _)).
Qed.
Next Obligation.
  simpl. split;
    apply (naturality_sym (to ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split; exact (transform[from ap_functor_iso] (_, _)).
Defined.
Next Obligation.
  simpl. split;
    apply (naturality (from ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split;
    apply (naturality_sym (from ap_functor_iso) (_, _) (_, _) (_, _)).
Qed.
Next Obligation.
  simpl. split.
  - sapply (iso_to_from (ap_functor_iso[O])).
  - sapply (iso_to_from (ap_functor_iso[P])).
Qed.
Next Obligation.
  simpl. split.
  - apply (iso_from_to (ap_functor_iso[O]) (_, _)).
  - apply (iso_from_to (ap_functor_iso[P]) (_, _)).
Qed.

(*
Strong monoidality is closed under the product of functors: if F and G are
   strong monoidal then so is F ∏⟶ G, with all comparisons formed pairwise. 

--------
强幺单性在函子的乘积下是封闭的：如果 F 和 G 是
 强幺半群，那么 F ∏⟶ G 也是如此，所有比较都是成对形成的。 
*)
Program Definition ProductFunctor_Monoidal :
  MonoidalFunctor F → MonoidalFunctor G
    → MonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
  pure_iso := _;
  ap_functor_iso := ProductFunctor_Monoidal_ap_functor_iso _ _;
  pure_iso_left  := _;
  pure_iso_right := _;
  ap_iso_assoc := _;
  monoidal_unit_left := _;
  monoidal_unit_right := _;
  monoidal_assoc := _
|}.
Next Obligation.
  unshelve esplit; split; apply pure_iso.
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_iso_left || apply pure_iso_right.
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_iso_left || apply pure_iso_right.
Defined.
Next Obligation.
  intros; isomorphism; split; apply ap_iso_assoc.
Qed.
Next Obligation.
  simpl.
  split; apply monoidal_unit_left.
Qed.
Next Obligation.
  simpl.
  split; apply monoidal_unit_right.
Qed.
Next Obligation.
  simpl.
  intros; split; apply monoidal_assoc.
Qed.

(*
Projection onto the first factor: the tensor comparison of F recovered from
   that of F ∏⟶ G by setting the second components to the unit I and taking the
   first component (fst) of each resulting pair. 

--------
投影到第一个因子：从 F 恢复的张量比较
 F ∏⟶ G 的第二个分量设置为单位 I 并取
 每个结果对的第一个分量 (fst)。 
*)
Program Definition ProductFunctor_Monoidal_proj1_ap_functor_iso
  (P : MonoidalFunctor F ∏⟶ G) :
    (⨂) ◯ F ∏⟶ F ≅[[(C ∏ C), J]] F ◯ (⨂) :=
  {|
    to := {| transform := _; naturality := _; naturality_sym := _ |};
    from := {| transform := _; naturality := _; naturality_sym := _ |};
    iso_to_from := _;
    iso_from_to := _;
  |}.
Next Obligation.
  exact (fst (transform[to (ap_functor_iso[P])] ((o, I), (o0, I)))).
Defined.
Next Obligation.
  simpl in *.
  epose proof (@naturality _ _ _ _ (to (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  epose proof (@naturality_sym _ _ _ _ (to (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  apply (fst (transform[from (ap_functor_iso[P])] ((_, I), (_, I)))).
Defined.
Next Obligation.
  simpl in *.
  epose proof (@naturality _ _ _ _ (from (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  simpl in *.
  epose proof (@naturality_sym _ _ _ _ (from (ap_functor_iso[P]))).
  simpl in X.
  epose proof (X (_, I, (_, I)) (_, I, (_, I))).
  simpl in X0.
  clear X.
  epose proof (X0 ((_, id), (_, id))).
  simpl in X.
  apply X.
Qed.
Next Obligation.
  apply (iso_to_from (ap_functor_iso[P]) (_, I, (_, I))).
Qed.
Next Obligation.
  apply (iso_from_to (ap_functor_iso[P]) (_, I, (_, I))).
Qed.

(*
Strong monoidality of F ∏⟶ G projects to strong monoidality of F. The
   associativity obligation uses naturality of the tensor comparison together
   with [unit_left] to discard the I ⨂ I slots that arise from the product
   unit, reducing the square to the one already proved for F ∏⟶ G. 

--------
F ∏⟶ G 的强单一性投射到 F 的强单一性。 
结合性义务使用张量比较的自然性
 使用 [unit_left] 丢弃产品中产生的 I ⨂ I 插槽
 单位，将平方减少到已经证明的 F ∏⟶ G 的平方。 
*)
Program Definition ProductFunctor_Monoidal_proj1 :
  MonoidalFunctor (F ∏⟶ G) → MonoidalFunctor F := fun P => {|
  pure_iso := _;
  ap_functor_iso := ProductFunctor_Monoidal_proj1_ap_functor_iso P;
  pure_iso_left  := _;
  pure_iso_right := _;
  ap_iso_assoc := _;
  monoidal_unit_left := _;
  monoidal_unit_right := _;
  monoidal_assoc := _
|}.
Next Obligation.
  isomorphism.
  - apply (fst (to (@pure_iso _ _ _ _ _ P))).
  - apply (fst (from (@pure_iso _ _ _ _ _ P))).
  - apply (fst (iso_to_from (@pure_iso _ _ _ _ _ P))).
  - apply (fst (iso_from_to (@pure_iso _ _ _ _ _ P))).
Defined.
Next Obligation.
  isomorphism.
  - apply (fst (to (@pure_iso_left _ _ _ _ _ P (x, I)))).
  - apply (fst (from (@pure_iso_left _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_to_from (@pure_iso_left _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_from_to (@pure_iso_left _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (fst (to (@pure_iso_right _ _ _ _ _ P (x, I)))).
  - apply (fst (from (@pure_iso_right _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_to_from (@pure_iso_right _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_from_to (@pure_iso_right _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (fst (to (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (from (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_left _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  apply (fst (@monoidal_unit_right _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  spose (fst (naturality (to ap_functor_iso[P])
                         ((x ⨂ y, I ⨂ I), (z, I))%object
                         ((x ⨂ y, I), (z, I))%object
                         ((id[x ⨂ y], to unit_left),
                          (id[z], id[I])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (fst (naturality (to ap_functor_iso[P])
                         ((x, I), (y ⨂ z, I ⨂ I))%object
                         ((x, I), (y ⨂ z, I))%object
                         ((id[x], id[I]),
                          (id[y ⨂ z], to unit_left)))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (fst (@monoidal_assoc _ _ _ _ _ P (x, I) (y, I) (z, I))).
Qed.

(*
Projection onto the second factor, dual to the proj1 case: the tensor
   comparison of G recovered by setting the first components to the unit I and
   taking the second component (snd) of each resulting pair. 

--------
投影到第二个因子，与 proj1 情况对偶：张量
 通过将第一个分量设置为单元 I 恢复的 G 的比较
 取每个结果对的第二个分量 (snd)。 
*)
Lemma ProductFunctor_Monoidal_proj2_ap_functor_iso :
  MonoidalFunctor F ∏⟶ G
    → (⨂) ◯ G ∏⟶ G ≅[[(D ∏ D), K]] G ◯ (⨂).
Proof.
  intros P.
  isomorphism.
  - transform. {
      intros [x y].
      exact (snd (transform[to (ap_functor_iso[P])] ((I, x), (I, y)))).
    }

    all:(try rename x into x0;
         try rename y into y0;
         try destruct x0 as [x y],
                      y0 as [z w],
                      f as [f g];
         try destruct A as [x y]; simpl).

    + exact (snd (naturality (to (ap_functor_iso[P]))
                             (I, x, (I, y)) (I, z, (I, w))
                             ((id, f), (id, g)))).

    + exact (snd (naturality_sym (to (ap_functor_iso[P]))
                                 (I, x, (I, y)) (I, z, (I, w))
                                 ((id, f), (id, g)))).
  - transform. {
      intros [x y].
      exact (snd (transform[from (ap_functor_iso[P])] ((I, x), (I, y)))).
    }

    all:(try rename x into x0;
         try rename y into y0;
         try destruct x0 as [x y],
                      y0 as [z w],
                      f as [f g];
         try destruct A as [x y]; simpl).

    + exact (snd (naturality (from (ap_functor_iso[P]))
                             (I, x, (I, y)) (I, z, (I, w))
                             ((id, f), (id, g)))).

    + exact (snd (naturality_sym (from (ap_functor_iso[P]))
                                 (I, x, (I, y)) (I, z, (I, w))
                                 ((id, f), (id, g)))).
  - destruct x; simpl.
    apply (iso_to_from (ap_functor_iso[P]) (I, o, (I, o0))).
  - destruct x; simpl.
    apply (iso_from_to (ap_functor_iso[P]) (I, o, (I, o0))).
Defined.

(*
Strong monoidality of F ∏⟶ G projects to strong monoidality of G, dual to
   ProductFunctor_Monoidal_proj1. 

--------
F ∏⟶ G 的强单调性投影到 G 的强单调性，对偶到
 ProductFunctor_Monoidal_proj1。 
*)
Program Definition ProductFunctor_Monoidal_proj2 :
  MonoidalFunctor (F ∏⟶ G) → MonoidalFunctor G := fun P => {|
  pure_iso            := _;
  ap_functor_iso      := ProductFunctor_Monoidal_proj2_ap_functor_iso P;
  pure_iso_left       := _;
  pure_iso_right      := _;
  ap_iso_assoc        := _;
  monoidal_unit_left  := _;
  monoidal_unit_right := _;
  monoidal_assoc      := _
|}.
Next Obligation.
  isomorphism.
  - apply (snd (to (@pure_iso _ _ _ _ _ P))).
  - apply (snd (from (@pure_iso _ _ _ _ _ P))).
  - apply (snd (iso_to_from (@pure_iso _ _ _ _ _ P))).
  - apply (snd (iso_from_to (@pure_iso _ _ _ _ _ P))).
Defined.
Next Obligation.
  isomorphism.
  - apply (snd (to (@pure_iso_left _ _ _ _ _ P (I, x)))).
  - apply (snd (from (@pure_iso_left _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_to_from (@pure_iso_left _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_from_to (@pure_iso_left _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (snd (to (@pure_iso_right _ _ _ _ _ P (I, x)))).
  - apply (snd (from (@pure_iso_right _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_to_from (@pure_iso_right _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_from_to (@pure_iso_right _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (snd (to (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (from (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (iso_to_from (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (iso_from_to (@ap_iso_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_left _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  apply (snd (@monoidal_unit_right _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  spose (snd (naturality (to ap_functor_iso[P])
                         ((I ⨂ I, x ⨂ y), (I, z))%object
                         ((I, x ⨂ y), (I, z))%object
                         ((to unit_left, id[x ⨂ y]),
                          (id[I], id[z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (snd (naturality (to ap_functor_iso[P])
                         ((I, x), (I ⨂ I, y ⨂ z))%object
                         ((I, x), (I, y ⨂ z))%object
                         ((id[I], id[x]),
                          (to unit_left, id[y ⨂ z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (snd (@monoidal_assoc _ _ _ _ _ P (I, x) (I, y) (I, z))).
Qed.

(*
The lax tensor comparison μ for F ∏⟶ G as a natural transformation (no
   invertibility required), built componentwise from the comparisons of F and
   G. This is the lax analogue of ProductFunctor_Monoidal_ap_functor_iso. 

--------
F ∏⟶ G 作为自然变换的松弛张量比较 μ（无
 需要可逆性），根据 F 和 F 的比较按组件构建
 G. 这是 ProductFunctor_Monoidal_ap_functor_iso 的松散模拟。 
*)
Lemma ProductFunctor_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor F → LaxMonoidalFunctor G
    → (⨂) ◯ (F ∏⟶ G) ∏⟶ (F ∏⟶ G) ⟹ F ∏⟶ G ◯ (⨂).
Proof.
  intros O P.

  transform. {
    intros [[x z] [y w]]; split.
    - exact (transform[ap_functor_nat] (x, y)).
    - exact (transform[ap_functor_nat] (z, w)).
  }

  all:(try destruct x as [[x1 x2] [y1 y2]],
                    y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  - split.
    + abstract apply (naturality ap_functor_nat (x1, y1)).
    + abstract apply (naturality ap_functor_nat (x2, y2)).

  - split.
    + abstract apply (naturality_sym ap_functor_nat
                                     (x1, y1) (z1, w1) (f1a, f2a)).
    + abstract apply (naturality_sym ap_functor_nat
                                     (x2, y2) (z2, w2) (f1b, f2b)).
Defined.

(*
Lax monoidality is closed under the product of functors: if F and G are lax
   monoidal then so is F ∏⟶ G, with all comparisons formed pairwise. This is
   the lax analogue of ProductFunctor_Monoidal. 

--------
松弛幺半性在函子的乘积下是封闭的：如果 F 和 G 是松弛的
 幺半群则 F ∏⟶ G 也是如此，所有比较都是成对形成的。 这是
 ProductFunctor_Monoidal 的松散模拟。 
*)
Program Definition ProductFunctor_LaxMonoidal :
  LaxMonoidalFunctor F → LaxMonoidalFunctor G
    → LaxMonoidalFunctor (F ∏⟶ G) := fun _ _ => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_ap_functor_nat _ _;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
|}.
Next Obligation.
  unshelve esplit; apply lax_pure.
Defined.
Next Obligation.
  intros; isomorphism; split; apply pure_left || apply pure_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply pure_left || apply pure_right.
Qed.
Next Obligation.
  intros; isomorphism; split; apply ap_assoc.
Qed.
Next Obligation. intros; split; apply lax_monoidal_unit_left. Qed.
Next Obligation. intros; split; apply lax_monoidal_unit_right. Qed.
Next Obligation. intros; split; apply lax_monoidal_assoc. Qed.

(*
Lax analogue of ProductFunctor_Monoidal_proj1_ap_functor_iso: the lax tensor
   comparison of F recovered from that of F ∏⟶ G by setting the second
   components to the unit I and taking the first component (fst) of each pair.
   Here no invertibility is assumed, so this is a bare natural transformation. 

--------
ProductFunctor_Monoidal_proj1_ap_functor_iso 的松弛类似物：松弛张量
 通过设置第二个参数从 F ∏⟶ G 恢复的 F 的比较
 单元 I 的分量并取每对的第一个分量 (fst)。 
这里没有假设可逆性，因此这是一个纯粹的自然变换。 
*)
Lemma ProductFunctor_LaxMonoidal_proj1_ap_functor_nat :
  LaxMonoidalFunctor F ∏⟶ G
    → (⨂) ◯ F ∏⟶ F ⟹ F ◯ (⨂).
Proof.
  intros P.

  transform. {
    intros [x y].
    exact (fst (transform[ap_functor_nat[P]] ((x, I), (y, I)))).
  }

  all:(try rename x into x0;
       try rename y into y0;
       try destruct x0 as [x y],
                    y0 as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  - exact (fst (naturality (ap_functor_nat[P])
                           (x, I, (y, I)) (z, I, (w, I))
                           ((f, id), (g, id)))).

  - exact (fst (naturality_sym (ap_functor_nat[P])
                               (x, I, (y, I)) (z, I, (w, I))
                               ((f, id), (g, id)))).
Defined.

(*
Lax monoidality of F ∏⟶ G projects to lax monoidality of F, the lax analogue
   of ProductFunctor_Monoidal_proj1. The associativity obligation uses
   naturality of the tensor comparison together with [unit_left] to discard the
   I ⨂ I slots arising from the product unit, reducing to the square already
   proved for F ∏⟶ G. 

--------
F ∏⟶ G 的松散单一性投射到 F 的松散单一性（松散类似物）
 ProductFunctor_Monoidal_proj1 的。 关联性义务使用
 张量比较的自然性与 [unit_left] 一起丢弃
 I ⨂ I 由产品单元产生的槽，已减少到平方
 证明了 F ∏⟶ G。 
*)
Program Definition ProductFunctor_LaxMonoidal_proj1 :
  LaxMonoidalFunctor (F ∏⟶ G) → LaxMonoidalFunctor F := fun P => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_proj1_ap_functor_nat P;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
|}.
Next Obligation.
  apply (fst (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  - apply (fst (to (@pure_left _ _ _ _ _ P (x, I)))).
  - apply (fst (from (@pure_left _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_to_from (@pure_left _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_from_to (@pure_left _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (fst (to (@pure_right _ _ _ _ _ P (x, I)))).
  - apply (fst (from (@pure_right _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_to_from (@pure_right _ _ _ _ _ P (x, I)))).
  - apply (fst (iso_from_to (@pure_right _ _ _ _ _ P (x, I)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (fst (to (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (from (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (iso_to_from (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
  - apply (fst (iso_from_to (@ap_assoc _ _ _ _ _ P (x, I) (y, I) (z, I)))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_left _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  apply (fst (@lax_monoidal_unit_right _ _ _ _ _ P (x, I))).
Qed.
Next Obligation.
  spose (fst (naturality (ap_functor_nat[P])
                         ((x ⨂ y, I ⨂ I), (z, I))%object
                         ((x ⨂ y, I), (z, I))%object
                         ((id[x ⨂ y], to unit_left),
                          (id[z], id[I])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (fst (naturality (ap_functor_nat[P])
                         ((x, I), (y ⨂ z, I ⨂ I))%object
                         ((x, I), (y ⨂ z, I))%object
                         ((id[x], id[I]),
                          (id[y ⨂ z], to unit_left)))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (fst (@lax_monoidal_assoc _ _ _ _ _ P (x, I) (y, I) (z, I))).
Qed.

(*
Lax analogue of the proj2 projection, dual to
   ProductFunctor_LaxMonoidal_proj1_ap_functor_nat: the lax tensor comparison of
   G recovered by setting the first components to the unit I and taking the
   second component (snd) of each pair. 

--------
proj2 投影的松散模拟，双
 ProductFunctor_LaxMonoidal_proj1_ap_functor_nat：松弛张量比较
 G 通过将第一个分量设置为单元 I 并取
 每对的第二个分量 (snd)。 
*)
Lemma ProductFunctor_LaxMonoidal_proj2_ap_functor_nat :
  LaxMonoidalFunctor F ∏⟶ G
    → (⨂) ◯ G ∏⟶ G ⟹ G ◯ (⨂).
Proof.
  intros P.

  transform. {
    intros [x y].
    exact (snd (transform[ap_functor_nat[P]] ((I, x), (I, y)))).
  }

  all:(try rename x into x0;
       try rename y into y0;
       try destruct x0 as [x y],
                    y0 as [z w],
                    f as [f g];
       try destruct A as [x y]; simpl).

  - exact (snd (naturality (ap_functor_nat[P])
                           (I, x, (I, y)) (I, z, (I, w))
                           ((id, f), (id, g)))).

  - exact (snd (naturality_sym (ap_functor_nat[P])
                               (I, x, (I, y)) (I, z, (I, w))
                               ((id, f), (id, g)))).
Defined.

(*
Lax monoidality of F ∏⟶ G projects to lax monoidality of G, dual to
   ProductFunctor_LaxMonoidal_proj1. 

--------
F ∏⟶ G 的松弛单一性投影到 G 的松弛单一性，对偶到
 ProductFunctor_LaxMonoidal_proj1。 
*)
Program Definition ProductFunctor_LaxMonoidal_proj2 :
  LaxMonoidalFunctor (F ∏⟶ G) → LaxMonoidalFunctor G := fun P => {|
  lax_pure                := _;
  ap_functor_nat          := ProductFunctor_LaxMonoidal_proj2_ap_functor_nat P;
  pure_left               := _;
  pure_right              := _;
  ap_assoc                := _;
  lax_monoidal_unit_left  := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc      := _
|}.
Next Obligation.
  apply (snd (@lax_pure _ _ _ _ _ P)).
Defined.
Next Obligation.
  isomorphism.
  - apply (snd (to (@pure_left _ _ _ _ _ P (I, x)))).
  - apply (snd (from (@pure_left _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_to_from (@pure_left _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_from_to (@pure_left _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (snd (to (@pure_right _ _ _ _ _ P (I, x)))).
  - apply (snd (from (@pure_right _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_to_from (@pure_right _ _ _ _ _ P (I, x)))).
  - apply (snd (iso_from_to (@pure_right _ _ _ _ _ P (I, x)))).
Qed.
Next Obligation.
  isomorphism.
  - apply (snd (to (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (from (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (iso_to_from (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
  - apply (snd (iso_from_to (@ap_assoc _ _ _ _ _ P (I, x) (I, y) (I, z)))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_left _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  apply (snd (@lax_monoidal_unit_right _ _ _ _ _ P (I, x))).
Qed.
Next Obligation.
  spose (snd (naturality (ap_functor_nat[P])
                         ((I ⨂ I, x ⨂ y), (I, z))%object
                         ((I, x ⨂ y), (I, z))%object
                         ((to unit_left, id[x ⨂ y]),
                          (id[I], id[z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  spose (snd (naturality (ap_functor_nat[P])
                         ((I, x), (I ⨂ I, y ⨂ z))%object
                         ((I, x), (I, y ⨂ z))%object
                         ((id[I], id[x]),
                          (to unit_left, id[y ⨂ z])))) as X.
  rewrite !fmap_id in X.
  rewrite !bimap_id_id in X.
  rewrite !fmap_id in X.
  rewrite id_left, id_right in X.
  rewrites.

  apply (snd (@lax_monoidal_assoc _ _ _ _ _ P (I, x) (I, y) (I, z))).
Qed.

End ProductMonoidal.

(*
A different projection: rather than splitting a product F ∏⟶ G of two
   functors, here we start from a single functor P : C ∏ J ⟶ D ∏ K on product
   categories and restrict it to each factor. [ProductFunctor_fst P : C ⟶ D]
   sends x to fst (P (x, I)) and [ProductFunctor_snd P : J ⟶ K] sends x to
   snd (P (I, x)) (see Functor.Construction.Product). When P is lax monoidal for
   the product monoidal structures, each restriction is again lax monoidal; the
   tensor comparison must be corrected by [unit_left] : I ⨂ I ≅ I to collapse
   the unit fed into the unused slot, hence the [bimap … unit_left] factors and
   the [unit_identity] rewrites in the proofs below. 

--------
不同的投影：而不是将乘积 F ∏⟶ G 分成两个
 函子，这里我们从单个函子 P 开始：C ∏ J ⟶ D ∏ K 的乘积
 类别并将其限制为每个因素。 保护0X
 将 x 发送到 fst (P (x, I)) 并且 [ProductFunctor_snd P : J ⟶ K] 将 x 发送到
 snd (P (I, x)) （参见 Functor.Construction.Product）。 当 P 是松弛幺半群时
 乘积幺半群结构，每个限制又是宽松的幺半群； 的
 张量比较必须通过 [unit_left] 进行纠正： I ⨂ I ≅ I 才能崩溃
 该单元馈入未使用的插槽，因此 [bimap … unit_left] 因子和
 [unit_identity] 在下面的校样中重写。 
*)
Section ProductMonoidalProj.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {J : Category}.
Context `{@Monoidal J}.
Context {K : Category}.
Context `{@Monoidal K}.

Variable (P : (C ∏ J) ⟶ D ∏ K).

(*
Lax tensor comparison for the first restriction ProductFunctor_fst P. The
   comparison of P maps fst (P (x, I)) ⨂ fst (P (y, I)) into fst (P (x ⨂ y,
   I ⨂ I)); precomposing with [bimap id (to unit_left)] inside P collapses the
   I ⨂ I in the unused J-slot back to I, landing in fst (P (x ⨂ y, I)). 

--------
第一个限制 ProductFunctor_fst P 的宽松张量比较。 
P 的比较将 fst (P (x, I)) ⨂ fst (P (y, I)) 映射为 fst (P (x ⨂ y,
 我 ⨂ 我)); 在 P 内使用 [bimap id (to unit_left)] 进行预组合会折叠
 I ⨂ I 在未使用的 J 槽中回到 I，落在 fst (P (x ⨂ y, I)) 中。 
*)
Lemma ProductFunctor_fst_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor P
    → (⨂) ◯ (ProductFunctor_fst P) ∏⟶ (ProductFunctor_fst P)
          ⟹ ProductFunctor_fst P ◯ (⨂).
Proof.
  intro L.
  transform; simpl.
  - intros [x y]; simpl.
    exact (fst (bimap id (to unit_left) ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((x, I), (y, I)))).
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (x1, I, (x2, I)) (y1, I, (y2, I))
                           ((f1, id), (f2, id)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite fst_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (x1, I, (x2, I)) (y1, I, (y2, I))
                           ((f1, id), (f2, id)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite fst_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite fst_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
Defined.

#[local] Obligation Tactic := program_simpl.

(*
ProductFunctor_fst P is lax monoidal whenever P is: unit and coherence data
   are obtained by projecting P's structure at the unit I in the J-slot and
   correcting with [unit_left]. The associativity obligation reassociates using
   naturality of P's tensor comparison plus the [triangle_identity]. 

--------
ProductFunctor_fst P 是松弛幺半群，只要 P 是： 单位和相干数据
 通过将 P 的结构投影到 J 槽中的单元 I 来获得
 使用 [unit_left] 进行校正。 关联性义务使用重新关联
 P 的张量比较加上 [triangle_identity] 的自然性。 
*)
Program Definition ProductFunctor_fst_LaxMonoidal :
  LaxMonoidalFunctor P
    → LaxMonoidalFunctor (ProductFunctor_fst P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_fst_LaxMonoidal_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  exact (fst (@lax_pure _ _ _ _ _ L)).
Defined.
Next Obligation.
  destruct (@pure_left _ _ _ _ _ L (x, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (I ⨂ x, I ⨂ I)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.to unit_left))).
    + exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.from unit_left))).
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_to_from.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_from_to.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (x, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (x ⨂ I, I ⨂ I)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.to unit_left))).
    + exact (fst (@bimap _ _ _ P _ _ _ _ id (Isomorphism.from unit_left))).
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_to_from.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_from_to.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (x, I) (y, I) (z, I));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (fst (P (x ⨂ y ⨂ z, I ⨂ I ⨂ I)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (fst (@bimap _ _ _ P _ _ _ _ id
                         (Isomorphism.to unit_left ∘
                          Isomorphism.to unit_left))).
    + exact (fst (@bimap _ _ _ P _ _ _ _ id
                         (Isomorphism.from unit_left ∘
                          Isomorphism.from unit_left))).
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc _ (Isomorphism.from _)).
      rewrite Isomorphism.iso_to_from.
      rewrite !id_left.
      rewrite Isomorphism.iso_to_from.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite fst_comp.
      rewrite <- bimap_comp.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc _ (Isomorphism.to _)).
      rewrite Isomorphism.iso_from_to.
      rewrite !id_left.
      rewrite Isomorphism.iso_from_to.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  unfold ProductFunctor_fst_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (fst (@lax_monoidal_unit_left _ _ _ _ _ L (x, I))) as X.
  rewrite <- X; clear X.
  destruct (P (x, I)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_fst_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (fst (@lax_monoidal_unit_right _ _ _ _ _ L (x, I))) as X.
  rewrite unit_identity.
  rewrite bimap_fmap in X.
  rewrite <- X; clear X.
  destruct (P (x, I)).
  reflexivity.
Qed.
Next Obligation.
  spose (fst (@lax_monoidal_assoc _ _ _ _ _ L (x, I) (y, I) (z, I))) as X.
  revert X.
  assert
    (fst (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (x, @I J H1)) (P (y, @I J H1)) (P (z, @I J H1))))
       = @to D _ _ (@tensor_assoc D H0 (fst (P (x, @I J H1)))
                                  (fst (P (y, @I J H1))) (fst (P (z, @I J H1))))). {
    destruct (P (x, I)), (P (y, I)), (P (z, I)).
    reflexivity.
  }
  srewrite H3; clear H3.
  spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (x, I, (y ⨂ z, I ⨂ I))%object
                         (x, I, (y ⨂ z, I))%object
                         ((id, id), (id, to unit_left)))) as X1.
  simpl in X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[fst (P (x, I))] ≈ id[fst (P (x, I))] ∘ id[fst (P (x, I))]) by cat.
  intros.
  rewrite X; clear X.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X0; clear X0.
  rewrite !comp_assoc.
  rewrite !fst_comp.
  assert (id[fst (P (z, I))] ≈ id[fst (P (z, I))] ∘ id[fst (P (z, I))]) by cat.
  rewrite X; clear X.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite !comp_assoc.
  apply compose_respects; [|cat].
  rewrite !bimap_fmap.
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  spose (fst (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (x ⨂ y, I ⨂ I, (z, I))%object
                         (x ⨂ y, I, (z, I))%object
                         ((id, to unit_left), (id, id)))) as X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  rewrite <- X1; clear X1.
  rewrite comp_assoc.
  rewrite fst_comp.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite unit_identity.
  reflexivity.
Qed.

(*
Lax tensor comparison for the second restriction ProductFunctor_snd P, dual
   to ProductFunctor_fst_LaxMonoidal_ap_functor_nat: the I ⨂ I now sits in the
   unused C-slot and is collapsed by [bimap (to unit_left) id]. 

--------
第二个限制的宽松张量比较 ProductFunctor_snd P，对偶
 到 ProductFunctor_fst_LaxMonoidal_ap_functor_nat： I ⨂ I 现在位于
 未使用的 C 槽并被 [bimap (to unit_left) id] 折叠。 
*)
Lemma ProductFunctor_snd_LaxMonoidal_ap_functor_nat :
  LaxMonoidalFunctor P
    → (⨂) ◯ (ProductFunctor_snd P) ∏⟶ (ProductFunctor_snd P)
          ⟹ ProductFunctor_snd P ◯ (⨂).
Proof.
  intro L.
  transform; simpl.
  - intros [x y]; simpl.
    exact (snd (bimap (to unit_left) id ∘ transform[@ap_functor_nat _ _ _ _ _ L]
                      ((I, x), (I, y)))).
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (I, x1, (I, x2)) (I, y1, (I, y2))
                           ((id, f1), (id, f2)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite snd_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
  - simpl in *.
    destruct x as [x1 x2];
    destruct y as [y1 y2];
    destruct f as [f1 f2]; simpl in *.
    spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                           (I, x1, (I, x2)) (I, y1, (I, y2))
                           ((id, f1), (id, f2)))) as X.
    rewrite comp_assoc.
    rewrite !bimap_fmap.
    rewrite snd_comp.
    rewrite <- bimap_comp.
    rewrite id_left, id_right.
    rewrite <- comp_assoc.
    rewrites.
    rewrite comp_assoc.
    rewrite snd_comp.
    rewrite bimap_fmap.
    rewrite <- bimap_comp.
    rewrite bimap_id_id.
    rewrite id_left, id_right.
    reflexivity.
Defined.

(*
ProductFunctor_snd P is lax monoidal whenever P is, dual to
   ProductFunctor_fst_LaxMonoidal. 

--------
当 P 为对偶时，ProductFunctor_snd P 是松弛幺半群
 ProductFunctor_fst_LaxMonoidal。 
*)
Program Definition ProductFunctor_snd_LaxMonoidal :
  LaxMonoidalFunctor P
    → LaxMonoidalFunctor (ProductFunctor_snd P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_snd_LaxMonoidal_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
Next Obligation.
  exact (snd (@lax_pure _ _ _ _ _ L)).
Defined.
Next Obligation.
  destruct (@pure_left _ _ _ _ _ L (I, x));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, I ⨂ x)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.to unit_left) id)).
    + exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.from unit_left) id)).
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_to_from.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_from_to.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  destruct (@pure_right _ _ _ _ _ L (I, x));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I, x ⨂ I)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.to unit_left) id)).
    + exact (snd (@bimap _ _ _ P _ _ _ _ (Isomorphism.from unit_left) id)).
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_to_from.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite Isomorphism.iso_from_to.
      rewrite id_left.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  destruct (@ap_assoc _ _ _ _ _ L (I, x) (I, y) (I, z));
  simplify; simpl in *;
  simplify; simpl in *.
  transitivity (snd (P (I ⨂ I ⨂ I, x ⨂ y ⨂ z)%object)).
  - isomorphism; auto.
  - isomorphism.
    + exact (snd (@bimap _ _ _ P _ _ _ _
                         (Isomorphism.to unit_left ∘
                          Isomorphism.to unit_left) id)).
    + exact (snd (@bimap _ _ _ P _ _ _ _
                         (Isomorphism.from unit_left ∘
                          Isomorphism.from unit_left) id)).
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc _ (Isomorphism.from _)).
      rewrite Isomorphism.iso_to_from.
      rewrite !id_left.
      rewrite Isomorphism.iso_to_from.
      rewrite bimap_id_id.
      reflexivity.
    + rewrite snd_comp.
      rewrite <- bimap_comp.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc _ (Isomorphism.to _)).
      rewrite Isomorphism.iso_from_to.
      rewrite !id_left.
      rewrite Isomorphism.iso_from_to.
      rewrite bimap_id_id.
      reflexivity.
Defined.
Next Obligation.
  unfold ProductFunctor_snd_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (snd (@lax_monoidal_unit_left _ _ _ _ _ L (I, x))) as X.
  rewrite <- X; clear X.
  destruct (P (I, x)).
  reflexivity.
Qed.
Next Obligation.
  unfold ProductFunctor_snd_LaxMonoidal_obligation_1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite bimap_fmap.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  spose (snd (@lax_monoidal_unit_right _ _ _ _ _ L (I, x))) as X.
  rewrite unit_identity.
  rewrite bimap_fmap in X.
  rewrite <- X; clear X.
  destruct (P (I, x)).
  reflexivity.
Qed.
Next Obligation.
  spose (snd (@lax_monoidal_assoc _ _ _ _ _ L (I, x) (I, y) (I, z))) as X.
  revert X.
  assert
    (snd (to (Product.Product_Monoidal_obligation_8
                D H0 K H2 (P (@I C H, x)) (P (@I C H, y)) (P (@I C H, z))))
       = @to K _ _ (@tensor_assoc K H2 (snd (P (@I C H, x)))
                                  (snd (P (@I C H, y))) (snd (P (@I C H, z))))). {
    destruct (P (I, x)), (P (I, y)), (P (I, z)).
    reflexivity.
  }
  srewrite H3; clear H3.
  intros.
  spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (I, x, (I ⨂ I, y ⨂ z))%object
                         (I, x, (I, y ⨂ z))%object
                         ((id, id), (to unit_left, id)))) as X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  assert (id[snd (P (I, x))] ≈ id[snd (P (I, x))] ∘ id[snd (P (I, x))]) by cat.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X1; clear X1.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite <- X; clear X.
  rewrite !comp_assoc.
  rewrite !snd_comp.
  assert (id[snd (P (I, z))] ≈ id[snd (P (I, z))] ∘ id[snd (P (I, z))]) by cat.
  rewrite X; clear X.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrite !comp_assoc.
  apply compose_respects; [|cat].
  rewrite !bimap_fmap.
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  spose (snd (naturality (@ap_functor_nat _ _ _ _ _ L)
                         (I ⨂ I, x ⨂ y, (I, z))%object
                         (I, x ⨂ y, (I, z))%object
                         ((to unit_left, id), (id, id)))) as X1.
  rewrite !bimap_fmap in X1.
  rewrite !bimap_id_id in X1.
  rewrite <- X1; clear X1.
  rewrite comp_assoc.
  rewrite snd_comp.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite unit_identity.
  reflexivity.
Qed.

(*
Recombining the two restrictions: the product of the factor functors is lax
   monoidal, by feeding ProductFunctor_fst_LaxMonoidal and
   ProductFunctor_snd_LaxMonoidal into ProductFunctor_LaxMonoidal. Note this
   reconstructs lax monoidality of ProductFunctor_fst P ∏⟶ ProductFunctor_snd P,
   which is in general only naturally isomorphic to P, not equal to it. 

--------
重新组合这两个限制：因子函子的乘积是宽松的
 幺半群，通过输入 ProductFunctor_fst_LaxMonoidal 和
 ProductFunctor_snd_LaxMonoidal 转换为 ProductFunctor_LaxMonoidal。 注意这一点
 重建 ProductFunctor_fst P ∏⟶ ProductFunctor_snd P 的松弛幺半性，
 一般来说，它只是自然同构于 P，而不是等于它。 
*)
Corollary ProductFunctor_proj_LaxMonoidal :
  LaxMonoidalFunctor P
    → LaxMonoidalFunctor ((ProductFunctor_fst P) ∏⟶ (ProductFunctor_snd P)).
Proof.
  intros L.
  exact (ProductFunctor_LaxMonoidal (ProductFunctor_fst_LaxMonoidal L)
                                    (ProductFunctor_snd_LaxMonoidal L)).
Qed.

End ProductMonoidalProj.
