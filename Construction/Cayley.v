Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The Cayley representation of a category. / 一个范畴的凯莱表示。 *)

(*
 nLab: https://ncatlab.org/nlab/show/Cayley's+theorem
 nLab: https://ncatlab.org/nlab/show/Yoneda+embedding
 Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem

 Cayley's theorem (group version) says every group G embeds into the
 symmetric group Sym(G) via left multiplication g ↦ (x ↦ g x); for a monoid
 M the same map g ↦ (x ↦ g · x) embeds M into the endofunction monoid
 (M → M, id, ∘).  Reading a category C as a many-object monoid, the
 corresponding statement is the covariant Yoneda embedding C ⟶ [C, Set]
 sending x to the corepresentable [Hom x,─], which is full and faithful.

 This file builds that embedding's image directly, without naming Sets or a
 functor category.  An object of Cayley is an object of C; a morphism
 x ~> y is the underlying data of a natural transformation
 [Hom y,─] ⟹ [Hom x,─] (post-composition acting on the left), namely a
 family

 f : ∀ r, (y ~> r) → (x ~> r)

 that is Proper in r and k and satisfies the naturality/representability
 law  f r k ≈ k ∘ f _ id, so every f is determined by the single morphism
 f _ id : x ~> y (this is the bijection of the Yoneda lemma).  Composition
 g ∘ f is r,k ↦ g r (f r k) and identity is r,k ↦ k; two morphisms are
 equivalent when they agree as functions, ∀ r k, `1 f r k ≈ `1 g r k.

 To_Cayley : C ⟶ Cayley and From_Cayley : Cayley ⟶ C below witness that this
 embedding is (split) faithful: From_Cayley (To_Cayley f) ≈ f.  Its point is
 that the round trip normalises composition.  Because each f is recovered as
 f _ id, a composite is always read back as a fully *left*-associated chain
 (… (id ∘ f) ∘ g) ∘ h regardless of how it was bracketed in Cayley; this is
 the categorical form of the “difference list” / Cayley-monoid trick, where
 a monoid is replaced by its endofunctions to reassociate · into ∘.  See
 Cayley_Right and Cayley_Left below. 

 --------
 nLab: https://ncatlab.org/nlab/show/Cayley's+theorem
 nLab: https://ncatlab.org/nlab/show/Yoneda+embedding
 Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem

 凯莱定理（群版本）指出，每个群 G 都可以通过左乘 g ↦ (x ↦ g x) 嵌入对称群 Sym(G)；对于一个幺半群 M，相同的映射 g ↦ (x ↦ g · x) 将 M 嵌入自函数幺半群 (M → M, id, ∘) 中。把一个范畴 C 看作一个多对象幺半群，相应的陈述是协变的 Yoneda 嵌入 C ⟶ [C, Set]，将 x 发送到共表示 [Hom x,─] ，它是满且忠实的。

 该文件直接构建该嵌入的像，而无需命名 Sets 或函子范畴。Cayley 的一个对象是 C 的一个对象；一个态射 x ~> y 是自然变换 [Hom y,─] ⟹ [Hom x,─]（后组合作用于左侧）的底层数据，具体来说是一个族

 f : ∀ r, (y ~> r) → (x ~> r)这是在 r 和 k 上合适的，并满足自然性/可表示性定律 f r k ≈ k ∘ f _ id，因此每个 f 都由单个态射 f _ id : x ~> y 决定（这就是 Yoneda 引理的双射）。复合 g ∘ f 定义为 r,k ↦ g r (f r k)，单位元为 r,k ↦ k；当两个态射作为函数在 ∀ r k 上相同时，它们是等价的，`1 f r k ≈ ` 1 g r k。To_Cayley : C ⟶ Cayley 和 From_Cayley : Cayley ⟶ C 在下面证明了这个嵌入是（可分裂的）忠实的：From_Cayley (To_Cayley f) ≈ f。其关键在于往返操作会规范化组合。因为每个 f 都被恢复为 f _ id，所以无论在 Cayley 中如何加括号，复合总是被读回为完全*左*结合的链 (… (id ∘ f) ∘ g) ∘ h；这是“差列表”/ Cayley-幺半群技巧的范畴形式，其中幺半群被其自函数所取代，以将 · 重新关联为 ∘。参见下面的 Cayley_Right 和 Cayley_Left。
*)

(*
 Where the theorem comes from, and what the image is for

 Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem
 Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

 The theorem is named for Arthur Cayley, who in 1854 observed that a
 group of order n can be presented as a subgroup of the symmetric group
 on n letters (Cayley, “On the theory of groups, as depending on the
 symbolic equation θⁿ = 1”, Philosophical Magazine 1854).  Cayley checked
 that the assignment of each element to its left multiplication is
 one-to-one, yet did not separately verify that it respects the group
 operation; the modern packaging as the left regular representation
 ℓ_g : x ↦ g x, an injective homomorphism into Sym(G), supplies that step
 (Wikipedia, “Cayley's theorem”).  The name has been disputed — Burnside
 credited Camille Jordan, and Nummela defended the attribution to Cayley,
 who had made the result known roughly sixteen years before Jordan.  The
 statement also reaches past groups: the Wagner–Preston theorem embeds
 every inverse semigroup into a semigroup of partial bijections of a set
 (nLab, “Cayley's theorem”).

 The many-object form is the Yoneda embedding, which Wikipedia describes
 as a vast generalisation of Cayley's theorem (Wikipedia, “Yoneda
 lemma”); at a one-object category it is exactly full faithfulness of the
 covariant embedding (Riehl, “Category Theory in Context”, Dover 2016,
 Corollary 2.2.11).  That framing, together with the reading that an
 object is determined by its web of maps, is developed in
 Functor/Hom/Yoneda.v, whose [Covariant_Yoneda_Embedding] this file
 consumes and which points back here; Functor/Hom.v carries the abstract
 [Yoneda_Full] and [Yoneda_Faithful] that [Cayley] realizes as a concrete
 image.  The distinctive contribution here is that image on its own
 terms — a standalone category rather than a functor into Sets — with the
 classical one-object cases living in Structure/Group.v and in the monoid
 objects of Structure/Monoid.v and Theory/Algebra/Monoid.v.

 Read as programming, the reassociation that [Cayley_Right] and
 [Cayley_Left] record is the difference list (Hughes, “A novel
 representation of lists and its application to the function reverse”,
 Information Processing Letters 1986).  A list l is represented by the
 function λ k, l ++ k, so that append becomes composition and the list is
 recovered by applying to the empty list; a left-nested chain of appends
 that would cost O(n²) is thereby run in O(n).  In the image this is the
 round trip: [To_Cayley] reifies a morphism as its post-composition
 action, the analogue of consing onto an accumulator, and [From_Cayley]
 runs the accumulated handler on the identity, the analogue of reading
 the list out.  Rather than stop at the free monoid, Rivas and Jaskelioff
 situate the pattern one level up, where monads, applicative functors,
 and arrows are monoids in monoidal categories and a monoid that is an
 exponent embeds into its endomorphism monoid; the difference list is the
 case of the free monoid on a type (Rivas and Jaskelioff, “Notions of
 Computation as Monoids”, Journal of Functional Programming 2017).
 Structure/Monoid.v cites the same work, and the continuation-transformer
 reading of the morphism data ∀ r, (y ~> r) → (x ~> r) is drawn out in
 Functor/Hom/Yoneda.v.

 The construction also transports finite products.  [Cayley_Cartesian]
 carries a cartesian structure on C (Structure/Cartesian.v) onto [Cayley]
 by moving fork, exl, and exr across the covariant Yoneda isomorphism on
 hom-sets, and [To_Cayley_CartesianFunctor] and
 [From_Cayley_CartesianFunctor], over Functor/Structure/Cartesian.v,
 record that both the embedding and its retraction preserve it. 

 --------
 定理的来源，以及图像的用途

 维基百科：https://en.wikipedia.org/wiki/Cayley%27s_theorem
 维基百科：https://en.wikipedia.org/wiki/Yoneda_lemma该定理以亚瑟·凯莱（Arthur Cayley）的名字命名，他在1854年观察到，阶为 n 的群可以表示为 n 个字母的对称群的子群（Cayley，《关于群的理论，依赖于符号方程 θⁿ = 1》，《哲学杂志》1854年）。凯莱检查了将每个元素映射到其左乘的指派是一一对应的，但并未单独验证它是否遵守群运算；现代将其表述为左正则表示 ℓ_g : x ↦ g x，作为到 Sym(G) 的单射同态，补充了这一步（维基百科，“凯莱定理”）。该命名曾被争议——伯恩赛德（Burnside）将其归功于卡米尔·乔丹（Camille Jordan），而努梅拉（Nummela）则为归功于凯莱辩护，凯莱大约在乔丹之前十六年就已公开了该结果。该陈述也涉及过去的群体：Wagner–Preston 定理将每个逆半群嵌入到一个集合的部分双射半群中（nLab，“Cayley 定理”）。多对象形式是Yoneda嵌入，维基百科将其描述为Cayley定理的一个广泛推广（维基百科，“Yoneda 引理”）；在单对象范畴中，它恰好是协变嵌入的完全忠实性（Riehl，《上下文中的范畴论》，Dover 2016，第2.2.11推论）。这一表述，以及对象由其映射网络决定的理解，在Functor/Hom/Yoneda.v中得到发展，该文件消耗了[Covariant_Yoneda_Embedding]，并指向此处；Functor/Hom.v承载抽象的[Yoneda_Full]和[Yoneda_Faithful]，而[Cayley]将其实现为具体图像。这里的独特贡献在于图像本身本身——作为一个独立类别而不是进入集合的函子——经典的单对象情况存在于 Structure/Group.v 中，以及 Structure/Monoid.v 和 Theory/Algebra/Monoid.v 中的幺半群对象。作为编程来阅读，[Cayley_Right] 和 [Cayley_Left] 记录的重组是差异列表（Hughes，《列表的新表示及其在 reverse 函数中的应用》，信息处理快报，1986 年）。一个列表 l 被表示为函数 λ k, l ++ k，因此 append 变成组合，并且通过应用于空列表来恢复列表；一个左嵌套的 append 链原本需要 O(n²) 时间，由此可以在 O(n) 时间内运行。在图像中，这是循环往返：[To_Cayley] 将一个态射重新具体化为它的后组合操作，相当于累加器上的 cons 操作，而 [From_Cayley] 在身份上运行累积的处理器，相当于读取列表内容。Rivas 和 Jaskelioff 并没有止步于自由幺半群，他们将模式提升到更高一级，其中单子、应用函子和箭头是在幺半群范畴中的幺半群，并且一个作为指数的幺半群可以嵌入到其自同态幺半群中；差分列表是类型上的自由幺半群的一个特例（Rivas 和 Jaskelioff，《Notions of Computation as Monoids》，《函数式编程杂志》2017 年）。Structure/Monoid.v 引用了同一工作，而对态射数据 ∀ r, (y ~> r) → (x ~> r) 的续延变换解读则在 Functor/Hom/Yoneda.v 中展开。该构造也传输有限积。[Cayley_Cartesian] 将 C（Structure/Cartesian.v）上的笛卡尔结构通过协变尤内达同构在 hom 集上移动 fork、exl 和 exr，传送到 [Cayley]；而 [To_Cayley_CartesianFunctor] 和 [From_Cayley_CartesianFunctor] 在 Functor/Structure/Cartesian.v 上记录了嵌入及其回退都保持这种结构。
*)

Section Cayley.

Context {C : Category}.

(*
 An object is just an object of C; a morphism x ~> y is the underlying
 transformation of [Hom y,─] ⟹ [Hom x,─], determined by f _ id (Yoneda). 

 --------
 一个对象只是 C 的一个对象；一个态射 x ~> y 是由 f _ id (Yoneda) 决定的 [Hom y,─] ⟹ [Hom x,─] 的基础变换。
*)
Program Instance Cayley : Category := {
  obj     := C;
  hom     := fun x y =>
    { f : ∀ r, (y ~> r) → (x ~> r)          (* the post-composition action / 后期组合操作 *)
    & Proper (forall_relation (fun _ => respectful equiv equiv)) f ∧
      ∀ (r : C) (k : y ~> r), f r k ≈ k ∘ f _ id };  (* naturality / Yoneda / 自然性 / 约内达 *)
  homset  := fun x y => {| equiv := fun f g => ∀ r k, `1 f r k ≈ `1 g r k |};
  id      := fun _ => (fun _ => Datatypes.id; _);
  compose := fun x y z f g  => (fun r k => `1 g r (`1 f r k); _)
}.
Next Obligation.
  equivalence.
  now rewrite X, X0.
Qed.
Next Obligation.
  split.
  - proper.
  - intros; cat.
Qed.
Next Obligation.
  split.
  - proper.
    apply p.
    apply p0.
    apply X.
  - intros.
    symmetry.
    rewrite e.
    rewrite comp_assoc.
    rewrite <- e0.
    rewrite <- e.
    reflexivity.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H, H0.
  rewrite X.
  comp_left.
  apply X0.
Qed.

(*
 The embedding: f : x ~> y is sent to its post-composition action
 k ↦ k ∘ f, the corepresentable transformation [Hom y,─] ⟹ [Hom x,─]. 

 --------
 嵌入：f : x ~> y 被发送到它的后组合作用 k ↦ k ∘ f，可余表示的变换 [Hom y,─] ⟹ [Hom x,─] 。
*)
Program Instance To_Cayley : C ⟶ Cayley := {
  fobj := fun x => x;
  fmap := fun _ _ f => (fun _ k => k ∘ f; _);
}.
Next Obligation.
  proper.
  proper.
Defined.

(*
 The retraction: read a Cayley-morphism f back as the C-morphism f _ id,
 recovering the original by the Yoneda law.  From_Cayley ∘ To_Cayley = Id. 

 --------
 收缩：将 Cayley 同态 f 作为 C 同态 f _ id 读回，通过 Yoneda 定律恢复原始的。从_Cayley ∘ To_Cayley = Id。
*)
Program Instance From_Cayley : Cayley ⟶ C := {
  fobj := fun x => x;
  fmap := fun _ y f => `1 f y (@id C y);
}.

Context `{Cayley}.

(*
 No matter how we associate the mapped morphisms, the functor back from
 Cayley yields them left-associated. 

 --------
 无论我们如何关联映射的态射，从凯莱返回的函子都会将它们左关联。
*)

Lemma Cayley_Right (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (fmap[To_Cayley] f ∘ (fmap[To_Cayley] g
                                          ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Lemma Cayley_Left (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (((fmap[To_Cayley] f ∘ fmap[To_Cayley] g)
                      ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

(*
 The embedding transports any cartesian structure on C onto Cayley: products
 are the same objects, and fork/exl/exr are obtained by carrying C's
 universal arrows across the covariant Yoneda isomorphism on hom-sets. 

 --------
 该嵌入将 C 上的任何笛卡尔结构传输到 Cayley：乘积是相同的对象，叉/左投影/右投影是通过将 C 的泛箭穿过同态集上的协变 Yoneda 同构得到的。
*)
Program Instance Cayley_Cartesian `{CA : @Cartesian C} : @Cartesian Cayley := {
  product_obj := @product_obj C CA;
  fork := fun x y z f g =>
    let f' := to (Covariant_Yoneda_Embedding C x y) (_ f) in
    let g' := to (Covariant_Yoneda_Embedding C x z) (_ g) in
    _ f' g';
  exl := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exl C CA x y) in
    _ f';
  exr := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exr C CA x y) in
    _ f';
}.
Next Obligation.
  construct.
  - construct.
    + apply f.
      exact X.
    + proper.
      rewrite e1.
      rewrite X.
      rewrite <- e1.
      reflexivity.
  - simpl.
    rewrite e1.
    rewrite comp_assoc.
    rewrite <- e1.
    reflexivity.
  - simpl.
    rewrite e1.
    rewrite <- comp_assoc.
    rewrite <- e1.
    reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + apply g.
      exact X.
    + proper.
      rewrite e0.
      rewrite X.
      rewrite <- e0.
      reflexivity.
  - simpl.
    rewrite e0.
    rewrite comp_assoc.
    rewrite <- e0.
    reflexivity.
  - simpl.
    rewrite e0.
    rewrite <- comp_assoc.
    rewrite <- e0.
    reflexivity.
Defined.
Next Obligation.
  exists (fun r h => h ∘ x0 △ x1).
  split.
  - proper.
  - intros; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  proper; simpl in *.
  comp_left.
  apply fork_respects.
  - apply X.
  - apply X0.
Qed.
Next Obligation.
  proper; simpl in *.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    rewrite <- e1.
    reflexivity.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite <- e0.
    reflexivity.
  - rewrite <- X, <- H0.
    rewrite e.
    comp_left.
    rewrite (e _ (_ ∘ exl)).
    rewrite (e _ (_ ∘ exr)).
    cat.
    rewrite fork_comp.
    rewrite fork_exl_exr.
    cat.
Qed.

End Cayley.

Require Import Category.Functor.Structure.Cartesian.

#[export]
Program Instance To_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ To_Cayley _ Cayley_Cartesian.

#[export]
Program Instance From_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ From_Cayley Cayley_Cartesian _.
