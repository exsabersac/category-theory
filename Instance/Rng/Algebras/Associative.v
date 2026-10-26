Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Associative K-algebras, and the underlying K-module

   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   GTM 5, §III.1, printed p. 59, Exercise 1 — the tensor algebra
   of a vector space and the exterior algebra, each as a universal
   arrow (maclane:III.1:ex1); the roster of free constructions on
   printed p. 56 (maclane:III.1:remark2)
   Book: Mac Lane, ibid., §I.8, printed p. 28 — Ab-categories and the
   hom-rings that make an algebra an algebra
   nLab:      https://ncatlab.org/nlab/show/associative+algebra
   nLab:      https://ncatlab.org/nlab/show/tensor+algebra
   Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

   WHY A SECOND CATEGORY OF ALGEBRAS.  Instance/Rng/Algebras.v already
   carries [KAlg K], and that category is the right home for the
   polynomial ring, for the coslice reading of Mac Lane §II.6 Exercise 1,
   and for everything else whose objects happen to be commutative.  It
   is NOT a possible home for the tensor algebra or the exterior
   algebra, and the obstruction is a field of its record rather than a
   matter of taste: [KAlgObject] carries

   kalg_comm : forall a b, rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a

   so every object of [KAlg K] is commutative.  The tensor algebra T(V)
   is not — Instance/Vect/TensorAlgebra.v's [tensor_not_commutative]
   proves it for a concrete V — and the exterior algebra Λ(V) is
   anticommutative rather than commutative, with
   [ext_anticomm_nontrivial] proving there that the two orders of a
   product of generators genuinely differ.  So a category of algebras
   that does not demand commutativity has to exist before §III.1
   Exercise 1 can be stated at all, and this file supplies it.

   That is the shape Instance/Rng/Algebras.v names and declines: its own
   deferral list says that a non-commutative K-algebra is one in which
   “the structure map is required to land in the CENTRE, a condition
   that is automatic exactly when the target is commutative”, and adds
   “No centre-valued variant is built here”.  [AAlgObject]'s
   [aalg_central] field IS that condition, so this file is the
   centre-valued variant.  What is NOT claimed is anything about what
   would happen to the universal property of T(V) or Λ(V) if it were
   stated over [KAlg K] instead: no such statement is formed here, and
   the reason for the choice is the two proved non-commutativity results
   above, not a claim about a construction that is not made.

   WHAT REPLACES COMMUTATIVITY.  A K-algebra in the classical sense is a
   K-MODULE with a bilinear associative multiplication.  Presented ring
   first, that is a ring A together with a homomorphism u : K → A whose
   image is CENTRAL in A — centrality is exactly what makes the induced
   action r·a := u(r)·a bilinear, and it is exactly what commutativity
   of A was silently supplying in [KAlgObject].  So [AAlgObject K] and
   [KAlgObject K] have three fields each, and they differ in exactly one:
   the ring and the structure map are shared, and centrality of the
   structure map's image stands where commutativity of the ring stood.
   Morphisms are unchanged — a ring
   homomorphism commuting with the two structure maps — which is what
   lets [KAlg_AAlg] below be full and faithful with no proof obligation
   on the hom side.

   THE TWO CATEGORIES ARE GENUINELY DIFFERENT, and this is proved rather
   than asserted.  [UT2] is the ring of upper-triangular 2×2 integer
   matrices, an object of [AAlg Int_CRng] by way of the scalar diagonal;
   [UT2_not_commutative] exhibits two of its elements whose products
   disagree in both orders, and [AAlg_not_all_commutative] packages the
   consequence.  Without such a witness the reader would have no way to
   tell whether [AAlg K] is a proper generalization of [KAlg K] or a
   re-spelling of it, and the tree contained no non-commutative
   [RingObject] before this file — Instance/Mod/Tensor.v enumerates the
   closed ones (“[Int_Ring], [Q_Ring], [Zero_Ring], [F2_Ring],
   [FracRing] and [CRingOb], all commutative”) in the course of deferring
   a result for want of exactly such an object.  That quoted list
   predates Instance/Rng/Polynomial.v and so omits [PolyRing]/[ZPoly];
   the conclusion is unaffected, [PolyRing] being commutative by
   construction (its [pe_mul_comm] constructor).  [UT2] is a closed
   non-commutative [RingObject] and so supplies what that file records as
   missing; whether it makes that file's collapse strict is NOT
   investigated here, and no claim about it is made.

   THE UNDERLYING K-MODULE, and why it is the interesting functor.  An
   associative K-algebra is a K-module for r·a := u(r)·a, and a
   K-algebra map is K-linear.  [AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)]
   packages that, and it is the functor to which the tensor algebra is a
   universal arrow — “T(V) is the free associative K-algebra on the
   K-module V” is precisely the statement that V has a universal arrow to
   [AAlg_Forget_Mod].  Each of the four module laws is one rig law
   conjugated by one preservation law of u, and none of them consumes
   centrality; centrality is consumed downstream, by the algebras that
   are built rather than by the module structure that is read off.

   WHAT IS DELIVERED.

   - [AAlgObject], [AAlgHom], [AAlg K]: associative unital K-algebras
   over a commutative base ring K, with morphisms the ring
   homomorphisms under K;
   - [AAlg_Forget : AAlg K ⟶ Sets] and
   [AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)], the underlying set and
   the underlying K-module;
   - [AAlgLinear], K-linear maps from a K-module into an algebra, with
   the setoid comparing underlying maps, and
   [aalg_linear_of_module_hom] identifying a module homomorphism into
   the underlying module of A with such a map;
   - [KAlg_AAlg : KAlg K ⟶ AAlg K], full and faithful, exhibiting the
   commutative algebras inside the associative ones;
   - [UT2] with [UT2_AAlg], [UT2_not_commutative],
   [AAlg_not_all_commutative] and [UT2_not_in_KAlg]: the inclusion is
   proper, proved;
   - [Base_AAlg]: the base ring is an algebra over itself, so [AAlg K]
   is inhabited for every K with no witness-hunting.

   WHAT IS NOT DELIVERED.  No comparison of [AAlg K] with a category of
   monoid objects in [RMod (`1 K)] — the tree has no monoidal structure
   on module categories (Instance/Mod/Tensor.v builds the tensor product
   of two modules as a universal element but no bifunctor, and says so).
   No opposite-algebra involution, no tensor product of algebras, no
   graded algebras, and in particular no category of graded
   anticommutative algebras — Instance/Vect/TensorAlgebra.v records why
   that last one matters and what it costs.  No claim that [KAlg_AAlg]
   is REPLETE or that its image is closed under any construction. 

   --------
   * * 结合 K-代数及其基础 K-模

   书籍：Mac Lane，《为工作中的数学家准备的范畴论》，第2版，
   GTM 5，第III.1节，第59页印刷，练习1 — 向量空间的张量代数
   和外代数，各作为一个泛箭头 (maclane:III.1:ex1)；第56页印刷的自由构造列表 (maclane:III.1:remark2)
   书籍：Mac Lane，同上，第I.8节，第28页印刷 — Ab-范畴以及使代数成为代数的同态环
   nLab:       https://ncatlab.org/nlab/show/associative+algebra 
   nLab:       https://ncatlab.org/nlab/show/tensor+algebra 
   维基百科:  https://en.wikipedia.org/wiki/Associative_algebra为什么需要第二类代数。Instance/Rng/Algebras.v 已经包含了 [KAlg K]，而这个类别是多项式环、Mac Lane §II.6 练习 1 的余片读法以及其他所有对象恰好是交换的情况的合适归宿。它并不是张量代数或外代数的可能归宿，其障碍是记录中的一个域问题，而不是品味问题：[KAlgObject] 包含

   kalg_comm : 对于所有 a b，有 rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a所以 [KAlg K] 的每个对象都是交换的。张量代数 T(V) 不是 —— Instance/Vect/TensorAlgebra.v 的 [tensor_not_commutative] 为具体的 V 证明了这一点 —— 并且外代数 Λ(V) 是反交换的而不是交换的，其中 [ext_anticomm_nontrivial] 在那里证明了生成元乘积的两种顺序确实不同。因此，在 §III.1 练习 1 可以被表述之前，必须存在一个不要求交换性的代数范畴，而这个文件提供了它。这是形状 Instance/Rng/Algebras.v 的名称和限定：它自己的延期列表指出，非交换 K-代数是指其中“结构映射要求落在中心，这是当目标是交换的情况下自动满足的条件”，并补充说“这里没有构建中心值的变体”。[AAlgObject] 的 [aalg_central] 域就是该条件，因此这个文件是中心值的变体。未声明的是，如果将 T(V) 或 Λ(V) 的泛性质在 [KAlg K] 上陈述，会发生什么：这里没有形成这样的声明，选择的原因是上面证明的两个非交换性结果，而不是对尚未构建的结构作出声明。什么取代了交换性。经典意义上的K代数是一个具有双线性结合乘法的K-模。先呈现环，即一个环A以及一个同态u : K → A，其像在A中是中心的——中心性正是使得诱导作用r·a := u(r)·a双线性的原因，并且也正是A的交换性在[KAlgObject]中默默提供的。于是[AAlgObject K]和[KAlgObject K]各有三个字段，它们只在一个字段上不同：共享环和结构映射，而结构映射像的中心性取代了环的交换性。态射保持不变——一个与两个结构映射交换的环同态——这正是使得以下[KAlg_AAlg]成为满且忠实的，没有在态射方面的证明义务。这两类确实不同，这一点是通过证明而非断言得出的。[UT2] 是上三角 2×2 整数矩阵的环，这是 [AAlg Int_CRng] 的一个对象，通过标量对角线构造；[UT2_not_commutative] 展示了它的两个元素，其乘积在两种顺序下都不相等，而 [AAlg_not_all_commutative] 则整理了这一结果。没有这样的见证，读者无法判断 [AAlg K] 是否是 [KAlg K] 的一个真正推广，还是它的一种重新表述，并且在此文件之前，树中没有非交换的 [RingObject] — Instance/Mod/Tensor.v 枚举了封闭的那些（“[Int_Ring]、[Q_Ring]、[Zero_Ring]、[F2_Ring]、[FracRing] 和 [CRingOb]，都可交换”）以延迟某个结果，因为正缺少这样一个对象。该引用的列表早于 Instance/Rng/Polynomial.v，因此遗漏了 [PolyRing] / [ZPoly]；结论不受影响，[PolyRing] 由于其 [pe_mul_comm] 构造而是交换的。[UT2] 是一个封闭的非交换 [RingObject]，因此提供了该文件记录为缺失的内容；是否使该文件的折叠严格在此未进行调查，也不对其作出任何声明。基础的K-模，以及为什么它是有趣的函子。一个结合K-代数是一个K-模，对于r·a := u(r)·a，并且K-代数映射是K-线性的。[AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)]打包了这个，它是张量代数的一个函子到哪——“T(V)是K-模V上的自由结合K-代数”正是声明V有一个到[AAlg_Forget_Mod]的普遍箭头。四条模定律中的每一条都是一个箝制定律由u的一个保持定律共轭产生的，没有一条消耗中心性；中心性是在下游消耗的，由构建的代数而不是从中读取的模结构消耗。交付的是什么。- [AAlgObject]、[AAlgHom]、[AAlg K]：在交换基环 K 上的结合单位 K-代数，其态射是在 K 下的环同态；
   - [AAlg_Forget : AAlg K ⟶ Sets] 和 [AAlg_Forget_Mod : AAlg K ⟶ RMod (`1 K)]：底层集合和底层 K-模；
   - [AAlgLinear]：从 K-模到代数的 K-线性映射，比较底层映射的集合结构，以及 [aalg_linear_of_module_hom]：将一个模同态映射到 A 的底层模与这样的映射对应；
   - [KAlg_AAlg : KAlg K ⟶ AAlg K]：满且忠实，展示了结合代数中存在的交换代数；
   - [UT2] 与 [UT2_AAlg]、[UT2_not_commutative]、[AAlg_not_all_commutative] 和 [UT2_not_in_KAlg]：包含是严格的，已证明；
   - [Base_AAlg]：基环是其自身的代数，因此对于每个 K，[AAlg K] 都是非空的寻找证人。未提供的内容。没有将 [AAlg K] 与 [RMod (`1 K)] 中的幺半群对象类别进行比较——该树在模范畴上没有幺半群结构（Instance/Mod/Tensor.v 将两个模的张量积构建为一个泛元素，但没有双函子，并且明确说明了这一点）。没有对偶代数反演，没有代数的张量积，没有分次代数，尤其没有分次反交换代数的类别——Instance/Vect/TensorAlgebra.v 记录了最后一点的重要性及其代价。没有声称 [KAlg_AAlg] 是完备的，也没有声称其像在任何构造下是封闭的。
*)

(** ** Objects *)

(*
 An associative unital K-algebra: a ring, a homomorphism out of the base
 ring, and centrality of the image.  The three fields correspond one for
 one to [KAlgObject]'s, with centrality in place of commutativity. 

 --------
 一个结合幺元 K-代数：一个环，一个来自基础环的同态，以及像的中心性。三个域一一对应于 [KAlgObject] 的，每个域用中心性代替交换性。
*)
Record AAlgObject (K : CRng) := {
  aalg_ring : RingObject;
  aalg_unit : `1 K ~{Rng}~> aalg_ring;
  aalg_central : ∀ k a,
    rig_mul aalg_ring (rig_map aalg_unit k) a
      ≈ rig_mul aalg_ring a (rig_map aalg_unit k)
}.

Arguments aalg_ring {K} _.
Arguments aalg_unit {K} _.
Arguments aalg_central {K} _ _ _.

(*
 A morphism of K-algebras is a ring homomorphism commuting with the two
 structure maps.  The orientation of the triangle is [KAlgHom]'s, hence
 [Coslice]'s (Construction/Slice.v). 

 --------
 K-代数的态射是与两个结构映射交换的环同态。三角形的方向是 [KAlgHom] 的，因此是 [Coslice] 的（Construction/Slice.v）。
*)
Definition AAlgHom {K : CRng} (A B : AAlgObject K) : Type :=
  ∃ f : aalg_ring A ~{Rng}~> aalg_ring B, aalg_unit B ≈ f ∘ aalg_unit A.

(*
 Two algebra morphisms are equal when their underlying ring
 homomorphisms are; the triangle proof is irrelevant, as in [KAlgHom]. 

 --------
 当它们的底层环同态相等时，两个代数同态就相等；三角形证明是无关的，如在 [KAlgHom] 中。
*)
Program Definition AAlgHom_Setoid {K : CRng} (A B : AAlgObject K) :
  Setoid (AAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  intros K A B.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Qed.

Lemma aalg_id_triangle {K : CRng} (A : AAlgObject K) :
  aalg_unit A ≈ id ∘ aalg_unit A.
Proof. now rewrite id_left. Qed.

Lemma aalg_comp_triangle {K : CRng} {A B C : AAlgObject K}
      (f : AAlgHom B C) (g : AAlgHom A B) :
  aalg_unit C ≈ (`1 f ∘ `1 g) ∘ aalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Qed.

Program Definition AAlg (K : CRng) : Category := {|
  obj     := AAlgObject K;
  hom     := @AAlgHom K;
  homset  := @AAlgHom_Setoid K;
  id      := fun A => (id; aalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; aalg_comp_triangle f g)
|}.
Next Obligation.
  intros K A B C f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.

(** ** The underlying set / ** 底层集合 *)

Program Definition AAlg_Forget (K : CRng) : AAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (aalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(*
   * ** The underlying K-module

   Each of the four module laws is one rig law of A conjugated by one
   preservation law of the structure map: distributivity on the left is
   [rig_distr_l] alone, distributivity on the right spends
   [rig_map_add], associativity of the action spends [rig_map_mul], and
   unitality spends [rig_map_one].  Centrality is not consumed. 

   --------
   * ** 基础 K-模

   四条模律中的每一条都是 A 的一条环律，通过一个结构映射的保持律进行共轭：左分配律仅涉及 [rig_distr_l]，右分配律涉及 [rig_map_add]，作用的结合律涉及 [rig_map_mul]，单位律涉及 [rig_map_one]。中心性不被消耗。
*)

Program Definition AAlg_RMod {K : CRng} (A : AAlgObject K)
  : RModObject (`1 K) := {|
  rm_ab   := ring_ab (aalg_ring A);
  rm_smul := fun r a => rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) a
|}.
Next Obligation.
  intros K A r r' Hr a a' Ha; simpl.
  apply rig_mul_respects; [| exact Ha ].
  now apply (proper_morphism (rig_map (aalg_unit A))).
Qed.
Next Obligation. intros K A r m n; simpl; apply rig_distr_l. Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_add (aalg_unit A) r s).
  apply rig_distr_r.
Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_mul (aalg_unit A) r s).
  apply rig_mul_assoc.
Qed.
Next Obligation.
  intros K A m; simpl.
  rewrite (rig_map_one (aalg_unit A)).
  apply rig_mul_one_l.
Qed.

(*
 A K-algebra map is K-linear: the triangle turns [f (u_A r · a)] into
 [u_B r · f a]. 

 --------
 一个 K-代数映射是 K-线性的：三角形将 [f (u_A r · a)] 变为 [u_B r · f a]。
*)
Program Definition AAlg_RModHom {K : CRng} {A B : AAlgObject K}
  (f : AAlgHom A B) : RModHom (AAlg_RMod A) (AAlg_RMod B) := {|
  rm_hom := {| cmon_map := rig_map (`1 f);
               cmon_map_zero := rig_map_zero (`1 f);
               cmon_map_plus := rig_map_add (`1 f) |}
|}.
Next Obligation.
  intros K A B f r m; simpl.
  rewrite (rig_map_mul (`1 f)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 f r).
Qed.

Program Definition AAlg_Forget_Mod (K : CRng) : AAlg K ⟶ RMod (`1 K) := {|
  fobj := @AAlg_RMod K;
  fmap := fun A B f => AAlg_RModHom f
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(*
 The two forgetful functors agree on carriers, definitionally: the
 underlying set of the underlying module IS the underlying set.  (This
 is the convertibility exception — an equation between setoids, not
 between morphisms.) 

 --------
 这两个遗忘函子在载体上从定义上是一致的：底层模的底层集合就是底层集合。（这是可转换性的例外——集合等价关系之间的等式，而不是态射之间的等式。）
*)
Example aalg_forget_agree (K : CRng) (A : AAlg K) :
  fobj[RMod_Forget (`1 K)] (fobj[AAlg_Forget_Mod K] A) = fobj[AAlg_Forget K] A
  := eq_refl.

(*
   * ** K-linear maps into an algebra

   The data a universal property of the tensor algebra consumes: an
   additive map out of a K-module whose interaction with the action is
   multiplication by the image of the scalar.  This is exactly a
   morphism into [AAlg_RMod A] with the packaging removed, and
   [aalg_linear_of_module_hom] and [module_hom_of_aalg_linear] are the
   two passages, mutually inverse on the underlying map by [eq_refl]. 

   --------
   * ** K-线性映射到一个代数

   张量代数的普遍性质所涉及的数据：一个从 K-模出来的加法映射，其与作用的交互是通过标量的像进行乘法。这正是一个到  [AAlg_RMod A] 的态射，只是包装被移除了，而  [aalg_linear_of_module_hom] 和  [module_hom_of_aalg_linear] 是两个通道，在通过  [eq_refl] 的基础映射上互为逆映。
*)

Record AAlgLinear {K : CRng} (V : RModObject (`1 K)) (A : AAlgObject K) := {
  alin_map :> SetoidMorphism (cmon_setoid V) (rig_setoid (aalg_ring A));

  alin_add : ∀ v w,
    alin_map (cmon_plus V v w)
      ≈ rig_add (aalg_ring A) (alin_map v) (alin_map w);
  alin_smul : ∀ r v,
    alin_map (rm_smul V r v)
      ≈ rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) (alin_map v)
}.

Arguments alin_map {K V A} _.
Arguments alin_add {K V A} _ _ _.
Arguments alin_smul {K V A} _ _ _.

Program Definition AAlgLinear_Setoid {K : CRng} (V : RModObject (`1 K))
  (A : AAlgObject K) : Setoid (AAlgLinear V A) := {|
  equiv := fun f g => ∀ v, alin_map f v ≈ alin_map g v
|}.
Next Obligation.
  intros K V A.
  constructor.
  - intros f v; reflexivity.
  - intros f g Hfg v; symmetry; apply Hfg.
  - intros f g h Hfg Hgh v; transitivity (alin_map g v);
      [ apply Hfg | apply Hgh ].
Qed.

(*
 An additive map is zero at zero, by cancellation in the target's
 additive group. 

 --------
 在目标加法群中，通过消去，一个加法映射在零点处为零。
*)
Lemma alin_zero {K : CRng} {V : RModObject (`1 K)} {A : AAlgObject K}
  (f : AAlgLinear V A) :
  alin_map f (cmon_zero V) ≈ rig_zero (aalg_ring A).
Proof.
  apply (ab_cancel_l (ring_ab (aalg_ring A)) (alin_map f (cmon_zero V))).
  simpl.
  rewrite <- (alin_add f (cmon_zero V) (cmon_zero V)).
  rewrite (proper_morphism (alin_map f) _ _
             (cmon_plus_zero_l V (cmon_zero V))).
  symmetry; apply rig_add_zero_r.
Qed.

Definition aalg_linear_of_module_hom {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) : AAlgLinear V A := {|
  alin_map   := cmon_map (rm_hom h);
  alin_add   := cmon_map_plus (rm_hom h);
  alin_smul  := rm_map_smul h
|}.

Program Definition module_hom_of_aalg_linear {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) : RModHom V (AAlg_RMod A) := {|
  rm_hom := {| cmon_map := alin_map f;
               cmon_map_zero := alin_zero f;
               cmon_map_plus := alin_add f |};
  rm_map_smul := alin_smul f
|}.

(* Both passages leave the underlying map alone, on the nose. / 两段文字都保持了底层地图本身，完全精准。 *)
Example aalg_linear_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) :
  alin_map (aalg_linear_of_module_hom (module_hom_of_aalg_linear f))
    = alin_map f := eq_refl.

Example module_hom_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) :
  cmon_map (rm_hom (module_hom_of_aalg_linear (aalg_linear_of_module_hom h)))
    = cmon_map (rm_hom h) := eq_refl.

(*
 The identity map of an algebra IS K-linear from its own underlying
 module: both laws hold by [reflexivity], the action of [AAlg_RMod]
 being multiplication by the image of the scalar.  This is the cheapest
 non-trivial linear map available, and it is uniform in A. 

 --------
 一个代数的恒等映射是从其自身底层模到 K-线性的：两条定律都通过 [reflexivity] 成立，[AAlg_RMod] 的作用是通过标量的像进行乘法。这是可用的最简单的非平凡线性映射，并且它在 A 中是统一的。
*)
Program Definition alin_id {K : CRng} (A : AAlgObject K)
  : AAlgLinear (AAlg_RMod A) A := {|
  alin_map := setoid_morphism_id
|}.
Next Obligation. intros K A v w; simpl; reflexivity. Qed.
Next Obligation. intros K A r v; simpl; reflexivity. Qed.

Example alin_id_computes {K : CRng} (A : AAlgObject K)
  (a : carrier (rig_setoid (aalg_ring A))) :
  alin_map (alin_id A) a = a := eq_refl.

(*
 Postcomposition with an algebra map carries a linear map to a linear
 map — the action on which the universal property is stated. 

 --------
 与代数映射的后合成将线性映射带到线性映射——其上陈述了通用性质的作用。
*)
Program Definition alin_compose {K : CRng} {V : RModObject (`1 K)}
  {A B : AAlgObject K} (g : AAlgHom A B) (f : AAlgLinear V A)
  : AAlgLinear V B := {|
  alin_map := setoid_morphism_compose (rig_map (`1 g)) (alin_map f)
|}.
Next Obligation.
  intros K V A B g f v w; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_add f v w)).
  apply (rig_map_add (`1 g)).
Qed.
Next Obligation.
  intros K V A B g f r v; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_smul f r v)).
  rewrite (rig_map_mul (`1 g)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 g r).
Qed.

(*
   * ** Commutative algebras sit inside associative ones

   The inclusion needs no data on morphisms: [KAlgHom] and [AAlgHom] are
   the same type once the objects are matched, so fullness and
   faithfulness are the identity implication.  On objects, commutativity
   supplies centrality. 

   --------
   * ** 交换代数位于结合代数之内

   这种包含不需要关于态射的数据：一旦对象匹配，[KAlgHom] 和 [AAlgHom] 是相同类型，因此丰裕性和忠实性就是恒等的含义。在对象上，交换性提供了中心性。
*)

Definition AAlg_of_KAlg {K : CRng} (A : KAlgObject K) : AAlgObject K := {|
  aalg_ring := kalg_ring A;
  aalg_unit := kalg_unit A;
  aalg_central := fun k a => kalg_comm A (rig_map (kalg_unit A) k) a
|}.

Program Definition KAlg_AAlg (K : CRng) : KAlg K ⟶ AAlg K := {|
  fobj := @AAlg_of_KAlg K;
  fmap := fun A B f => (`1 f; `2 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

#[export] Instance KAlg_AAlg_Faithful (K : CRng) : Faithful (KAlg_AAlg K).
Proof. constructor; intros A B f g E; exact E. Qed.

#[export] Instance KAlg_AAlg_Full (K : CRng) : Full (KAlg_AAlg K).
Proof.
  unshelve econstructor.
  - intros A B g; exact (`1 g; `2 g).
  - intros A B g a; simpl; reflexivity.
Qed.

(*
   * ** The base ring is an algebra over itself

   So [AAlg K] is inhabited for every K, with no witness-hunting: the
   structure map is the identity and centrality IS K's own
   commutativity. 

   --------
   * ** 基环是自身上的代数

   因此对于每个 K，[AAlg K] 都是非空的，无需寻找证据：
   结构映射就是恒等映射，而中心性就是 K 自身的交换性。
*)
Definition Base_AAlg (K : CRng) : AAlgObject K := {|
  aalg_ring := `1 K;
  aalg_unit := @id Rng (`1 K);
  aalg_central := fun k a => `2 K k a
|}.

Example Base_AAlg_unit (K : CRng) (k : carrier (rig_setoid (`1 K))) :
  rig_map (aalg_unit (Base_AAlg K)) k = k := eq_refl.

(*
   * * A non-commutative witness: upper-triangular 2×2 integer matrices

   The matrix [[a, b], [0, c]] is carried as the triple (a, b, c).  This
   is built by hand rather than read off Instance/Matr.v because that
   file's [Matr] is a CATEGORY of matrices, not a ring: its objects are
   the naturals and there is no [RingObject] anywhere in its output.
   The tree contained no non-commutative [RingObject] at all before this
   file — Instance/Mod/Tensor.v's deferral list says so in terms — so
   the witness is new, not a re-packaging. 

   --------
   * * 一个非交换的证据：上三角 2×2 整数矩阵

   矩阵 [[a, b], [0, c] 被表示为三元组 (a, b, c)。这不是从 Instance/Matr.v 文件中读取的，而是手工构建的，因为该文件的 [Matr] 是一个矩阵的 CATEGORY，而不是一个环：它的对象是自然数，并且其输出中没有 [RingObject]。
   在此文件之前的树中根本没有非交换的 [RingObject] —— Instance/Mod/Tensor.v 的延迟列表已经在术语上说明了这一点 —— 因此这个证据是新的，而不是重新打包的。
*)

Definition ut2 : Type := (Z * Z * Z)%type.

Definition ut2_eqT (x y : ut2) : Type := x = y.

Lemma ut2_eqT_Equivalence : Equivalence ut2_eqT.
Proof.
  constructor; unfold ut2_eqT.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition ut2_setoid_object : SetoidObject := {|
  carrier := ut2;
  is_setoid := {| equiv := ut2_eqT; setoid_equiv := ut2_eqT_Equivalence |}
|}.

Definition ut2_zero : ut2 := (0, 0, 0)%Z.
Definition ut2_one : ut2 := (1, 0, 1)%Z.

Definition ut2_add (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') => ((a + a')%Z, (b + b')%Z, (c + c')%Z)
  end.

Definition ut2_neg (x : ut2) : ut2 :=
  match x with (a, b, c) => ((- a)%Z, (- b)%Z, (- c)%Z) end.

(* [[a,b],[0,c]] · [[a',b'],[0,c']] = [[a a', a b' + b c'], [0, c c']] / [[a,b] , [0,c] ] · [[a',b'] , [0,c'] ] = [[a a', a b' + b c'] , [0, c c'] ] *)
Definition ut2_mul (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') =>
      ((a * a')%Z, (a * b' + b * c')%Z, (c * c')%Z)
  end.

(* The scalar diagonal r ↦ [[r, 0], [0, r]]. / 标量对角线 r ↦ [[r, 0] , [0, r] ]。 *)
Definition ut2_scal (r : Z) : ut2 := (r, 0, r)%Z.

Lemma ut2_eq3 (a b c a' b' c' : Z) :
  a = a' → b = b' → c = c' → ((a, b, c) : ut2) = (a', b', c').
Proof. intros H1 H2 H3; now subst. Qed.

Ltac ut2_crunch :=
  cbv beta iota delta [ut2_eqT ut2_add ut2_neg ut2_mul ut2_zero ut2_one ut2_scal];
  apply ut2_eq3; ring.

Ltac ut2_1 := intros [[? ?] ?]; ut2_crunch.
Ltac ut2_2 := intros [[? ?] ?] [[? ?] ?]; ut2_crunch.
Ltac ut2_3 := intros [[? ?] ?] [[? ?] ?] [[? ?] ?]; ut2_crunch.

Lemma ut2_add_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_add.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Lemma ut2_mul_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_mul.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2_Rig : RigObject := {|
  rig_setoid := ut2_setoid_object;
  rig_zero := ut2_zero;
  rig_add := ut2_add;
  rig_one := ut2_one;
  rig_mul := ut2_mul;
  rig_add_respects := ut2_add_respects;
  rig_mul_respects := ut2_mul_respects;
  (*
 Since the PR “algebraic carriers are sets” (2026-09-17) a [RigObject]
 carries a [PropEquiv] for its carrier.  [ut2_eqT] is Coq's [eq] under a
 [Type] ascription, hence already a [Prop]-valued relation, so it is its
 own mirror and both implications are the identity. 

 --------
 自从 PR “代数承载是集合”（2026-09-17）以来，[RigObject] 为其承载提供了 [PropEquiv]。[ut2_eqT] 是 Coq 在 [Type] 指定下的 [eq]，因此已经是一个 [Prop] 值的关系，所以它是它自身的镜像，并且两个蕴含都是恒等的。
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid ut2_setoid_object)
                (@eq ut2) (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_2. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.

Lemma ut2_neg_respects : Proper (ut2_eqT ==> ut2_eqT) ut2_neg.
Proof. intros x y Hxy; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2 : RingObject := {|
  ring_rig := UT2_Rig;
  ring_neg := ut2_neg;
  ring_neg_respects := ut2_neg_respects
|}.
Next Obligation. ut2_1. Qed.

(*
 The scalar diagonal ℤ → UT2, whose image is central because ℤ is
 commutative. 

 --------
 标量对角线 ℤ → UT2，其像是中心的，因为 ℤ 是可交换的。
*)
(*
 The respectfulness witness is written out as a pointwise term rather
 than left to instance resolution — the engineering finding recorded in
 Theory/Universal/Element.v, where resolving [Proper] at a concrete
 setoid pinned a carrier universe. 

 --------
 尊重性证据被写成逐点项，而不是交给实例解析——这是在 Theory/Universal/Element.v 中记录的工程发现，其中在具体集合等价关系上解析 [Proper] 固定了一个承载宇宙。
*)
Definition ut2_scal_proper
  : Proper (@equiv _ (is_setoid Z_setoid_object)
              ==> @equiv _ (is_setoid ut2_setoid_object)) ut2_scal :=
  fun r s H => f_equal (fun z : Z => ((z, 0, z) : ut2)%Z) H.

Definition ut2_scal_morphism
  : SetoidMorphism (is_setoid Z_setoid_object) (is_setoid ut2_setoid_object) :=
  {| morphism := ut2_scal; proper_morphism := ut2_scal_proper |}.

(*
 Stated over plain [Z] rather than over [carrier Int_Ring]: the [ring]
 tactic reads the ring structure off the syntactic type of the
 equation, and it does not see through [carrier].  The obligations
 below then close by conversion. 

 --------
 陈述在普通的 [Z] 上，而不是在 [carrier Int_Ring] 上：[ring] 策略从方程的句法类型读取环结构，它无法看穿 [carrier]。下面的义务随后通过转换闭合。
*)
Lemma ut2_scal_add (a b : Z) :
  ut2_scal (a + b)%Z = ut2_add (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_add; apply ut2_eq3; ring. Qed.

Lemma ut2_scal_mul (a b : Z) :
  ut2_scal (a * b)%Z = ut2_mul (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_mul; apply ut2_eq3; ring. Qed.

Program Definition ut2_scalar : Int_Ring ~{Rng}~> UT2 := {|
  rig_map := ut2_scal_morphism
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_add a b). Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_mul a b). Qed.

Lemma ut2_scalar_central : ∀ (k : Z) (a : ut2),
  rig_mul UT2 (rig_map ut2_scalar k) a ≈ rig_mul UT2 a (rig_map ut2_scalar k).
Proof. intros k [[x y] z]; ut2_crunch. Qed.

Definition UT2_AAlg : AAlgObject Int_CRng :=
  Build_AAlgObject Int_CRng UT2 ut2_scalar ut2_scalar_central.

(* The two matrix units E11 and E12 do not commute: E11·E12 = E12 while E12·E11 = 0. / 两个矩阵单位 E11 和 E12 不可交换：E11·E12 = E12，而 E12·E11 = 0。 *)
Definition ut2_e11 : ut2 := (1, 0, 0)%Z.
Definition ut2_e12 : ut2 := (0, 1, 0)%Z.

Example ut2_e11_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.
Example ut2_e12_e11 : rig_mul UT2 ut2_e12 ut2_e11 = ut2_zero := eq_refl.

Theorem UT2_not_commutative :
  rig_mul UT2 ut2_e11 ut2_e12 ≈ rig_mul UT2 ut2_e12 ut2_e11 → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

(*
 Hence [AAlg] does not consist of commutative algebras: the witness is
 an object of [AAlg Int_CRng] whose ring is not commutative. 

 --------
 因此 [AAlg] 并不由交换代数组成：证据是 [AAlg Int_CRng] 中的一个对象，其环不是交换的。
*)
Theorem AAlg_not_all_commutative :
  (∀ (A : AAlgObject Int_CRng) a b,
     rig_mul (aalg_ring A) a b ≈ rig_mul (aalg_ring A) b a) → False.
Proof.
  intro H.
  exact (UT2_not_commutative (H UT2_AAlg ut2_e11 ut2_e12)).
Qed.

(* ...and the same witness is outside the image of [KAlg_AAlg] on the nose: no [KAlgObject] has [UT2] for its ring. / ...同样的证人在[KAlg_AAlg]的图像之外，在鼻子上：没有[KAlgObject]有[UT2]的环。 *)
Theorem UT2_not_in_KAlg (A : KAlgObject Int_CRng) :
  kalg_ring A = UT2 → False.
Proof.
  destruct A as [Ar Acomm Aunit]; simpl; intro HA; subst Ar.
  exact (UT2_not_commutative (Acomm ut2_e11 ut2_e12)).
Qed.

(*
   * The base-ring algebra and the matrix algebra are both objects, so
   [AAlg Int_CRng] has at least two, and a morphism between them: the
   scalar diagonal is itself a map of ℤ-algebras. 

   --------
   * 基环代数和矩阵代数都是对象，所以 [AAlg Int_CRng] 至少有两个，以及它们之间的一个态射：标量对角线本身就是一个 ℤ-代数的映射。
*)
Lemma ut2_scalar_triangle :
  aalg_unit UT2_AAlg ≈ ut2_scalar ∘ aalg_unit (Base_AAlg Int_CRng).
Proof. intro r; simpl; reflexivity. Qed.

Definition Base_to_UT2 : Base_AAlg Int_CRng ~{AAlg Int_CRng}~> UT2_AAlg :=
  (ut2_scalar; ut2_scalar_triangle).

(* The underlying module of UT2 has the expected action: scalars act entrywise, and it computes. / UT2 的底层模块具有预期的行为：标量按元素作用，并且它会进行计算。 *)
Example ut2_module_action :
  rm_smul (AAlg_RMod UT2_AAlg) 3%Z (2, 5, 7)%Z = (6, 15, 21)%Z := eq_refl.
