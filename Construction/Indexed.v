Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(* * * Indexed categories: the coherent pseudofunctor-lite / * * 索引类别：相干伪函子-lite *)

(*
 nLab:      https://ncatlab.org/nlab/show/indexed+category
 nLab:      https://ncatlab.org/nlab/show/pseudofunctor
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

 An indexed category over a base category [B] assigns to every object
 [x : B] a fibre category [idx_fib x] and to every morphism [f : x ~> y] a
 reindexing functor [idx_map f : idx_fib x ⟶ idx_fib y] — covariantly here,
 matching the opfibration that the Grothendieck construction
 (Construction/Grothendieck.v) produces; the classical contravariant
 presentation of an indexed category as a pseudofunctor out of [B^op] is
 recovered by instantiating the base at [B^op].  Functoriality holds only up
 to *chosen, coherent* natural isomorphisms:

 - [idx_resp] mediates reindexing along equivalent base morphisms (B's homs
 are setoids, so [idx_map] can respect [≈] only up to isomorphism),
 - [idx_id] compares [idx_map id] with the identity functor,
 - [idx_comp] compares [idx_map f ∘ idx_map g] with [idx_map (f ∘ g)],

 subject to naturality in the fibre argument and to the pseudofunctor
 coherence laws: proof irrelevance and transitivity for [idx_resp]
 ([idx_resp_id], [idx_resp_trans]), the unit laws [idx_unit_left] and
 [idx_unit_right], the associativity cocycle [idx_cocycle], and
 compatibility of [idx_comp] with [idx_resp] in each base-morphism
 argument ([idx_comp_resp_l], [idx_comp_resp_r]).  This is
 “pseudofunctor-lite”: exactly the coherent data that the Grothendieck
 construction consumes, with no 2-categorical superstructure.

 HONESTY NOTE (binding design decision).  In this library a bare
 [Functor B Cat] does NOT suffice for the Grothendieck construction: Cat's
 hom-equivalence is [Functor_Setoid], so [fmap_comp], [fmap_id] and
 [fmap_respects] are *chosen natural isos carrying no coherence between
 different applications* — an adversarial instance can twist [fmap_comp] by
 a nontrivial central automorphism in a fibre, and the total category's
 associativity becomes unprovable.  [StrictCat]-valued functors shift the
 problem to coherence of propositional object-equality proofs (no UIP in
 general).  The honest “pseudofunctor-lite” is therefore an explicit
 coherent-data record, [IndexedCat], with the cocycle and unit coherence as
 fields; constructors are provided elsewhere in this development (a) from
 split cleavages, where the coherence is trivial
 (Construction/Grothendieck/RoundTrip.v), and (b) from [F : B ⟶ StrictCat]
 under fibrewise UIP, dischargeable via Hedberg wherever object equality is
 decidable (as in FinSet-like fibres); the constructor and a local Hedberg
 live in Construction/Grothendieck/Strict.v, whose only concrete Grothendieck
 is the constant one, so the UIP branch is proven but not itself instantiated
 on a decidable fibre.
 Displayed categories (Theory/Displayed.v) remain the primitive Coq-friendly
 presentation.

 Shape of the twist counterexample.  Fix any [F : B ⟶ Cat] having a fibre
 with a nontrivial central automorphism [θ] (e.g. a one-object fibre given
 by a group with nontrivial centre), and fix one composable pair [(f, g)]
 in [B].  Because [Cat] compares functors by [Functor_Setoid], the functor
 law [fmap_comp f g : fmap (f ∘ g) ≈ fmap f ∘ fmap g] is *data*: a natural
 isomorphism chosen independently at each pair of morphisms.  Replace the
 chosen iso at exactly the pair [(f, g)] by its composite with [θ].
 Centrality keeps every component natural, and every [Functor] law still
 holds, because each law constrains one application at a time and never
 relates [fmap_comp f g] to [fmap_comp (f ∘ g) h] or to [fmap_comp g h].
 Yet associativity of composition in the would-be total category is
 precisely such a cross-application equation — the cocycle [idx_cocycle]
 below — and the twist breaks it, since it introduces a stray factor of
 [θ ≠ id] on one side only.  Hence the coherence must be carried as data,
 in the fields below, rather than recovered from bare functoriality. 

 --------
 nLab:       https://ncatlab.org/nlab/show/indexed+category 
 nLab:       https://ncatlab.org/nlab/show/pseudofunctor 
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+construction 
 Wikipedia:  https://en.wikipedia.org/wiki/Grothendieck_construction 

 在一个基类  [B]  上的索引范畴为每个对象
 [x : B] 指派一个纤维范畴  [idx_fib x]，并为每个态射  [f : x ~> y] 指派一个
 重新索引函子  [idx_map f : idx_fib x ⟶ idx_fib y] ——这里是协变的，
 对应于 Grothendieck 构造（Construction/Grothendieck.v）生成的上纤维；
 将一个索引范畴经典的逆变表示作为从  [B^op] 出发的伪函子，可通过在 [B^op] 上实例化基类来恢复。
 函子性仅在 *选定的、相容的* 自然同构下成立：-  [idx_resp] 对等基态同态（B 的 hom 是集合同构体，所以 [idx_map] 只能在同构意义上尊重 [≈]）进行重新索引，
 -  [idx_id] 将 [idx_map id] 与恒等函子进行比较，
 -  [idx_comp] 将 [idx_map f ∘ idx_map g] 与 [idx_map (f ∘ g)] 进行比较，

 需满足纤维变量的自然性以及伪函子一致性律：[idx_resp]（[idx_resp_id], [idx_resp_trans]）的证明无关性和传递性，单位律 [idx_unit_left] 和 [idx_unit_right]，结合律 cocycle [idx_cocycle]，以及 [idx_comp] 与 [idx_resp] 在每个基态同态参数下的兼容性（[idx_comp_resp_l], [idx_comp_resp_r]）。 这是“伪函子轻量版”：完全是 Grothendieck 构造所需的相容数据，没有 2-范畴上的超结构。诚信说明（具有约束性的设计决定）。在这个库中，一个裸露的 [Functor B Cat] 对于 Grothendieck 构造来说是不够的：Cat 的 hom-等价是 [Functor_Setoid]，因此 [fmap_comp]、[fmap_id] 和 [fmap_respects] 是*选择的自然同构，但不同应用之间不具备一致性*——一个对抗性实例可以通过纤维中的非平凡中心自同构扭曲 [fmap_comp]，从而整个范畴的结合律变得无法证明。[StrictCat] 值函子将问题转移到命题对象等式证明的一致性上（通常不存在 UIP）。因此，真正的“伪函子轻量版”是一个显式的连续性数据记录 [IndexedCat]，其中包含 cocycle 和单位连续性作为字段；构造函数在本开发的其他地方提供：(a) 来自分裂劈裂的构造，其中连续性是平凡的 (Construction/Grothendieck/RoundTrip.v)，以及 (b) 来自 [F : B ⟶ StrictCat] 在纤维上的 UIP 条件下，可通过 Hedberg 在对象相等可判定时消解（如在类似 FinSet 的纤维中）；构造函数和本地 Hedberg 位于 Construction/Grothendieck/Strict.v，其唯一具体的 Grothendieck 是常量的，因此 UIP 分支已被证明，但本身未在可判定纤维上实例化。显示的范畴 (Theory/Displayed.v) 仍然是原始的、适合 Coq 的呈现方式。扭曲反例的形状。固定任何具有非平凡中心自同构纤维的  [F : B ⟶ Cat] （例如一个由具有非平凡中心的群给出的单对象纤维），并在  [B] 中固定一对可复合的 [(f, g)]。因为  [Cat] 通过  [Functor_Setoid] 比较函子，所以函子定律  [fmap_comp f g : fmap (f ∘ g) ≈ fmap f ∘ fmap g] 是*数据*：在每对态射中独立选择的自然同构。在正好的一对  [(f, g)] 上，将选定的同构替换为其与  [θ] 的复合。中心性保持每个分量的自然性，并且每个  [Functor] 定律仍然成立，因为每条定律一次约束一次应用，并且从不将  [fmap_comp f g] 与  [fmap_comp (f ∘ g) h] 或  [fmap_comp g h] 联系起来。然而，在假设的全类别中，复合的结合性正是这样一个跨应用方程 —— 下面的旋子 [idx_cocycle] —— 而扭曲会破坏它，因为它只在一边引入了一个额外的因子 [θ ≠ id]。因此，相干性必须作为数据在下面的字段中携带，而不是从纯函子性中恢复。
*)

Record IndexedCat (B : Category) : Type := {
  idx_fib : B → Category;

  idx_map {x y : B} (f : x ~> y) : idx_fib x ⟶ idx_fib y;

  (*
 Reindexing respects ≈ on base morphisms, up to a chosen fibre iso,
 natural in the fibre argument and proof-irrelevant ([idx_resp_id],
 [idx_resp_trans] make any two such isos agree). 

 --------
 重索引在基态态射上尊重 ≈，在所选择的纤维同构下，自然于纤维参数，并且与证明无关（[idx_resp_id]，[idx_resp_trans] 使任何两个这样的同构一致）。
*)
  idx_resp {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib x) :
    idx_map f a ≅[idx_fib y] idx_map g a;
  idx_resp_natural {x y : B} {f g : x ~> y} (e : f ≈ g)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map g] k ∘ to (idx_resp e a)
      ≈ to (idx_resp e b) ∘ fmap[idx_map f] k;
  idx_resp_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib x) :
    to (idx_resp e a) ≈ id;
  idx_resp_trans {x y : B} {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h)
                 (a : idx_fib x) :
    to (idx_resp e2 a) ∘ to (idx_resp e1 a)
      ≈ to (idx_resp (Equivalence_Transitive _ _ _ e1 e2) a);

  (*
 Unit: reindexing along the identity is isomorphic to doing nothing,
 naturally in the fibre argument. 

 --------
 单位：沿恒等映射的重新索引同构于什么都不做，在纤维论证中是自然的。
*)
  idx_id {x : B} (a : idx_fib x) : idx_map (@id B x) a ≅ a;
  idx_id_natural {x : B} {a b : idx_fib x} (k : a ~> b) :
    k ∘ to (idx_id a) ≈ to (idx_id b) ∘ fmap[idx_map (@id B x)] k;

  (*
 Composition: reindexing twice is isomorphic to reindexing along the
 composite, naturally in the fibre argument. 

 --------
 组合：对索引进行两次重索引与沿复合进行重索引是同构的，并且在纤维参数中是自然的。
*)
  idx_comp {x y z : B} (f : y ~> z) (g : x ~> y) (a : idx_fib x) :
    idx_map f (idx_map g a) ≅ idx_map (f ∘ g) a;
  idx_comp_natural {x y z : B} (f : y ~> z) (g : x ~> y)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map (f ∘ g)] k ∘ to (idx_comp f g a)
      ≈ to (idx_comp f g b) ∘ fmap[idx_map f] (fmap[idx_map g] k);

  (*
 Compatibility of the composition isos with the ≈-mediators: [idx_comp]
 is natural in each base-morphism argument, with [idx_resp] supplying
 the connecting components.  Bicategorically, a pseudofunctor's
 compositor is natural in both 1-cell arguments; here the 2-cells are
 proofs of ≈, so naturality says that reindexing along equivalent
 composites commutes with the chosen composition isos.  These fields
 are not derivable from the others: on the one-object base with
 hom-monoid (ℤ, +) under congruence mod 2, with a one-object fibre
 whose hom-group is (ℤ, +) and every [idx_map] the identity functor,
 take every [idx_resp] and [idx_id] iso to be the identity and
 [idx_comp f g] to be the bilinear twist f·g.  Bilinearity is exactly
 the cocycle, and f·g vanishes when either argument is 0, so every
 other field holds; yet [idx_comp (f+2) g] and [idx_comp f g] differ
 by 2·g ≠ 0, violating the left compatibility below.  The Grothendieck
 construction (Construction/Grothendieck.v) consumes exactly these
 fields to interchange [dtransport] with [dcomp] ([dtransport_comp_l]
 and [dtransport_comp_r] of Theory/Displayed.v).  The composite-side
 proof [e'] is universally quantified rather than pinned to the
 canonical [compose_respects] witness; by proof irrelevance of
 [idx_resp] the two phrasings are interderivable. 

 --------
 与≈-介子兼容的组合同构：[idx_comp]在每个基态态射参数中是自然的，而[idx_resp]提供连接分量。从双范畴的角度来看，一个伪函子的组合子在两个1-胞参数中都是自然的；这里的2-胞是≈的证明，因此自然性意味着沿等价复合的重新索引与所选择的组合同构是交换的。这些域不能从其他域导出：在具有同余模2的同态单子(ℤ, +)的一对象基底下，具有单对象纤维，其同态群是(ℤ, +)，并且每个[idx_map]都是恒等函子，取每个[idx_resp]和[idx_id]同构为恒等，[idx_comp f g]为双线性交换f·g。双线性恰好是
 余环，而 f·g 在任一参数为 0 时消失，所以其他所有字段都成立；然而 [idx_comp (f+2) g] 和 [idx_comp f g] 相差 2·g ≠ 0，违反了下面的左兼容性。Grothendieck 构造 (Construction/Grothendieck.v) 精确地使用这些字段来互换 [dtransport] 和 [dcomp]（Theory/Displayed.v 中的 [dtransport_comp_l] 和 [dtransport_comp_r]）。复合侧证明 [e'] 是全称量化的，而不是固定在典型的 [compose_respects] 见证上；根据 [idx_resp] 的证明无关性，这两种表述可以相互推导。
*)
  idx_comp_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
                  (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib x) :
    to (idx_comp f' g a) ∘ to (idx_resp e (idx_map g a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);
  idx_comp_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
                  (e' : f ∘ g ≈ f ∘ g') (a : idx_fib x) :
    to (idx_comp f g' a) ∘ fmap[idx_map f] (to (idx_resp e a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);

  (*
 Pseudofunctor coherence: the unit isos and the composition isos agree
 with each other across applications.  These are the cross-application
 equations that a bare [Functor B Cat] cannot supply (see the honesty
 note above); Construction/Grothendieck.v discharges the [Displayed]
 laws of the total category from exactly these fields. 

 --------
 伪函子一致性：单位同构和复合同构在各种应用中彼此一致。这些是一个裸 [Functor B Cat] 无法提供的跨应用方程（见上述诚实性说明）；Construction/Grothendieck.v 正是从这些字段中解除总范畴的 [Displayed] 定律。
*)
  idx_unit_left {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_left f) a) ∘ to (idx_comp id f a)
      ≈ to (idx_id (idx_map f a));
  idx_unit_right {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_right f) a) ∘ to (idx_comp f id a)
      ≈ fmap[idx_map f] (to (idx_id a));
  idx_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
              (a : idx_fib w) :
    to (idx_comp (f ∘ g) h a) ∘ to (idx_comp f g (idx_map h a))
      ≈ to (idx_resp (comp_assoc f g h) a)
          ∘ to (idx_comp f (g ∘ h) a) ∘ fmap[idx_map f] (to (idx_comp g h a))
}.

Arguments idx_fib {B} _ _.
Arguments idx_map {B} _ {x y} _.
Arguments idx_resp {B} _ {x y f g} _ _.
Arguments idx_resp_natural {B} _ {x y f g} _ {a b} _.
Arguments idx_resp_id {B} _ {x y f} _ _.
Arguments idx_resp_trans {B} _ {x y f g h} _ _ _.
Arguments idx_id {B} _ {x} _.
Arguments idx_id_natural {B} _ {x a b} _.
Arguments idx_comp {B} _ {x y z} _ _ _.
Arguments idx_comp_natural {B} _ {x y z} _ _ {a b} _.
Arguments idx_comp_resp_l {B} _ {x y z f f'} _ _ _ _.
Arguments idx_comp_resp_r {B} _ {x y z} _ {g g'} _ _ _.
Arguments idx_unit_left {B} _ {x y} _ _.
Arguments idx_unit_right {B} _ {x y} _ _.
Arguments idx_cocycle {B} _ {w x y z} _ _ _ _.

(*
 Derived corollaries of the [idx_resp] coherence fields.  These are the
 forms the Grothendieck construction actually consumes: its [dtransport]
 post-composes with [from (idx_resp _ _)], so the [from]-side restatements
 of identity, transitivity, proof irrelevance and naturality are collected
 here once, rather than re-derived at every use site. 

 --------
 [idx_resp] 相干场的推导推论。这些是 Grothendieck 构造实际使用的形式：其 [dtransport] 在组合时与 [from (idx_resp _ _)] 后置组合，因此 [from] 方面的同一性、传递性、证明无关性和自然性的重述在这里集中列出，而不是在每个使用点重新推导。
*)
Section IndexedCatLemmas.

Context {B : Category}.
Context (A : IndexedCat B).

(*
 [idx_resp] at a reflexivity-flavoured proof has identity inverse as well:
 the [from]-side companion to [idx_resp_id]. 

 --------
 [idx_resp] 在一个带有反身性色彩的证明中也有单位逆：[from] 是 [idx_resp_id] 的对应伴随。
*)
Lemma idx_resp_from_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib A x) :
  from (idx_resp A e a) ≈ id.
Proof.
  rewrite <- (iso_from_to (idx_resp A e a)).
  rewrite (idx_resp_id A e a).
  now rewrite id_right.
Qed.

(*
 The chosen iso at a symmetric proof is the inverse of the chosen iso:
 [to] at [symmetry e] agrees with [from] at [e]. 

 --------
 在对称证明中选择的同构是所选同构的逆：
 [to] 在 [symmetry e] 与 [from] 在 [e] 相一致。
*)
Lemma idx_resp_to_sym {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib A x) :
  to (idx_resp A (symmetry e) a) ≈ from (idx_resp A e a).
Proof.
  apply (comp_inverse_unique (to (idx_resp A e a))).
  - rewrite (idx_resp_trans A (symmetry e) e a).
    apply idx_resp_id.
  - apply iso_from_to.
Qed.

(*
 Proof irrelevance: the chosen isos at any two proofs of [f ≈ g] agree.
 This is the [idx_resp_id]/[idx_resp_trans] pair in the form downstream
 proofs use directly. 

 --------
 证明无关性：在 [f ≈ g] 的任意两个证明中选择的同构是一致的。这是下游形式中直接使用的 [idx_resp_id] / [idx_resp_trans] 对。
*)
Lemma idx_resp_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  to (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  apply (comp_inverse_unique (from (idx_resp A e' a))).
  - rewrite <- (idx_resp_to_sym e' a).
    rewrite (idx_resp_trans A e (symmetry e') a).
    apply idx_resp_id.
  - apply iso_to_from.
Qed.

(*
 [from] at [symmetry e] agrees with [to] at [e]. 

 --------
 [from] 在 [symmetry e] 与 [to] 在 [e] 一致。
*)
Lemma idx_resp_from_sym {x y : B} {f g : x ~> y} (e : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A (symmetry e) a) ≈ to (idx_resp A e a).
Proof.
  rewrite <- (idx_resp_to_sym (symmetry e) a).
  apply idx_resp_irrel.
Qed.

(* Proof irrelevance on the [from] side. / 在 [from] 方面的证明无关性。 *)
Lemma idx_resp_from_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A e a) ≈ from (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym e a), <- (idx_resp_to_sym e' a).
  apply idx_resp_irrel.
Qed.

(*
 Transitivity on the [from] side: inverses compose in reverse order. 

 --------
 [from] 侧的传递性：逆元按相反顺序组合。
*)
Lemma idx_resp_from_trans {x y : B} {f g h : x ~> y}
      (e1 : f ≈ g) (e2 : g ≈ h) (a : idx_fib A x) :
  from (idx_resp A e1 a) ∘ from (idx_resp A e2 a)
    ≈ from (idx_resp A (Equivalence_Transitive _ _ _ e1 e2) a).
Proof.
  rewrite <- (idx_resp_to_sym e1 a), <- (idx_resp_to_sym e2 a),
          <- (idx_resp_to_sym (Equivalence_Transitive _ _ _ e1 e2) a).
  rewrite (idx_resp_trans A (symmetry e2) (symmetry e1) a).
  apply idx_resp_irrel.
Qed.

(*
 Naturality of [idx_resp] on the [from] side, by conjugating
 [idx_resp_natural] with the inverses. 

 --------
 通过用逆元共轭 [idx_resp_natural]，在 [from] 端上 [idx_resp] 的自然性。
*)
Lemma idx_resp_natural_from {x y : B} {f g : x ~> y} (e : f ≈ g)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] k ∘ from (idx_resp A e a)
    ≈ from (idx_resp A e b) ∘ fmap[idx_map A g] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] k)).
  rewrite <- (iso_from_to (idx_resp A e b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_resp_natural A e k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_resp A e a)).
  apply id_right.
Qed.

(* Naturality of [idx_id] on the [from] side. / [idx_id] 在 [from] 端的自然性。 *)
Lemma idx_id_natural_from {x : B} {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A (@id B x)] k ∘ from (idx_id A a) ≈ from (idx_id A b) ∘ k.
Proof.
  rewrite <- (id_left (fmap[idx_map A (@id B x)] k)).
  rewrite <- (iso_from_to (idx_id A b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_id_natural A k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_id A a)).
  apply id_right.
Qed.

(* Naturality of [idx_comp] on the [from] side. / [idx_comp] 在 [from] 一侧的自然性。 *)
Lemma idx_comp_natural_from {x y z : B} (f : y ~> z) (g : x ~> y)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] (fmap[idx_map A g] k) ∘ from (idx_comp A f g a)
    ≈ from (idx_comp A f g b) ∘ fmap[idx_map A (f ∘ g)] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] (fmap[idx_map A g] k))).
  rewrite <- (iso_from_to (idx_comp A f g b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_comp_natural A f g k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_comp A f g a)).
  apply id_right.
Qed.

End IndexedCatLemmas.
