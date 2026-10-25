Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/transport+of+structure

   Transport of monoidal structure along an equivalence of categories.
   Given an equivalence F : C ⟶ D with quasi-inverse G and a monoidal
   structure (I, ⨂, λ, ρ, α) on C, the category D acquires a monoidal
   structure with unit F I and tensor

       (d, d') ↦ F (G d ⨂ G d'),

   whose unitors and associator are assembled from the unit and counit
   isomorphisms of the equivalence together with the images under F of
   the unitors and associator of C.

   Two design points:

   1. STAGING.  The construction is delivered in two layers.  The record
      [MonoidalTransportData] packages the data of a monoidal structure
      *without* the triangle and pentagon coherence laws: unit, tensor,
      unitors, associator, and the six naturality squares.  The assembler
      [Monoidal_from_transport_data] upgrades such data to a genuine
      [Monoidal] once the two coherence laws are supplied.  The transported
      structure is first built as [Transported_Monoidal_Data]; the laws
      [Transported_triangle_identity] and [Transported_pentagon_identity]
      are the final lemmas of the file, and [Transported_Monoidal] puts the
      pieces together.

   2. THE RECTIFIED COUNIT.  An arbitrary quasi-inverse (G, unit, counit)
      need not satisfy the zig-zag identities, and the triangle law of the
      transported structure genuinely needs the zig-zag

          fmap[G] counit'_d ∘ unit_{G d} ≈ id.

      We therefore first correct the counit by the classical adjustment
          counit'_d := counit_d ∘ fmap[F] (defect_d)⁻¹,
          defect_d  := fmap[G] counit_d ∘ unit_{G d},
      which keeps G and the unit and makes the displayed zig-zag hold
      ([quasi_inverse_transport_counit]).  Consequently
      [fmap[G]] of the corrected counit *is* the inverse of the unit
      component, so every coherence computation happens purely in terms of
      the unit isomorphism and the structure of C.  The pentagon needs no
      zig-zag at all: the transported associator mentions only the unit.

   Everything here is a Definition, never an Instance (the [Monoidal_op]
   convention of Construction/Opposite/Monoidal.v): a transported monoidal
   structure is a choice, made explicitly at use sites.  Nothing in this
   file is registered for typeclass resolution.

--------
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
nLab: https://ncatlab.org/nlab/show/monoidal+category
nLab: https://ncatlab.org/nlab/show/transport+of+structure

沿着范畴的等价传输幺半群结构。
给定一个等价 F : C ⟶ D 及其准逆 G，以及 C 上的幺半群结构 (I, ⨂, λ, ρ, α)，范畴 D 将获得一个幺半群结构，其单位元为 F I，张量为

(d, d') ↦ F (G d ⨂ G d')，

其单位元和结合元是由等价的单位同构和余单位同构以及 C 的单位元和结合元在 F 下的像组装而成的。

两个设计要点：

1. 阶段。该构造以两层交付。记录 [MonoidalTransportData] 封装了一个幺半群结构的数据，*不包含*三角形和五边形的相干律：单位元、张量、单位子、结合子，以及六个自然性方格。汇编器 [Monoidal_from_transport_data] 在提供两条相干律后，将这些数据升级为真正的 [Monoidal]。传输的结构首先作为 [Transported_Monoidal_Data] 构建；定律 [Transported_triangle_identity] 和 [Transported_pentagon_identity] 是文件的最终引理，而 [Transported_Monoidal] 将各部分组合在一起。

2. 校正余单位。任意的准逆 (G, 单位, 余单位) 不必满足之字形恒等式，而传输结构的三角定律确实需要之字形恒等式

fmap[G] counit'_d ∘ unit_{G d} ≈ id.

因此，我们首先通过经典调整修正余单位 
          counit'_d := counit_d ∘ fmap[F] (defect_d)⁻¹,
          defect_d  := fmap[G] counit_d ∘ unit_{G d},
      这样可以保持 G 和单位，并使显示的之字形成立
      ([quasi_inverse_transport_counit])。因此
      [fmap[G]] 修正后的余单位 *确实* 是单位分量的逆，因此每个相干性计算完全依赖于单位同构和 C 的结构。五边形根本不需要任何之字形：传输的结合子仅提到单位。

这里的一切都是定义，从来不是实例（Construction/Opposite/Monoidal.v 的 [Monoidal_op] 约定）：一个传递的幺半群结构是在使用时明确选择的。这个文件中的内容没有注册用于类型类解析。
*)

#[local] Obligation Tactic := intros.

(*
Functorial images of isomorphisms are taken with the library's
   [fobj_iso] (Theory/Functor.v, the [Proper] instance for [fobj]): its
   [to] and [from] components are the literal [fmap] terms behind a
   transparent obligation, so the [*_unfold] equations below remain
   Leibniz (=) after unfolding.

--------
同构的函子像是用库的 [fobj_iso]（Theory/Functor.v，[fobj] 的 [Proper] 实例）获取的：它的 [to] 和 [from] 组件是一个透明义务背后的字面 [fmap] 项，所以下面的 [*_unfold] 方程在展开后仍然是 Leibniz (=) 的。
*)

(*
Rewriting toolkit for iso and [bimap] chains along left-nested
   composition spines, used by every coherence proof of the transported
   structure: composites are first normalized to the left-nested form
   (via [rewrite !comp_assoc]) and then advanced by spine lemmas, each
   keyed to match exactly one intended redex.  The toolkit is
   transport-agnostic infrastructure, so it is scoped inside a module:
   [Require Import]ing this file does not spill its generically named
   lemmas into the top-level namespace.  The transport development
   [Import]s it right below the module; downstream users opt in with
   [Import Category.Theory.Equivalence.Monoidal.MonoidalTransportSpine].

--------
用于沿左嵌套组合主干重写 iso 和 [bimap] 链的工具包，由每个传输结构的一致性证明使用：复合首先通过 [rewrite !comp_assoc] 归一化为左嵌套形式，然后通过主干引理推进，每个引理的键匹配恰好一个预期的可约表达式。该工具包是与传输无关的基础设施，因此它被限定在一个模块内：[Require Import] 本文件不会将其通用命名的引理泄露到顶层命名空间。传输开发 [Import] 就在模块下方；下游用户通过 [Import Category.Theory.Equivalence.Monoidal.MonoidalTransportSpine] 选择性使用。
*)

Module MonoidalTransportSpine.

(* Folding a pair of [fmap]s across a left-nested composition spine. / 将一对 [fmap] 沿左嵌套组合主轴折叠。 *)
Lemma fmap_fold_spine {A B : Category} (H : A ⟶ B) {t : B} {x y z : A}
  (X : H z ~> t) (f : y ~> z) (g : x ~> y) :
  (X ∘ fmap[H] f) ∘ fmap[H] g ≈ X ∘ fmap[H] (f ∘ g).
Proof.
  rewrite <- comp_assoc.
  now rewrite <- fmap_comp.
Qed.

Section IsoSpine.

Context {A : Category}.

(*
From a commuting square against the [to] components of two
   isomorphisms, derive the corresponding square against the [from]
   components.  This turns each to-naturality lemma below into its
   from-naturality companion.

--------
从关于两个同构的 [to] 分量的换位正方形出发，推导出相应的关于 [from] 分量的正方形。这将下面的每个“到自然性”引理转变为它的“从自然性”对应引理。
*)
Lemma iso_from_natural {x y x' y' : A}
  (i : x ≅ y) (j : x' ≅ y') (f : x ~> x') (g : y ~> y')
  (H : g ∘ to i ≈ to j ∘ f) :
  f ∘ from i ≈ from j ∘ g.
Proof.
  rewrite <- (id_left (f ∘ from i)).
  rewrite <- (iso_from_to j).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to j)).
  rewrite <- H.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* Cancelling a [to]/[from] pair at the tail of a left-nested spine. / 取消位于左嵌套脊尾部的 [to]/[from] 对。 *)
Lemma iso_cancel_spine_tf {t x y : A} (X : x ~> t) (i : y ≅ x) :
  (X ∘ to i) ∘ from i ≈ X.
Proof.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

Lemma iso_cancel_spine_ft {t x y : A} (X : x ~> t) (i : x ≅ y) :
  (X ∘ from i) ∘ to i ≈ X.
Proof.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  apply id_right.
Qed.

End IsoSpine.

(* The [bimap]-chain spine lemmas. / [bimap] 链脊引理。 *)
Section BimapSpine.

Context {J K L : Category}.
Context {T : J ∏ K ⟶ L}.

Lemma bimap_split_first {x y z : J} {v w : K}
  (g : x ~> y) (k : y ~> z) (h : v ~> w) :
  bimap[T] (k ∘ g) h ≈ bimap[T] k id ∘ bimap[T] g h.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_left.
Qed.

Lemma bimap_split_first' {x y z : J} {v w : K}
  (g : x ~> y) (k : y ~> z) (h : v ~> w) :
  bimap[T] (k ∘ g) h ≈ bimap[T] k h ∘ bimap[T] g id.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_right.
Qed.

Lemma bimap_split_second {x y : J} {v w u : K}
  (g : x ~> y) (h : v ~> w) (k : w ~> u) :
  bimap[T] g (k ∘ h) ≈ bimap[T] id k ∘ bimap[T] g h.
Proof.
  rewrite <- bimap_comp.
  now rewrite id_left.
Qed.

Lemma bimap_fold_spine {t : L} {x y z : J} {v w u : K}
  (X : T (y, w) ~> t) (f : x ~> y) (g : v ~> w) (h : z ~> x) (i : u ~> v) :
  (X ∘ bimap[T] f g) ∘ bimap[T] h i ≈ X ∘ bimap[T] (f ∘ h) (g ∘ i).
Proof.
  rewrite <- comp_assoc.
  now rewrite <- bimap_comp.
Qed.

Lemma bimap_swap_spine {t : L} {x y : J} {v w : K}
  (X : T (y, w) ~> t) (f : x ~> y) (g : v ~> w) :
  (X ∘ bimap[T] f (id[w])) ∘ bimap[T] (id[x]) g
    ≈ (X ∘ bimap[T] (id[y]) g) ∘ bimap[T] f (id[v]).
Proof.
  rewrite !bimap_fold_spine.
  rewrite !id_left.
  now rewrite !id_right.
Qed.

(* Cancelling an inverse pair of second components along the spine. / 沿脊柱取消第二组件的逆对。 *)
Lemma bimap_id_cancel_ft_spine {t : L} {x : J} {v w : K}
  (X : T (x, v) ~> t) (i : v ≅ w) :
  (X ∘ bimap[T] (id[x]) (from i)) ∘ bimap[T] (id[x]) (to i) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  apply id_right.
Qed.

(* Cancelling an inverse pair of first components along the spine. / 沿脊柱取消第一分量的反向对。 *)
Lemma bimap_cancel_ft_spine_l {t : L} {x y : J} {v : K}
  (X : T (x, v) ~> t) (i : x ≅ y) :
  (X ∘ bimap[T] (from i) (id[v])) ∘ bimap[T] (to i) (id[v]) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  apply id_right.
Qed.

End BimapSpine.

(*
The nested variant of [bimap_id_cancel_ft_spine]: the cancelling pair
   sits in the first slot of the second component, one bifunctor down.

--------
[bimap_id_cancel_ft_spine] 的嵌套变体：取消对位于第二组件的第一个位置，下降一个双函子。
*)
Lemma bimap_bimap_id_cancel_ft_spine
  {J K1 K2 K L : Category} {T : J ∏ K ⟶ L} {S : K1 ∏ K2 ⟶ K}
  {t : L} {a : J} {x' y' : K1} {v : K2}
  (X : T (a, S (x', v)) ~> t) (i : x' ≅ y') :
  (X ∘ bimap[T] (id[a]) (bimap[S] (from i) (id[v])))
    ∘ bimap[T] (id[a]) (bimap[S] (to i) (id[v])) ≈ X.
Proof.
  rewrite bimap_fold_spine.
  rewrite <- bimap_comp.
  rewrite iso_from_to.
  rewrite !id_left.
  rewrite !bimap_id_id.
  apply id_right.
Qed.

(*
Spine forms of the naturality of the associator and of the pentagon
   law of a monoidal category.

--------
单类范畴中结合子自然性的脊形态及五边形律的脊形态。
*)
Section MonoidalSpine.

Context {C : Category}.
Context (M : @Monoidal C).

Lemma alpha_natural_spine {t x y z w v u : C}
  (X : (y ⨂ (w ⨂ u)) ~> t) (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  (X ∘ bimap g (bimap h i)) ∘ tensor_assoc
    ≈ (X ∘ tensor_assoc) ∘ bimap (bimap g h) i.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply to_tensor_assoc_natural.
Qed.

Lemma alpha_natural_spine_r {t x y z w v u : C}
  (X : (y ⨂ (w ⨂ u)) ~> t) (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  (X ∘ tensor_assoc) ∘ bimap (bimap g h) i
    ≈ (X ∘ bimap g (bimap h i)) ∘ tensor_assoc.
Proof.
  symmetry.
  apply alpha_natural_spine.
Qed.

Lemma alpha_move_third_spine {t x y v u : C}
  (X : (x ⨂ (y ⨂ u)) ~> t) (i : v ~> u) :
  (X ∘ tensor_assoc) ∘ bimap (id[x ⨂ y]) i
    ≈ (X ∘ bimap (id[x]) (bimap (id[y]) i)) ∘ tensor_assoc.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- (@bimap_id_id _ _ _ (@tensor C M) x y).
  symmetry.
  apply to_tensor_assoc_natural.
Qed.

Lemma alpha_move_left_spine {t x y z w : C}
  (X : (y ⨂ (z ⨂ w)) ~> t) (g : x ~> y) :
  (X ∘ bimap g (id[z ⨂ w])) ∘ tensor_assoc
    ≈ (X ∘ tensor_assoc) ∘ bimap (bimap g (id[z])) (id[w]).
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- (@bimap_id_id _ _ _ (@tensor C M) z w).
  apply to_tensor_assoc_natural.
Qed.

Lemma pentagon_spine {t x y z w : C}
  (X : (x ⨂ (y ⨂ (z ⨂ w))) ~> t) :
  ((X ∘ bimap (id[x]) tensor_assoc) ∘ tensor_assoc)
      ∘ bimap tensor_assoc (id[w])
    ≈ (X ∘ tensor_assoc) ∘ tensor_assoc.
Proof.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply pentagon_identity.
Qed.

End MonoidalSpine.

End MonoidalTransportSpine.

Import MonoidalTransportSpine.

(* ------------------------------------------------------------------ *)
(* The staging record: monoidal data without the coherence laws. / 暂存记录：没有相干律的幺半群数据。       *)

Section TransportData.

Context (X : Category).

(*
The data of a monoidal structure on X — unit, tensor, unitors,
   associator, and the six naturality squares — with the triangle and
   pentagon laws deliberately left out.  This is the staging vehicle for
   transported structures: the data and naturality land first, the two
   coherence proofs are supplied separately to
   [Monoidal_from_transport_data].

--------
关于 X 上单模结构的数据——单位、张量、单位变换器、结合子，以及六个自然性方框——三角律和五边形律被故意省略。这是传输结构的预备阶段：首先传递数据和自然性，然后两个相干性证明会单独提供给 [Monoidal_from_transport_data]。
*)
Record MonoidalTransportData : Type := {
  transport_unit : X;
  transport_tensor : X ∏ X ⟶ X;

  transport_unit_left {x} :
    transport_tensor (transport_unit, x) ≅ x;
  transport_unit_right {x} :
    transport_tensor (x, transport_unit) ≅ x;
  transport_tensor_assoc {x y z} :
    transport_tensor (transport_tensor (x, y), z)
      ≅ transport_tensor (x, transport_tensor (y, z));

  transport_to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ transport_unit_left
      << transport_tensor (transport_unit, x) ~~> y >>
    transport_unit_left ∘ bimap[transport_tensor] id g;
  transport_from_unit_left_natural {x y} (g : x ~> y) :
    bimap[transport_tensor] id g ∘ transport_unit_left⁻¹
      << x ~~> transport_tensor (transport_unit, y) >>
    transport_unit_left⁻¹ ∘ g;

  transport_to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ transport_unit_right
      << transport_tensor (x, transport_unit) ~~> y >>
    transport_unit_right ∘ bimap[transport_tensor] g id;
  transport_from_unit_right_natural {x y} (g : x ~> y) :
    bimap[transport_tensor] g id ∘ transport_unit_right⁻¹
      << x ~~> transport_tensor (y, transport_unit) >>
    transport_unit_right⁻¹ ∘ g;

  transport_to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap[transport_tensor] g (bimap[transport_tensor] h i)
      ∘ transport_tensor_assoc
      << transport_tensor (transport_tensor (x, z), v)
           ~~> transport_tensor (y, transport_tensor (w, u)) >>
    transport_tensor_assoc
      ∘ bimap[transport_tensor] (bimap[transport_tensor] g h) i;
  transport_from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap[transport_tensor] (bimap[transport_tensor] g h) i
      ∘ transport_tensor_assoc⁻¹
      << transport_tensor (x, transport_tensor (z, v))
           ~~> transport_tensor (transport_tensor (y, w), u) >>
    transport_tensor_assoc⁻¹
      ∘ bimap[transport_tensor] g (bimap[transport_tensor] h i)
}.

(* The triangle coherence law over a [MonoidalTransportData]. / [MonoidalTransportData] 上的三角一致性法则。 *)
Definition transport_triangle (T : MonoidalTransportData) : Type :=
  ∀ x y,
    bimap[transport_tensor T] (to (transport_unit_right T)) id
      << transport_tensor T (transport_tensor T (x, transport_unit T), y)
           ~~> transport_tensor T (x, y) >>
    bimap[transport_tensor T] id (to (transport_unit_left T))
      ∘ to (transport_tensor_assoc T).

(* The pentagon coherence law over a [MonoidalTransportData]. / 五边形相干定律在 [MonoidalTransportData] 上。 *)
Definition transport_pentagon (T : MonoidalTransportData) : Type :=
  ∀ x y z w,
    bimap[transport_tensor T] id (to (transport_tensor_assoc T))
      ∘ to (transport_tensor_assoc T)
      ∘ bimap[transport_tensor T] (to (transport_tensor_assoc T)) id
      << transport_tensor T
           (transport_tensor T (transport_tensor T (x, y), z), w)
           ~~> transport_tensor T
                 (x, transport_tensor T (y, transport_tensor T (z, w))) >>
    to (transport_tensor_assoc T) ∘ to (transport_tensor_assoc T).

(*
Assemble a genuine monoidal structure from staged transport data plus
   the two coherence proofs.

--------
从分阶段传输数据加上两个相干性证明组装一个真正的幺半群结构。
*)
Definition Monoidal_from_transport_data
  (T : MonoidalTransportData)
  (tri : transport_triangle T)
  (pent : transport_pentagon T) : @Monoidal X :=
  @Build_Monoidal X
    (transport_unit T)
    (transport_tensor T)
    (@transport_unit_left T)
    (@transport_unit_right T)
    (@transport_tensor_assoc T)
    (@transport_to_unit_left_natural T)
    (@transport_from_unit_left_natural T)
    (@transport_to_unit_right_natural T)
    (@transport_from_unit_right_natural T)
    (@transport_to_tensor_assoc_natural T)
    (@transport_from_tensor_assoc_natural T)
    (fun x y => tri x y)
    (fun x y z w => pent x y z w).

End TransportData.

Arguments transport_unit {X} _.
Arguments transport_tensor {X} _.
Arguments transport_unit_left {X} _ {x}.
Arguments transport_unit_right {X} _ {x}.
Arguments transport_tensor_assoc {X} _ {x y z}.
Arguments transport_to_unit_left_natural {X} _ {x y} g.
Arguments transport_from_unit_left_natural {X} _ {x y} g.
Arguments transport_to_unit_right_natural {X} _ {x y} g.
Arguments transport_from_unit_right_natural {X} _ {x y} g.
Arguments transport_to_tensor_assoc_natural {X} _ {x y z w v u} g h i.
Arguments transport_from_tensor_assoc_natural {X} _ {x y z w v u} g h i.
Arguments transport_triangle {X} T.
Arguments transport_pentagon {X} T.
Arguments Monoidal_from_transport_data {X} T tri pent.

(* ------------------------------------------------------------------ *)
(* The transported structure. / 被运输的结构。                                          *)

Section TransportedMonoidal.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).
Context (M : @Monoidal C).

Local Notation G := (@quasi_inverse C D F E).
Local Notation eta := (@equivalence_unit_at C D F E).
Local Notation eps := (@equivalence_counit_at C D F E).

(*
Naturality of the unit and counit components — and the conjugation
   form describing how G ◯ F acts on morphisms — is provided by
   [equivalence_unit_to_natural]/[equivalence_unit_from_natural],
   [equivalence_counit_to_natural]/[equivalence_counit_from_natural] and
   [equivalence_unit_conjugate] of Theory/Equivalence.v, stated there
   beside the accessors [equivalence_unit_at]/[equivalence_counit_at].

--------
单位和余单位分量的自然性——以及描述 G ◯ F 如何作用于态射的共轭形式——由 Theory/Equivalence.v 中的 [equivalence_unit_to_natural]/[equivalence_unit_from_natural]、[equivalence_counit_to_natural]/[equivalence_counit_from_natural] 和 [equivalence_unit_conjugate] 提供，它们在那里与访问器 [equivalence_unit_at]/[equivalence_counit_at] 一起陈述。
*)

(*
The defect of the chosen unit/counit pair: the composite
   G d ~> G F G d ~> G d measuring how far the pair is from satisfying
   the zig-zag identity at G.  For an adjoint equivalence it would be the
   identity; in general it is merely a natural automorphism of G d.

--------
所选择的单位/余单位对的缺陷：复合
   G d ~> G F G d ~> G d，用于测量该对偏离在 G 上满足之锯齿形恒等式的程度。对于伴随等价，它将是恒等映射；一般情况下，它仅是 G d 的自然自同构。
*)
Definition transport_defect (d : D) : G d ≅ G d :=
  fobj_iso G _ _ (eps d) ⊙ eta (G d).

(*
The [*_unfold] equations here and below spell out the components of the
   isomorphisms just defined.  Each is Leibniz (=), not ≈, because the two
   sides are the very same term after unfolding the definition — the
   [bimap_fmap] convention of Functor/Bifunctor.v — which lets them be
   used as rewrite rules with no setoid side conditions.

--------
下面的 [*_unfold] 方程列出了刚定义的同构的各个组成部分。每个都是 Leibniz (=)，而不是 ≈，因为在展开定义后，两边实际上是相同的项——这是 Functor/Bifunctor.v 的 [bimap_fmap] 约定——这使得它们可以作为重写规则使用，而无需集合条件。
*)
Lemma transport_defect_to_unfold (d : D) :
  to (transport_defect d) = fmap[G] (to (eps d)) ∘ to (eta (G d)).
Proof. reflexivity. Qed.

Lemma transport_defect_from_unfold (d : D) :
  from (transport_defect d) = from (eta (G d)) ∘ fmap[G] (from (eps d)).
Proof. reflexivity. Qed.

Lemma transport_defect_to_natural {x y : D} (g : x ~> y) :
  to (transport_defect y) ∘ fmap[G] g ≈ fmap[G] g ∘ to (transport_defect x).
Proof.
  rewrite !transport_defect_to_unfold.
  rewrite <- comp_assoc.
  rewrite equivalence_unit_to_natural.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite equivalence_counit_to_natural.
  rewrite fmap_comp.
  now rewrite <- !comp_assoc.
Qed.

Lemma transport_defect_from_natural {x y : D} (g : x ~> y) :
  from (transport_defect y) ∘ fmap[G] g
    ≈ fmap[G] g ∘ from (transport_defect x).
Proof.
  symmetry.
  apply iso_from_natural.
  symmetry.
  apply transport_defect_to_natural.
Qed.

(*
The rectified counit: correcting the chosen counit by the inverse of
   the defect yields a counit for the same quasi-inverse and unit that
   satisfies the zig-zag identity at G (proved below).  This is the
   classical improvement step in showing that every equivalence refines
   to an adjoint equivalence, done here only on the counit side.

--------
修正的余单位：通过缺陷的逆来修正所选的余单位，会得到相同准逆和单位的余单位，并且在 G 上满足之字形恒等式（如下所示证明）。这是展示每个等价可以细化为伴随等价的经典改进步骤，这里仅在余单位方面进行。
*)
Definition transport_counit (d : D) : F (G d) ≅ d :=
  eps d ⊙ fobj_iso F _ _ (iso_sym (transport_defect d)).

Lemma transport_counit_to_unfold (d : D) :
  to (transport_counit d)
    = to (eps d) ∘ fmap[F] (from (transport_defect d)).
Proof. reflexivity. Qed.

Lemma transport_counit_from_unfold (d : D) :
  from (transport_counit d)
    = fmap[F] (to (transport_defect d)) ∘ from (eps d).
Proof. reflexivity. Qed.

Lemma transport_counit_to_natural {x y : D} (g : x ~> y) :
  to (transport_counit y) ∘ fmap[F] (fmap[G] g)
    ≈ g ∘ to (transport_counit x).
Proof.
  rewrite !transport_counit_to_unfold.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite transport_defect_from_natural.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite equivalence_counit_to_natural.
  now rewrite <- !comp_assoc.
Qed.

Lemma transport_counit_from_natural {x y : D} (g : x ~> y) :
  fmap[F] (fmap[G] g) ∘ from (transport_counit x)
    ≈ from (transport_counit y) ∘ g.
Proof.
  apply iso_from_natural.
  symmetry.
  apply transport_counit_to_natural.
Qed.

(*
The zig-zag identity at G, in its most usable form: G takes the
   rectified counit to the inverse of the unit component.

--------
G 的之字形恒等式，在其最可用的形式中：G 将整流余单元映射到单元分量的逆。
*)
Lemma quasi_inverse_transport_counit (d : D) :
  fmap[G] (to (transport_counit d)) ≈ from (eta (G d)).
Proof.
  rewrite transport_counit_to_unfold.
  rewrite fmap_comp.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite <- transport_defect_to_unfold.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma quasi_inverse_transport_counit_from (d : D) :
  fmap[G] (from (transport_counit d)) ≈ to (eta (G d)).
Proof.
  rewrite transport_counit_from_unfold.
  rewrite fmap_comp.
  rewrite equivalence_unit_conjugate.
  rewrite <- !comp_assoc.
  rewrite <- transport_defect_from_unfold.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(* The transported tensor: (d, d') ↦ F (G d ⨂ G d'). / 被传输的张量： (d, d') ↦ F (G d ⨂ G d')。 *)
Program Definition Transported_Tensor : D ∏ D ⟶ D := {|
  fobj := fun p => F ((G (fst p) ⨂[M] G (snd p))%object);
  fmap := fun x y f => fmap[F] (fmap[G] (fst f) ⨂[M] fmap[G] (snd f))
|}.
Next Obligation.
  intros f g e; destruct e as [e1 e2]; simpl.
  now rewrite e1, e2.
Qed.
Next Obligation.
  simpl.
  rewrite !fmap_id.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.
Next Obligation.
  simpl.
  rewrite !fmap_comp.
  rewrite bimap_comp.
  apply fmap_comp.
Qed.

(*
The action of the transported tensor on a pair of morphisms, written
   out.  [bimap[Transported_Tensor] f g] reduces to exactly this term; the
   D-side lemmas below are stated directly in this form so that every
   object index in a proof goal is in the same (reduced) representation.
   The [Build_MonoidalTransportData] at the end of the file converts them
   back to the [bimap] phrasing of the record fields definitionally.

--------
传输张量在一对态射上的作用，写出来。[bimap[Transported_Tensor] f g] 减少为完全相同的项；下面的 D 侧引理直接以这种形式陈述，以便证明目标中的每个对象索引都采用相同（简化的）表示。文件末尾的 [Build_MonoidalTransportData] 将它们转换回记录字段定义上的 [bimap] 表述。
*)
Local Notation Tbimap f g := (fmap[F] (fmap[G] f ⨂[M] fmap[G] g)).

(*
The transported left unitor:
   F I ⊗' d = F (G (F I) ⨂ G d) ≅ F (I ⨂ G d) ≅ F (G d) ≅ d.

--------
传输后的左单位元：
   F I ⊗' d = F (G (F I) ⨂ G d) ≅ F (I ⨂ G d) ≅ F (G d) ≅ d。
*)
Program Definition Transported_unit_left (x : D) :
  F ((G (F (@I C M)) ⨂[M] G x)%object) ≅ x := {|
  to := to (transport_counit x)
          ∘ fmap[F] (to (@unit_left C M (G x))
                       ∘ (from (eta (@I C M)) ⨂[M] id[G x]));
  from := fmap[F] ((to (eta (@I C M)) ⨂[M] id[G x])
                     ∘ from (@unit_left C M (G x)))
            ∘ from (transport_counit x)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite fmap_fold_spine.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_to_from.
  rewrite fmap_id.
  rewrite id_right.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

(* The transported right unitor. / 被传输的右单位元。 *)
Program Definition Transported_unit_right (x : D) :
  F ((G x ⨂[M] G (F (@I C M)))%object) ≅ x := {|
  to := to (transport_counit x)
          ∘ fmap[F] (to (@unit_right C M (G x))
                       ∘ (id[G x] ⨂[M] from (eta (@I C M))));
  from := fmap[F] ((id[G x] ⨂[M] to (eta (@I C M)))
                     ∘ from (@unit_right C M (G x)))
            ∘ from (transport_counit x)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite fmap_fold_spine.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_to_from.
  rewrite fmap_id.
  rewrite id_right.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

Lemma transported_unit_left_to_unfold (x : D) :
  to (Transported_unit_left x)
    = to (transport_counit x)
        ∘ fmap[F] (to (@unit_left C M (G x))
                     ∘ bimap (from (eta (@I C M))) (id[G x])).
Proof. reflexivity. Qed.

Lemma transported_unit_right_to_unfold (x : D) :
  to (Transported_unit_right x)
    = to (transport_counit x)
        ∘ fmap[F] (to (@unit_right C M (G x))
                     ∘ bimap (id[G x]) (from (eta (@I C M)))).
Proof. reflexivity. Qed.

(*
The transported associator, assembled purely from the unit
   isomorphism and the associator of C.

--------
这个传输的结合子，完全由单位同构和 C 的结合子组装而成。
*)
Program Definition Transported_tensor_assoc (x y z : D) :
  F ((G (F ((G x ⨂[M] G y)%object)) ⨂[M] G z)%object)
    ≅ F ((G x ⨂[M] G (F ((G y ⨂[M] G z)%object)))%object) := {|
  to := fmap[F] ((id[G x] ⨂[M] to (eta ((G y ⨂[M] G z)%object)))
                   ∘ to (@tensor_assoc C M (G x) (G y) (G z))
                   ∘ (from (eta ((G x ⨂[M] G y)%object)) ⨂[M] id[G z]));
  from := fmap[F] ((to (eta ((G x ⨂[M] G y)%object)) ⨂[M] id[G z])
                     ∘ from (@tensor_assoc C M (G x) (G y) (G z))
                     ∘ (id[G x] ⨂[M] from (eta ((G y ⨂[M] G z)%object))))
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_cancel_spine_tf.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite iso_from_to.
  rewrite id_left.
  rewrite bimap_id_id.
  rewrite id_right.
  rewrite iso_cancel_spine_ft.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  rewrite id_left.
  rewrite bimap_id_id.
  apply fmap_id.
Qed.

Lemma transported_tensor_assoc_to_unfold (x y z : D) :
  to (Transported_tensor_assoc x y z)
    = fmap[F] (bimap (id[G x]) (to (eta ((G y ⨂ G z)%object)))
                 ∘ to (@tensor_assoc C M (G x) (G y) (G z))
                 ∘ bimap (from (eta ((G x ⨂ G y)%object))) (id[G z])).
Proof. reflexivity. Qed.

(*
The image under G of the transported unitors: the zig-zag identity
   collapses the counit factor, so the image is the corresponding unitor
   of C conjugated by a single unit component.

--------
在 G 下传送的单位子上的图像：之字形恒等式折叠了余单位因子，因此图像是 C 的相应单位子，通过一个单一的单位分量进行共轭。
*)
Lemma G_transported_unit_left (y : D) :
  fmap[G] (to (Transported_unit_left y))
    ≈ to (@unit_left C M (G y)) ∘ bimap (from (eta (@I C M))) (id[G y])
        ∘ from (eta ((G (F (@I C M)) ⨂ G y)%object)).
Proof.
  rewrite transported_unit_left_to_unfold.
  rewrite fmap_comp.
  rewrite quasi_inverse_transport_counit.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Lemma G_transported_unit_right (x : D) :
  fmap[G] (to (Transported_unit_right x))
    ≈ to (@unit_right C M (G x)) ∘ bimap (id[G x]) (from (eta (@I C M)))
        ∘ from (eta ((G x ⨂ G (F (@I C M)))%object)).
Proof.
  rewrite transported_unit_right_to_unfold.
  rewrite fmap_comp.
  rewrite quasi_inverse_transport_counit.
  rewrite equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

(* The C-side naturality squares of the transported unitors. / 传输后的幺元的C面自然性平方。 *)

Lemma transported_unit_left_square {x y : D} (g : x ~> y) :
  (to (@unit_left C M (G y)) ∘ bimap (from (eta (@I C M))) (id[G y]))
      ∘ bimap (id[G (F (@I C M))]) (fmap[G] g)
    ≈ fmap[G] g
        ∘ (to (@unit_left C M (G x)) ∘ bimap (from (eta (@I C M))) (id[G x])).
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_id_right_left.
  rewrite <- bimap_id_left_right.
  rewrite comp_assoc.
  rewrite <- to_unit_left_natural.
  now rewrite <- comp_assoc.
Qed.

Lemma transported_unit_right_square {x y : D} (g : x ~> y) :
  (to (@unit_right C M (G y)) ∘ bimap (id[G y]) (from (eta (@I C M))))
      ∘ bimap (fmap[G] g) (id[G (F (@I C M))])
    ≈ fmap[G] g
        ∘ (to (@unit_right C M (G x))
             ∘ bimap (id[G x]) (from (eta (@I C M)))).
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_id_left_right.
  rewrite <- bimap_id_right_left.
  rewrite comp_assoc.
  rewrite <- to_unit_right_natural.
  now rewrite <- comp_assoc.
Qed.

(* The six naturality fields of the transported structure. / 被运送结构的六个自然性领域。 *)

Lemma Transported_to_unit_left_natural {x y : D} (g : x ~> y) :
  g ∘ to (Transported_unit_left x)
    ≈ to (Transported_unit_left y) ∘ Tbimap (id[F (@I C M)]) g.
Proof.
  rewrite !transported_unit_left_to_unfold.
  rewrite fmap_id.
  rewrite <- (comp_assoc (to (transport_counit y))).
  rewrite <- fmap_comp.
  rewrite transported_unit_left_square.
  rewrite (fmap_comp (fmap[G] g)).
  rewrite (comp_assoc (to (transport_counit y))).
  rewrite transport_counit_to_natural.
  now rewrite !comp_assoc.
Qed.

Lemma Transported_from_unit_left_natural {x y : D} (g : x ~> y) :
  Tbimap (id[F (@I C M)]) g ∘ from (Transported_unit_left x)
    ≈ from (Transported_unit_left y) ∘ g.
Proof.
  apply iso_from_natural.
  apply Transported_to_unit_left_natural.
Qed.

Lemma Transported_to_unit_right_natural {x y : D} (g : x ~> y) :
  g ∘ to (Transported_unit_right x)
    ≈ to (Transported_unit_right y) ∘ Tbimap g (id[F (@I C M)]).
Proof.
  rewrite !transported_unit_right_to_unfold.
  rewrite fmap_id.
  rewrite <- (comp_assoc (to (transport_counit y))).
  rewrite <- fmap_comp.
  rewrite transported_unit_right_square.
  rewrite (fmap_comp (fmap[G] g)).
  rewrite (comp_assoc (to (transport_counit y))).
  rewrite transport_counit_to_natural.
  now rewrite !comp_assoc.
Qed.

Lemma Transported_from_unit_right_natural {x y : D} (g : x ~> y) :
  Tbimap g (id[F (@I C M)]) ∘ from (Transported_unit_right x)
    ≈ from (Transported_unit_right y) ∘ g.
Proof.
  apply iso_from_natural.
  apply Transported_to_unit_right_natural.
Qed.

Lemma Transported_to_tensor_assoc_natural {x y z w v u : D}
  (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  Tbimap g (Tbimap h i) ∘ to (Transported_tensor_assoc x z v)
    ≈ to (Transported_tensor_assoc y w u) ∘ Tbimap (Tbimap g h) i.
Proof.
  rewrite !transported_tensor_assoc_to_unfold.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  rewrite !comp_assoc.
  rewrite bimap_fold_spine.
  rewrite id_left.
  rewrite <- equivalence_unit_from_natural.
  rewrite bimap_split_first'.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite id_right.
  rewrite <- equivalence_unit_to_natural.
  rewrite bimap_split_second.
  rewrite alpha_natural_spine.
  reflexivity.
Qed.

Lemma Transported_from_tensor_assoc_natural {x y z w v u : D}
  (g : x ~> y) (h : z ~> w) (i : v ~> u) :
  Tbimap (Tbimap g h) i ∘ from (Transported_tensor_assoc x z v)
    ≈ from (Transported_tensor_assoc y w u) ∘ Tbimap g (Tbimap h i).
Proof.
  apply iso_from_natural.
  apply Transported_to_tensor_assoc_natural.
Qed.

(* The staged transport data for the transported structure. / 运输结构的分阶段运输数据。 *)
Definition Transported_Monoidal_Data : MonoidalTransportData D :=
  @Build_MonoidalTransportData D
    (F (@I C M))
    Transported_Tensor
    Transported_unit_left
    Transported_unit_right
    Transported_tensor_assoc
    (@Transported_to_unit_left_natural)
    (@Transported_from_unit_left_natural)
    (@Transported_to_unit_right_natural)
    (@Transported_from_unit_right_natural)
    (@Transported_to_tensor_assoc_natural)
    (@Transported_from_tensor_assoc_natural).

(*
The triangle law of the transported structure.  The zig-zag identity
   collapses the counit factors of the two unitors, after which the law
   reduces to the triangle of C conjugated by unit components.

--------
被传递结构的三角定律。之字形恒等式折叠了两个幺元子的余幺因子，之后该定律简化为由幺元组件共轭的C的三角形。
*)
Lemma Transported_triangle_identity (x y : D) :
  Tbimap (to (Transported_unit_right x)) (id[y])
    ≈ Tbimap (id[x]) (to (Transported_unit_left y))
        ∘ to (Transported_tensor_assoc x (F (@I C M)) y).
Proof.
  rewrite transported_tensor_assoc_to_unfold.
  rewrite <- fmap_comp.
  apply fmap_respects.
  rewrite !fmap_id.
  rewrite G_transported_unit_right.
  rewrite G_transported_unit_left.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite iso_cancel_spine_ft.
  rewrite id_left.
  rewrite bimap_split_second.
  rewrite alpha_natural_spine.
  rewrite <- triangle_identity.
  rewrite bimap_fold_spine.
  rewrite id_left.
  rewrite <- bimap_comp.
  rewrite id_left.
  now rewrite !comp_assoc.
Qed.

(*
The pentagon law of the transported structure.  No zig-zag is needed:
   the associator mentions only the unit isomorphism, whose components
   cancel pairwise, and the residue is the pentagon of C surrounded by
   naturality moves of the associator.

--------
被传输结构的五边形法则。不需要之字形：结合子只提到单位同构，其分量成对消去，剩余部分是由结合子的自然性移动包围的 C 的五边形。
*)
Lemma Transported_pentagon_identity (x y z w : D) :
  Tbimap (id[x]) (to (Transported_tensor_assoc y z w))
      ∘ to (Transported_tensor_assoc x (F ((G y ⨂[M] G z)%object)) w)
      ∘ Tbimap (to (Transported_tensor_assoc x y z)) (id[w])
    ≈ to (Transported_tensor_assoc x y (F ((G z ⨂[M] G w)%object)))
        ∘ to (Transported_tensor_assoc (F ((G x ⨂[M] G y)%object)) z w).
Proof.
  rewrite !transported_tensor_assoc_to_unfold.
  rewrite !fmap_id.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  rewrite !equivalence_unit_conjugate.
  rewrite !comp_assoc.
  rewrite !bimap_split_second.
  rewrite !bimap_split_first.
  rewrite !comp_assoc.
  rewrite bimap_id_cancel_ft_spine.
  rewrite bimap_cancel_ft_spine_l.
  rewrite alpha_natural_spine_r.
  rewrite bimap_bimap_id_cancel_ft_spine.
  rewrite pentagon_spine.
  rewrite bimap_swap_spine.
  rewrite alpha_move_third_spine.
  rewrite alpha_move_left_spine.
  reflexivity.
Qed.

(*
The transported monoidal structure, assembled from the staged data and
   the two coherence laws.  A Definition, never an Instance.

--------
由分阶段数据和两个相干律组装而成的运输单元结构。一个定义，而不是实例。
*)
Definition Transported_Monoidal : @Monoidal D :=
  Monoidal_from_transport_data Transported_Monoidal_Data
    (fun x y => Transported_triangle_identity x y)
    (fun x y z w => Transported_pentagon_identity x y z w).

End TransportedMonoidal.
