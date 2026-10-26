Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.

Generalizable All Variables.

(*
   * * Hypergraph categories

   A hypergraph category is a symmetric monoidal category [(C, ⨂, I, σ)]
   equipped with a special commutative Frobenius algebra (SCFA) on every
   object, such that the SCFA on [X ⨂ Y] is canonically constructed from
   those on [X] and [Y].

   Following Carboni–Walters and Fong–Spivak, the canonical SCFA on the
   tensor is built from the “middle-interchange” isomorphism
   [(X ⨂ Y) ⨂ (X ⨂ Y) ≅ (X ⨂ X) ⨂ (Y ⨂ Y)] obtained by braiding the
   middle two factors:

   μ_{X⨂Y} : (X⨂Y) ⨂ (X⨂Y) -mid-> (X⨂X) ⨂ (Y⨂Y) -μ⊗μ-> X⨂Y
   η_{X⨂Y} : I = I⨂I -η⊗η-> X⨂Y
   δ_{X⨂Y} : X⨂Y -δ⊗δ-> (X⨂X) ⨂ (Y⨂Y) -mid-> (X⨂Y) ⨂ (X⨂Y)
   ε_{X⨂Y} : X⨂Y -ε⊗ε-> I⨂I = I

   Each of these is definable in terms of the [braid], [tensor_assoc],
   [unit_left] and [unit_right] structure of the symmetric monoidal
   category.

   Mathematical comments:

   - The middle-interchange iso is what nLab denotes “Tau” or
   “swap-inner-two-of-four”.
   - On the unit object [I] the canonical SCFA is trivial:
   μ = unit_left, η = id, δ = unit_left⁻¹, ε = id.  These four
   coherence axioms are stated as the [scfa_unit_*] fields of the
   [Hypergraph] class.  Fong–Spivak prove this is the *only* Frobenius
   structure on [I] with η_I = id = ε_I (and λ_I = ρ_I on the unit, so
   [unit_left] and [unit_right] agree there).

   nLab:      https://ncatlab.org/nlab/show/hypergraph+category
   Wikipedia: no dedicated article (the underlying special commutative
   Frobenius algebra is covered at
   https://en.wikipedia.org/wiki/Frobenius_algebra)
   Reference: Fong & Spivak, “Hypergraph Categories”,
   J. Pure Appl. Algebra 223(11):4746–4777, 2019
   (arXiv:1806.08304) — the compatibility law
   μ_{X⨂Y} = (μ_X ⨂ μ_Y) ∘ (1_X ⨂ σ_{Y,X} ⨂ 1_Y) is the
   [scfa_tensor_mu]/[mid_swap] coherence below. 

   --------
   * * 超图范畴

   超图范畴是一个对称单位范畴 [(C, ⨂, I, σ)]，
   在每个对象上配备一个特殊的交换 Frobenius 代数 (SCFA)，
   使得 [X ⨂ Y] 上的 SCFA 可以从 [X] 和 [Y] 上的 SCFA 自然构造。

   根据 Carboni–Walters 和 Fong–Spivak 的方法，
   张量上的标准 SCFA 是通过“中间交换”同构 [(X ⨂ Y) ⨂ (X ⨂ Y) ≅ (X ⨂ X) ⨂ (Y ⨂ Y)] 构建的，
   该同构是通过对中间两个因子进行编织得到的：

   μ_{X⨂Y} : (X⨂Y) ⨂ (X⨂Y) -mid-> (X⨂X) ⨂ (Y⨂Y) -μ⊗μ-> X⨂Y
   η_{X⨂Y} : I = I⨂I -η⊗η-> X⨂Y
   δ_{X⨂Y} : X⨂Y -δ⊗δ-> (X⨂X) ⨂ (Y⨂Y) -mid-> (X⨂Y) ⨂ (X⨂Y)
   ε_{X⨂Y} : X⨂Y -ε⊗ε-> I⨂I = I

   这些都可以通过对称单位范畴的 [braid]、[tensor_assoc]、[unit_left] 和 [unit_right] 结构来定义。数学评论：

   - 中间交换同构是 nLab 所标记为“Tau”或“交换四个元素中的中间两个”的概念。
   - 在单位对象 [I] 上，典型 SCFA 是平凡的：
   μ = unit_left，η = id，δ = unit_left⁻¹，ε = id。这四个相容公理被陈述为 [Hypergraph] 类的 [scfa_unit_*] 字段。Fong–Spivak 证明这是 [I] 上 η_I = id = ε_I（且在单位上 λ_I = ρ_I，因此 [unit_left] 和 [unit_right] 在那里是一致的）情况下的*唯一* Frobenius 结构。nLab：https://ncatlab.org/nlab/show/hypergraph+category
   Wikipedia：没有专门的条目（基础的特殊交换Frobenius代数在https://en.wikipedia.org/wiki/Frobenius_algebra)中有介绍）
   参考文献：Fong & Spivak，《超图范畴》，J. Pure Appl. Algebra 223(11):4746–4777, 2019（arXiv:1806.08304）——兼容性法则 μ_{X⨂Y} = (μ_X ⨂ μ_Y) ∘ (1_X ⨂ σ_{Y,X} ⨂ 1_Y) 是下面的 [scfa_tensor_mu] / [mid_swap] 一致性。
*)

Section Hypergraph.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(*
   * The “middle two factors” swap [(X⨂Y) ⨂ (X⨂Y) ≅ (X⨂X) ⨂ (Y⨂Y)],
   built by re-associating, braiding the middle pair, then re-associating
   back.  Concretely, the chain is

   (X⨂Y) ⨂ (X⨂Y)
   =α=> X ⨂ (Y ⨂ (X⨂Y))
   =id⨂α⁻¹=> X ⨂ ((Y⨂X) ⨂ Y)
   =id⨂(braid⨂id)=> X ⨂ ((X⨂Y) ⨂ Y)
   =id⨂α=> X ⨂ (X ⨂ (Y⨂Y))
   =α⁻¹=> (X⨂X) ⨂ (Y⨂Y).

   --------
   * “中间两个因子”交换 [(X⨂Y) ⨂ (X⨂Y) ≅ (X⨂X) ⨂ (Y⨂Y)] ，通过重新结合、中间一对的交错，然后再重新结合回去构建。具体而言，链条为：

   (X⨂Y) ⨂ (X⨂Y)
   =α=> X ⨂ (Y ⨂ (X⨂Y))
   =id⨂α⁻¹=> X ⨂ ((Y⨂X) ⨂ Y)
   =id⨂(braid⨂id)=> X ⨂ ((X⨂Y) ⨂ Y)
   =id⨂α=> X ⨂ (X ⨂ (Y⨂Y))
   =α⁻¹=> (X⨂X) ⨂ (Y⨂Y).
*)
Definition mid_swap (X Y : C) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> (X ⨂ X) ⨂ (Y ⨂ Y) :=
  (@tensor_assoc C _ X X (Y ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ X Y Y))
    ∘ bimap id[X] (bimap (@braid C _ Y X) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ Y X Y)⁻¹)
    ∘ to (@tensor_assoc C _ X Y (X ⨂ Y)).

(** Inverse direction, used in the canonical [delta]. / 逆方向，用于规范的 [delta]。 *)
Definition mid_swap_inv (X Y : C) :
  (X ⨂ X) ⨂ (Y ⨂ Y) ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  (@tensor_assoc C _ X Y (X ⨂ Y))⁻¹
    ∘ bimap id[X] (to (@tensor_assoc C _ Y X Y))
    ∘ bimap id[X] (bimap (@braid C _ X Y) id[Y])
    ∘ bimap id[X] ((@tensor_assoc C _ X Y Y)⁻¹)
    ∘ to (@tensor_assoc C _ X X (Y ⨂ Y)).

(*
   * ** The middle-swap is an isomorphism

   [mid_swap X Y] and [mid_swap_inv X Y] are definitionally the
   interchange instances [swap_inner X Y X Y] and [swap_inner X X Y Y]
   of Structure/Monoidal/Braided/Proofs.v, so both composites are
   instances of the general involution [swap_inner_invol]. 

   --------
   * ** 中间交换是一个同构

   [mid_swap X Y] 和 [mid_swap_inv X Y] 在定义上是 Structure/Monoidal/Braided/Proofs.v 的互换实例 [swap_inner X Y X Y] 和 [swap_inner X X Y Y] ，所以两个复合都是一般自反 [swap_inner_invol] 的实例。
*)

Lemma mid_swap_iso (X Y : C) :
  mid_swap X Y ∘ mid_swap_inv X Y ≈ id[(X ⨂ X) ⨂ (Y ⨂ Y)].
Proof. exact (@swap_inner_invol C S X X Y Y). Qed.

Lemma mid_swap_iso_sym (X Y : C) :
  mid_swap_inv X Y ∘ mid_swap X Y ≈ id[(X ⨂ Y) ⨂ (X ⨂ Y)].
Proof. exact (@swap_inner_invol C S X Y X Y). Qed.

(** Canonical [mu] on [X ⨂ Y] from those on [X] and [Y]. / 规范的 [mu] 在 [X ⨂ Y] 上来自 [X] 和 [Y] 上的那些。 *)
Definition canonical_tensor_mu {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  (X ⨂ Y) ⨂ (X ⨂ Y) ~> X ⨂ Y :=
  bimap (@mu _ _ _ MX) (@mu _ _ _ MY) ∘ mid_swap X Y.

(** Canonical [eta] on [X ⨂ Y]. / 规范 [eta] 在 [X ⨂ Y] 上。 *)
Definition canonical_tensor_eta {X Y : C}
           (MX : Monoid X) (MY : Monoid Y) :
  I ~> X ⨂ Y :=
  bimap (@eta _ _ _ MX) (@eta _ _ _ MY) ∘ from (@unit_left C _ I).

(** Canonical [delta] on [X ⨂ Y]. / 规范 [delta] 在 [X ⨂ Y] 上。 *)
Definition canonical_tensor_delta {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> (X ⨂ Y) ⨂ (X ⨂ Y) :=
  mid_swap_inv X Y ∘ bimap (@delta _ _ _ CX) (@delta _ _ _ CY).

(** Canonical [epsilon] on [X ⨂ Y]. / 规范 [epsilon] 在 [X ⨂ Y] 上。 *)
Definition canonical_tensor_epsilon {X Y : C}
           (CX : Comonoid X) (CY : Comonoid Y) :
  X ⨂ Y ~> I :=
  to (@unit_left C _ I) ∘ bimap (@epsilon _ _ _ CX) (@epsilon _ _ _ CY).

(*
   * ** The hypergraph category class

   A hypergraph category is a symmetric monoidal category with a chosen
   SCFA on every object, satisfying:

   - the tensor coherence: the SCFA on [X ⨂ Y] agrees with the canonical
   SCFA assembled from those of [X] and [Y];
   - the unit coherence: the SCFA on [I] is the trivial one (μ ≈ unit_left,
   η ≈ id, δ ≈ unit_left⁻¹, ε ≈ id).

   Without the unit coherence the user could supply an arbitrary
   incoherent SCFA on [I]; the unit fields close that gap. 

   --------
   * ** 超图分类类

   超图分类是一个对称单体范畴，每个对象上选定了一个 SCFA，满足：

   - 张量相容性：[X ⨂ Y] 上的 SCFA 与由 [X] 和 [Y] 的 SCFA 组装而成的规范 SCFA 一致；
   - 单位相容性：[I] 上的 SCFA 是平凡的（μ ≈ unit_left，η ≈ id，δ ≈ unit_left⁻¹，ε ≈ id）。

   如果没有单位相容性，用户可以在 [I] 上提供任意不相容的 SCFA；单位字段弥补了这一差距。
*)
Class Hypergraph : Type := {
  scfa : forall (X : C), SpecialCommutativeFrobenius X;

  scfa_tensor_mu : forall (X Y : C),
    scfa_mu (scfa (X ⨂ Y)) ≈ canonical_tensor_mu (scfa X) (scfa Y);

  scfa_tensor_eta : forall (X Y : C),
    scfa_eta (scfa (X ⨂ Y)) ≈ canonical_tensor_eta (scfa X) (scfa Y);

  scfa_tensor_delta : forall (X Y : C),
    scfa_delta (scfa (X ⨂ Y)) ≈ canonical_tensor_delta (scfa X) (scfa Y);

  scfa_tensor_epsilon : forall (X Y : C),
    scfa_epsilon (scfa (X ⨂ Y)) ≈ canonical_tensor_epsilon (scfa X) (scfa Y);

  (*
   * Unit-object coherence — closes CRIT-1.  The canonical SCFA on [I]
   is the trivial one: [μ_I ≈ unit_left], [η_I ≈ id], etc. 

   --------
   * 单位-对象连贯性 — 关闭 CRIT-1。[I] 上的典型 SCFA 是平凡的：[μ_I ≈ unit_left]、[η_I ≈ id] 等。
*)

  scfa_unit_mu :
    scfa_mu (scfa I) ≈ to (@unit_left C _ I);

  scfa_unit_eta :
    scfa_eta (scfa I) ≈ id[I];

  scfa_unit_delta :
    scfa_delta (scfa I) ≈ from (@unit_left C _ I);

  scfa_unit_epsilon :
    scfa_epsilon (scfa I) ≈ id[I]
}.

End Hypergraph.

Arguments scfa {C S _} X.
Arguments Hypergraph C {S}.
