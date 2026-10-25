Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section BalancedMonoidal.

Context {C : Category}.

(** Balanced monoidal category. / 平衡幺半范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/balanced+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Ribbon_category

 A balanced monoidal category is a braided monoidal category equipped with a
 natural isomorphism, the twist (or balancing),

 theta : x ≅ x                      ([twist]),

 self-natural (theta is a natural automorphism of the identity functor) and
 compatible with the braiding (beta = [braid]). The defining coherence law
 relates the twist on a tensor product to the double braiding. In the
 orientation of both sources, writing composition right to left,

 theta_{x⊗y} = beta_{y,x} ∘ beta_{x,y} ∘ (theta_x ⊗ theta_y)
 ([balanced_to_commutes]),

 together with the unit condition

 theta_I = id                       ([balanced_to], [balanced_from]).

 This file states the coherence law in the naturality-shifted form

 theta_{x⊗y} = beta_{y,x} ∘ (theta_y ⊗ theta_x) ∘ beta_{x,y},

 which is equal to the source form: naturality of [braid] gives
 beta_{x,y} ∘ (theta_x ⊗ theta_y) = (theta_y ⊗ theta_x) ∘ beta_{x,y}, so the
 factor (theta_y ⊗ theta_x) can be slid leftward across the inner braiding to
 recover the canonical statement. [balanced_from_commutes] is the same
 coherence for the inverse twist (theta⁻¹), the law obtained by inverting
 both sides; it is recorded as a field so the inverse direction need not be
 re-derived at each use.

 Every symmetric monoidal category is balanced with theta = id: when
 beta ∘ beta = id (see Structure/Monoidal/Symmetric.v) the law reduces to
 id = beta ∘ id ∘ beta. A balanced monoidal category that is additionally
 rigid (has duals whose twist is compatible with duality, theta on the dual
 of x being the dual of theta on x) is a ribbon, or tortile, category;
 rigidity is not required here. 

 --------
 nLab:  https://ncatlab.org/nlab/show/balanced+monoidal+category
 维基百科:  https://en.wikipedia.org/wiki/Ribbon_category

 平衡的单范畴是一个带有自然同构——扭转（或平衡）的编织单范畴，

 theta : x ≅ x                      ([twist]),

 自然自身（theta 是恒等函子的一种自然自同构）并且与编织兼容（beta = [braid]）。定义的一致性律将张量积上的扭转与双编织关联起来。在两个来源的方向中，写作从右到左的复合，

 theta_{x⊗y} = beta_{y,x} ∘ beta_{x,y} ∘ (theta_x ⊗ theta_y)
 ([balanced_to_commutes]),

 以及单位条件

 theta_I = id                       ([balanced_to], [balanced_from]).

 本文档以自然性位移的形式陈述了一致性律theta_{x⊗y} = beta_{y,x} ∘ (theta_y ⊗ theta_x) ∘ beta_{x,y},

 这等于原来的形式：[braid] 的自然性给出
 beta_{x,y} ∘ (theta_x ⊗ theta_y) = (theta_y ⊗ theta_x) ∘ beta_{x,y}, 因此
 因子 (theta_y ⊗ theta_x) 可以沿着内部的换位向左滑动，
 以恢复标准表述。[balanced_from_commutes] 对逆旋转 (theta⁻¹) 也是同样的一致性，
 这是通过对两边同时取逆得到的定律；它被记录为一个字段，因此在每次使用时不必重新推导逆方向。每一个对称单幺范畴都是平衡的，其中 theta = id：当
 beta ∘ beta = id（参见 Structure/Monoidal/Symmetric.v）时，定律简化为
 id = beta ∘ id ∘ beta。一个平衡的单幺范畴，如果此外是
 刚性（具有与对偶兼容的扭结，对 x 的对偶上的 theta 是 x 上 theta 的对偶），则是丝带范畴或卷曲范畴；
 刚性在这里不是必需的。
*)

Class BalancedMonoidal := {
  balanced_is_braided : @BraidedMonoidal C;

  (* The twist theta : x ≅ x, a natural automorphism of the identity. / 扭转 θ : x ≅ x，是恒等函子上的一个自然自同构。 *)
  twist {x} : x ≅ x;
  twist_natural : natural (@twist);

  (* Unit condition theta_I = id, in both isomorphism directions. / 单位条件 θ_I = id，在两个同构方向都是如此。 *)
  balanced_to   : to   (@twist I) ≈ id;
  balanced_from : from (@twist I) ≈ id;

  (*
 Twist/braiding coherence: theta on x ⊗ y is the double braiding wrapping
 theta ⊗ theta (naturality-shifted form; see the header). 

 --------
 扭结/编织一致性：x ⊗ y 上的 theta 是双重编织环绕 theta ⊗ theta（范性位移的形式；见标题）。
*)
  balanced_to_commutes {x y} :
    braid ∘ twist ⨂ twist ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist;

  (* The same coherence for the inverse twist theta⁻¹. / 逆扭转 θ⁻¹ 的相同相干性。 *)
  balanced_from_commutes {x y} :
    braid ∘ twist⁻¹ ⨂ twist⁻¹ ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist⁻¹;
}.
#[export] Existing Instance balanced_is_braided.

Coercion balanced_is_braided : BalancedMonoidal >-> BraidedMonoidal.

End BalancedMonoidal.
