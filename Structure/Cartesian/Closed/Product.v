Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/product+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

 The product C ∏ D of two cartesian closed categories is again cartesian
 closed, with all of the structure computed componentwise. Neither
 reference states this closure result directly; it is the standard
 corollary that limits and exponentials in a product category are taken
 factorwise (see [product+category]: objects, morphisms, and composition
 of C ∏ D are pairs handled componentwise).

 Recall from [Closed] that exponent_obj x y is displayed as y ^ x. The
 exponential of (c, d) over (c', d') is therefore taken in each factor:

 (e, f) ^ (c, d) = (e ^ c, f ^ d)

 so [exponent_obj (c,d) (e,f)] = (fst·^fst·, snd·^snd·) below. The
 product-exponential adjunction (- × y) ⊣ (- ^ y) holds factorwise: the
 currying iso Hom((c,d)×(c',d'), e) ≅ Hom((c,d), e^(c',d')) is the
 pointwise pairing of the two component isos [exp_iso] of C and D, so
 evaluation and currying both act componentwise. 

 --------
 nLab：https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab：https://ncatlab.org/nlab/show/product+category
 Wikipedia：https://en.wikipedia.org/wiki/Cartesian_closed_category

 两个笛卡尔闭范畴的积 C ∏ D 仍然是笛卡尔闭的，其所有结构都是按分量计算的。没有一个参考文献直接陈述了这个闭性结果；这是一个标准的推论，即积范畴中的极限和指数是按因子逐一取的（参见 [product+category]：C ∏ D 的对象、态射和复合是按分量处理的对）。

 回想 [Closed] 中 exponent_obj x y 显示为 y ^ x。因此，(c, d) 在 (c', d') 上的指数是在每个因子中取的：

 (e, f) ^ (c, d) = (e ^ c, f ^ d)所以 [exponent_obj (c,d) (e,f)] = (fst·^fst·, snd·^snd·) 如下。积-指数伴随关系 (- × y) ⊣ (- ^ y) 在每个分量上都成立：柯里化同构 Hom((c,d)×(c',d'), e) ≅ Hom((c,d), e^(c',d')) 是 C 和 D 的两个分量同构 [exp_iso] 的逐点配对，因此求值和柯里化都按分量进行。
*)

Section ProductClosed.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.
Context `{@Closed C _}.
Context `{@Closed D _}.

Program Instance Product_Closed : @Closed (C ∏ D) Product_Cartesian := {
  (*
 internal hom, componentwise: (e,f) ^ (c,d) = (e^c, f^d) 

 --------
 内部同态，按分量计算: (e,f) ^ (c,d) = (e^c, f^d)
*)
  exponent_obj := fun x y => (fst y ^ fst x, snd y ^ snd x);
  (*
 currying iso, the factorwise pairing of the component exp_iso's 

 --------
 currying iso，组件 exp_iso 的按因子配对
*)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    (to exp_iso (fst f), to exp_iso (snd f)) |}
     ; from := {| morphism := fun f =>
                    (from exp_iso (fst f), from exp_iso (snd f)) |} |}
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. split; exact (iso_to_from (@exp_iso _ _ _ _ _ _) _). Qed.
Next Obligation. split; exact (iso_from_to (@exp_iso _ _ _ _ _ _) _). Qed.

End ProductClosed.
