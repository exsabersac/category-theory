Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(*
   * * The braided and symmetric monoidal structures on the free coloured PROP 

   --------
   * * 自由彩色 PROP 上的编织与对称单体范畴结构
*)

(*
 nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 This file equips THE shared [Monoidal] record on [CFreeCat S] — the
 [CFreeCat_Monoidal S Cdec] of [Construction/ColouredPROP/Monoidal.v]
 — with the block braiding [CT_braid cs ds], which crosses a
 [cs]-typed bundle of wires past a [ds]-typed bundle, yielding the
 [BraidedMonoidal] instance on the free coloured PROP; the braid
 involution [CTE_braid_invol] then upgrades it to the
 [SymmetricMonoidal] instance.  Downstream, the Strict and bundled
 coloured-PROP instances all project this single Monoidal record, so
 their agreement is definitional and [Instance.v] can discharge the
 [cprop_monoidal_coherence] field of [Construction/ColouredPROP.v]'s
 class by [eq_refl].

 This file merges the one-sorted spine's donor pair
 [Construction/PROP/Braided.v] + [Construction/PROP/Symmetric.v],
 the same layout compression as [Free.v] (Free + Tensor), [Cast.v]
 (Cast + CastTensor + Structural) and [Monoidal.v] (Naturality +
 Monoidal).  The proofs are the donors' proofs with [list Colour]
 replacing [nat], [++] replacing [Nat.add], and [app_assoc]
 replacing [Nat.add_assoc]; the naming flip between the donor's
 [T_cast_inv]/[T_cast_inv_sym] and the coloured
 [CT_cast_inv]/[CT_cast_inv_sym] is accounted for below (the
 coloured [CT_cast_inv] is the TARGET-side cancellation
 [cast e ⊙c cast (eq_sym e) ≈ id], which the donor called
 [T_cast_inv_sym]).

 Three proof fields are needed beyond the braid itself (writing
 [⊙c = CT_comp], [⊕c = CT_tens], [σ = CT_braid], and [α] for the
 associator casts of [Cast.v]):

 - [braid_natural], the joint naturality square in the [ArityTwo]
 form of [Theory/Naturality.v]: for [g : x ⇒ y], [h : z ⇒ w],

 (h ⊕c id_y) ⊙c (id_z ⊕c g) ⊙c σ_{x,z}
 ≈ σ_{y,w} ⊙c (id_y ⊕c h) ⊙c (g ⊕c id_z).

 Fusing the adjacent half-identity tensors on each side
 ([ctens_fuse_l] / [ctens_fuse_r]) reduces the square to the
 primitive constructor [CTE_braid_natural].  (Per the design
 note at the foot of [Monoidal.v], the coloured spine defines
 no [braid_natural]-named synonym lemma that could shadow the
 [BraidedMonoidal] projection in the record below.)

 - [hexagon_identity], braiding [x] past the tensor [y ⨂ z]:

 α_{y,z,x} ⊙c σ_{x,y++z} ⊙c α_{x,y,z}
 ≈ (id_y ⊕c σ_{x,z}) ⊙c α_{y,x,z} ⊙c (σ_{x,y} ⊕c id_z).

 Its source is the [CTE_braid_hex_right] axiom of [TermEq],
 stated there in [eq_rect] transport form; the transport
 bridges of [Construction/ColouredPROP/Monoidal.v]
 ([ceq_rect_cod_cast], [ceq_rect_dom_cast], [CT_cast_sym_sym])
 rewrite every transport as composition with a [CT_cast], and
 one inverse-cast cancellation ([CT_cast_inv]) aligns the
 result with the class field.

 - [hexagon_identity_sym], braiding the tensor [x ⨂ y] past [z]
 along the inverse associators: the same recipe applied to
 [CTE_braid_hex_left].

 The [braid_invol] field of [SymmetricMonoidal] is the
 [CTE_braid_invol] axiom on the nose: crossing a [cs]-typed bundle
 past a [ds]-typed bundle and back untangles completely.  Since the
 tensor of [CFreeCat S] is [++] on objects, [cs ⨂ ds] and
 [cs ++ ds] agree definitionally and the axiom matches the class
 field verbatim.

 Decidability discipline (design decision D2): every lemma in this
 file is UIP-free — the donor's appeals to UIP on [nat] were already
 replaced in [Monoidal.v]'s bridges by destructing the quantified
 boundary equation.  Only the record instances depend on the colour
 decider [Cdec], and only through their [braided_is_monoidal]
 projection [CFreeCat_Monoidal S Cdec] (see the D2 WARNING at the
 foot of [Monoidal.v]: instance sites must fix ONE canonical [Cdec]
 per colour type).

 All proof fields of the records are supplied from standalone,
 named lemmas (the [Free.v] discipline), and the records themselves
 are explicit [Build_BraidedMonoidal] / [Build_SymmetricMonoidal]
 applications, so no Program obligations are generated and
 successor files — Strict, the bundled coloured-PROP instance, and
 the presentation layer — can reuse the very same lemmas. 

 --------
 nLab:  https://ncatlab.org/nlab/show/braided+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 Wikipedia:  https://en.wikipedia.org/wiki/Braided_monoidal_category 
 Wikipedia:  https://en.wikipedia.org/wiki/Symmetric_monoidal_category 
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 该文件为在  [CFreeCat S] 上共享的  [Monoidal] 记录提供了块编织  [CT_braid cs ds] ，它将一个 [cs] 类型的导线束穿过一个 [ds] 类型的导线束，从而在自由彩色 PROP 上生成 [BraidedMonoidal] 实例；然后编织反演 [CTE_braid_invol] 将其升级为 [SymmetricMonoidal] 实例。下游，严格的和彩色 PROP 捆绑实例都投影这个单一的单体记录，因此它们的一致性是定义性的，而 [Instance.v] 可以通过 [eq_refl] 解除 [Construction/ColouredPROP.v] 类的 [cprop_monoidal_coherence] 字段。该文件合并了单排序脊柱的供体对 [Construction/PROP/Braided.v] + [Construction/PROP/Symmetric.v]，与 [Free.v]（自由 + 张量）、[Cast.v]（铸造 + 铸造张量 + 结构）以及 [Monoidal.v]（自然性 + 单性）具有相同的布局压缩。证明使用了供体的证明，并将 [list Colour] 替代 [nat]，[++] 替代 [Nat.add]，[app_assoc] 替代 [Nat.add_assoc]；供体的 [T_cast_inv] / [T_cast_inv_sym] 与彩色的 [CT_cast_inv] / [CT_cast_inv_sym] 之间的命名翻转在下文中已处理（彩色的 [CT_cast_inv] 是目标端的消去 [cast e ⊙c cast (eq_sym e) ≈ id]，供体称其为 [T_cast_inv_sym]）。

 除了编织本身之外，还需要三个证明域（写作 [⊙c = CT_comp]、[⊕c = CT_tens]、[σ = CT_braid] 和 [α]，作为 [Cast.v] 的结合子类型）：- [braid_natural]，在 [ArityTwo] 形式的 [Theory/Naturality.v] 中的联合自然方阵：对于 [g : x ⇒ y]，[h : z ⇒ w]，

 (h ⊕c id_y) ⊙c (id_z ⊕c g) ⊙c σ_{x,z} 
 ≈ σ_{y,w} ⊙c (id_y ⊕c h) ⊙c (g ⊕c id_z)。

 通过融合每一边相邻的半恒等张量（[ctens_fuse_l] / [ctens_fuse_r]）将该方阵简化为原始构造器 [CTE_braid_natural]。（根据 [Monoidal.v] 页脚的设计说明，彩色主干不定义任何可能遮蔽下方记录中 [BraidedMonoidal] 投影的 [braid_natural] 命名同义引理。）

 - [hexagon_identity]，将 [x] 编织到张量 [y ⨂ z] 之后：

 α_{y,z,x} ⊙c σ_{x,y++z} ⊙c α_{x,y,z} 
 ≈ (id_y ⊕c σ_{x,z}) ⊙c α_{y,x,z} ⊙c (σ_{x,y} ⊕c id_z)。它的源头是 [CTE_braid_hex_right] 公理 [TermEq]， 在 [eq_rect] 运输形式中陈述；[Construction/ColouredPROP/Monoidal.v] 的运输桥（[ceq_rect_cod_cast]、[ceq_rect_dom_cast]、[CT_cast_sym_sym]）将每个运输重写为与 [CT_cast] 的组合，并且一次逆投射消去（[CT_cast_inv]）将结果与类域对齐。

 - [hexagon_identity_sym]，将张量 [x ⨂ y] 绕过 [z] 沿逆结合子编织：同样的方法应用于 [CTE_braid_hex_left]。[braid_invol] 的 [SymmetricMonoidal] 字段是 [CTE_braid_invol] 公理的准确体现：将一个 [cs] 类型的束穿过一个 [ds] 类型的束再返回时会完全解开。由于 [CFreeCat S] 的张量在对象上是 [++]，[cs ⨂ ds] 和 [cs ++ ds] 在定义上是一致的，而且该公理与类字段逐字匹配。

 可判定性纪律（设计决策 D2）：本文件中的每个引理都不依赖 UIP——捐赠者对 [nat] 使用 UIP 的部分已经在 [Monoidal.v] 的桥中通过析构量化边界方程被替换。只有记录实例依赖颜色判定器 [Cdec]，并且仅通过它们的 [braided_is_monoidal] 投影 [CFreeCat_Monoidal S Cdec]（参见 [Monoidal.v] 底部的 D2 警告：实例位置必须为每种颜色类型固定一个规范的 [Cdec]）。记录的所有证明字段都来自独立命名的引理（[Free.v] 学科），而记录本身是明确的 [Build_BraidedMonoidal] / [Build_SymmetricMonoidal] 应用，因此不会生成程序义务，且后续文件——Strict、捆绑的彩色 PROP 实例以及展示层——可以重用相同的引理。
*)

Section CFreeBraided.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(*
   * ** Braid naturality in [ArityTwo] form

   The [braid_natural] field of [BraidedMonoidal] unfolds, through
   the [Mapping] instances of [Structure/Monoidal/Naturality.v], to
   the square below: each side tensors one morphism against a
   half-identity before composing with the braid.  [ctens_fuse_l]
   collapses the left-hand pair to [h ⊕c g] and [ctens_fuse_r] the
   right-hand pair to [g ⊕c h], after which the square is exactly
   [CTE_braid_natural]. 

   --------
   * ** 在 [ArityTwo] 形式中的编织自然性

   [BraidedMonoidal] 的 [braid_natural] 场通过 [Structure/Monoidal/Naturality.v] 的 [Mapping] 实例展开，形成下面的方形：每一边在与编织组合之前，将一个态射与半单位张量。[ctens_fuse_l] 把左边的对折叠为 [h ⊕c g]，把右边的对折叠为 [g ⊕c h]，之后该方形正好是 [CTE_braid_natural]。
*)

Lemma cfree_braid_square {x y z w : list Colour}
  (g : CTerm S x y) (h : CTerm S z w) :
  CTermEq S
    (CT_comp (CT_comp (CT_tens h (CT_id y)) (CT_tens (CT_id z) g))
             (CT_braid x z))
    (CT_comp (CT_comp (CT_braid y w) (CT_tens (CT_id y) h))
             (CT_tens g (CT_id z))).
Proof.
  apply CTE_trans with (CT_comp (CT_tens h g) (CT_braid x z)).
  - apply CTE_comp_cong.
    + apply ctens_fuse_l.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp (CT_braid y w) (CT_tens g h)).
    + apply CTE_braid_natural.
    + apply CTE_sym.
      apply CTE_trans with
        (CT_comp (CT_braid y w)
                 (CT_comp (CT_tens (CT_id y) h) (CT_tens g (CT_id z)))).
      * apply CTE_assoc.
      * apply CTE_comp_cong.
        -- apply CTE_refl.
        -- apply ctens_fuse_r.
Qed.

(*
   * ** The right hexagon in [CT_cast] form

   [CTE_braid_hex_right x y z] asserts the hexagon for [σ_{x,y++z}]
   with its boundary mismatches carried by [eq_rect] transports over
   [app_assoc] equations.  Converting the codomain transport on the
   left-hand side by [ceq_rect_cod_cast] and the two domain
   transports on the right-hand side by [ceq_rect_dom_cast] (plus
   [CT_cast_sym_sym] to erase a double [eq_sym]) restates the axiom
   purely in terms of [CT_cast] composites. 

   --------
   * ** [CT_cast] 形式的右六边形

   [CTE_braid_hex_right x y z] 断言了 [σ_{x,y++z}] 的六边形，其边界不匹配由 [eq_rect] 在 [app_assoc] 方程上进行传输。通过 [ceq_rect_cod_cast] 转换左侧的陪域传输，以及通过 [ceq_rect_dom_cast] 转换右侧的两个域传输（加上 [CT_cast_sym_sym] 消去一个重复的 [eq_sym]），可以将公理纯粹用 [CT_cast] 复合来重新表述。
*)

Lemma cbraid_hex_right_cast (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_cast (eq_sym (app_assoc y z x))) (CT_braid x (y ++ z)))
    (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                      (CT_cast (eq_sym (app_assoc y x z))))
             (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                      (CT_cast (app_assoc x y z)))).
Proof.
  apply CTE_trans with
    (eq_rect ((y ++ z) ++ x)
             (fun t => CTerm S (x ++ (y ++ z)) t)
             (CT_braid x (y ++ z))
             (y ++ (z ++ x))
             (eq_sym (app_assoc y z x))).
  - apply CTE_sym, ceq_rect_cod_cast.
  - apply CTE_trans with
      (CT_comp
         (eq_rect (y ++ (x ++ z))
                  (fun s => CTerm S s (y ++ (z ++ x)))
                  (CT_tens (CT_id y) (CT_braid x z))
                  ((y ++ x) ++ z)
                  (app_assoc y x z))
         (eq_rect ((x ++ y) ++ z)
                  (fun s => CTerm S s ((y ++ x) ++ z))
                  (CT_tens (CT_braid x y) (CT_id z))
                  (x ++ (y ++ z))
                  (eq_sym (app_assoc x y z)))).
    + apply CTE_braid_hex_right.
    + apply CTE_comp_cong.
      * apply ceq_rect_dom_cast.
      * rewrite <- (CT_cast_sym_sym S (app_assoc x y z)).
        apply ceq_rect_dom_cast.
Qed.

(*
   * ** First hexagon identity

   The [hexagon_identity] field of [BraidedMonoidal] at [x y z],
   with every associator spelled as the [CT_cast] of the matching
   [app_assoc] equation (the [to] direction is the [eq_sym] cast,
   per [CFreeCat_tensor_assoc]).  Post-composing both sides of
   [cbraid_hex_right_cast] with the incoming associator and
   cancelling the resulting cast-inverse pair by [CT_cast_inv]
   yields the class field verbatim. 

   --------
   * ** 第一个六边形恒等式

   在 [x y z] 的 [BraidedMonoidal] 场的 [hexagon_identity]，
   每个结合子都拼写为匹配的 [app_assoc] 方程的 [CT_cast]（[CFreeCat_tensor_assoc] 指出 [to] 方向是 [eq_sym] 的类型转换）。后将 [cbraid_hex_right_cast] 的两边与输入结合子作后复合，并通过 [CT_cast_inv] 消去生成的类型转换逆对，即得到类域完全原文。
*)

Lemma cfree_hexagon (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc y z x)))
                      (CT_braid x (y ++ z)))
             (CT_cast (eq_sym (app_assoc x y z))))
    (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                      (CT_cast (eq_sym (app_assoc y x z))))
             (CT_tens (CT_braid x y) (CT_id z))).
Proof.
  apply CTE_trans with
    (CT_comp (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                               (CT_cast (eq_sym (app_assoc y x z))))
                      (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                               (CT_cast (app_assoc x y z))))
             (CT_cast (eq_sym (app_assoc x y z)))).
  - apply CTE_comp_cong.
    + apply cbraid_hex_right_cast.
    + apply CTE_refl.
  - apply CTE_trans with
      (CT_comp (CT_comp (CT_tens (CT_id y) (CT_braid x z))
                        (CT_cast (eq_sym (app_assoc y x z))))
               (CT_comp (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                                 (CT_cast (app_assoc x y z)))
                        (CT_cast (eq_sym (app_assoc x y z))))).
    + apply CTE_assoc.
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply CTE_trans with
          (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                   (CT_comp (CT_cast (app_assoc x y z))
                            (CT_cast (eq_sym (app_assoc x y z))))).
        -- apply CTE_assoc.
        -- apply CTE_trans with
             (CT_comp (CT_tens (CT_braid x y) (CT_id z))
                      (CT_id ((x ++ y) ++ z))).
           ++ apply CTE_comp_cong.
              ** apply CTE_refl.
              ** apply CT_cast_inv.
           ++ apply CTE_id_right.
Qed.

(*
   * ** The left hexagon in [CT_cast] form

   Mirror bridge: [CTE_braid_hex_left x y z] is the hexagon for
   [σ_{x++y,z}], and its transports convert by the same three
   bridges.  Here the inverse associators appear, so the casts are
   the forward [app_assoc] equations (the [from] direction of
   [CFreeCat_tensor_assoc]). 

   --------
   * ** [CT_cast] 形式中的左六边形

   镜像桥：[CTE_braid_hex_left x y z] 是 [σ_{x++y,z}] 的六边形，并且它的传输通过相同的三个桥转换。这里出现了逆结合子，因此转换是前向的 [app_assoc] 方程（[CFreeCat_tensor_assoc] 的 [from] 方向）。
*)

Lemma cbraid_hex_left_cast (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_braid (x ++ y) z) (CT_cast (app_assoc x y z)))
    (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                      (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                               (CT_cast (app_assoc x z y))))
             (CT_tens (CT_id x) (CT_braid y z))).
Proof.
  apply CTE_trans with
    (eq_rect ((x ++ y) ++ z)
             (fun s => CTerm S s (z ++ (x ++ y)))
             (CT_braid (x ++ y) z)
             (x ++ (y ++ z))
             (eq_sym (app_assoc x y z))).
  - apply CTE_sym.
    rewrite <- (CT_cast_sym_sym S (app_assoc x y z)).
    apply ceq_rect_dom_cast.
  - apply CTE_trans with
      (CT_comp
         (eq_rect ((z ++ x) ++ y)
                  (fun t => CTerm S (x ++ (z ++ y)) t)
                  (eq_rect ((x ++ z) ++ y)
                           (fun s => CTerm S s ((z ++ x) ++ y))
                           (CT_tens (CT_braid x z) (CT_id y))
                           (x ++ (z ++ y))
                           (eq_sym (app_assoc x z y)))
                  (z ++ (x ++ y))
                  (eq_sym (app_assoc z x y)))
         (CT_tens (CT_id x) (CT_braid y z))).
    + apply CTE_braid_hex_left.
    + apply CTE_comp_cong.
      * apply CTE_trans with
          (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                   (eq_rect ((x ++ z) ++ y)
                            (fun s => CTerm S s ((z ++ x) ++ y))
                            (CT_tens (CT_braid x z) (CT_id y))
                            (x ++ (z ++ y))
                            (eq_sym (app_assoc x z y)))).
        -- apply ceq_rect_cod_cast.
        -- apply CTE_comp_cong.
           ++ apply CTE_refl.
           ++ rewrite <- (CT_cast_sym_sym S (app_assoc x z y)).
              apply ceq_rect_dom_cast.
      * apply CTE_refl.
Qed.

(*
   * ** Second hexagon identity

   The [hexagon_identity_sym] field of [BraidedMonoidal] at [x y z],
   phrased through the inverse associators.  Pre-composing both
   sides of [cbraid_hex_left_cast] with the outgoing inverse
   associator [CT_cast (app_assoc z x y)], reassociating, and
   cancelling the cast-inverse pair by [CT_cast_inv] gives the class
   field. 

   --------
   * ** 第二六边形恒等式

   在 [x y z] 处的 [BraidedMonoidal] 的 [hexagon_identity_sym] 场，通过逆结合子来表达。将 [cbraid_hex_left_cast] 的两边预先与外向逆结合子 [CT_cast (app_assoc z x y)] 组合，重新结合，并通过 [CT_cast_inv] 消去投射-逆元对，即得到类场。
*)

Lemma cfree_hexagon_sym (x y z : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_cast (app_assoc z x y)) (CT_braid (x ++ y) z))
             (CT_cast (app_assoc x y z)))
    (CT_comp (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                      (CT_cast (app_assoc x z y)))
             (CT_tens (CT_id x) (CT_braid y z))).
Proof.
  apply CTE_trans with
    (CT_comp (CT_cast (app_assoc z x y))
             (CT_comp (CT_braid (x ++ y) z) (CT_cast (app_assoc x y z)))).
  - apply CTE_assoc.
  - apply CTE_trans with
      (CT_comp (CT_cast (app_assoc z x y))
               (CT_comp (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                                 (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                          (CT_cast (app_assoc x z y))))
                        (CT_tens (CT_id x) (CT_braid y z)))).
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply cbraid_hex_left_cast.
    + apply CTE_trans with
        (CT_comp (CT_comp (CT_cast (app_assoc z x y))
                          (CT_comp (CT_cast (eq_sym (app_assoc z x y)))
                                   (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                            (CT_cast (app_assoc x z y)))))
                 (CT_tens (CT_id x) (CT_braid y z))).
      * apply CTE_sym, CTE_assoc.
      * apply CTE_comp_cong.
        -- apply CTE_trans with
             (CT_comp (CT_comp (CT_cast (app_assoc z x y))
                               (CT_cast (eq_sym (app_assoc z x y))))
                      (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                               (CT_cast (app_assoc x z y)))).
           ++ apply CTE_sym, CTE_assoc.
           ++ apply CTE_trans with
                (CT_comp (CT_id ((z ++ x) ++ y))
                         (CT_comp (CT_tens (CT_braid x z) (CT_id y))
                                  (CT_cast (app_assoc x z y)))).
              ** apply CTE_comp_cong.
                 --- apply CT_cast_inv.
                 --- apply CTE_refl.
              ** apply CTE_id_left.
        -- apply CTE_refl.
Qed.

(*
   * ** THE BraidedMonoidal record on [CFreeCat S]

   [braided_is_monoidal] names the ONE shared [Monoidal] record
   [CFreeCat_Monoidal S Cdec]; the braid is [CT_braid] (recall that
   on objects the tensor is [++], so [cs ⨂ ds] and [cs ++ ds] agree
   definitionally); all proof fields are the standalone lemmas
   above.  The record is an explicit [Build_BraidedMonoidal]
   application, so no Program obligations are generated and no
   inference is left to a record literal. 

   --------
   * **在 [CFreeCat S] 上的 BraidedMonoidal 记录

   [braided_is_monoidal] 指定了唯一共享的 [Monoidal] 记录 [CFreeCat_Monoidal S Cdec]；编织是 [CT_braid]（回想在对象上张量是 [++]，因此 [cs ⨂ ds] 和 [cs ++ ds] 在定义上是一致的）；所有证明字段都是上面独立的引理。该记录是显式的 [Build_BraidedMonoidal] 应用，因此不会生成 Program 义务，也不会留下任何推导给记录字面值。
*)

Definition CFreeCat_Braided : @BraidedMonoidal (CFreeCat S) :=
  @Build_BraidedMonoidal (CFreeCat S)
    (CFreeCat_Monoidal S Cdec)
    (fun cs ds => CT_braid cs ds)
    (fun x y g z w h => cfree_braid_square g h)
    (fun x y z => cfree_hexagon x y z)
    (fun x y z => cfree_hexagon_sym x y z).

(*
   * ** Braid involution

   The [braid_invol] field of [SymmetricMonoidal] at [x y]: the
   composite [σ_{y,x} ⊙c σ_{x,y} : x ++ y ⇒ x ++ y] is the identity.
   This is the primitive constructor [CTE_braid_invol] applied at
   [cs := x], [ds := y]. 

   --------
   * ** 辫子变换

   在 [x y] 的 [SymmetricMonoidal] 上的 [braid_invol] 场：复合 [σ_{y,x} ⊙c σ_{x,y} : x ++ y ⇒ x ++ y] 是恒等。
   这是在 [cs := x]、[ds := y] 上应用的原始构造函数 [CTE_braid_invol] 。
*)

Lemma cfree_braid_invol (x y : list Colour) :
  CTermEq S (CT_comp (CT_braid y x) (CT_braid x y)) (CT_id (x ++ y)).
Proof.
  apply CTE_braid_invol.
Qed.

(*
   * ** THE SymmetricMonoidal record on [CFreeCat S]

   A coloured PROP is a SYMMETRIC strict monoidal category, so the
   braiding installed above must be its own inverse.
   [symmetric_is_braided] names the ONE braided record
   [CFreeCat_Braided] (hence, through it, the ONE shared [Monoidal]
   record [CFreeCat_Monoidal S Cdec]); the involution proof is the
   standalone lemma above. 

   --------
   * ** [CFreeCat S] 上的对称幺半群记录

   彩色 PROP 是一个对称严格幺半范畴，所以上面安装的交换律必须是它自己的逆。
   [symmetric_is_braided] 命名了单一的带编织记录
   [CFreeCat_Braided]（因此，通过它，单一的共享 [Monoidal] 记录 [CFreeCat_Monoidal S Cdec]）；反 involution 的证明是上面的独立引理。
*)

Definition CFreeCat_Symmetric : @SymmetricMonoidal (CFreeCat S) :=
  @Build_SymmetricMonoidal (CFreeCat S)
    CFreeCat_Braided
    (fun x y => cfree_braid_invol x y).

End CFreeBraided.

Arguments CFreeCat_Braided {Colour} S Cdec : assert.
Arguments CFreeCat_Symmetric {Colour} S Cdec : assert.
