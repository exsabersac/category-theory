Require Import Category.Lib.
Require Import Category.Construction.ColouredPROP.Signature.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * Equational theory of free coloured-PROP terms / * * 自由有色-PROP 项的方程理论 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 The equivalence relation [CTermEq] on [CTerm S cs ds] quotients the
 raw syntax of [Construction/ColouredPROP/Signature.v] by the strict
 symmetric monoidal category axioms.  The quotient
 [CTerm S / CTermEq S] is the free COLOURED PROP (= free strict
 symmetric monoidal category whose objects are the finite words over
 [Colour] under concatenation) on the signature [S].

 In library notation, with [⊙c = CT_comp], [⊕c = CT_tens],
 [id = CT_id], [σ = CT_braid], the constructors below assert:

 - reflexivity, symmetry, transitivity (the setoid laws)
 - congruences for [CT_comp] and [CT_tens]
 - category laws: identity-left, identity-right, associativity
 - bifunctor (tensor) laws: identity, sequential interchange,
 functoriality
 - symmetric-monoidal coherence: braid naturality, braid
 involution, hexagon

 The strict-PROP axioms on colour words — [CT_id cs ⊕c CT_id ds ≈
 CT_id (cs ++ ds)], the concatenation-as-tensor strict laws — are
 present as primitive constructors of [CTermEq] because the [CTerm]
 type is indexed by [list Colour] and [CT_id cs ⊕c CT_id ds] has
 type [CTerm S (cs ++ ds) (cs ++ ds)] while [CT_id (cs ++ ds)] has
 the same type by definition; the equation is well-typed without
 any [eq_rect] casts.

 This file defines just the equivalence relation.  The [Setoid]
 instance and the [Category] / coloured-PROP structure on the
 quotient live in successor files ([Construction/ColouredPROP/
 Free.v] onward).

 In a STRICT symmetric monoidal category the associator and unitors
 are identities, so the pentagon and triangle coherences hold on the
 nose and the only substantive coherences left are the hexagon and
 the symmetry/involution equation [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id] (cf.
 the nLab and Wikipedia pages above).  Because list concatenation is
 strictly associative/right-unital only up to propositional [=]
 (exactly the asymmetry of [Nat.add] in the one-sorted donor:
 [[] ++ l] is definitional but [l ++ []] and re-association are
 not), several of those “on the nose” equations are nonetheless
 stated below in [eq_rect] transport form. 

 --------
 nLab:  https://ncatlab.org/nlab/show/PROP
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia:  https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory)

 等价关系 [CTermEq] 在 [CTerm S cs ds] 上通过严格的对称单体范畴公理对 [Construction/ColouredPROP/Signature.v] 的原始语法进行商化。商 [CTerm S / CTermEq S] 是签名 [S] 上的自由 COLOURED PROP（= 对象是在 [Colour] 上通过连接形成的有限词的自由严格对称单体范畴）。

 在库表示法中，利用 [⊙c = CT_comp]、[⊕c = CT_tens]、[id = CT_id]、[σ = CT_braid]，下列构造器断言：- 自反性，对称性，传递性（等价类定律）
 - 对 [CT_comp] 和 [CT_tens] 的同余
 - 范畴定律：左单位元、右单位元、结合律
 - 双函子（张量）定律：单位元、顺序交换、函子性
 - 对称单态性一致性：编织的自然性，编织的自反性，六边形律

 关于色词的严格-PROP公理 — [CT_id cs ⊕c CT_id ds ≈ CT_id (cs ++ ds)]，作为张量的串联严格定律 — 被作为 [CTermEq] 的原始构造子存在，因为 [CTerm] 类型由 [list Colour] 索引，而 [CT_id cs ⊕c CT_id ds] 的类型为 [CTerm S (cs ++ ds) (cs ++ ds)]，而 [CT_id (cs ++ ds)] 根据定义具有相同类型；该等式在没有任何 [eq_rect] 转换的情况下是良类型的。此文件仅定义了等价关系。[Setoid] 实例以及商上的 [Category] / 彩色 PROP 结构位于后续文件中（从 [Construction/ColouredPROP/Free.v] 开始）。在一个严格对称单体范畴中，结合子和单位子都是恒等，所以五边形和三角形的相干性在本质上成立，唯一剩下的实质性相干性是六边形以及对称/反演方程 [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id]（参见上面的 nLab 和 Wikipedia 页面）。因为列表连接严格的结合性/右单位性仅在命题 [=] 下成立（正是单一类型捐赠者中 [Nat.add] 的不对称性：[[] ++ l] 是定义性的，但 [l ++ []] 和重新结合则不是），下面 [eq_rect] 的传输形式中仍然陈述了几个这样的“本质上成立”的方程。
*)

Section CTermEq.

Context {Colour : Type}.
Context (S : CSignature Colour).

(*
   * Strict tensor coherence requires equating terms whose types
   involve different parenthesisations of [++] on [list Colour].
   Because concatenation is associative ONLY up to propositional [=]
   (not definitional), we cannot state e.g. an associator
   [CT_assoc : CTerm S ((cs ++ ds) ++ es) (cs ++ (ds ++ es))] in
   [CTerm] alone.  The equational theory bridges these via the strict
   tensor axioms [CTE_tens_assoc] / [CTE_tens_id0_left] /
   [CTE_tens_id0_right]; in practice they are used as rewrite rules to
   bring a term into a canonical right-associated form on its
   boundaries. 

   --------
   * 严格的张量一致性要求将类型涉及  [list Colour] 上  [++]  不同括号化方式的项进行等同。由于连接只是命题性的  [=]  关联（而不是定义性的），我们不能仅在  [CTerm]  中陈述例如结合子  [CT_assoc : CTerm S ((cs ++ ds) ++ es) (cs ++ (ds ++ es))] 。等式理论通过严格的张量公理  [CTE_tens_assoc] / [CTE_tens_id0_left] / [CTE_tens_id0_right] 将这些联系起来；在实际操作中，它们被用作重写规则，将一个项的边界变换为规范的右关联形式。
*)

Inductive CTermEq : forall {cs ds}, CTerm S cs ds -> CTerm S cs ds -> Prop :=

  (** Setoid laws. / 集合等价律。 *)
  | CTE_refl {cs ds} (f : CTerm S cs ds) :                   (* equivalence: reflexivity / 等价性：自反性 *)
      CTermEq f f
  | CTE_sym {cs ds} (f g : CTerm S cs ds) :                  (* equivalence: symmetry / 等价：对称 *)
      CTermEq f g -> CTermEq g f
  | CTE_trans {cs ds} (f g h : CTerm S cs ds) :              (* equivalence: transitivity / 等价性：传递性 *)
      CTermEq f g -> CTermEq g h -> CTermEq f h

  (** Congruence of sequential composition. / 顺序组合的一致性。 *)
  | CTE_comp_cong {cs ds es}                                 (* congruence of [CT_comp] / [CT_comp] 的全等 *)
      (f f' : CTerm S ds es) (g g' : CTerm S cs ds) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_comp f g) (CT_comp f' g')

  (** Congruence of parallel composition (tensor). / 并行组合（张量）的相合性。 *)
  | CTE_tens_cong {cs1 ds1 cs2 ds2}                          (* congruence of [CT_tens] / [CT_tens] 的合同性 *)
      (f f' : CTerm S cs1 ds1) (g g' : CTerm S cs2 ds2) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_tens f g) (CT_tens f' g')

  (** Category laws: id-left, id-right, associativity. / 范畴律：左单位元、右单位元、结合律。 *)
  | CTE_id_left {cs ds} (f : CTerm S cs ds) :                (* category: left identity / 类别：左身份 *)
      CTermEq (CT_comp (CT_id ds) f) f
  | CTE_id_right {cs ds} (f : CTerm S cs ds) :               (* category: right identity / 类别：右派身份 *)
      CTermEq (CT_comp f (CT_id cs)) f
  | CTE_assoc {cs ds es fs}                                  (* category: associativity of [⊙c] / 类别：[⊙c]的结合性 *)
      (h : CTerm S es fs) (g : CTerm S ds es) (f : CTerm S cs ds) :
      CTermEq (CT_comp (CT_comp h g) f)
              (CT_comp h (CT_comp g f))

  (*
   * Bifunctor laws: identity, sequential interchange.

   [CTE_tens_id]: [id_cs ⊕c id_ds = id_(cs ++ ds)] — typing OK
   because [CTerm] is [list Colour]-indexed and concatenation is
   the tensor on boundaries. 

   --------
   * 双函子定律：恒等，顺序交换。

   [CTE_tens_id] :  [id_cs ⊕c id_ds = id_(cs ++ ds)] — 类型正确
   因为 [CTerm] 是 [list Colour] 索引的，并且连接是边界上的张量。
*)
  | CTE_tens_id (cs ds : list Colour) :                      (* bifunctor: tensor preserves identity / 双函子：张量保持恒等式 *)
      CTermEq (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds))

  (*
   * [CTE_interchange]: (f₁ ⊕c g₁) ⊙c (f₂ ⊕c g₂) ≈ (f₁ ⊙c f₂) ⊕c (g₁ ⊙c g₂)
   — the parallel/sequential interchange law. 

   --------
   *  [CTE_interchange] : (f₁ ⊕c g₁) ⊙c (f₂ ⊕c g₂) ≈ (f₁ ⊙c f₂) ⊕c (g₁ ⊙c g₂)
   — 并行/顺序交换律。
*)
  | CTE_interchange {cs ds es cs' ds' es'}                   (* bifunctor: middle-four interchange / 双函子：中间四交换 *)
      (f1 : CTerm S ds es) (f2 : CTerm S cs ds)
      (g1 : CTerm S ds' es') (g2 : CTerm S cs' ds') :
      CTermEq (CT_comp (CT_tens f1 g1) (CT_tens f2 g2))
              (CT_tens (CT_comp f1 f2) (CT_comp g1 g2))

  (*
   * Braid involution: [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id_{cs ++ ds}].
   Block-braiding twice returns to identity. 

   --------
   * 辫子反演：[σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id_{cs ++ ds}]。
   对区块进行两次编排会返回到恒等式。
*)
  | CTE_braid_invol (cs ds : list Colour) :                  (* symmetry: involution σ⊙σ = id / 对称：反演 σ⊙σ = id *)
      CTermEq (CT_comp (CT_braid ds cs) (CT_braid cs ds)) (CT_id (cs ++ ds))

  (*
   * Braid naturality (top form):
   (g ⊕c f) ⊙c σ_{cs1,cs2} ≈ σ_{ds1,ds2} ⊙c (f ⊕c g)
   where f : cs1 -> ds1, g : cs2 -> ds2. 

   --------
   * 拓扑结构的天然性（顶层形式）：
   (g ⊕c f) ⊙c σ_{cs1,cs2} ≈ σ_{ds1,ds2} ⊙c (f ⊕c g)
   其中 f : cs1 -> ds1, g : cs2 -> ds2。
*)
  | CTE_braid_natural {cs1 ds1 cs2 ds2}                      (* symmetry: braiding naturality / 对称性：编织自然性 *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
      CTermEq (CT_comp (CT_tens g f) (CT_braid cs1 cs2))
              (CT_comp (CT_braid ds1 ds2) (CT_tens f g))

  (*
   * Strict-PROP unit on tensor: tensoring with the empty term
   [CT_id []] on the LEFT is an identity operation modulo the
   definitional equation [[] ++ cs = cs].

   This axiom is the analogue of the strict-unit law in a
   [StrictMonoidal] category.  In a generic [Monoidal] category
   it would be a natural ISOMORPHISM (the left unitor), not an
   equation; coloured PROPs are strict on the nose, so we assert
   it as an equation in [CTermEq].

   Both sides have type [CTerm S ([] ++ cs) ds] = [CTerm S cs ds]
   on the nose, so no transport is needed — [[] ++ l] reduces
   definitionally, just as [0 + n] does on [nat]. 

   --------
   * 张量上的严格-PROP单位：在左侧用空项 [CT_id [] 张量运算是一个恒等操作（模定义方程 [[] ++ cs = cs）。

   该公理是 [StrictMonoidal] 范畴中严格单位律的类比。在一个通用的 [Monoidal] 范畴中，它将是一个自然同构（左单位子），而不是一个方程；有色PROP在本质上是严格的，因此我们将其作为 [CTermEq] 中的方程来断言。

   双方的类型都是 [CTerm S ([] ++ cs) ds] = [CTerm S cs ds]，因此不需要迁移——[[] ++ l] 定义上会约简，就像 [0 + n] 在 [nat] 上所做的那样。
*)
  | CTE_tens_id0_left {cs ds} (f : CTerm S cs ds) :          (* strict unit: left unitor λ = id / 严格单位：左单位子 λ = 恒等 *)
      CTermEq (CT_tens (CT_id []) f) f

  (*
   * Strict-PROP unit on the right: dually, tensoring with [CT_id []]
   on the RIGHT is identity modulo [cs ++ [] = cs].

   Stated in transport form via [eq_rect] over the boundary
   equations.  Concretely [CT_tens f (CT_id [])] has type
   [CTerm S (cs ++ []) (ds ++ [])]; we transport it to
   [CTerm S cs ds] using [app_nil_r] on both indices, and assert
   the result equals [f]. 

   --------
   * 右边的严格-PROP单元：相应地，用 [CT_id [] 张量右边是 [cs ++ [] 模下的恒等 = cs。

   通过边界方程的 [eq_rect] 以传输形式陈述。具体地，[CT_tens f (CT_id [] ）] 的类型为 [CTerm S (cs ++ [] ） (ds ++ [])]；我们使用 [app_nil_r] 在两个指标上将其传输到 [CTerm S cs ds]，并断言结果等于 [f] 。
*)
  | CTE_tens_id0_right {cs ds} (f : CTerm S cs ds) :         (* strict unit: right unitor ρ = id / 严格幺元：右幺元ρ = 身份 *)
      CTermEq (eq_rect (ds ++ [])
                       (fun k => CTerm S (cs ++ []) k)
                       (CT_tens f (CT_id []))
                       ds
                       (app_nil_r ds))
              (eq_rect_r (fun k => CTerm S k ds)
                         f
                         (app_nil_r cs))

  (** Strict-PROP associativity of tensor. Transport form. / 张量的严格-PROP结合性。传输形式。 *)
  | CTE_tens_assoc {cs1 ds1 cs2 ds2 cs3 ds3}                 (* strict associator α = id / 严格结合子 α = id *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) (h : CTerm S cs3 ds3) :
      CTermEq (eq_rect ((ds1 ++ ds2) ++ ds3)
                       (fun k => CTerm S ((cs1 ++ cs2) ++ cs3) k)
                       (CT_tens (CT_tens f g) h)
                       (ds1 ++ (ds2 ++ ds3))
                       (eq_sym (app_assoc ds1 ds2 ds3)))
              (eq_rect_r (fun k => CTerm S k (ds1 ++ (ds2 ++ ds3)))
                         (CT_tens f (CT_tens g h))
                         (eq_sym (app_assoc cs1 cs2 cs3)))

  (*
   * ** Hexagon axioms for block braids

   In a strict symmetric monoidal category the braid decomposes
   additively in either argument (Mac Lane CWM Ch.VII §7;
   Joyal–Street §2; Selinger, “A survey of graphical languages for
   monoidal categories” (arXiv:0908.3347), §3.3/§3.5 — braided
   resp. symmetric):

   σ_{m++n,p} ≈ (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})     (hex-left)
   σ_{m,n++p} ≈ (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)     (hex-right)

   The LHS and RHS do not have matching types on the nose because
   concatenation on [list Colour] is associative only up to
   propositional [=], so both equations are stated in transport
   form via [eq_rect] against [app_assoc], analogous to
   [CTE_tens_assoc].

   Without these, e.g. [CT_braid [c1; c2; c3] [d1; d2]] is not
   provably equal to the layered composite of single-wire swaps,
   and the [BraidedMonoidal] layer beneath the [SymmetricMonoidal]
   instance on [CFreeCat S] cannot discharge [hexagon_identity] /
   [hexagon_identity_sym] for non-trivial colour words.

   ** Minimality note (nLab/Wikipedia, symmetric_monoidal_category)

   In a SYMMETRIC (as opposed to merely braided) monoidal category
   the two hexagons are NOT independent: given the symmetry equation
   [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id] ([CTE_braid_invol]) together with
   braid naturality ([CTE_braid_natural]), either hexagon implies
   the other.  So exactly one of [CTE_braid_hex_left] /
   [CTE_braid_hex_right] is logically necessary; the other is a
   derivable theorem we keep as a primitive constructor for
   ergonomics (the [eq_rect] transport bookkeeping makes the formal
   derivation tedious).  As with the unit-braid constructors below,
   the redundancy is sound and cannot make [CTermEq] inconsistent
   (every constructor is inhabited by the standard model in which a
   term denotes the colour-preserving permutation of its wires).
   Deriving one as a [Lemma] after the inductive would change only
   the axiom budget, not any [CTermEq]-judgement. 

   --------
   * ** 块状编织的六边形公理

   在严格对称单体范畴中，编织在任一参数下都是可加分解的（Mac Lane《CWM》第七章§7；Joyal–Street§2；Selinger，《单体范畴的图形语言综述》(arXiv:0908.3347)，§3.3/§3.5 — 分别为编织与对称）：

   σ_{m++n,p} ≈ (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})     （六边形-左）
   σ_{m,n++p} ≈ (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)     （六边形-右）

   左边和右边的类型并不完全匹配，因为在 [list Colour] 上的连接仅在命题 [=] 意义下是结合性的，所以两个方程都通过 [eq_rect] 对 [app_assoc] 以变换形式陈述，这类似于 [CTE_tens_assoc] 。没有这些，例如 [CT_braid [c1; c2; c3] [d1; d2] ] 无法证明等于单线交换的分层复合，并且 [BraidedMonoidal] 层位于 [SymmetricMonoidal] 实例的下面，在 [CFreeCat S] 上无法对非平凡的颜色词释放 [hexagon_identity] / [hexagon_identity_sym]。

   ** 最小性说明（nLab/Wikipedia，对称单闪范畴）在一个对称（相对于仅仅是编织的）单体范畴中，两个六边形并不是独立的：给定对称性方程 [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id]（[CTE_braid_invol]）以及编织的自然性（[CTE_braid_natural]），任意一个六边形都可以推导出另一个。因此，[CTE_braid_hex_left] / [CTE_braid_hex_right] 中恰好一个在逻辑上是必要的；另一个是一个可导出的定理，我们保留它作为原始构造器以便于使用（[eq_rect] 的传输记账使得形式推导变得繁琐）。正如下面的单位-编织构造器一样，这种冗余是合理的，并不会使 [CTermEq] 不一致（每个构造器都由标准模型填充，在该模型中，一个项表示其线的保持颜色的置换）。在归纳之后将其作为 [Lemma] 推导出来只会改变公理预算，而不会改变任何 [CTermEq] 判断。
*)

  | CTE_braid_hex_left (m n p : list Colour) :               (* symmetry: hexagon (left argument) / 对称性：六边形（左边参数） *)
      CTermEq
        (*
 LHS: σ_{m++n,p} with source cast (m++n)++p → m++(n++p). 

 --------
 左边: σ_{m++n,p} 源类型转换 (m++n)++p → m++(n++p)。
*)
        (eq_rect ((m ++ n) ++ p)
                 (fun s => CTerm S s (p ++ (m ++ n)))
                 (CT_braid (m ++ n) p)
                 (m ++ (n ++ p))
                 (eq_sym (app_assoc m n p)))
        (*
 RHS: (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})
 — the outer term needs both source and target casts to
 reach type CTerm S (m++(p++n)) (p++(m++n)); the inner term
 already has type CTerm S (m++(n++p)) (m++(p++n)). 

 --------
 右侧: (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})
 — 外部项需要源和目标类型转换才能达到类型 CTerm S (m++(p++n)) (p++(m++n)); 内部项已经具有类型 CTerm S (m++(n++p)) (m++(p++n))。
*)
        (CT_comp
           (eq_rect ((p ++ m) ++ n)
                    (fun t => CTerm S (m ++ (p ++ n)) t)
                    (eq_rect ((m ++ p) ++ n)
                             (fun s => CTerm S s ((p ++ m) ++ n))
                             (CT_tens (CT_braid m p) (CT_id n))
                             (m ++ (p ++ n))
                             (eq_sym (app_assoc m p n)))
                    (p ++ (m ++ n))
                    (eq_sym (app_assoc p m n)))
           (CT_tens (CT_id m) (CT_braid n p)))

  | CTE_braid_hex_right (m n p : list Colour) :              (* symmetry: hexagon (right argument) / 对称性：六边形（右参数） *)
      CTermEq
        (*
 LHS: σ_{m,n++p} with target cast (n++p)++m → n++(p++m). 

 --------
 左边: σ_{m,n++p} 目标类型转换 (n++p)++m → n++(p++m)。
*)
        (eq_rect ((n ++ p) ++ m)
                 (fun t => CTerm S (m ++ (n ++ p)) t)
                 (CT_braid m (n ++ p))
                 (n ++ (p ++ m))
                 (eq_sym (app_assoc n p m)))
        (*
 RHS: (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)
 — outer source: n++(m++p) → (n++m)++p (app_assoc forward);
 inner source: (m++n)++p → m++(n++p) (eq_sym). 

 --------
 右侧: (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)
 — 外部来源: n++(m++p) → (n++m)++p (app_assoc forward);
 内部来源: (m++n)++p → m++(n++p) (eq_sym).
*)
        (CT_comp
           (eq_rect (n ++ (m ++ p))
                    (fun s => CTerm S s (n ++ (p ++ m)))
                    (CT_tens (CT_id n) (CT_braid m p))
                    ((n ++ m) ++ p)
                    (app_assoc n m p))
           (eq_rect ((m ++ n) ++ p)
                    (fun s => CTerm S s ((n ++ m) ++ p))
                    (CT_tens (CT_braid m n) (CT_id p))
                    (m ++ (n ++ p))
                    (eq_sym (app_assoc m n p))))

  (*
   * ** Unit-braid coherence

   In any symmetric monoidal category the braid involving the unit
   object collapses to the unitor: [σ_{I,X} = ρ_X^{-1} ∘ λ_X].  In
   the strict coloured-PROP setting on colour words, this becomes
   [CT_braid [] n ≈ CT_id n] and [CT_braid n [] ≈ CT_id n] modulo
   the boundary equation [n ++ [] = n] (which is propositional, not
   definitional — [app] is left-strict only, exactly like
   [Nat.add]).

   ** Minimality note (Joyal–Street §2 Prop. 2.1; Mac Lane CWM VII §1)

   In the literature these unit-braid equations are NOT independent
   axioms — they are theorems of [hexagon + naturality + invol +
   triangle].  Sketch of the derivation in our setting (we omit the
   formal proof's eq_rect bookkeeping for brevity):

   1. Instantiate [CTE_braid_hex_right] at [m := n], [n := []],
   [p := []]:
   σ_{n, [] ++ []} ≈ (id_[] ⊕c σ_{n,[]}) ⊙c (σ_{n,[]} ⊕c id_[]).
   2. Collapse the [id_[] ⊕c _] and [_ ⊕c id_[]] tensors via
   [CTE_tens_id0_left] / [CTE_tens_id0_right]:
   σ_{n, []} ≈ σ_{n, []} ⊙c σ_{n, []}                  (idempotency)
   3. By [CTE_braid_invol]: [σ_{[], n} ⊙c σ_{n, []} ≈ id_{n ++ []}
   ≈ id_n].  Compose both sides of (2) with [σ_{[], n}] on the
   left:
   σ_{[], n} ⊙c σ_{n, []} ≈ σ_{[], n} ⊙c (σ_{n, []} ⊙c σ_{n, []}).
   id_n        ≈  σ_{[], n} ⊙c σ_{n, []} ⊙c σ_{n, []}    (assoc)
   id_n        ≈  id_n ⊙c σ_{n, []}                      (involution)
   id_n        ≈  σ_{n, []}                              (id-left)
   4. The dual [σ_{[], n} ≈ id_n] follows by applying
   [CTE_braid_invol] once more to step (3)'s conclusion.

   We keep them as primitive constructors here for ergonomics: the
   formal derivation requires substantial [eq_rect] bookkeeping
   across hexagon-, strict-unit-, and involution-form transports
   (the unit-boundary cases of those transports do not reduce
   definitionally in [app]), and the relabelling congruence
   (Relabel.v), the interpretation soundness cases (Interp.v), and
   the supply instance (Supply/Instance.v) consume the strict form
   directly.

   Adding sound redundant constructors is harmless (it cannot make
   [CTermEq] inconsistent — every constructor remains inhabited by
   the standard colour-preserving-permutation model).  A future
   refactor that derives these as [Lemma]s after the inductive
   declaration would not change any [CTermEq]-judgements, only the
   axiom budget. 

   --------
   * ** 单位编织一致性

   在任何对称单范畴中，涉及单位对象的编织会塌缩为单位子：[σ_{I,X} = ρ_X^{-1} ∘ λ_X]。在严格的彩色-PROP 颜色单词设置中，这变为 [CT_braid [] n ≈ CT_id n] 和 [CT_braid n [] ≈ CT_id n] 模边界方程 [n ++ [] = n]（这是命题性的，而不是定义性的 — [app] 仅是左严格的，就像 [Nat.add] 一样）。

   ** 最小性注（Joyal–Street §2 命题 2.1；Mac Lane CWM VII §1）

   在文献中，这些单位编织方程并非独立公理 — 它们是 [六边形 + 自然性 + 自反 + 三角形] 的定理。 在我们的设置中的推导概要（为了简洁省略了形式证明的 eq_rect 记账）：1. 在 [m := n] 、 [n := [] ]、[p := [] ] 实例化 [CTE_braid_hex_right] ：
   σ_{n, [] ++ []} ≈ (id_[] ⊕c σ_{n,[]}) ⊙c (σ_{n,[]} ⊕c id_[])。
   2. 通过 [CTE_tens_id0_left] / [CTE_tens_id0_right] 崩溃 [id_[] ⊕c _] 和 [_ ⊕c id_[] ] 张量：
   σ_{n, []} ≈ σ_{n, []} ⊙c σ_{n, []} （幂等性）
   3. 根据 [CTE_braid_invol] ：[σ_{[] , n} ⊙c σ_{n, []} ≈ id_{n ++ []} ≈ id_n]。
   将（2）的两边在左侧与 [σ_{[] , n}] 组合：
   σ_{[], n} ⊙c σ_{n, []} ≈ σ_{[], n} ⊙c (σ_{n, []} ⊙c σ_{n, []})。
   id_n ≈ σ_{[], n} ⊙c σ_{n, []} ⊙c σ_{n, []} （结合律）
   id_n ≈ id_n ⊙c σ_{n, []} （反演律）
   id_n ≈ σ_{n, []} （左单位元）
   4.通过再次将 [CTE_braid_invol] 应用于步骤 (3) 的结论，可得双重 [σ_{[]，n} ≈ id_n]。

   为了方便使用，我们在这里将它们保留为原始构造器：正式推导需要在六边形、严格单位和逆运算形式的运输之间进行大量 [eq_rect] 的记录（那些运输的单位边界情况在 [app] 中不会定义性地简化），而重标记合同（Relabel.v）、解释有效性情况（Interp.v）以及供应实例（Supply/Instance.v）直接使用严格形式。添加冗余构造函数是无害的（它不会使 [CTermEq] 不一致——每个构造函数仍然由标准的保持颜色的排列模型所充满）。 将来在归纳声明之后将这些推导为 [Lemma] 的重构不会改变任何 [CTermEq] 的判断，只会改变公理预算。
*)

  | CTE_braid_unit_left (n : list Colour) :                  (* symmetry: unit braid σ_{[],n} = id (derivable) / 对称性：单位编织 σ_{[],n} = id（可推导） *)
      CTermEq
        (*
 CT_braid [] n : CTerm S ([] ++ n) (n ++ []) = CTerm S n (n ++ []).
 Cast the target n ++ [] → n. 

 --------
 CT_braid [] n : CTerm S ([] ++ n) (n ++ []) = CTerm S n (n ++ [])。
 将目标 n ++ [] → n。
*)
        (eq_rect (n ++ []) (fun t => CTerm S n t)
                 (CT_braid [] n)
                 n
                 (app_nil_r n))
        (CT_id n)

  | CTE_braid_unit_right (n : list Colour) :                 (* symmetry: unit braid σ_{n,[]} = id (derivable) / 对称性：单位编织 σ_{n,[]} = id（可推导） *)
      CTermEq
        (*
 CT_braid n [] : CTerm S (n ++ []) ([] ++ n) = CTerm S (n ++ []) n.
 Cast the source n ++ [] → n. 

 --------
 CT_braid n [] : CTerm S (n ++ []) ([] ++ n) = CTerm S (n ++ []) n。
 将源 n ++ [] → n。
*)
        (eq_rect (n ++ []) (fun s => CTerm S s n)
                 (CT_braid n [])
                 n
                 (app_nil_r n))
        (CT_id n).

End CTermEq.

Arguments CTE_refl  {Colour S cs ds}.
Arguments CTE_sym   {Colour S cs ds}.
Arguments CTE_trans {Colour S cs ds}.
Arguments CTE_comp_cong {Colour S cs ds es}.
Arguments CTE_tens_cong {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_id_left  {Colour S cs ds}.
Arguments CTE_id_right {Colour S cs ds}.
Arguments CTE_assoc {Colour S cs ds es fs}.
Arguments CTE_tens_id {Colour S}.
Arguments CTE_interchange {Colour S cs ds es cs' ds' es'}.
Arguments CTE_braid_invol {Colour S}.
Arguments CTE_braid_natural {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_tens_id0_left {Colour S cs ds}.
Arguments CTE_tens_id0_right {Colour S cs ds}.
Arguments CTE_tens_assoc {Colour S cs1 ds1 cs2 ds2 cs3 ds3}.
Arguments CTE_braid_hex_left {Colour S}.
Arguments CTE_braid_hex_right {Colour S}.
Arguments CTE_braid_unit_left {Colour S}.
Arguments CTE_braid_unit_right {Colour S}.

(*
   * ** Identity bookkeeping

   The strict monoidal functors built downstream on free and
   presented coloured PROPs all have comparison maps that are
   identities or tensors of identities, so their coherence squares
   reduce to the same four identity-collapsing equations.  They are
   stated here once, over an arbitrary signature, and consumed by
   [Construction/ColouredPROP/Presentation.v] (at the signature of a
   [CSMT]) and [Construction/ColouredPROP/Relabel.v] — the coloured
   mirror of the [tm_*] quartet of [Construction/PROP/TermEq.v]. 

   --------
   * ** 身份簿记

   下游在自由和呈现的彩色 PROP 上构建的严格幺半群函子，其比较映射都是恒等映射或恒等映射的张量，因此它们的相干方格简化为相同的四个恒等塌缩方程。这里在任意符号表上陈述一次，并被 [Construction/ColouredPROP/Presentation.v]（在 [CSMT] 的符号表上）和 [Construction/ColouredPROP/Relabel.v] 使用——这是 [tm_*] 四重奏中 [Construction/PROP/TermEq.v] 的彩色镜像。
*)

(*
   * An identity slides from one side of a morphism to the other. 

   --------
   * 一个恒等映射从一个态射的一边滑到另一边。
*)
Lemma ctm_id_swap {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (t : CTerm S cs ds) :
  CTermEq S (CT_comp t (CT_id cs)) (CT_comp (CT_id ds) t).
Proof.
  apply CTE_trans with t.
  - apply CTE_id_right.
  - apply CTE_sym, CTE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. / 身份的复合等于身份的张量。 *)
Lemma ctm_comp_id_tens {Colour : Type} {S : CSignature Colour}
  (m n : list Colour) :
  CTermEq S (CT_comp (CT_id (m ++ n)) (CT_id (m ++ n)))
            (CT_tens (CT_id m) (CT_id n)).
Proof.
  apply CTE_trans with (CT_id (m ++ n)).
  - apply CTE_id_left.
  - apply CTE_sym, CTE_tens_id.
Qed.

(*
   * Collapsing an identity and a tensor of identities after [t]. 

   --------
   * 在 [t] 之后，折叠一个单位矩阵和一组单位矩阵的张量。
*)
Lemma ctm_collapse_r {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S (m ++ n) p) :
  CTermEq S (CT_comp (CT_comp t (CT_id (m ++ n)))
                     (CT_tens (CT_id m) (CT_id n))) t.
Proof.
  apply CTE_trans with (CT_comp t (CT_tens (CT_id m) (CT_id n))).
  - apply CTE_comp_cong.
    + apply CTE_id_right.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp t (CT_id (m ++ n))).
    + apply CTE_comp_cong.
      * apply CTE_refl.
      * apply CTE_tens_id.
    + apply CTE_id_right.
Qed.

(*
   * Collapsing an identity and a tensor of identities before [t]. 

   --------
   * 在 [t] 之前，折叠一个恒等和一个恒等张量。
*)
Lemma ctm_collapse_l {Colour : Type} {S : CSignature Colour}
  {m n p : list Colour} (t : CTerm S p (m ++ n)) :
  CTermEq S (CT_comp (CT_comp (CT_id (m ++ n))
                              (CT_tens (CT_id m) (CT_id n))) t) t.
Proof.
  apply CTE_trans with (CT_comp (CT_tens (CT_id m) (CT_id n)) t).
  - apply CTE_comp_cong.
    + apply CTE_id_left.
    + apply CTE_refl.
  - apply CTE_trans with (CT_comp (CT_id (m ++ n)) t).
    + apply CTE_comp_cong.
      * apply CTE_tens_id.
      * apply CTE_refl.
    + apply CTE_id_left.
Qed.
