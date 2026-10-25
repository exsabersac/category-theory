Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.

From Coq Require Import Arith.

Generalizable All Variables.

Local Open Scope nat_scope.

(* * * Equational theory of free-PROP terms / * * 自由-PROP项的方程理论 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 The equivalence relation [TermEq] on [Term S m n] quotients the
 raw syntax of [Construction/PROP/Term.v] by the strict symmetric
 monoidal category axioms.  The quotient [Term S / TermEq] is the
 free PROP (= free strict symmetric monoidal category whose objects
 are the naturals under [+]) on the signature [S].

 In library notation, with [⊙ = T_comp], [⊕ = T_tens],
 [id = T_id], [σ = T_braid], the constructors below assert:

 - reflexivity, symmetry, transitivity (the setoid laws)
 - congruences for [T_comp] and [T_tens]
 - category laws: identity-left, identity-right, associativity
 - bifunctor (tensor) laws: identity, sequential interchange,
 functoriality
 - symmetric-monoidal coherence: braid naturality, braid
 involution, hexagon

 The strict-PROP axioms on naturals — [T_id n ⊕ T_id m ≈ T_id (n+m)],
 the addition-as-tensor strict laws — are present as primitive
 constructors of [TermEq] because the [Term] type is indexed by [nat]
 and [T_id n ⊕ T_id m] has type [Term S (n+m) (n+m)] while
 [T_id (n+m)] has the same type by definition; the equation is
 well-typed without any [eq_rect] casts.

 This file defines just the equivalence relation.  The [Setoid]
 instance and the [Category] / [PROP] structure on the quotient
 live in successor files.

 In a STRICT symmetric monoidal category the associator and unitors
 are identities, so the pentagon and triangle coherences hold on the
 nose and the only substantive coherences left are the hexagon and
 the symmetry/involution equation [σ_{n,m} ⊙ σ_{m,n} ≈ id] (cf. the
 nLab and Wikipedia pages above).  Because [nat] addition is strictly
 associative/unital only up to propositional [=], several of those
 "on the nose" equations are nonetheless stated below in [eq_rect]
 transport form. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/symmetric+monoidal+category
 维基百科：https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)

 关系等价 [TermEq] 在 [Term S m n] 上，将 [Construction/PROP/Term.v] 的原始语法按严格对称幺半范畴公理进行商化。商 [Term S / TermEq] 是签名 [S] 的自由 PROP（= 自由严格对称幺半范畴，其对象是在 [+] 下的自然数）。

 在库符号中，使用 [⊙ = T_comp]、[⊕ = T_tens]、[id = T_id]、[σ = T_braid]，以下构造函数断言：- 反身性、对称性、传递性（集合律）
 - [T_comp] 和 [T_tens] 的合同律
 - 范畴律：左身份、右身份、结合律
 - 双函子（张量）律：身份、顺序交换、函子性
 - 对称模范单律的一致性：编织自然性、编织自反性、六边形

 在自然数上的严格 PROP 公理 — [T_id n ⊕ T_id m ≈ T_id (n+m)]，
 作为张量的加法严格律 — 作为 [TermEq] 的原始构造存在，
 因为 [Term] 类型由 [nat] 索引，
 且 [T_id n ⊕ T_id m] 类型为 [Term S (n+m) (n+m)]，而 [T_id (n+m)] 根据定义具有相同类型；该方程在没有任何 [eq_rect] 强制类型转换情况下是类型正确的。此文件仅定义等价关系。商上的 [Setoid] 实例以及 [Category] / [PROP] 结构将在后续文件中出现。

 在严格对称单体范畴中，结合子和单位子是恒等式，因此五边形和三角形的相容律严格成立，唯一实质性的相容律是六边形以及对称性/自反方程 [σ_{n,m} ⊙ σ_{m,n} ≈ id]（参见上述 nLab 和维基百科页面）。由于 [nat] 加法严格结合/单位性仅在命题性 [=] 下成立，因此下面的一些“严格”方程仍以 [eq_rect] 传递形式给出。
*)

Section TermEq.

Context (S : Signature).

(*
   * Strict tensor coherence requires equating terms whose types
   involve different parenthesisations of [+] on [nat].  Because
   [nat] addition is associative ONLY up to propositional [=]
   (not definitional), we cannot state e.g. an associator
   [T_assoc : Term S ((m+n)+p) (m+(n+p))] in [Term] alone.  The
   equational theory bridges these via the strict tensor axioms
   [TE_tens_assoc] / [TE_tens_id0_left] / [TE_tens_id0_right]; in
   practice they are used as rewrite rules to bring a term into a
   canonical right-associated form on its arities. 

   --------
   * 严格张量相干性要求将类型涉及在  [+]  上的  [nat]  不同括号化的项进行等同。因为  [nat]  的加法仅在命题性  [=]  下是结合的（而不是定义性结合的），所以我们不能仅在  [Term]  中声明例如  [T_assoc : Term S ((m+n)+p) (m+(n+p))]  这种结合子。方程理论通过严格张量公理  [TE_tens_assoc] / [TE_tens_id0_left] / [TE_tens_id0_right]  将这些联系起来；在实践中，它们被用作重写规则，将一个项转化为其元数的标准右结合形式。
*)

Inductive TermEq : forall {m n}, Term S m n -> Term S m n -> Prop :=

  (** Setoid laws. / 集合等价律。 *)
  | TE_refl  : forall {m n} (t : Term S m n), TermEq t t     (* equivalence: reflexivity / 等价性：自反性 *)
  | TE_sym   : forall {m n} (s t : Term S m n),              (* equivalence: symmetry / 等价：对称 *)
               TermEq s t -> TermEq t s
  | TE_trans : forall {m n} (s t u : Term S m n),            (* equivalence: transitivity / 等价性：传递性 *)
               TermEq s t -> TermEq t u -> TermEq s u

  (** Congruence of sequential composition. / 顺序组合的一致性。 *)
  | TE_comp_cong : forall {m n p}                            (* congruence of [T_comp] / [T_comp] 的全等 *)
                          (f f' : Term S n p) (g g' : Term S m n),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_comp f g) (T_comp f' g')

  (** Congruence of parallel composition (tensor). / 并行组合（张量）的相合性。 *)
  | TE_tens_cong : forall {m1 n1 m2 n2}                      (* congruence of [T_tens] / [T_tens] 的全等性 *)
                          (f f' : Term S m1 n1) (g g' : Term S m2 n2),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_tens f g) (T_tens f' g')

  (** Category laws: id-left, id-right, associativity. / 范畴律：左单位元、右单位元、结合律。 *)
  | TE_id_left  : forall {m n} (f : Term S m n),             (* category: left identity / 类别：左身份 *)
                  TermEq (T_comp (T_id n) f) f
  | TE_id_right : forall {m n} (f : Term S m n),             (* category: right identity / 类别：右派身份 *)
                  TermEq (T_comp f (T_id m)) f
  | TE_assoc    : forall {m n p q}                           (* category: associativity of [⊙] / 类别：[⊙]的结合性 *)
                         (h : Term S p q) (g : Term S n p) (f : Term S m n),
                  TermEq (T_comp (T_comp h g) f)
                         (T_comp h (T_comp g f))

  (*
   * Bifunctor laws: identity, sequential interchange.

   [TE_tens_id]: [id_m ⊕ id_n = id_(m+n)] — typing OK because [Term]
   is [nat]-indexed and addition is the tensor on arities. 

   --------
   * 双函子律：恒等律，顺序交换律。

   [TE_tens_id] :  [id_m ⊕ id_n = id_(m+n)] — 类型检查通过，因为 [Term] 是以 [nat] 为索引的，并且加法是在元数上的张量。
*)
  | TE_tens_id : forall (m n : nat),                         (* bifunctor: tensor preserves identity / 双函子：张量保持恒等式 *)
                 TermEq (T_tens (T_id m) (T_id n)) (T_id (m + n))

  (*
   * [TE_interchange]: (f₁ ⊕ g₁) ⊙ (f₂ ⊕ g₂) ≈ (f₁ ⊙ f₂) ⊕ (g₁ ⊙ g₂)
   — the parallel/sequential interchange law. 

   --------
   *  [TE_interchange] : (f₁ ⊕ g₁) ⊙ (f₂ ⊕ g₂) ≈ (f₁ ⊙ f₂) ⊕ (g₁ ⊙ g₂)
   — 并行/顺序交换律。
*)
  | TE_interchange :                                         (* bifunctor: middle-four interchange / 双函子：中间四交换 *)
      forall {m1 n1 p1 m2 n2 p2}
             (f1 : Term S n1 p1) (g1 : Term S n2 p2)
             (f2 : Term S m1 n1) (g2 : Term S m2 n2),
        TermEq (T_comp (T_tens f1 g1) (T_tens f2 g2))
               (T_tens (T_comp f1 f2) (T_comp g1 g2))

  (*
   * Braid involution: [σ_{m,n} ⊙ σ_{n,m} ≈ id_{m+n}].  Block-braiding
   twice returns to identity. 

   --------
   * 辫子反演：[σ_{m,n} ⊙ σ_{n,m} ≈ id_{m+n}]。双重区块编织返回到单位元。
*)
  | TE_braid_invol :                                         (* symmetry: involution σ⊙σ = id / 对称：反演 σ⊙σ = id *)
      forall (m n : nat),
        TermEq (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n))

  (*
   * Braid naturality (top form):
   (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
   where f : m1 -> n1, g : m2 -> n2. 

   --------
   * 拓扑形式的编织自然性：
   (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
   其中 f : m1 -> n1, g : m2 -> n2。
*)
  | TE_braid_natural :                                       (* symmetry: braiding naturality / 对称性：编织自然性 *)
      forall {m1 n1 m2 n2}
             (f : Term S m1 n1) (g : Term S m2 n2),
        TermEq (T_comp (T_tens g f) (T_braid m1 m2))
               (T_comp (T_braid n1 n2) (T_tens f g))

  (*
   * Strict-PROP unit on tensor: tensoring with the empty term
   [T_id 0] on the LEFT is an identity operation modulo the
   definitional equation [0 + n = n].

   This axiom is the analogue of the strict-unit law in a
   [StrictMonoidal] category.  In a generic [Monoidal] category
   it would be a natural ISOMORPHISM (the left unitor), not an
   equation; PROPs are strict on the nose, so we assert it as
   an equation in [TermEq].

   We state it as commuting with arity-zero through a [T_id]
   composition wrapper, so the types line up: both sides have
   type [Term S (0 + n) n]. 

   --------
   * 张量的严格 PROP 单位：在左侧与空项 [T_id 0] 张量操作，模定义方程 [0 + n = n]，是恒等操作。

   此公理相当于 [StrictMonoidal] 范畴中的严格单位律。在一般的 [Monoidal] 范畴中，它将是一个自然同构（左单子子），而不是一个方程；PROP 是严格意义上的，因此我们在 [TermEq] 中将其作为方程断言。

   我们将其表述为与零元数通过 [T_id] 组合包封器交换，从而类型匹配：两边类型都是 [Term S (0 + n) n]。
*)
  | TE_tens_id0_left :                                       (* strict unit: left unitor λ = id / 严格单位：左单位子 λ = 恒等 *)
      forall {m n : nat} (f : Term S m n),
        TermEq (T_tens (T_id 0) f) f

  (*
   * Strict-PROP unit on the right: dually, tensoring with [T_id 0]
   on the RIGHT is identity modulo [n + 0 = n].

   Stated in transport form via [eq_rect] over the
   arity-equations.  Concretely [T_tens f (T_id 0)] has type
   [Term S (m + 0) (n + 0)]; we transport it to [Term S m n] using
   [Nat.add_0_r] on both indices, and assert the result equals [f]. 

   --------
   * 右侧的 Strict-PROP 单元：双重地，与  [T_id 0] 在右侧张量化是模  [n + 0 = n] 的同一性。

   通过 [eq_rect] 在元数方程上以传递形式陈述。具体来说，[T_tens f (T_id 0)] 的类型为 [Term S (m + 0) (n + 0)]；我们使用 [Nat.add_0_r] 对两个指标进行传递，将其传递到 [Term S m n]，并断言结果等于 [f]。
*)
  | TE_tens_id0_right :                                      (* strict unit: right unitor ρ = id / 严格幺元：右幺元ρ = 身份 *)
      forall {m n : nat} (f : Term S m n),
        TermEq (eq_rect (Nat.add n O)
                        (fun k => Term S (Nat.add m O) k)
                        (T_tens f (T_id O))
                        n
                        (Nat.add_0_r n))
               (eq_rect_r
                  (fun k => Term S k n)
                  f
                  (Nat.add_0_r m))

  (** Strict-PROP associativity of tensor. Transport form. / 张量的严格-PROP结合性。传输形式。 *)
  | TE_tens_assoc :                                          (* strict associator α = id / 严格结合子 α = id *)
      forall {m1 n1 m2 n2 m3 n3 : nat}
             (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3),
        TermEq (eq_rect (Nat.add (Nat.add n1 n2) n3)
                        (fun k => Term S (Nat.add (Nat.add m1 m2) m3) k)
                        (T_tens (T_tens f g) h)
                        (Nat.add n1 (Nat.add n2 n3))
                        (eq_sym (Nat.add_assoc n1 n2 n3)))
               (eq_rect_r
                  (fun k => Term S k (Nat.add n1 (Nat.add n2 n3)))
                  (T_tens f (T_tens g h))
                  (eq_sym (Nat.add_assoc m1 m2 m3)))

  (*
   * ** Hexagon axioms for block braids

   In a strict symmetric monoidal category the braid decomposes
   additively in either argument (Mac Lane CWM Ch.VII §7;
   Joyal–Street §2; Selinger §3.2):

   σ_{m+n,p} ≈ (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})       (hex-left)
   σ_{m,n+p} ≈ (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)       (hex-right)

   The LHS and RHS do not have matching types on the nose because
   addition on [nat] is associative only up to propositional [=],
   so both equations are stated in transport form via [eq_rect]
   against [Nat.add_assoc], analogous to [TE_tens_assoc].

   Without these, e.g. [T_braid 3 2] is not provably equal to the
   layered composite of single-wire swaps, and the [SymmetricMonoidal]
   instance on [FreeCat S] cannot discharge [hexagon_to] /
   [hexagon_from] for non-trivial arities.

   ** Minimality note (nLab/Wikipedia, symmetric_monoidal_category)

   In a SYMMETRIC (as opposed to merely braided) monoidal category
   the two hexagons are NOT independent: given the symmetry equation
   [σ_{n,m} ⊙ σ_{m,n} ≈ id] ([TE_braid_invol]) together with braid
   naturality ([TE_braid_natural]), either hexagon implies the other.
   So exactly one of [TE_braid_hex_left] / [TE_braid_hex_right] is
   logically necessary; the other is a derivable theorem we keep as a
   primitive constructor for ergonomics (the [eq_rect] transport
   bookkeeping makes the formal derivation tedious).  As with the
   unit-braid constructors below, the redundancy is sound and cannot
   make [TermEq] inconsistent (every constructor is inhabited by the
   standard permutation model).  Deriving one as a [Lemma] after the
   inductive would change only the axiom budget, not any
   [TermEq]-judgement.  See review FLAG (needs-followup). 

   --------
   * ** 块编织的六边形公理

   在严格对称单体范畴中，编织在任一参数上都是可加地分解的 (Mac Lane CWM Ch.VII §7;
   Joyal–Street §2; Selinger §3.2):

   σ_{m+n,p} ≈ (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})       (六边形-左)
   σ_{m,n+p} ≈ (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)       (六边形-右)

   左侧和右侧在类型上不是完全匹配的，因为 [nat] 上的加法仅在命题 [=] 下满足结合律，
   因此这两个方程都是通过 [eq_rect] 对 [Nat.add_assoc] 进行传递形式的表述，类似于 [TE_tens_assoc]。

   没有这些，例如 [T_braid 3 2] 无法被证明等于单线交换的分层复合，而 [SymmetricMonoidal] 在 [FreeCat S] 上的实例
   也无法对非平凡算子释放 [hexagon_to] / [hexagon_from]。** 最小性注释（nLab/维基百科，对称单模范畴）在对称（而不仅仅是编织）单体范畴中，这两个六边形并不是独立的：给定对称方程 [σ_{n,m} ⊙ σ_{m,n} ≈ id]（[TE_braid_invol]）以及编织自然性（[TE_braid_natural]），任一六边形都可以推出另一六边形。因此，[TE_braid_hex_left]/[TE_braid_hex_right] 中恰好有一个在逻辑上是必要的；另一个是一个可推导的定理，我们保留它作为原始构造器以方便使用（[eq_rect] 的传输记录使正式推导变得繁琐）。与下面的单位-编织构造器类似，这种冗余是合理的，不会导致 [TermEq] 不一致（每个构造器都由标准置换模型填充）。在归纳之后将其中一个作为 [Lemma] 来推导，只会改变公理预算，而不会影响任何 [TermEq] 判定。参见评论 FLAG（需要后续跟进）。
*)

  | TE_braid_hex_left :                                       (* symmetry: hexagon (left argument) / 对称性：六边形（左边参数） *)
      forall (m n p : nat),
        TermEq
          (*
 LHS: σ_{m+n,p} with source cast (m+n)+p → m+(n+p). 

 --------
 左边: σ_{m+n,p}，源类型转换 (m+n)+p → m+(n+p)。
*)
          (eq_rect ((m + n) + p)
                   (fun s => Term S s (p + (m + n)))
                   (T_braid (m + n) p)
                   (m + (n + p))
                   (eq_sym (Nat.add_assoc m n p)))
          (*
 RHS: (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})
 — the outer term needs both source and target casts to
 reach types Term S (m+(p+n)) (p+(m+n)); the inner term
 already has type Term S (m+(n+p)) (m+(p+n)). 

 --------
 右边: (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})
 — 外层项需要对源和目标进行类型转换，
 以达到类型 Term S (m+(p+n)) (p+(m+n)); 内层项
 已经具有类型 Term S (m+(n+p)) (m+(p+n))。
*)
          (T_comp
             (eq_rect ((p + m) + n)
                      (fun t => Term S (m + (p + n)) t)
                      (eq_rect ((m + p) + n)
                               (fun s => Term S s ((p + m) + n))
                               (T_tens (T_braid m p) (T_id n))
                               (m + (p + n))
                               (eq_sym (Nat.add_assoc m p n)))
                      (p + (m + n))
                      (eq_sym (Nat.add_assoc p m n)))
             (T_tens (T_id m) (T_braid n p)))

  | TE_braid_hex_right :                                      (* symmetry: hexagon (right argument) / 对称性：六边形（右参数） *)
      forall (m n p : nat),
        TermEq
          (*
 LHS: σ_{m,n+p} with target cast (n+p)+m → n+(p+m). 

 --------
 左边: σ_{m,n+p} 的目标类型转换 (n+p)+m → n+(p+m)。
*)
          (eq_rect ((n + p) + m)
                   (fun t => Term S (m + (n + p)) t)
                   (T_braid m (n + p))
                   (n + (p + m))
                   (eq_sym (Nat.add_assoc n p m)))
          (*
 RHS: (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)
 — outer source: n+(m+p) → (n+m)+p (Nat.add_assoc forward);
 inner source: (m+n)+p → m+(n+p) (eq_sym). 

 --------
 右侧: (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)
 — 外部来源: n+(m+p) → (n+m)+p (Nat.add_assoc 前向);
 内部来源: (m+n)+p → m+(n+p) (eq_sym).
*)
          (T_comp
             (eq_rect (n + (m + p))
                      (fun s => Term S s (n + (p + m)))
                      (T_tens (T_id n) (T_braid m p))
                      ((n + m) + p)
                      (Nat.add_assoc n m p))
             (eq_rect ((m + n) + p)
                      (fun s => Term S s ((n + m) + p))
                      (T_tens (T_braid m n) (T_id p))
                      (m + (n + p))
                      (eq_sym (Nat.add_assoc m n p))))

  (*
   * ** Unit-braid coherence

   In any symmetric monoidal category the braid involving the unit
   object collapses to the unitor: [σ_{I,X} = λ_X ∘ ρ_X^{-1}].  In
   the strict-PROP setting on [nat], this becomes
   [T_braid 0 n ≈ T_id n] and [T_braid n 0 ≈ T_id n] modulo the
   arity equation [n + 0 = n] (which is propositional, not
   definitional — [Nat.add] is left-strict only).

   ** Minimality note (Joyal–Street §2 Prop. 2.1; Mac Lane CWM VII §1)

   In the literature these unit-braid equations are NOT independent
   axioms — they are theorems of [hexagon + naturality + invol +
   triangle].  Sketch of the derivation in our setting (we omit the
   formal proof's eq_rect bookkeeping for brevity):

   1. Instantiate [TE_braid_hex_right] at [m := n], [n := 0],
   [p := 0]:
   σ_{n, 0+0} ≈ (id_0 ⊕ σ_{n,0}) ⊙ (σ_{n,0} ⊕ id_0).
   2. Collapse the [id_0 ⊕ _] and [_ ⊕ id_0] tensors via
   [TE_tens_id0_left] / [TE_tens_id0_right]:
   σ_{n, 0} ≈ σ_{n, 0} ⊙ σ_{n, 0}                   (idempotency)
   3. By [TE_braid_invol]: [σ_{0, n} ⊙ σ_{n, 0} ≈ id_{n+0} ≈ id_n].
   Compose both sides of (2) with [σ_{0, n}] on the left:
   σ_{0, n} ⊙ σ_{n, 0} ≈ σ_{0, n} ⊙ (σ_{n, 0} ⊙ σ_{n, 0}).
   id_n        ≈  σ_{0, n} ⊙ σ_{n, 0} ⊙ σ_{n, 0}      (assoc)
   id_n        ≈  id_n ⊙ σ_{n, 0}                     (involution)
   id_n        ≈  σ_{n, 0}                            (id-left)
   4. The dual [σ_{0, n} ≈ id_n] follows by applying [TE_braid_invol]
   once more to step (3)'s conclusion.

   We keep them as primitive constructors here for ergonomics: the
   formal derivation requires substantial [eq_rect] bookkeeping
   across hexagon-, strict-unit-, and involution-form transports
   (the unit-arity cases of those transports do not reduce
   definitionally in [Nat.add]), and the downstream [SymmetricMonoidal]
   instance on [FreeCat S] consumes the strict form directly.

   Adding sound redundant constructors is harmless (it cannot make
   [TermEq] inconsistent — every constructor remains inhabited by
   the standard permutation model).  A future refactor that
   derives these as [Lemma]s after the inductive declaration would
   not change any [TermEq]-judgements, only the axiom budget. 

   --------
   * ** 单位编织一致性

   在任何对称单量范畴中，涉及单位对象的编织会简化为单位器：[σ_{I,X} = λ_X ∘ ρ_X^{-1}]。在严格 PROP 环境下的[nat]中，这变为[T_braid 0 n ≈ T_id n]和[T_braid n 0 ≈ T_id n]，模算子公式[n + 0 = n]（这是命题性的，而非定义性的——[Nat.add]仅是左严格的）。

   ** 最小性备注（Joyal–Street §2 命题 2.1；Mac Lane CWM VII §1）

   文献中这些单位编织方程不是独立公理——它们是[六角形 + 自然性 + 逆 + 三角形]的定理。我们的环境中的推导概要如下（为了简洁，我们省略了形式证明中的eq_rect记账）：1. 在 [m := n]、[n := 0]、[p := 0] 处实例化 [TE_braid_hex_right] ：
   σ_{n, 0+0} ≈ (id_0 ⊕ σ_{n,0}) ⊙ (σ_{n,0} ⊕ id_0)。
   2. 通过 [TE_tens_id0_left] / [TE_tens_id0_right] 崩塌 [id_0 ⊕ _] 和 [_ ⊕ id_0] 张量：
   σ_{n, 0} ≈ σ_{n, 0} ⊙ σ_{n, 0}（幂等性）
   3. 通过 [TE_braid_invol] ：[σ_{0, n} ⊙ σ_{n, 0} ≈ id_{n+0} ≈ id_n]。
   在左侧用 [σ_{0, n}] 组合步骤 (2) 的两边：
   σ_{0, n} ⊙ σ_{n, 0} ≈ σ_{0, n} ⊙ (σ_{n, 0} ⊙ σ_{n, 0})。
   id_n ≈ σ_{0, n} ⊙ σ_{n, 0} ⊙ σ_{n, 0}（结合律）
   id_n ≈ id_n ⊙ σ_{n, 0}（自反性）
   id_n ≈ σ_{n, 0}（左单位）
   4. 对偶 [σ_{0, n} ≈ id_n] 通过再次应用 [TE_braid_invol] 到步骤 (3) 的结论得到。我们在这里保持它们作为原始构造函数以便于使用：形式化推导需要在六边形、严格单位和反演形式的传输之间进行大量的 [eq_rect] 记录（这些传输的单位元数情况在 [Nat.add] 中不会定义性地化简），而下游的 [SymmetricMonoidal] 实例在 [FreeCat S] 上直接使用严格形式。

   添加合理的冗余构造函数是无害的（它不会使 [TermEq] 出现不一致——每个构造函数仍然由标准置换模型所填充）。将来若进行重构，在归纳声明之后将它们作为 [Lemma] 推导出来，也不会改变任何 [TermEq] 判断，只会改变公理预算。
*)

  | TE_braid_unit_left :                                      (* symmetry: unit braid σ_{0,n} = id (derivable) / 对称性：单位编织 σ_{0,n} = id（可推导） *)
      forall (n : nat),
        TermEq
          (*
 T_braid 0 n : Term S (0+n) (n+0) = Term S n (n+0).
 Cast the target n+0 → n. 

 --------
 T_braid 0 n : Term S (0+n) (n+0) = Term S n (n+0)。
 将目标 n+0 → n。
*)
          (eq_rect (n + 0) (fun t => Term S n t)
                   (T_braid 0 n)
                   n
                   (Nat.add_0_r n))
          (T_id n)

  | TE_braid_unit_right :                                     (* symmetry: unit braid σ_{n,0} = id (derivable) / 对称性：单位编织 σ_{n,0} = id（可推导） *)
      forall (n : nat),
        TermEq
          (*
 T_braid n 0 : Term S (n+0) (0+n) = Term S (n+0) n.
 Cast the source n+0 → n. 

 --------
 T_braid n 0 ：项 S (n+0) (0+n) = 项 S (n+0) n。
 将源 n+0 → n。
*)
          (eq_rect (n + 0) (fun s => Term S s n)
                   (T_braid n 0)
                   n
                   (Nat.add_0_r n))
          (T_id n).

End TermEq.

Arguments TE_refl  {S m n}.
Arguments TE_sym   {S m n}.
Arguments TE_trans {S m n}.
Arguments TE_comp_cong {S m n p}.
Arguments TE_tens_cong {S m1 n1 m2 n2}.
Arguments TE_id_left  {S m n}.
Arguments TE_id_right {S m n}.
Arguments TE_assoc {S m n p q}.
Arguments TE_tens_id {S}.
Arguments TE_interchange {S m1 n1 p1 m2 n2 p2}.
Arguments TE_braid_invol {S}.
Arguments TE_braid_natural {S m1 n1 m2 n2}.
Arguments TE_tens_id0_left {S m n}.
Arguments TE_tens_id0_right {S m n}.
Arguments TE_tens_assoc {S m1 n1 m2 n2 m3 n3}.
Arguments TE_braid_hex_left {S}.
Arguments TE_braid_hex_right {S}.
Arguments TE_braid_unit_left {S}.
Arguments TE_braid_unit_right {S}.

(*
   * ** Identity bookkeeping

   The strict monoidal functors built downstream on free and
   presented PROPs all have comparison maps that are identities or
   tensors of identities, so their coherence squares reduce to the
   same four identity-collapsing equations.  They are stated here
   once, over an arbitrary signature, and consumed by
   [Construction/PROP/Presentation.v] (at the signature of an [SMT])
   and [Construction/PROP/Tietze.v]. 

   --------
   * ** 身份簿记

   在自由和呈现的 PROP 上下游构建的严格幺半群函子，其比较映射都是恒等映射或恒等映射的张量，因此它们的相干方格约化为相同的四个恒等折叠方程。这里在任意符号上陈述一次，并由 [Construction/PROP/Presentation.v]（在 [SMT] 的符号上）和 [Construction/PROP/Tietze.v] 使用。
*)

(*
   * An identity slides from one side of a morphism to the other. 

   --------
   * 一个恒等映射从一个态射的一边滑到另一边。
*)
Lemma tm_id_swap {S : Signature} {m n : nat} (t : Term S m n) :
  TermEq S (T_comp t (T_id m)) (T_comp (T_id n) t).
Proof.
  apply TE_trans with t.
  - apply TE_id_right.
  - apply TE_sym, TE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. / 身份的复合等于身份的张量。 *)
Lemma tm_comp_id_tens {S : Signature} (m n : nat) :
  TermEq S (T_comp (T_id (m + n)) (T_id (m + n))) (T_tens (T_id m) (T_id n)).
Proof.
  apply TE_trans with (T_id (m + n)).
  - apply TE_id_left.
  - apply TE_sym, TE_tens_id.
Qed.

(*
   * Collapsing an identity and a tensor of identities after [t]. 

   --------
   * 在 [t] 之后，折叠一个单位矩阵和一组单位矩阵的张量。
*)
Lemma tm_collapse_r {S : Signature} {m n p : nat} (t : Term S (m + n) p) :
  TermEq S (T_comp (T_comp t (T_id (m + n))) (T_tens (T_id m) (T_id n))) t.
Proof.
  apply TE_trans with (T_comp t (T_tens (T_id m) (T_id n))).
  - apply TE_comp_cong.
    + apply TE_id_right.
    + apply TE_refl.
  - apply TE_trans with (T_comp t (T_id (m + n))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_tens_id.
    + apply TE_id_right.
Qed.

(*
   * Collapsing an identity and a tensor of identities before [t]. 

   --------
   * 在 [t] 之前，折叠一个恒等和一个恒等张量。
*)
Lemma tm_collapse_l {S : Signature} {m n p : nat} (t : Term S p (m + n)) :
  TermEq S (T_comp (T_comp (T_id (m + n)) (T_tens (T_id m) (T_id n))) t) t.
Proof.
  apply TE_trans with (T_comp (T_tens (T_id m) (T_id n)) t).
  - apply TE_comp_cong.
    + apply TE_id_left.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_id (m + n)) t).
    + apply TE_comp_cong.
      * apply TE_tens_id.
      * apply TE_refl.
    + apply TE_id_left.
Qed.

(*
   * ** Generic substitution

   [T_subst sub] replaces every generator leaf [T_gen s] by the term
   [sub _ _ s] and leaves the structural constructors untouched.  It
   is the common skeleton of the term homomorphisms defined
   downstream in [Construction/PROP/Tietze.v] — relabelling along a
   signature morphism ([T_map], whose generator action is [T_gen]
   after the morphism) and the definitional-extension retraction
   ([ext_retract], whose generator action substitutes the defining
   word) — so the nineteen-case preservation induction
   [T_subst_TermEq] below is proved ONCE and instantiated there. 

   --------
   * ** 泛化替换

   [T_subst sub] 用术语 [sub _ _ s] 替换每个生成器叶子 [T_gen s]，并保持结构构造器不变。它是下游在 [Construction/PROP/Tietze.v] 中定义的项同态的通用骨架——沿签名同态重标记（[T_map]，其生成器操作在同态之后为 [T_gen]）以及定义扩展的收缩（[ext_retract]，其生成器操作替换定义词）——因此下面的十九种情况保持归纳 [T_subst_TermEq] 只需证明一次并在此处实例化。
*)

Fixpoint T_subst {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} (t : Term S m n) : Term T m n :=
  match t in Term _ m' n' return Term T m' n' with
  | T_id k      => T_id k
  | T_braid a b => T_braid a b
  | T_comp g f  => T_comp (T_subst sub g) (T_subst sub f)
  | T_tens f g  => T_tens (T_subst sub f) (T_subst sub g)
  | T_gen s     => sub _ _ s
  end.

(*
   * *** Transport seams

   The strict-PROP axioms of [TermEq] carry their arity mismatches as
   [eq_rect] transports; [T_subst] commutes with each transport shape
   by Leibniz equality (destruct the arity equation). 

   --------
   * *** 传输接缝

   [TermEq] 的严格 PROP 公理将它们的元数不匹配作为 [eq_rect] 传输；[T_subst] 通过莱布尼茨等式（拆解元数方程）与每个传输形状交换。
*)

Lemma T_subst_eq_rect_cod {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a b b' : nat} (e : b = b') (t : Term S a b) :
  T_subst sub (eq_rect b (fun k : nat => Term S a k) t b' e)
  = eq_rect b (fun k : nat => Term T a k) (T_subst sub t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a = a') (t : Term S a b) :
  T_subst sub (eq_rect a (fun k : nat => Term S k b) t a' e)
  = eq_rect a (fun k : nat => Term T k b) (T_subst sub t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_r_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a' = a) (t : Term S a b) :
  T_subst sub (eq_rect_r (fun k : nat => Term S k b) t e)
  = eq_rect_r (fun k : nat => Term T k b) (T_subst sub t) e.
Proof. destruct e; reflexivity. Qed.

(*
   * *** Preservation of the free equations

   [T_subst sub] carries every free equation of [TermEq S] to the
   corresponding free equation of [TermEq T], for ANY generator
   action [sub].  The induction covers all nineteen constructors:
   the thirteen constructor-to-constructor cases reduce by
   computation, and the six transport-form cases first move
   [T_subst] across the [eq_rect] seams by the Leibniz bridges
   above, then close with the same primitive constructor. 

   --------
   * *** 自由方程的保持

   [T_subst sub] 将 [TermEq S] 的每一个自由方程带到 [TermEq T] 的对应自由方程，对于任何生成元作用 [sub] 都成立。归纳覆盖了所有十九个构造子：十三个构造子到构造子的情况通过计算归约，六个传输形式的情况首先通过上述 Leibniz 桥将 [T_subst] 移动到 [eq_rect] 接缝处，然后用相同的原始构造子闭合。
*)

Lemma T_subst_TermEq {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} {s t : Term S m n} :
  TermEq S s t -> TermEq T (T_subst sub s) (T_subst sub t).
Proof.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply TE_refl.
  - (* TE_sym *)
    exact (TE_sym _ _ IHHT).
  - (* TE_trans *)
    exact (TE_trans _ _ _ IHHT1 IHHT2).
  - (* TE_comp_cong / TE_复合_会聚 *)
    cbn [T_subst]; apply TE_comp_cong; assumption.
  - (* TE_tens_cong / TE_张力_从 *)
    cbn [T_subst]; apply TE_tens_cong; assumption.
  - (* TE_id_left / TE_id_左 *)
    cbn [T_subst]; apply TE_id_left.
  - (* TE_id_right / TE_id_右 *)
    cbn [T_subst]; apply TE_id_right.
  - (* TE_assoc *)
    cbn [T_subst]; apply TE_assoc.
  - (* TE_tens_id / TE_张力_编号 *)
    cbn [T_subst]; apply TE_tens_id.
  - (* TE_interchange / TE_交换 *)
    cbn [T_subst]; apply TE_interchange.
  - (* TE_braid_invol / TE_编织_卷入 *)
    cbn [T_subst]; apply TE_braid_invol.
  - (* TE_braid_natural / TE_天然编织 *)
    cbn [T_subst]; apply TE_braid_natural.
  - (* TE_tens_id0_left / TE_张力_id0_左 *)
    cbn [T_subst]; apply TE_tens_id0_left.
  - (* TE_tens_id0_right / TE_张力_id0_右 *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_id0_right.
  - (* TE_tens_assoc / TE_张力_关联 *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_assoc.
  - (* TE_braid_hex_left / TE_编织_六边形_左 *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_left.
  - (* TE_braid_hex_right / TE_右编织六边形 *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_right.
  - (* TE_braid_unit_left / TE_编织单元_左 *)
    rewrite T_subst_eq_rect_cod.
    cbn [T_subst]; apply TE_braid_unit_left.
  - (* TE_braid_unit_right / TE_右编织单元 *)
    rewrite T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_unit_right.
Qed.
