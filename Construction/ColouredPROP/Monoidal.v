Require Import Category.Lib.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * The Monoidal structure on the free coloured PROP / * * 自由有色PROP上的单体结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 This file assembles THE [Monoidal] record on [CFreeCat S]: the unit
 object is the empty colour word [[]], the tensor is the
 parallel-composition bifunctor [CFreeCat_Tensor] (concatenation on
 colour words), and the structural isomorphisms are the [CT_cast]
 isos of [Construction/ColouredPROP/Cast.v].  Every downstream
 instance on [CFreeCat S] — Braided, Symmetric, Strict, and the
 bundled coloured PROP of [Instance.v] — names this ONE record, so
 the strict/symmetric projections agree definitionally, and the
 [cprop_monoidal_coherence] field of [Construction/ColouredPROP.v]'s
 class can be discharged by [eq_refl].

 The strict-PROP right-unit and associativity axioms of
 [CTermEq] are stated in [eq_rect] transport form
 ([CTE_tens_id0_right], [CTE_tens_assoc]).  The [Monoidal] class
 instead wants naturality squares phrased through the [CT_cast]
 structural maps.  The bridge lemmas below convert between the two
 spellings by quantifying over the boundary equation and destructing
 it — which is exactly the generalisation that is unavailable once a
 fixed colour word pins the transport proof (see the right-unit note
 below, ported from the one-sorted donor's [Naturality.v]).  With
 the bridges in hand, the previously-blocked right-unitor and
 associator naturality squares are ordinary consequences of the
 [CTermEq] axioms.

 This file merges the one-sorted spine's donor pair
 [Construction/PROP/Naturality.v] + [Construction/PROP/Monoidal.v]:
 the naturality bank and the record that consumes it live together,
 the same layout compression as [Free.v] (Free + Tensor) and
 [Cast.v] (Cast + CastTensor + Structural).

 Decidability discipline (design decision D2): the boundary
 equations live on [list Colour], which has UIP only when [Colour]
 has decidable equality.  Every lemma below whose proof invokes the
 UIP layer of [Cast.v] ([CT_cast_id] / [CT_cast_irrelevant]) is
 conditional on the section decider [Cdec], carries an explicit
 [Proof using] clause naming it, and abstracts over it on section
 close.  The UIP-free majority (transport bridges, cast shifting,
 tensor fusion, the right-unit and associator naturality squares)
 needs no decidability at all.

 All proof fields of the record are supplied from standalone, named
 lemmas (the [Free.v] discipline), so no Program obligations are
 generated and successor files can reuse the very same lemmas. 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 维基百科:  https://en.wikipedia.org/wiki/Monoidal_category 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 本文件汇总了  [CFreeCat S] 上的  [Monoidal] 记录：单位对象是空色词  [[] ]，张量是并行组合双函子  [CFreeCat_Tensor] （对色词的串联），结构同构是  [CT_cast] 的  [Construction/ColouredPROP/Cast.v] 同构。每一个下游实例在  [CFreeCat S] — 编织型、对称型、严格型，以及  [Instance.v] 的捆绑彩色 PROP — 都引用这个 ONE 记录，因此严格/对称投影在定义上是一致的，并且  [Construction/ColouredPROP.v] 类的  [cprop_monoidal_coherence] 字段可以被  [eq_refl] 消解。[CTermEq] 的严格 PROP 右单位和结合律公理在 [eq_rect] 的传输形式中表述（[CTE_tens_id0_right], [CTE_tens_assoc]）。而 [Monoidal] 类则希望通过 [CT_cast] 结构映射来表述自然性方阵。下面的桥引理通过对边界方程进行量化并解构它，将这两种表述方式转换——这正是当固定颜色字固定了传输证明时无法使用的一般化（见下面的右单位注释，从单排序提供者的 [Naturality.v] 移植而来）。有了这些桥梁后，之前被阻塞的右单位子和结合器自然性方阵成为 [CTermEq] 公理的普通推论。此文件合并了单排序脊的捐赠者对
 [Construction/PROP/Naturality.v] + [Construction/PROP/Monoidal.v]：
 自然性库和使用它的记录共存，
 布局压缩与 [Free.v]（Free + Tensor）和
 [Cast.v]（Cast + CastTensor + Structural）相同。

 可判定性规范（设计决策 D2）：边界方程存在于 [list Colour] 上，
 仅当 [Colour] 具有可判定等式时才具有 UIP。下面每一个其证明调用了 
 [Cast.v]（[CT_cast_id] / [CT_cast_irrelevant]）UIP 层的引理
 都依赖于区段判定器 [Cdec]，带有明确的 [Proof using] 条款命名它，
 并在区段关闭时对其抽象。无 UIP 的主要部分（传输桥、类型转换移动、
 张量融合、右单位和结合器自然性方块）完全不需要可判定性。记录的所有证明字段都由独立的、命名的引理提供（[Free.v] 学科），因此不会生成程序义务，后续文件可以重复使用相同的引理。
*)

Section CFreeMonoidal.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(*
   * ** Transport bridges: [eq_rect] spellings vs. [CT_cast] composites

   A codomain transport is post-composition by the cast; a domain
   transport is pre-composition by the (inverted) cast.  Each proof
   destructs the boundary equation, after which both sides collapse
   to an identity law of [CTermEq].  No decidability is involved. 

   --------
   * ** 传输桥梁：[eq_rect] 拼写 vs. [CT_cast] 复合

   余域传输是通过类型转换的后合成；定义域传输是通过（反转的）类型转换的前合成。每个证明都会解构边界方程，然后两边都会简化为 [CTermEq] 的恒等律。这里不涉及可判定性。
*)

(*
   * Codomain transport equals post-composition with [CT_cast e]. 

   --------
   * 值域的传输等于与 [CT_cast e] 的后组合。
*)
Lemma ceq_rect_cod_cast {a b b' : list Colour}
  (t : CTerm S a b) (e : b = b') :
  CTermEq S (eq_rect b (fun k => CTerm S a k) t b' e)
            (CT_comp (CT_cast e) t).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_left.
Qed.

(*
   * Domain transport equals pre-composition with [CT_cast (eq_sym e)]. 

   --------
   * 域传输等于与 [CT_cast (eq_sym e)] 的预组合。
*)
Lemma ceq_rect_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a = a') :
  CTermEq S (eq_rect a (fun k => CTerm S k b) t a' e)
            (CT_comp t (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(*
   * Reverse-direction domain transport ([eq_rect_r]) equals
   pre-composition with [CT_cast e] directly. 

   --------
   * 反向域传输（[eq_rect_r]）等于直接与[CT_cast e]的前置组合。
*)
Lemma ceq_rect_r_dom_cast {a a' b : list Colour}
  (t : CTerm S a b) (e : a' = a) :
  CTermEq S (eq_rect_r (fun k => CTerm S k b) t e)
            (CT_comp t (CT_cast e)).
Proof.
  destruct e; cbn.
  apply CTE_sym, CTE_id_right.
Qed.

(*
   * Double [eq_sym] is invisible to [CT_cast].  Unlike the one-sorted
   donor (which went through UIP on [nat]), destructing the equation
   closes this by reflexivity, so the lemma is decidability-free. 

   --------
   * 双重 [eq_sym] 对 [CT_cast] 是不可见的。不同于单类捐赠者（它在 [nat] 上通过了 UIP），破坏这个等式通过自反性关闭了它，因此该引理不依赖可判定性。
*)
Lemma CT_cast_sym_sym {cs ds : list Colour} (e : cs = ds) :
  CT_cast (S := S) (eq_sym (eq_sym e)) = CT_cast e.
Proof. destruct e; reflexivity. Qed.

(*
   * ** Cast shifting: moving a cast across a [CTermEq] equation

   Solving [f ∘ cast ≈ g] for [f], and dually.  [ccast_shift_l] and
   [ccast_shift_r] are exported kit with no in-tree consumer yet: the
   from-direction naturality squares below are all derived through
   [ccast_square_flip], which flips both casts of a square at once,
   rather than through these one-sided shifts. 

   --------
   * ** 类型转换移动：在 [CTermEq] 方程中移动类型转换

   求解 [f ∘ cast ≈ g] 的 [f]，以及相反的情况。[ccast_shift_l] 和 [ccast_shift_r] 是导出的套件，目前在树内还没有使用者：下面的 from-direction 自然性平方都是通过 [ccast_square_flip] 推导的，它可以一次翻转方形中的两个类型转换，而不是通过这些单边移动。
*)

Lemma ccast_shift_l {a b c : list Colour} (e : a = b)
  (f : CTerm S b c) (g : CTerm S a c) :
  CTermEq S (CT_comp f (CT_cast e)) g ->
  CTermEq S f (CT_comp g (CT_cast (eq_sym e))).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp f (CT_id a)).
    + apply CTE_sym, CTE_id_right.
    + exact H.
  - apply CTE_sym, CTE_id_right.
Qed.

Lemma ccast_shift_r {a b c : list Colour} (e : b = c)
  (f : CTerm S a b) (g : CTerm S a c) :
  CTermEq S (CT_comp (CT_cast e) f) g ->
  CTermEq S f (CT_comp (CT_cast (eq_sym e)) g).
Proof.
  destruct e; cbn; intros H.
  apply CTE_trans with g.
  - apply CTE_trans with (CT_comp (CT_id b) f).
    + apply CTE_sym, CTE_id_left.
    + exact H.
  - apply CTE_sym, CTE_id_left.
Qed.

(*
   * Flipping a naturality square along both casts: from
   [q ∘ cast ≈ cast ∘ p] conclude [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q].
   This turns every [to]-direction structural naturality square
   into its [from]-direction companion. 

   --------
   * 沿着两个方向翻转一个自然性方格：从 [q ∘ cast ≈ cast ∘ p] 推出 [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q] 。这将每个 [to] 方向的结构自然性方格转变为其 [from] 方向的伴随方格。
*)
Lemma ccast_square_flip {a b c d : list Colour} (e1 : a = b) (e2 : c = d)
  (p : CTerm S a c) (q : CTerm S b d) :
  CTermEq S (CT_comp q (CT_cast e1)) (CT_comp (CT_cast e2) p) ->
  CTermEq S (CT_comp p (CT_cast (eq_sym e1))) (CT_comp (CT_cast (eq_sym e2)) q).
Proof.
  destruct e1, e2; cbn; intros H.
  assert (Hqp : CTermEq S q p).
  { apply CTE_trans with (CT_comp q (CT_id a)).
    - apply CTE_sym, CTE_id_right.
    - apply CTE_trans with (CT_comp (CT_id c) p).
      + exact H.
      + apply CTE_id_left. }
  apply CTE_trans with p.
  - apply CTE_id_right.
  - apply CTE_trans with q.
    + apply CTE_sym, Hqp.
    + apply CTE_sym, CTE_id_left.
Qed.

(*
   * ** Tensor fusion

   A tensor of morphisms decomposes as either sliding order of the
   two "half-identity" tensors; both composites fuse back to the
   plain tensor via the interchange law. 

   --------
   * ** 张量融合

   一个态射的张量可以分解为两个“半单位”张量的滑动顺序；两种组合都通过交换律融合回普通张量。
*)

Lemma ctens_fuse_l {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens f (CT_id d)) (CT_tens (CT_id a) g))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp f (CT_id a)) (CT_comp (CT_id d) g)).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_right.
    + apply CTE_id_left.
Qed.

Lemma ctens_fuse_r {a b c d : list Colour}
  (f : CTerm S a b) (g : CTerm S c d) :
  CTermEq S (CT_comp (CT_tens (CT_id b) g) (CT_tens f (CT_id c)))
            (CT_tens f g).
Proof.
  apply CTE_trans with (CT_tens (CT_comp (CT_id b) f) (CT_comp g (CT_id c))).
  - apply CTE_interchange.
  - apply CTE_tens_cong.
    + apply CTE_id_left.
    + apply CTE_id_right.
Qed.

(*
   * ** Left-unitor naturality in [CT_cast] form

   Goal (in [CFreeCat S]):
   g ∘ unit_left ≈ unit_left ∘ bimap id g
   expanded to [CTerm]:
   g ⊙c CT_cast (app_nil_l x) ≈ CT_cast (app_nil_l y) ⊙c (CT_id [] ⊕c g)

   [app_nil_l x : [] ++ x = x] is an OPAQUE stdlib proof of a
   DEFINITIONAL equation ([app] is left-strict, like [Nat.add]), so
   the cast does not reduce by computation; [CT_cast_id] (UIP on
   colour words, hence [Cdec]-conditional) rewrites it to the literal
   identity, after which the strict left-unit axiom
   [CTE_tens_id0_left] closes the square. 

   --------
   * ** 左单位元自然性在 [CT_cast] 形式中

   目标（在 [CFreeCat S] 中）：
   g ∘ unit_left ≈ unit_left ∘ bimap id g
   展开到 [CTerm]：
   g ⊙c CT_cast (app_nil_l x) ≈ CT_cast (app_nil_l y) ⊙c (CT_id [] ⊕c g)

   [app_nil_l x : [] ++ x = x] 是一个 OPAQUE 标准库证明，
   一个定义性方程（[app] 是左严格的，像 [Nat.add]），所以
   类型转换不会通过计算进行化简；[CT_cast_id]（在颜色字上的 UIP，因此
   条件为 [Cdec]）将其重写为字面上的恒等式，之后严格的左单位元公理
   [CTE_tens_id0_left] 关闭了该方。
*)

Lemma cleft_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_l x)))
            (CT_comp (CT_cast (app_nil_l y)) (CT_tens (CT_id []) g)).
Proof using Cdec.
  rewrite (CT_cast_id Cdec (app_nil_l x)).
  rewrite (CT_cast_id Cdec (app_nil_l y)).
  apply CTE_trans with g.
  - apply CTE_id_right.
  - apply CTE_sym.
    apply CTE_trans with (CT_tens (CT_id []) g).
    + apply CTE_id_left.
    + apply CTE_tens_id0_left.
Qed.

(*
   * The [from]-direction square [bimap id g ∘ λ⁻¹ ≈ λ⁻¹ ∘ g], obtained
   by flipping the [to]-direction square through [ccast_square_flip];
   the [Cdec] dependency is inherited from [cleft_unit_natural]. 

   --------
   * 通过沿 [ccast_square_flip] 翻转 [to] 方向的方块获得 [from] 方向的方块 [bimap id g ∘ λ⁻¹ ≈ λ⁻¹ ∘ g]；[Cdec] 依赖性继承自 [cleft_unit_natural]。
*)
Lemma cleft_unit_natural_from {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens (CT_id []) g) (CT_cast (eq_sym (app_nil_l x))))
            (CT_comp (CT_cast (eq_sym (app_nil_l y))) g).
Proof using Cdec.
  apply ccast_square_flip, cleft_unit_natural.
Qed.

(* * ** Simple corollaries of the strict-unit axioms / * ** 严格单位公理的简单推论 *)

(*
   * Tensoring an identity with [CT_id []] on the left collapses to a
   single identity term. 

   --------
   * 在左侧用 [CT_id [] 与 identity 做张量运算会简化为一个单一的 identity 项。
*)
Lemma ctens_id0_id (n : list Colour) :
  CTermEq S (CT_tens (CT_id []) (CT_id n)) (CT_id n).
Proof. apply CTE_tens_id0_left. Qed.

(*
   * Repeated tensor of [CT_id []] on the left is still [CT_id []]. 

   --------
   * 左边重复的张量 [CT_id [] ] 仍然是 [CT_id [] ]。
*)
Lemma ctens_id0_id0 :
  CTermEq S (CT_tens (CT_id []) (CT_id [])) (CT_id []).
Proof. apply CTE_tens_id0_left. Qed.

(*
   * ** Strict-PROP right-unit at the [CT_cast] level

   [CTE_tens_id0_right] states the right-unit law in [eq_rect]
   transport form.  We can extract its content as a [CT_cast]
   sandwich: pre/post-composing by appropriate casts gives a direct
   [CT_tens f (CT_id []) ↔ f]-style equation. 

   --------
   * ** 在 [CT_cast] 级别的严格 PROP 右单位

   [CTE_tens_id0_right] 以 [eq_rect] 传输形式表述了右单位律。我们可以将其内容提取为 [CT_cast] 三明治：通过适当的类型转换的前/后组合即可得到直接的 [CT_tens f (CT_id [] ) ↔ f]-风格方程。
*)

(*
 Note (ported from the one-sorted donor's [Naturality.v]): a clean
 [CT_cast]-form right-unit lemma — bridging [CTE_tens_id0_right]'s
 [eq_rect] transport form to a sandwiched [CT_cast] composition at a
 FIXED boundary — requires generalising over the right-summand
 word, which Coq cannot do while [f]'s type pins it.  This is a
 known limitation of the [CTE_tens_id0_right] axiom's [eq_rect]
 form when consumed pointwise.  For downstream use, prefer
 [CTE_tens_id0_left] (definitional case) and work with the
 right-unit case ONLY when the boundary is syntactically known — or
 go through the transport bridges above, which quantify over the
 boundary equation first and therefore CAN destruct it; that is
 precisely how [cright_unit_natural] below succeeds where the
 pointwise approach stalls.

 Like [ccast_shift_l]/[ccast_shift_r] above, the three pointwise
 lemmas that follow ([ctens_id0_right_at_0], [ctens_id0_right_at],
 [ctens_assoc_at]) are exported kit with no in-tree consumer: every
 naturality square below is derived through the transport bridges
 instead.  They are kept as the record of what the pointwise route
 does reach. 

 --------
 注意（移植自单类型捐赠者的 [Naturality.v]）：一个干净的 [CT_cast] 形式的右单位引理——将 [CTE_tens_id0_right] 的 [eq_rect] 传输形式桥接到固定边界上的 [CT_cast] 组合——需要对右加子词进行泛化，而在 [f] 的类型固定的情况下，Coq 无法做到。这是 [CTE_tens_id0_right] 公理的 [eq_rect] 形式在逐点使用时的已知限制。对于下游使用，优先考虑 [CTE_tens_id0_left]（定义性情况），并且仅在边界在语法上已知时使用右单位情况——或者通过上述传输桥接，这些桥接首先对边界方程进行量化，因此可以对其进行析构；这正是 [cright_unit_natural] 在逐点方法停滞时仍然成功的方式。像上面的 [ccast_shift_l] / [ccast_shift_r] 一样，接下来的三个逐点引理（[ctens_id0_right_at_0]、[ctens_id0_right_at]、[ctens_assoc_at]）是作为独立模块导出的，并且在树内没有使用者：下面的每一个自然性方格都是通过传输桥来推导的。它们被保留下来，作为逐点路径所能达到的记录。
*)

(*
   * ** Right-unit at the trivial boundary ([[] ++ [] = []])

   When both boundaries are empty, the transport in
   [CTE_tens_id0_right] is along [app_nil_r []], an opaque proof of
   a definitional equation; UIP on colour words (via [Cdec]) rewrites
   it to [eq_refl], after which the [eq_rect] collapses by
   computation. 

   --------
   * ** 在平凡边界处的右单元 ([[]  ++ [] = [])

   当两个边界都为空时，[CTE_tens_id0_right] 中的传输沿着 [app_nil_r [] ] 进行，这是一个定义方程的不透明证明；通过 [Cdec] 对颜色词的 UIP 重写为 [eq_refl]，之后 [eq_rect] 通过计算而坍塌。
*)

Lemma ctens_id0_right_at_0 (f : CTerm S [] []) :
  CTermEq S (CT_tens f (CT_id [])) f.
Proof using Cdec.
  pose proof (CTE_tens_id0_right f) as Hr.
  unfold eq_rect_r in Hr.
  rewrite (UIP_dec (list_eq_dec Cdec)
             (app_nil_r (@nil Colour)) eq_refl) in Hr.
  cbn in Hr.
  exact Hr.
Qed.

(*
   * ** Boundary-specialised right-unit at any concrete boundaries 

   --------
   * ** 在任何具体边界处的边界专用右单元
*)

Lemma ctens_id0_right_at {m n : list Colour} (f : CTerm S m n) :
  CTermEq S
    (eq_rect (n ++ []) (fun k => CTerm S (m ++ []) k)
             (CT_tens f (CT_id [])) n (app_nil_r n))
    (eq_rect_r (fun k => CTerm S k n) f (app_nil_r m)).
Proof. exact (CTE_tens_id0_right f). Qed.

(* * ** Tensor-associativity at any concrete boundaries / * ** 任意具体边界处的张量结合性 *)

Lemma ctens_assoc_at {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (eq_rect ((n1 ++ n2) ++ n3)
             (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
             (CT_tens (CT_tens f g) h)
             (n1 ++ (n2 ++ n3))
             (eq_sym (app_assoc n1 n2 n3)))
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
Proof. exact (CTE_tens_assoc f g h). Qed.

(*
   * ** Right-unitor naturality in [CT_cast] form

   The [to]-direction square [g ∘ ρ ≈ ρ ∘ (g ⊕c id_[])].  This is
   the statement the pointwise approach in the note above could not
   reach at pinned boundaries; here the transport bridges convert
   [CTE_tens_id0_right]'s [eq_rect] spelling wholesale, with no UIP
   involved. 

   --------
   * ** 在  [CT_cast]  形式中的右单元自然性

   这个  [to]  方向的方形  [g ∘ ρ ≈ ρ ∘ (g ⊕c id_[] )]。这是
   上述笔记中逐点方法在固定边界处无法达到的陈述；在这里，传输桥将
   [CTE_tens_id0_right] 的  [eq_rect]  拼写整体转换，不涉及 UIP。
*)

Lemma cright_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp g (CT_cast (app_nil_r x)))
            (CT_comp (CT_cast (app_nil_r y)) (CT_tens g (CT_id []))).
Proof.
  apply CTE_sym.
  apply CTE_trans with
    (eq_rect (y ++ []) (fun k => CTerm S (x ++ []) k)
             (CT_tens g (CT_id [])) y (app_nil_r y)).
  - apply CTE_sym, ceq_rect_cod_cast.
  - apply CTE_trans with (eq_rect_r (fun k => CTerm S k y) g (app_nil_r x)).
    + apply CTE_tens_id0_right.
    + apply ceq_rect_r_dom_cast.
Qed.

(*
   * The [from]-direction square [(g ⊕c id_[]) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]. 

   --------
   *  [from] 方向平方  [(g ⊕c id_[] ) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g].
*)
Lemma cfrom_right_unit_natural {x y : list Colour} (g : CTerm S x y) :
  CTermEq S (CT_comp (CT_tens g (CT_id [])) (CT_cast (eq_sym (app_nil_r x))))
            (CT_comp (CT_cast (eq_sym (app_nil_r y))) g).
Proof.
  apply ccast_square_flip, cright_unit_natural.
Qed.

(*
   * ** Associator naturality in [CT_cast] form

   The [to]-direction square
   [(f ⊕c (g ⊕c h)) ∘ α ≈ α ∘ ((f ⊕c g) ⊕c h)],
   obtained from [CTE_tens_assoc] through the transport bridges.
   Recall the stdlib orientation [app_assoc x y z :
   x ++ y ++ z = (x ++ y) ++ z], so the associator's [to] direction
   is the [eq_sym] cast (see [CFreeCat_tensor_assoc] in [Cast.v]). 

   --------
   * ** 在 [CT_cast] 形式下的结合子自然性

   通过运输桥从 [CTE_tens_assoc] 得到的 [to] 方向平方
   [(f ⊕c (g ⊕c h)) ∘ α ≈ α ∘ ((f ⊕c g) ⊕c h)] ，
   回忆一下 stdlib 方向 [app_assoc x y z :
   x ++ y ++ z = (x ++ y) ++ z]，因此结合子的 [to] 方向
   是 [eq_sym] 类型转换（见 [CFreeCat_tensor_assoc] 在 [Cast.v] 中）。
*)

Lemma cassoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens f (CT_tens g h))
             (CT_cast (eq_sym (app_assoc m1 m2 m3))))
    (CT_comp (CT_cast (eq_sym (app_assoc n1 n2 n3)))
             (CT_tens (CT_tens f g) h)).
Proof.
  apply CTE_trans with
    (eq_rect_r (fun k => CTerm S k (n1 ++ (n2 ++ n3)))
               (CT_tens f (CT_tens g h))
               (eq_sym (app_assoc m1 m2 m3))).
  - apply CTE_sym, ceq_rect_r_dom_cast.
  - apply CTE_trans with
      (eq_rect ((n1 ++ n2) ++ n3)
               (fun k => CTerm S ((m1 ++ m2) ++ m3) k)
               (CT_tens (CT_tens f g) h)
               (n1 ++ (n2 ++ n3))
               (eq_sym (app_assoc n1 n2 n3))).
    + apply CTE_sym, CTE_tens_assoc.
    + apply ceq_rect_cod_cast.
Qed.

(*
   * The [from]-direction square
   [((f ⊕c g) ⊕c h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕c (g ⊕c h))]. 

   --------
   * [from] 方向正方形
   [((f ⊕c g) ⊕c h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕c (g ⊕c h))] 。
*)
Lemma cfrom_assoc_natural {m1 n1 m2 n2 m3 n3 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) (h : CTerm S m3 n3) :
  CTermEq S
    (CT_comp (CT_tens (CT_tens f g) h) (CT_cast (app_assoc m1 m2 m3)))
    (CT_comp (CT_cast (app_assoc n1 n2 n3)) (CT_tens f (CT_tens g h))).
Proof.
  rewrite <- (CT_cast_sym_sym (app_assoc m1 m2 m3)).
  rewrite <- (CT_cast_sym_sym (app_assoc n1 n2 n3)).
  apply ccast_square_flip, cassoc_natural.
Qed.

(*
 Note on braid lemmas: the one-sorted donor's [Naturality.v] also
 re-exported [TE_braid_natural] / [TE_braid_invol] under the
 friendly names [braid_natural] / [braid_invol].  The coloured
 spine deliberately does NOT define such synonyms here:
 [Braided.v], the sole would-be consumer, works with the
 [CTE_braid_*] constructors directly, and re-exported synonyms in
 this file would shadow the donor's names for any file importing
 both spines (the one-sorted PROP files of [Construction/PROP/]
 likewise decline to import [Naturality.v]'s synonyms, for the same
 reason).  This comment records the decision. 

 --------
 关于辫子引理的说明：单类型捐赠者的 [Naturality.v] 也重新导出了 [TE_braid_natural] / [TE_braid_invol] ，并使用友好名称 [braid_natural] / [braid_invol] 。彩色主干故意没有在这里定义这些同义词：[Braided.v] ，唯一可能的使用者，直接使用 [CTE_braid_*] 构造器，而在此文件中重新导出的同义词将会覆盖捐赠者的名称，对于同时导入两个主干的任何文件（[Construction/PROP/] 的单类型 PROP 文件出于相同原因同样拒绝导入 [Naturality.v] 的同义词）。此评论记录了该决定。
*)

(*
   * ** Triangle coherence

   [ρ ⊕c id ≈ (id ⊕c λ) ∘ α] on [(x ++ []) ++ y].  Every arrow
   involved is a cast or an identity tensored with a cast, so both
   sides collapse to a single [CT_cast] via the tensor-cast fusion
   kit of [Cast.v] and [CT_cast_compose], and UIP on colour words
   (via [Cdec]) closes the gap between the two boundary proofs. 

   --------
   * ** 三角一致性

   [ρ ⊕c id ≈ (id ⊕c λ) ∘ α] 在 [(x ++ [] 上）++ y]。 每个涉及的箭头都是一个类型转换或与类型转换张量的恒等映射，因此双方通过 [Cast.v] 和 [CT_cast_compose] 的张量-类型转换融合工具都简化为单个 [CT_cast]，并且通过颜色词上的 UIP（通过 [Cdec]）封闭了两个边界证明之间的差距。
*)

Lemma cfree_triangle (x y : list Colour) :
  CTermEq S (CT_tens (CT_cast (app_nil_r x)) (CT_id y))
            (CT_comp (CT_tens (CT_id x) (CT_cast (app_nil_l y)))
                     (CT_cast (eq_sym (app_assoc x [] y)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_cast (f_equal (fun ks => ks ++ y) (app_nil_r x))).
  - apply CT_tens_cast_id_right.
  - apply CTE_sym.
    apply CTE_trans with
      (CT_comp (CT_cast (f_equal (fun ks => x ++ ks) (app_nil_l y)))
               (CT_cast (eq_sym (app_assoc x [] y)))).
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (eq_sym (app_assoc x [] y))
                           (f_equal (fun ks => x ++ ks) (app_nil_l y)))).
      * apply CT_cast_compose.
      * rewrite (CT_cast_irrelevant Cdec
                   (eq_trans (eq_sym (app_assoc x [] y))
                             (f_equal (fun ks => x ++ ks) (app_nil_l y)))
                   (f_equal (fun ks => ks ++ y) (app_nil_r x))).
        apply CTE_refl.
Qed.

(*
   * ** Pentagon coherence

   [(id ⊕c α) ∘ α ∘ (α ⊕c id) ≈ α ∘ α] on [((x ++ y) ++ z) ++ w].
   Same recipe as the triangle: collapse each tensor-with-identity
   via the tensor-cast fusion kit, fuse the compositions of casts via
   [CT_cast_compose], and close with [CT_cast_irrelevant]. 

   --------
   * ** 五边形相干性

   [(id ⊕c α) ∘ α ∘ (α ⊕c id) ≈ α ∘ α] 在 [((x ++ y) ++ z) ++ w] 上。
   与三角形的做法相同：通过张量-恒等式融合工具折叠每个张量与恒等式的组合，
   通过 [CT_cast_compose] 融合类型转换的组合，然后以 [CT_cast_irrelevant] 结束。
*)

Lemma cfree_pentagon (x y z w : list Colour) :
  CTermEq S
    (CT_comp (CT_comp (CT_tens (CT_id x)
                               (CT_cast (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_tens (CT_cast (eq_sym (app_assoc x y z))) (CT_id w)))
    (CT_comp (CT_cast (eq_sym (app_assoc x y (z ++ w))))
             (CT_cast (eq_sym (app_assoc (x ++ y) z w)))).
Proof using Cdec.
  apply CTE_trans with
    (CT_comp (CT_comp (CT_cast (f_equal (fun ks => x ++ ks)
                                        (eq_sym (app_assoc y z w))))
                      (CT_cast (eq_sym (app_assoc x (y ++ z) w))))
             (CT_cast (f_equal (fun ks => ks ++ w)
                               (eq_sym (app_assoc x y z))))).
  - apply CTE_comp_cong.
    + apply CTE_comp_cong.
      * apply CT_tens_id_cast_left.
      * apply CTE_refl.
    + apply CT_tens_cast_id_right.
  - apply CTE_trans with
      (CT_comp (CT_cast (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                  (f_equal (fun ks => x ++ ks)
                                           (eq_sym (app_assoc y z w)))))
               (CT_cast (f_equal (fun ks => ks ++ w)
                                 (eq_sym (app_assoc x y z))))).
    + apply CTE_comp_cong.
      * apply CT_cast_compose.
      * apply CTE_refl.
    + apply CTE_trans with
        (CT_cast (eq_trans (f_equal (fun ks => ks ++ w)
                                    (eq_sym (app_assoc x y z)))
                           (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                     (f_equal (fun ks => x ++ ks)
                                              (eq_sym (app_assoc y z w)))))).
      * apply CT_cast_compose.
      * apply CTE_sym.
        apply CTE_trans with
          (CT_cast (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                             (eq_sym (app_assoc x y (z ++ w))))).
        -- apply CT_cast_compose.
        -- rewrite (CT_cast_irrelevant Cdec
                      (eq_trans (eq_sym (app_assoc (x ++ y) z w))
                                (eq_sym (app_assoc x y (z ++ w))))
                      (eq_trans (f_equal (fun ks => ks ++ w)
                                         (eq_sym (app_assoc x y z)))
                                (eq_trans (eq_sym (app_assoc x (y ++ z) w))
                                          (f_equal (fun ks => x ++ ks)
                                                   (eq_sym (app_assoc y z w)))))).
           apply CTE_refl.
Qed.

(*
   * ** THE shared Monoidal record on [CFreeCat S]

   All fields explicit, no Program obligations.  The Braided,
   Symmetric, Strict, and coloured-PROP instances downstream all
   project this single record, so their agreement is definitional
   and [Instance.v] can discharge the class's coherence field with
   [eq_refl] over it. 

   --------
   * ** 在 [CFreeCat S] 上共享的 Monoidal 记录

   所有字段都是显式的，没有程序义务。下游的编织（Braided）、对称（Symmetric）、严格（Strict）和带颜色的 PROP 实例都投影此单一记录，因此它们的一致性是定义性的，并且 [Instance.v] 可以使用 [eq_refl] 来处理该类的相干字段。
*)

Program Definition CFreeCat_Monoidal : @Monoidal (CFreeCat S) := {|
  I            := ([] : list Colour);
  tensor       := CFreeCat_Tensor S;
  unit_left    := fun x => CFreeCat_unit_left S x;
  unit_right   := fun x => CFreeCat_unit_right S x;
  tensor_assoc := fun x y z => CFreeCat_tensor_assoc S x y z;
  to_unit_left_natural      := fun x y g => cleft_unit_natural g;
  from_unit_left_natural    := fun x y g => cleft_unit_natural_from g;
  to_unit_right_natural     := fun x y g => cright_unit_natural g;
  from_unit_right_natural   := fun x y g => cfrom_right_unit_natural g;
  to_tensor_assoc_natural   := fun _ _ _ _ _ _ g h i => cassoc_natural g h i;
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
                                 cfrom_assoc_natural g h i;
  triangle_identity := fun x y => cfree_triangle x y;
  pentagon_identity := fun x y z w => cfree_pentagon x y z w
|}.

End CFreeMonoidal.

Arguments CFreeCat_Monoidal {Colour} S Cdec : assert.

(*
 D2 WARNING: [CFreeCat_Monoidal S Cdec] depends on the colour
 decider [Cdec] through its UIP-conditional proof fields, so two
 DIFFERENT [Cdec] terms for the same colour type yield
 propositionally different (though pointwise-equal) [Monoidal]
 records.  Downstream files that assert definitional agreement over
 this record — in particular the [eq_refl] discharge of
 [cprop_monoidal_coherence] in [Instance.v] — require every
 instance site to fix ONE canonical [Cdec] per colour type; mixing
 deciders surfaces as an opaque unification error at exactly that
 [eq_refl].  The machine-checked Examples of [Instance.v] exist to
 catch such violations at their source. 

 --------
 D2 警告：[CFreeCat_Monoidal S Cdec] 依赖于颜色决定器 [Cdec]，通过其 UIP 条件证明字段，因此同一颜色类型的两个不同 [Cdec] 项会产生命题上不同（尽管逐点相等）的 [Monoidal] 记录。下游文件在断言对该记录的定义一致性时——尤其是在 [eq_refl] 中 [cprop_monoidal_coherence] 在 [Instance.v] 的释放——要求每个实例位置为每种颜色类型固定一个标准 [Cdec]；混合使用决定器会在恰好 [eq_refl] 处暴露为不透明的统一错误。存在经过机器检查的 [Instance.v] 示例，用于在源头捕获此类违规行为。
*)
