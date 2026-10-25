Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Naturality.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The Monoidal structure on the free PROP / * * 自由 PROP 上的幺半群结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 This file assembles THE [Monoidal] record on [FreeCat S]: the unit
 object is [0], the tensor is the parallel-composition bifunctor
 [FreeCat_Tensor] (addition on arities), and the structural
 isomorphisms are the [T_cast] isos of [Structural.v].  Every
 downstream instance on [FreeCat S] — Braided, Symmetric, Strict, and
 the bundled PROP — names this ONE record, so the strict/symmetric
 projections agree definitionally.

 The strict-PROP right-unit and associativity axioms of [TermEq] are
 stated in [eq_rect] transport form ([TE_tens_id0_right],
 [TE_tens_assoc]).  The [Monoidal] class instead wants naturality
 squares phrased through the [T_cast] structural maps.  The bridge
 lemmas below convert between the two spellings by quantifying over
 the arity equation and destructing it — which is exactly the
 generalisation that is unavailable once a fixed arity pins the
 transport proof (see the discussion at [Naturality.v]'s right-unit
 note).  With the bridges in hand, the previously-blocked right-unitor
 and associator naturality squares are ordinary consequences of the
 [TermEq] axioms.

 All proof fields of the record are supplied from standalone, named
 lemmas (the [Free.v] discipline), so no Program obligations are
 generated and successor files can reuse the very same lemmas. 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 Wikipedia:  https://en.wikipedia.org/wiki/Monoidal_category 
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 该文件汇总了  [Monoidal] 在  [FreeCat S] 上的记录：
 单位对象是  [0] ，张量是平行组合双函子
 [FreeCat_Tensor]（元数上的加法），结构同构是  [T_cast] 的 [Structural.v] 同构。每个
 在 [FreeCat S] 上的下游实例——编织、对称、严格，以及捆绑的 PROP——都引用这个唯一的记录，因此严格/对称投影在定义上是一致的。[TermEq] 的严格 PROP 右单位和结合律公理以 [eq_rect] 的传输形式陈述（[TE_tens_id0_right]，[TE_tens_assoc]）。而 [Monoidal] 类则希望通过 [T_cast] 结构映射来表述自然性图形。下面的桥梁引理通过对元数方程进行量化并分解它，在两种表述之间进行转换——这正是当固定元数固定了传输证明时无法获得的推广（见 [Naturality.v] 关于右单位的备注中的讨论）。有了这些桥梁，之前受阻的右单位和结合子自然性图形便成为 [TermEq] 公理的普通推论。记录的所有证明字段都由独立的、命名的引理提供（[Free.v] 学科），因此不会生成程序义务，后续文件可以重复使用相同的引理。
*)

Section FreeMonoidal.

Context (S : Signature).

Open Scope nat_scope.

(*
   * ** Transport bridges: [eq_rect] spellings vs. [T_cast] composites

   A codomain transport is post-composition by the cast; a domain
   transport is pre-composition by the (inverted) cast.  Each proof
   destructs the arity equation, after which both sides collapse to
   an identity law of [TermEq]. 

   --------
   * ** 传输桥：[eq_rect] 拼写与 [T_cast] 复合

   对陪域的传输是通过类型转换的后组合；对自域的传输是通过（反转的）类型转换的前组合。每个证明都会析构元数方程，然后双方都会简化为 [TermEq] 的恒等律。
*)

(*
   * Codomain transport equals post-composition with [T_cast e]. 

   --------
   * 上射空间的迁移等于与 [T_cast e] 的后复合。
*)
Lemma eq_rect_cod_cast {a b b' : nat} (e : b = b') (t : Term S a b) :
  TermEq S (eq_rect b (fun k => Term S a k) t b' e)
           (T_comp (T_cast e) t).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_left.
Qed.

(*
   * Domain transport equals pre-composition with [T_cast (eq_sym e)]. 

   --------
   * 域传输等于与 [T_cast (eq_sym e)] 的预组合。
*)
Lemma eq_rect_dom_cast {a a' b : nat} (e : a = a') (t : Term S a b) :
  TermEq S (eq_rect a (fun k => Term S k b) t a' e)
           (T_comp t (T_cast (eq_sym e))).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_right.
Qed.

(*
   * Reverse-direction domain transport ([eq_rect_r]) equals
   pre-composition with [T_cast e] directly. 

   --------
   * 反向域传输（[eq_rect_r]）等于直接与[T_cast e]的前置组合。
*)
Lemma eq_rect_r_dom_cast {a a' b : nat} (e : a' = a) (t : Term S a b) :
  TermEq S (eq_rect_r (fun k => Term S k b) t e)
           (T_comp t (T_cast e)).
Proof.
  destruct e; cbn.
  apply TE_sym, TE_id_right.
Qed.

(*
   * Double [eq_sym] is invisible to [T_cast] (UIP on [nat]). 

   --------
   * Double [eq_sym] 对 [T_cast]（在 [nat] 上的 UIP）是不可见的。
*)
Lemma T_cast_sym_sym {m n : nat} (e : m = n) :
  T_cast (S:=S) (eq_sym (eq_sym e)) = T_cast e.
Proof. apply T_cast_irrelevant. Qed.

(*
   * ** Cast shifting: moving a cast across a [TermEq] equation

   Solving [f ∘ cast ≈ g] for [f], and dually.  [cast_shift_l] and
   [cast_shift_r] are exported kit with no in-tree consumer yet: the
   from-direction naturality squares below are all derived through
   [cast_square_flip], which flips both casts of a square at once,
   rather than through these one-sided shifts. 

   --------
   * ** 类型转换移动：在 [TermEq] 方程中移动类型转换

   求解 [f ∘ cast ≈ g] 的 [f]，以及相反的情况。[cast_shift_l] 和 [cast_shift_r] 是导出的套件，目前在树内还没有使用者：下面的 from-direction 自然性平方都是通过 [cast_square_flip] 推导的，它可以一次翻转方形中的两个类型转换，而不是通过这些单侧移动。
*)

Lemma cast_shift_l {a b c : nat} (e : a = b) (f : Term S b c) (g : Term S a c) :
  TermEq S (T_comp f (T_cast e)) g ->
  TermEq S f (T_comp g (T_cast (eq_sym e))).
Proof.
  destruct e; cbn; intros H.
  apply TE_trans with g.
  - apply TE_trans with (T_comp f (T_id a)).
    + apply TE_sym, TE_id_right.
    + exact H.
  - apply TE_sym, TE_id_right.
Qed.

Lemma cast_shift_r {a b c : nat} (e : b = c) (f : Term S a b) (g : Term S a c) :
  TermEq S (T_comp (T_cast e) f) g ->
  TermEq S f (T_comp (T_cast (eq_sym e)) g).
Proof.
  destruct e; cbn; intros H.
  apply TE_trans with g.
  - apply TE_trans with (T_comp (T_id b) f).
    + apply TE_sym, TE_id_left.
    + exact H.
  - apply TE_sym, TE_id_left.
Qed.

(*
   * Flipping a naturality square along both casts: from
   [q ∘ cast ≈ cast ∘ p] conclude [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q].
   This turns every [to]-direction structural naturality square
   into its [from]-direction companion. 

   --------
   * 沿着两个方向翻转一个自然性方格：从 [q ∘ cast ≈ cast ∘ p] 推出 [p ∘ cast⁻¹ ≈ cast⁻¹ ∘ q] 。这将每个 [to] 方向的结构自然性方格转变为其 [from] 方向的伴随方格。
*)
Lemma cast_square_flip {a b c d : nat} (e1 : a = b) (e2 : c = d)
      (p : Term S a c) (q : Term S b d) :
  TermEq S (T_comp q (T_cast e1)) (T_comp (T_cast e2) p) ->
  TermEq S (T_comp p (T_cast (eq_sym e1))) (T_comp (T_cast (eq_sym e2)) q).
Proof.
  destruct e1, e2; cbn; intros H.
  assert (Hqp : TermEq S q p).
  { apply TE_trans with (T_comp q (T_id a)).
    - apply TE_sym, TE_id_right.
    - apply TE_trans with (T_comp (T_id c) p).
      + exact H.
      + apply TE_id_left. }
  apply TE_trans with p.
  - apply TE_id_right.
  - apply TE_trans with q.
    + apply TE_sym, Hqp.
    + apply TE_sym, TE_id_left.
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

Lemma tens_fuse_l {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  TermEq S (T_comp (T_tens f (T_id d)) (T_tens (T_id a) g)) (T_tens f g).
Proof.
  apply TE_trans with (T_tens (T_comp f (T_id a)) (T_comp (T_id d) g)).
  - apply TE_interchange.
  - apply TE_tens_cong.
    + apply TE_id_right.
    + apply TE_id_left.
Qed.

Lemma tens_fuse_r {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  TermEq S (T_comp (T_tens (T_id b) g) (T_tens f (T_id c))) (T_tens f g).
Proof.
  apply TE_trans with (T_tens (T_comp (T_id b) f) (T_comp g (T_id c))).
  - apply TE_interchange.
  - apply TE_tens_cong.
    + apply TE_id_left.
    + apply TE_id_right.
Qed.

(*
   * ** Right-unitor naturality in [T_cast] form

   The [to]-direction square [g ∘ ρ ≈ ρ ∘ (g ⊕ id₀)].  This is the
   statement [Naturality.v] could not derive at pinned arities; here
   the transport bridges convert [TE_tens_id0_right]'s [eq_rect]
   spelling wholesale. 

   --------
   * ** 在 [T_cast] 形式中的右单元自然性

   [to] 方向的方形 [g ∘ ρ ≈ ρ ∘ (g ⊕ id₀)] 。这是 
   陈述 [Naturality.v] 无法在固定元数下推导出；在这里
   传输桥将 [TE_tens_id0_right] 的 [eq_rect] 拼写整体转换。
*)

Lemma right_unit_natural {x y : nat} (g : Term S x y) :
  TermEq S (T_comp g (T_cast (Nat.add_0_r x)))
           (T_comp (T_cast (Nat.add_0_r y)) (T_tens g (T_id 0))).
Proof.
  apply TE_sym.
  apply TE_trans with
    (eq_rect (y + 0) (fun k => Term S (x + 0) k)
             (T_tens g (T_id 0)) y (Nat.add_0_r y)).
  - apply TE_sym, eq_rect_cod_cast.
  - apply TE_trans with (eq_rect_r (fun k => Term S k y) g (Nat.add_0_r x)).
    + apply TE_tens_id0_right.
    + apply eq_rect_r_dom_cast.
Qed.

(*
   * The [from]-direction square [(g ⊕ id₀) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]. 

   --------
   * [from]方向的正方形[(g ⊕ id₀) ∘ ρ⁻¹ ≈ ρ⁻¹ ∘ g]。
*)
Lemma right_unit_natural_from {x y : nat} (g : Term S x y) :
  TermEq S (T_comp (T_tens g (T_id 0)) (T_cast (eq_sym (Nat.add_0_r x))))
           (T_comp (T_cast (eq_sym (Nat.add_0_r y))) g).
Proof.
  apply cast_square_flip, right_unit_natural.
Qed.

(*
   * ** Associator naturality in [T_cast] form

   The [to]-direction square
   [(f ⊕ (g ⊕ h)) ∘ α ≈ α ∘ ((f ⊕ g) ⊕ h)],
   obtained from [TE_tens_assoc] through the transport bridges. 

   --------
   * ** [T_cast] 形式下的结合子自然性

   通过运输桥获得的 [TE_tens_assoc] 
   的 [to] 方向平方
   [(f ⊕ (g ⊕ h)) ∘ α ≈ α ∘ ((f ⊕ g) ⊕ h)] 。
*)

Lemma assoc_natural {m1 n1 m2 n2 m3 n3 : nat}
      (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (T_comp (T_tens f (T_tens g h)) (T_cast (eq_sym (Nat.add_assoc m1 m2 m3))))
    (T_comp (T_cast (eq_sym (Nat.add_assoc n1 n2 n3))) (T_tens (T_tens f g) h)).
Proof.
  apply TE_trans with
    (eq_rect_r (fun k => Term S k (n1 + (n2 + n3)))
               (T_tens f (T_tens g h))
               (eq_sym (Nat.add_assoc m1 m2 m3))).
  - apply TE_sym, eq_rect_r_dom_cast.
  - apply TE_trans with
      (eq_rect ((n1 + n2) + n3) (fun k => Term S ((m1 + m2) + m3) k)
               (T_tens (T_tens f g) h)
               (n1 + (n2 + n3))
               (eq_sym (Nat.add_assoc n1 n2 n3))).
    + apply TE_sym, TE_tens_assoc.
    + apply eq_rect_cod_cast.
Qed.

(*
   * The [from]-direction square
   [((f ⊕ g) ⊕ h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕ (g ⊕ h))]. 

   --------
   * [from] 方向正方形
   [((f ⊕ g) ⊕ h) ∘ α⁻¹ ≈ α⁻¹ ∘ (f ⊕ (g ⊕ h))] 。
*)
Lemma assoc_natural_from {m1 n1 m2 n2 m3 n3 : nat}
      (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (T_comp (T_tens (T_tens f g) h) (T_cast (Nat.add_assoc m1 m2 m3)))
    (T_comp (T_cast (Nat.add_assoc n1 n2 n3)) (T_tens f (T_tens g h))).
Proof.
  rewrite <- (T_cast_sym_sym (Nat.add_assoc m1 m2 m3)).
  rewrite <- (T_cast_sym_sym (Nat.add_assoc n1 n2 n3)).
  apply cast_square_flip, assoc_natural.
Qed.

(*
   * ** Triangle coherence

   [ρ ⊕ id ≈ (id ⊕ λ) ∘ α] on [(x + 0) + y].  Every arrow involved
   is a cast or an identity tensored with a cast, so both sides
   collapse to a single [T_cast] and UIP on [nat] closes the gap. 

   --------
   * ** 三角相干性

   [ρ ⊕ id ≈ (id ⊕ λ) ∘ α] 在 [(x + 0) + y] 上。涉及的每一个箭头
   都是一个转换或与转换张量的恒等，因此两边
   都会简化为一个 [T_cast]，且在 [nat] 上的 UIP 关闭了间隙。
*)

Lemma free_triangle (x y : nat) :
  TermEq S (T_tens (T_cast (Nat.add_0_r x)) (T_id y))
           (T_comp (T_tens (T_id x) (T_cast (Nat.add_0_l y)))
                   (T_cast (eq_sym (Nat.add_assoc x 0 y)))).
Proof.
  apply TE_trans with (T_cast (f_equal (fun k => k + y) (Nat.add_0_r x))).
  - apply T_tens_cast_id_right.
  - apply TE_sym.
    apply TE_trans with
      (T_comp (T_cast (f_equal (fun k => x + k) (Nat.add_0_l y)))
              (T_cast (eq_sym (Nat.add_assoc x 0 y)))).
    + apply TE_comp_cong.
      * apply T_tens_id_cast_left.
      * apply TE_refl.
    + apply TE_trans with
        (T_cast (eq_trans (eq_sym (Nat.add_assoc x 0 y))
                          (f_equal (fun k => x + k) (Nat.add_0_l y)))).
      * apply T_cast_compose.
      * rewrite (T_cast_irrelevant
                   (eq_trans (eq_sym (Nat.add_assoc x 0 y))
                             (f_equal (fun k => x + k) (Nat.add_0_l y)))
                   (f_equal (fun k => k + y) (Nat.add_0_r x))).
        apply TE_refl.
Qed.

(*
   * ** Pentagon coherence

   [(id ⊕ α) ∘ α ∘ (α ⊕ id) ≈ α ∘ α] on [((x + y) + z) + w].  Same
   recipe as the triangle: collapse each tensor-with-identity via
   [CastTensor.v], fuse the compositions of casts via
   [T_cast_compose], and close with [T_cast_irrelevant]. 

   --------
   * ** 五边形相干性

   [(id ⊕ α) ∘ α ∘ (α ⊕ id) ≈ α ∘ α] 在 [((x + y) + z) + w] 上。与三角形的做法相同：通过 [CastTensor.v] 崩塌每个带单位的张量，通过 [T_cast_compose] 融合类型转换的组合，并通过 [T_cast_irrelevant] 闭合。
*)

Lemma free_pentagon (x y z w : nat) :
  TermEq S
    (T_comp (T_comp (T_tens (T_id x) (T_cast (eq_sym (Nat.add_assoc y z w))))
                    (T_cast (eq_sym (Nat.add_assoc x (y + z) w))))
            (T_tens (T_cast (eq_sym (Nat.add_assoc x y z))) (T_id w)))
    (T_comp (T_cast (eq_sym (Nat.add_assoc x y (z + w))))
            (T_cast (eq_sym (Nat.add_assoc (x + y) z w)))).
Proof.
  apply TE_trans with
    (T_comp (T_comp (T_cast (f_equal (fun k => x + k)
                                     (eq_sym (Nat.add_assoc y z w))))
                    (T_cast (eq_sym (Nat.add_assoc x (y + z) w))))
            (T_cast (f_equal (fun k => k + w)
                             (eq_sym (Nat.add_assoc x y z))))).
  - apply TE_comp_cong.
    + apply TE_comp_cong.
      * apply T_tens_id_cast_left.
      * apply TE_refl.
    + apply T_tens_cast_id_right.
  - apply TE_trans with
      (T_comp (T_cast (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                (f_equal (fun k => x + k)
                                         (eq_sym (Nat.add_assoc y z w)))))
              (T_cast (f_equal (fun k => k + w)
                               (eq_sym (Nat.add_assoc x y z))))).
    + apply TE_comp_cong.
      * apply T_cast_compose.
      * apply TE_refl.
    + apply TE_trans with
        (T_cast (eq_trans (f_equal (fun k => k + w)
                                   (eq_sym (Nat.add_assoc x y z)))
                          (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                    (f_equal (fun k => x + k)
                                             (eq_sym (Nat.add_assoc y z w)))))).
      * apply T_cast_compose.
      * apply TE_sym.
        apply TE_trans with
          (T_cast (eq_trans (eq_sym (Nat.add_assoc (x + y) z w))
                            (eq_sym (Nat.add_assoc x y (z + w))))).
        -- apply T_cast_compose.
        -- rewrite (T_cast_irrelevant
                      (eq_trans (eq_sym (Nat.add_assoc (x + y) z w))
                                (eq_sym (Nat.add_assoc x y (z + w))))
                      (eq_trans (f_equal (fun k => k + w)
                                         (eq_sym (Nat.add_assoc x y z)))
                                (eq_trans (eq_sym (Nat.add_assoc x (y + z) w))
                                          (f_equal (fun k => x + k)
                                                   (eq_sym (Nat.add_assoc y z w)))))).
           apply TE_refl.
Qed.

(*
   * ** THE shared Monoidal record on [FreeCat S]

   All fields explicit, no Program obligations.  The Braided,
   Symmetric, Strict, and PROP instances downstream all project this
   single record, so their agreement is definitional. 

   --------
   * ** 在 [FreeCat S] 上共享的 Monoidal 记录  

   所有字段都是显式的，没有程序义务。下游的编织、对称、严格和 PROP 实例都投射这个单一记录，因此它们的一致性是定义性的。
*)

Program Definition FreeCat_Monoidal : @Monoidal (FreeCat S) := {|
  I            := 0;
  tensor       := FreeCat_Tensor S;
  unit_left    := fun x => FreeCat_unit_left S x;
  unit_right   := fun x => FreeCat_unit_right S x;
  tensor_assoc := fun x y z => FreeCat_tensor_assoc S x y z;
  to_unit_left_natural      := fun x y g => left_unit_natural S g;
  from_unit_left_natural    := fun x y g => left_unit_natural_from S g;
  to_unit_right_natural     := fun x y g => right_unit_natural g;
  from_unit_right_natural   := fun x y g => right_unit_natural_from g;
  to_tensor_assoc_natural   := fun _ _ _ _ _ _ g h i => assoc_natural g h i;
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i => assoc_natural_from g h i;
  triangle_identity := fun x y => free_triangle x y;
  pentagon_identity := fun x y z w => free_pentagon x y z w
|}.

End FreeMonoidal.

Arguments FreeCat_Monoidal S : assert.
