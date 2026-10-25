Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.FreeMonoidal.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   * * Normalisation into a monoidal category

   The engine room of Mac Lane's Theorem 1 [maclane:VII.2:thm1].  Fix a
   monoidal category [B] and an object [b].  Substituting [b] into a binary
   word gives one bracketing of an iterated tensor; this file builds, for
   every word, a canonical isomorphism [can w] from that bracketing to the
   RIGHT-NORMALISED form [nf (wlen w) I], and proves the two equations about
   the normaliser that the freeness theorem spends coherence on:

   - [J_assoc]      — associativity of the join; this is the PENTAGON.
   - [J_right_unit] — the join against an empty tail is rho; this is the
   TRIANGLE together with Kelly's [unit_identity].

   Every other proof in the development is cast bookkeeping or naturality.

   PROOF ROUTE, disclosed.  Mac Lane proves Theorem 1 by a rank induction on
   a graph of basic arrows (CWM §VII.2, pp. 166-168) — a confluence argument.
   We instead take the strictification / normalisation-by-evaluation route
   (Beylin-Dybjer 1996, "Extracting a proof of coherence for monoidal
   categories from a proof of normalization for monoids"; Schauenburg 2001,
   "Turning monoidal categories into strict ones"): normalise every word to
   the right-normalised form and observe that the normaliser is canonically
   isomorphic to the identity.  The STATEMENT proved downstream is Mac
   Lane's; only the route differs.

   DESIGN NOTE, load-bearing.  [J m n X] is given the codomain [nf (m + n) X]
   rather than [nf m (nf n X)].  With that choice every branch of every
   [Fixpoint] below typechecks BY CONVERSION and no transport appears in the
   definitions at all: [nf (0 + n) X] reduces to [nf n X], and
   [nf (S k + n) X] to [b ⨂ nf (k + n) X].  The only transports in the whole
   development are then of the single shape

   id_cast (f_equal (fun i => nf i X) e)      with   e : m = n   in nat,

   and [nat] has decidable equality, so uniqueness of identity proofs for
   these casts is Hedberg's theorem ([UIP_dec Nat.eq_dec]) — axiom-free.
   This is why the file needs no [ObjDecEq] hypothesis on [B]: the casts
   never live at an arbitrary object of [B], only on the [nf] family indexed
   by [nat].

   The [id_cast]/[hom_cast] kit is Construction/Quotient.v. 

   --------
   * * 归一化到幺半群范畴

   Mac Lane 定理 1 的引擎房 [maclane:VII.2:thm1]。固定一个幺半群范畴 [B] 和一个对象 [b]。将 [b] 代入一个二元字得到迭代张量的一种括号方式；该文件为每个字构建了一个从该括号方式到右归一化形式 [nf (wlen w) I] 的典范同构 [can w]，并证明了与归一化器相关的两个方程，这是自由性定理所关注的一致性问题：

   -  [J_assoc]  — 连接的结合律；这是五边形。
   -  [J_right_unit]  — 当尾部为空时连接等于 rho；这是三角形以及 Kelly 的 [unit_identity]。

   其他的发展中的证明都是账务处理或自然性证明。证明路线，已披露。Mac Lane 通过对基本箭头图的秩归纳证明定理 1（CWM §VII.2，第 166-168 页）——这是一个汇合性论证。我们则采用严格化 / 通过求值归一化的路线（Beylin-Dybjer 1996，“从半群的归一化证明中提取单体范畴的相干性证明”；Schauenburg 2001，“将单体范畴转化为严格范畴”）：将每个词归一化为右归一化形式，并观察归一化器与恒等函子在概念上同构。下游证明的陈述是 Mac Lane 的；唯一路线不同。设计说明，可承重。[J m n X] 被赋予了值域 [nf (m + n) X]，而不是 [nf m (nf n X)]。通过这种选择，下面每个 [Fixpoint] 的每个分支都通过转换进行类型检查，并且在定义中根本没有出现传输：[nf (0 + n) X] 会简化为 [nf n X]，[nf (S k + n) X] 会简化为 [b ⨂ nf (k + n) X]。整个开发中唯一的传输形式是

   id_cast (f_equal (fun i => nf i X) e)      其中 e : m = n 在自然数中，

   并且 [nat] 具有可判定的等式，因此这些转换的身份唯一性证明是 Hedberg 定理（[UIP_dec Nat.eq_dec]）——无公理。这就是为什么文件不需要在 [B] 上有 [ObjDecEq] 假设：这些转换从不在 [B] 的任意对象上生效，只在由 [nat] 索引的 [nf] 系列上生效。[id_cast] / [hom_cast] 套件是 Construction/Quotient.v。
*)

Section Normal.

Context {B : Category}.
Context `{MB : @Monoidal B}.
Context (b : B).

(* * ** The right-normalised tensor and the join / * ** 右正规化张量和连接 *)

(*
 [nf n X] is b ⨂ (b ⨂ (… ⨂ X)), n copies of b with tail X. 

 --------
 [nf n X] 是 b ⨂ (b ⨂ (… ⨂ X))，b 的 n 个副本与尾部 X。
*)
Fixpoint nf (n : nat) (X : B) : B :=
  match n with
  | O   => X
  | S m => b ⨂ nf m X
  end.

(*
 The join: appending under the tail parameter.  See the header design note
 for why the codomain is [nf (m + n) X]. 

 --------
 连接：在尾参数下追加。请参阅头文件设计说明，了解为什么值域是 [nf (m + n) X]。
*)
Fixpoint J (m n : nat) (X : B) : (nf m I ⨂ nf n X) ≅ nf (m + n) X :=
  match m with
  | O   => unit_left
  | S k => tensor_iso iso_id (J k n X) ⊙ tensor_assoc
  end.

(*
 Mac Lane's "substitute b into all blanks" — (e0)_b = e, (-)_b = b,
 (v □ w)_b = v_b ⨂ w_b.  Strict on the nose, by construction. 

 --------
 Mac Lane 的“将 b 代入所有空白”——(e0)_b = e, (-)_b = b, (v □ w)_b = v_b ⨂ w_b。严格来说，按照构造方法完全正确。
*)
Fixpoint subst (w : Word) : B :=
  match w with
  | WE     => I
  | WI     => b
  | WT v u => subst v ⨂ subst u
  end.

(*
 The normalisation isomorphism.  The [WT] branch IS the multiplicativity of
 the normaliser, definitionally — there is no separate lemma to prove. 

 --------
 归一化同构。[WT] 分支，本质上就是正规子群的乘法性——定义上如此——没有需要单独证明的引理。
*)
Fixpoint can (w : Word) : subst w ≅ nf (wlen w) I :=
  match w with
  | WE     => iso_id
  | WI     => iso_sym unit_right
  | WT v u => J (wlen v) (wlen u) I ⊙ tensor_iso (can v) (can u)
  end.

(*
   * ** The cast kit

   All transports are [id_cast (f_equal (fun i => nf i X) e)] with [e] a nat
   equality.  Discipline for everything downstream: NEVER [destruct] a proof
   of [wlen v = wlen w] — its endpoints are not variables and [destruct]
   refuses; route through these lemmas, which quantify over bare naturals. 

   --------
   * ** 铸造工具包

   所有传输都是 [id_cast (f_equal (fun i => nf i X) e)]，并且 [e] 为自然数相等。对下游的一切操作的规范：绝不 [destruct] 一个 [wlen v = wlen w] 的证明——其端点不是变量且 [destruct] 拒绝；通过这些引理进行路由，这些引理对裸自然数进行量化。
*)

Lemma nf_cast_irr {m n : nat} {X : B} (e e' : m = n) :
  id_cast (f_equal (fun i => nf i X) e)
    ≈ id_cast (f_equal (fun i => nf i X) e').
Proof. now rewrite (UIP_dec Nat.eq_dec e e'). Qed.

Lemma nf_cast_loop {m : nat} {X : B} (e : m = m) :
  id_cast (f_equal (fun i => nf i X) e) ≈ id.
Proof. rewrite (UIP_dec Nat.eq_dec e eq_refl); reflexivity. Qed.

Lemma nf_cast_trans {m n k : nat} {X : B} (e1 : m = n) (e2 : n = k) :
  id_cast (f_equal (fun i => nf i X) e2)
    ∘ id_cast (f_equal (fun i => nf i X) e1)
    ≈ id_cast (f_equal (fun i => nf i X) (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  change (id[nf m X] ∘ id[nf m X] ≈ id[nf m X]).
  now rewrite id_left.
Qed.

Lemma nf_cast_succ {m n : nat} {X : B} (e : m = n) :
  id_cast (f_equal (fun i => nf i X) (f_equal S e))
    ≈ bimap id[b] (id_cast (f_equal (fun i => nf i X) e)).
Proof.
  destruct e.
  change (id[(b ⨂ nf m X)%object] ≈ bimap id[b] id[nf m X]).
  symmetry; apply bimap_id_id.
Qed.

(* Casting commutes with the join. / 类型转换与连接运算可交换。 *)
Lemma J_cast {m m' n n' : nat} {X : B} (p : m = m') (q : n = n') :
  id_cast (f_equal (fun i => nf i X) (f_equal2 Nat.add p q)) ∘ to (J m n X)
    ≈ to (J m' n' X)
        ∘ bimap (id_cast (f_equal (fun i => nf i I) p))
                (id_cast (f_equal (fun i => nf i X) q)).
Proof.
  (*
 [f_equal2] is opaque (Qed) in the stdlib, so after [destruct] its result
 does not reduce to [eq_refl] — but it is still a LOOP equality, which
 [nf_cast_loop] handles through nat-UIP. 

 --------
 [f_equal2] 在标准库中是不可约的（Qed），所以在 [destruct] 之后，其结果不会归约为 [eq_refl] —— 但它仍然是一个 LOOP 等式，[nf_cast_loop] 通过 nat-UIP 来处理。
*)
  destruct p, q.
  rewrite nf_cast_loop, id_left.
  change (to (J m n X) ≈ to (J m n X) ∘ bimap id[nf m I] id[nf n X]).
  now rewrite bimap_id_id, id_right.
Qed.

(* * ** Where the coherence of B is spent / * ** B 的连贯性消耗的地方 *)

(*
 Associativity of the join: joining (m + m') then n agrees with joining m
 then (m' + n), up to the nat-level reassociation cast.  Induction on [m];
 the inductive step is the PENTAGON. 

 --------
 连接的结合性：先连接 (m + m') 然后连接 n 与先连接 m 然后连接 (m' + n) 一致，直到 nat 级别的重新关联转换。在 [m] 上进行归纳；归纳步骤是五边形（PENTAGON）。
*)
Theorem J_assoc (m m' n : nat) (X : B) :
  to (J (m + m') n X) ∘ bimap (to (J m m' I)) id[nf n X]
    ≈ id_cast (f_equal (fun i => nf i X) (Nat.add_assoc m m' n))
        ∘ to (J m (m' + n) X)
        ∘ bimap id[nf m I] (to (J m' n X))
        ∘ to (@tensor_assoc B _ (nf m I) (nf m' I) (nf n X)).
Proof.
  induction m; simpl.
  - (* Both outer joins are the left unitor and the cast is a loop; the residue is λ-naturality against J m' n X plus the left triangle. / 两个外连接都是左单位元，而类型转换是一个循环；剩余部分是针对 J m' n X 加上左三角形的 λ-自然性。 *)
    rewrite nf_cast_loop, id_left.
    rewrite <- (to_unit_left_natural (to (J m' n X))).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    apply triangle_identity_left.
  - (* The successor cast becomes [bimap id (cast)]; two associator naturalities bring the two sides into a common shape, the induction hypothesis rewrites under [bimap id (-)], and the residue is the PENTAGON verbatim. / 继任者的范畴变为 [bimap id (cast)]；两个结合子的自然性将两边带入一个共同的形状，归纳假设在 [bimap id (-)] 下重写，残余部分是 PENTAGON 原样。 *)
    rewrite (UIP_dec Nat.eq_dec (Nat.add_assoc (S m) m' n)
               (f_equal S (Nat.add_assoc m m' n))).
    rewrite (@nf_cast_succ (m + (m' + n)) (m + m' + n) X
               (Nat.add_assoc m m' n)).
    normal.
    (*
 Right side: peel the associator across the (id ⨂ J m' n) factor. 

 --------
 右边：沿着 (id ⨂ J m' n) 因子剥开结合子。
*)
    pose proof (to_tensor_assoc_natural
                  (id[b]) (id[nf m I]) (to (J m' n X))) as N1.
    rewrite bimap_id_id in N1.
    rewrite <- (comp_assoc _ (to tensor_assoc)
                  (bimap id (to (J m' n X)))).
    rewrite <- N1.
    (*
 Left side: split the bimap-of-composite, then peel its associator. 

 --------
 左侧：拆分复合双映射，然后剥离它的结合子。
*)
    rewrite (bimap_comp_id_right (bimap id[b] (to (J m m' I)))
                                 (to tensor_assoc)).
    rewrite (comp_assoc _ (bimap (bimap id[b] (to (J m m' I))) id)
                          (bimap (to tensor_assoc) id)).
    rewrite <- (comp_assoc _ (to tensor_assoc)
                  (bimap (bimap id[b] (to (J m m' I))) id)).
    pose proof (to_tensor_assoc_natural
                  (id[b]) (to (J m m' I)) (id[nf n X])) as N2.
    rewrite <- N2.
    normal.
    rewrite IHm.
    rewrite (bimap_comp_id_left _ (to tensor_assoc)).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    rewrite !comp_assoc.
    apply pentagon_identity.
Qed.

(*
 The join with an empty tail is the right unitor.  Induction on [n]; the
 base is Kelly's λ_I ≈ ρ_I, the step is the (right) triangle. 

 --------
 与空尾的连接是右单位元。对 [n] 进行归纳；基础是 Kelly 的 λ_I ≈ ρ_I，步骤是（三角形）右边的部分。
*)
Theorem J_right_unit (n : nat) :
  id_cast (f_equal (fun i => nf i I) (Nat.add_0_r n)) ∘ to (J n 0 I)
    ≈ to (@unit_right B _ (nf n I)).
Proof.
  induction n; simpl.
  - (* The cast's index pair (0 + 0, 0) never matches the kit lemmas syntactically (rewrite does not convert inside implicit arguments), so normalise the PROOF to [eq_refl] — a closed subterm, always matchable — and let reduction erase the cast. / 类型转换的索引对 (0 + 0, 0) 在语法上从未与套件引理匹配（重写不会转换隐式参数内部），所以将 PROOF 规范化为 [eq_refl] —— 一个封闭的子项，总是可匹配的 —— 并让归约擦除类型转换。 *)
    rewrite (UIP_dec Nat.eq_dec (Nat.add_0_r 0) eq_refl).
    simpl.
    rewrite id_left.
    apply unit_identity.
  - (* Same implicit-index obstruction in the successor case; route the cast step through [apply] (full conversion) instead of [rewrite]. / 在后继情况中相同的隐式索引阻塞；将类型转换步骤通过 [apply]（完全转换）而不是 [rewrite] 转发。 *)
    etransitivity.
    { apply compose_respects.
      - rewrite (UIP_dec Nat.eq_dec (Nat.add_0_r (S n))
                   (f_equal S (Nat.add_0_r n))).
        apply nf_cast_succ.
      - reflexivity. }
    normal.
    rewrite IHn.
    symmetry; apply bimap_triangle_right.
Qed.

(** ** Acceptance tests / ** 验收测试 *)

(* Substitution is definitional. / 代换是定义上的。 *)
Example subst_mix : subst (WT (WT WI WE) WI) = ((b ⨂ I) ⨂ b)%object := eq_refl.

(*
 The normal form of length 3, and its agreement with the normalised word. 

 --------
 长度为3的标准形式，以及它与标准化单词的一致性。
*)
Example nf_3 : nf 3 I = (b ⨂ (b ⨂ (b ⨂ I)))%object := eq_refl.
Example subst_nfword_3 : subst (nfword 3) = nf 3 I := eq_refl.

End Normal.
