Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Two-sided ideals, the quotient ring, and its universal property

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
   Exercise 6 (printed p. 59, PDF p. 68) [maclane:III.1:ex6].
   nLab: https://ncatlab.org/nlab/show/quotient+ring
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_ring

   For I a two-sided ideal of R, the projection p : R -> R/I is a
   UNIVERSAL ELEMENT of the functor of ring homomorphisms killing I.
   This is the ring half of §III.1's pair; the module half is
   Instance/Mod/Quotient.v, and the two are deliberately NOT one file,
   because the condition that makes the quotient work is different in
   the two cases and that difference is the content.

   THE CONDITION.  A module's addition is commutative, so every
   submodule quotients and Instance/Mod/Quotient.v carries ONE record
   with no normality layer ([smod_normal] proves the group-level
   conjugation field is a theorem there).  A ring's MULTIPLICATION is
   not commutative, and this is exactly where the group case's [ns_conj]
   reappears: for the relation x ~ y :⟺ x - y ∈ I to be a congruence for
   multiplication one needs

   x·y - x'·y' ≈ x·(y - y') + (x - x')·y'

   to have BOTH summands in I, and the two summands are absorbed on
   OPPOSITE SIDES.  So [Ideal] carries both [idl_absorb_l] and
   [idl_absorb_r], each spent exactly once, in [rquot_rel_mul].

   A ONE-SIDED IDEAL WILL NOT DO, and that is proved rather than
   asserted.  [LeftIdeal] below is the record with [idl_absorb_r]
   dropped, [IdealMulCongruence] names the property [rquot_rel_mul]
   establishes, [ideal_mul_congruence] shows every two-sided ideal has
   it, and Instance/Rng/Quotient/OneSided.v REFUTES it for an explicit
   left ideal of an explicit non-commutative ring -- ℤ·E₁₁ inside the
   upper-triangular 2×2 integer matrices [UT2]
   (Instance/Rng/Algebras/Associative.v).  That file also proves the
   left ideal is genuinely not a right one, so the separation is not
   vacuous.  It is a separate file for a dependency reason and not a
   stylistic one: [UT2] lives under Instance/Rng/Algebras/, which
   requires Instance/Mod.v and the associative-algebra tower, and no
   consumer of quotient rings should inherit that.

   ONE FEWER LAW.  [Ideal] carries FIVE laws and not six (six fields in
   all, the first being membership itself): closure under
   negation is DERIVED ([idl_neg]), since -a is (-1)·a and the record
   already absorbs multiplication.  Instance/Rng.v's
   [rig_mul_neg_one] is what makes that a one-line citation.  This is
   the same economy Instance/Mod/Quotient.v's [Submodule] takes, and for
   the same reason: a ring has a unit and a negation, so (-1) is
   available.

   ERRATUM.  Issue #314's "Current state in the library" section is
   stale; Instance/Mod/Quotient.v's header records the measurement in
   full and it is not repeated here.  The clause that matters for THIS
   file is that Instance/Rng.v (#257) exists and is REQUIRED below, and
   that an anchored sweep for a [Record], [Class], [Inductive],
   [Definition] or [Structure] whose name contains "Ideal" or
   "TwoSided", over every [.v] file in the tree, reads NONE -- so the
   interface is new even though the category is not.  Note also that the
   absence of quotient rings was load-bearing prose elsewhere:
   Instance/Rng/Frac.v's comment above [IntDom_Incl] and
   Instance/Field/Frac.v's quotation of it both say "the tree has no
   quotient rings yet"; the first is annotated by this same change, and
   the second is a QUOTATION of the first and is deliberately left
   intact so that it stays an accurate quotation.

   THE SETOID QUOTIENT.  As throughout this tree, R/I needs no new
   carrier: it is R's carrier under the coarser relation
   [rquot_rel I x y := inhabited (idl_mem I (x - y))], with the
   subtraction taken in the additive group [ring_ab R] and the shuffles
   supplied by Instance/Ab/Subtract.v.  No coset object is formed.  An
   earlier revision wrote the relation without the [inhabited]; since the
   PR "algebraic carriers are sets" (2026-09-17) a [RigObject] owes a
   [Prop]-valued mirror of its equality, and this relation is the
   PROPOSITIONAL TRUNCATION of a [Type]-valued membership, exactly as
   Instance/Mod/Quotient.v's [mquot_rel] is.  See the note on [Ideal]
   below for why membership itself stays [Type]-valued.

   WHAT IS DELIVERED HERE.  [Ideal] with the derived [idl_neg];
   [QuotientRing] with the projection [rquot_proj]; the functor
   [RKillsFunctor I : Rng ⟶ Sets] of ring homomorphisms killing I, and
   [rquot_universal_element], the statement that ⟨R/I, p⟩ is a universal
   element of it, over #303's [AUniversalElement] -- the CLASS is used
   directly and none of Theory/Universal/Element.v's Yoneda packaging is
   touched, so the universe restriction that packaging carries is not
   inherited; the homomorphism theorem as the biconditional
   [ring_hom_theorem]; the kernel of a ring homomorphism as an ideal;
   quotients by coextensive ideals; the degenerate ideals named and
   separated by proof; and non-vacuity at ℤ ⊇ 2ℤ, where ℤ/2ℤ's
   arithmetic is COMPUTED and the mediator out of ℤ/6ℤ is exercised.

   WHAT IS NOT DELIVERED HERE.  No ring isomorphism theorems: the image
   of a ring homomorphism is a SUBRING and not an ideal, so R/ker f ≅
   im f needs a [Subring] interface that the issue does not ask for and
   that nothing else in the tree wants yet; the module isomorphism
   theorems, which the issue DOES ask for, are in
   Instance/Mod/Quotient/Isomorphism.v.  Also absent: no sum, product or
   intersection of ideals; no principal, prime or maximal ideals, hence
   no Noetherian conditions and no Chinese remainder theorem; no
   identification of ℤ/2ℤ with Instance/Field.v's [F2_Ring] (which would
   make this file depend on the field layer); and no [Rng]-level
   cokernel or [HasCokernels] instance. 

   --------
   * * 双边理想、商环及其泛性质

   Mac Lane，《面向工作数学家的范畴论》，第2版，§III.1
   练习6（印刷版第59页，PDF第68页）  [maclane:III.1:ex6]。
   nLab：  https://ncatlab.org/nlab/show/quotient+ring
   维基百科：  https://en.wikipedia.org/wiki/Quotient_ring

   对于R的双边理想I，投射映射 p : R -> R/I 是
   消去I的环同态函子中的一个
   泛元素。
   这是§III.1中那对中的环部分；模块部分是
   Instance/Mod/Quotient.v，这两者故意不是同一个文件，
   因为使商成立的条件在两种情况下不同，而这种差异就是内容本身。条件。一个模的加法是交换的，所以每个子模的商以及 Instance/Mod/Quotient.v 都携带一个没有正规性层的记录（[smod_normal] 证明了群级共轭域在那是一个定理）。一个环的乘法不是交换的，这正是群情况的 [ns_conj] 再次出现的地方：为了关系 x ~ y :⟺ x - y ∈ I 成为乘法的同余，需要

   x·y - x'·y' ≈ x·(y - y') + (x - x')·y'

   两个项都在 I 中，并且这两个项被吸收到相反的两边。所以 [Ideal] 同时携带了 [idl_absorb_l] 和 [idl_absorb_r]，每个只使用一次，在 [rquot_rel_mul] 中。单边理想是不行的，这一点不仅被断言，而且被证明了。下面的 [LeftIdeal] 是去掉 [idl_absorb_r] 的记录，[IdealMulCongruence] 命名了属性，[rquot_rel_mul] 建立了属性，[ideal_mul_congruence] 表明每个双边理想都有它，而 Instance/Rng/Quotient/OneSided.v 针对一个明确的左理想在一个明确的非交换环——位于上三角 2×2 整数矩阵中的 ℤ·E₁₁ 里 [UT2]——证伪了它（Instance/Rng/Algebras/Associative.v）。该文件还证明了这个左理想确实不是右理想，因此这种区分不是空洞的。这是一个单独的文件出于依赖原因，而不是风格原因：[UT2] 位于 Instance/Rng/Algebras/ 下，而那里需要 Instance/Mod.v 和结合代数塔，并且没有商环的使用者应该继承它。少一条法则。[Ideal] 包含五条法则，而不是六条（总共有六个字段，第一条是关于本身的成员资格）：对取反的封闭性是派生的（[idl_neg]），因为 -a 等于 (-1)·a，而记录已经吸收了乘法。Instance/Rng.v 的 [rig_mul_neg_one] 使这成为一行引用。这与 Instance/Mod/Quotient.v 的 [Submodule] 所采用的节约方式相同，原因也相同：一个环有单位元和取反，所以 (-1) 可用。勘误。第314期的“库中的当前状态”部分已过时；Instance/Mod/Quotient.v 的头部完整记录了测量内容，这里不再重复。对于本文件重要的条款是 Instance/Rng.v（第257号）存在并且在下文中是必需的，并且针对 [Record]、[Class]、[Inductive]、[Definition] 或 [Structure]，其名称包含“Ideal”或“TwoSided”的固定扫描，在树中的每个 [.v] 文件上读取为 NONE——因此即使类别没有变化，接口也是新的。还要注意，商环的缺失在其他地方也是重要的说明：Instance/Rng/Frac.v 中上述 [IntDom_Incl] 的注释以及 Instance/Field/Frac.v 对它的引用都说“树上还没有商环”；第一个注释已由同样的更改进行标注，第二个是对第一个的引用，并故意保持不变，以便它仍然是一个准确的引用。集合商（Setoid Quotient）。正如在整个树中一样，R/I 不需要新的承载类型：它是 R 在较粗关系 [rquot_rel I x y := inhabited (idl_mem I (x - y))] 下的承载类型，其中减法在加法群 [ring_ab R] 中进行，并且由 Instance/Ab/Subtract.v 提供乱序操作。没有形成陪集对象。早期的一个版本在关系中没有写 [inhabited]；由于 PR "代数承载类型是集合"（2026-09-17），一个 [RigObject] 值需要一个 [Prop] 值的等式镜像，而这个关系是 [Type] 值的成员关系的命题截断（PROPOSITIONAL TRUNCATION），正如 Instance/Mod/Quotient.v 的 [mquot_rel] 一样。关于为什么成员关系本身保持 [Type] 值，请参见下面关于 [Ideal] 的注释。这里交付的内容。[Ideal] 与导出 [idl_neg]；[QuotientRing] 与投影 [rquot_proj]；零理想同态的函子 [RKillsFunctor I : Rng ⟶ Sets]，以及 [rquot_universal_element]，即 ⟨R/I, p⟩ 是其普遍元素的陈述，在 #303 的 [AUniversalElement] 上 —— 该 CLASS 被直接使用，Theory/Universal/Element.v 的 Yoneda 封装未被触及，因此封装所携带的宇宙限制未被继承；同态定理作为双条件 [ring_hom_theorem]；环同态的核作为理想；按共扩展理想的商；由证明命名并区分的退化理想；以及在 ℤ ⊇ 2ℤ 处的非空性，其中 ℤ/2ℤ 的运算被计算并且 ℤ/6ℤ 的中介被使用。这里未提供的内容。没有环同构定理：环同态的像是一个子环而不是理想，因此 R/ker f ≅ im f 需要一个 [Subring] 接口，而该问题未要求，且树中的其他部分也不需要；该问题要求的模同构定理在 Instance/Mod/Quotient/Isomorphism.v 中。也缺失：没有理想的和、积或交；没有主理想、素理想或极大理想，因此没有诺特条件，也没有中国剩余定理；没有将 ℤ/2ℤ 与 Instance/Field.v 的 [F2_Ring] 识别（这会使该文件依赖于域层）；也没有 [Rng] 级别的余核或 [HasCokernels] 实例。
*)

(** ** Two-sided ideals / ** 双边理想 *)

(*
 Membership is [Type]-valued, following Instance/Mod/Quotient.v's
 [Submodule] and Instance/Grp/Quotient.v's [Subgroup].

 AN EARLIER REVISION gave the reason as: "the library's `≈` is itself
 [Type]-valued, so a [Prop]-valued membership could not be eliminated into
 a hom-setoid equation."  That reason is GONE since the PR "algebraic
 carriers are sets" (2026-09-17): every ring carrier now carries
 [rig_prop], so [pequiv_to] performs exactly that elimination.  Membership
 stays [Type]-valued for a different reason, the one Instance/Mod/Quotient.v
 records for [Submodule]: the consumers here READ WITNESSES out of it --
 [EvenIdeal]'s and [SixIdeal]'s closure obligations below take the integer
 k apart and rebuild it, and [E11Left_is_not_an_Ideal] in
 Instance/Rng/Quotient/OneSided.v pulls the column entry out -- and those
 are data.  What DID move is the quotient RELATION [rquot_rel], which is
 now the propositional truncation of membership.

 There is deliberately no decidability field and nothing below decides
 membership. 

 --------
 成员资格是 [Type] 值，遵循 Instance/Mod/Quotient.v 的 [Submodule] 和 Instance/Grp/Quotient.v 的 [Subgroup]。早期的修订给出的理由是：“库的 `≈` 本身是 [Type] 值的，因此 [Prop] 值的成员资格无法消除为同余集方程。” 由于 PR “代数载体是集合”（2026-09-17），这个理由已经不存在：现在每个环载体都承载 [rig_prop]，因此 [pequiv_to] 正好执行那种消除。成员资格由于不同的原因保持为 [Type] 值，这是 Instance/Mod/Quotient.v 为 [Submodule] 记录的原因：这里的使用者从中读取 WITNESSES —— 下文 [EvenIdeal] 和 [SixIdeal] 的闭包义务将整数 k 拆开并重新组合，而 Instance/Rng/Quotient/OneSided.v 中的 [E11Left_is_not_an_Ideal] 拉出了列条目 —— 而这些都是数据。真正发生变化的是商关系 [rquot_rel]，它现在是成员资格的命题截断。故意没有可判定性字段，下面也没有任何东西决定成员资格。
*)

Record Ideal (R : RingObject) := {
  idl_mem : carrier (rig_setoid R) → Type;

  (* (1) ≈-saturation / (1) ≈-饱和 *)
  idl_resp : ∀ a b : carrier (rig_setoid R),
    a ≈ b → idl_mem a → idl_mem b;
  (* (2) zero *)
  idl_zero : idl_mem (rig_zero R);
  (* (3) closure under addition / (3) 在加法下的封闭性 *)
  idl_plus : ∀ a b : carrier (rig_setoid R),
    idl_mem a → idl_mem b → idl_mem (rig_add R a b);
  (* (4) absorption on the left / (4) 左侧吸收 *)
  idl_absorb_l : ∀ r a : carrier (rig_setoid R),
    idl_mem a → idl_mem (rig_mul R r a);
  (* (5) absorption on the RIGHT -- the field a one-sided ideal drops, and the one Instance/Rng/Quotient/OneSided.v proves indispensable / (5) 右吸收——当场是单边理想消失时，一个实例/Rng/Quotient/OneSided.v 显得不可或缺 *)
  idl_absorb_r : ∀ a r : carrier (rig_setoid R),
    idl_mem a → idl_mem (rig_mul R a r)
}.

Arguments idl_mem {R} _ _.
Arguments idl_resp {R} _ _ _ _ _.
Arguments idl_zero {R} _.
Arguments idl_plus {R} _ _ _ _ _.
Arguments idl_absorb_l {R} _ _ _ _.
Arguments idl_absorb_r {R} _ _ _ _.

(* A LEFT ideal: the same record with [idl_absorb_r] dropped. It exists in order to be refuted. / 一个左理想：与删除了 [idl_absorb_r] 的记录相同。它存在的目的是为了被反驳。 *)
Record LeftIdeal (R : RingObject) := {
  lidl_mem : carrier (rig_setoid R) → Type;

  lidl_resp : ∀ a b : carrier (rig_setoid R),
    a ≈ b → lidl_mem a → lidl_mem b;
  lidl_zero : lidl_mem (rig_zero R);
  lidl_plus : ∀ a b : carrier (rig_setoid R),
    lidl_mem a → lidl_mem b → lidl_mem (rig_add R a b);
  lidl_absorb_l : ∀ r a : carrier (rig_setoid R),
    lidl_mem a → lidl_mem (rig_mul R r a)
}.

Arguments lidl_mem {R} _ _.
Arguments lidl_resp {R} _ _ _ _ _.
Arguments lidl_zero {R} _.
Arguments lidl_plus {R} _ _ _ _ _.
Arguments lidl_absorb_l {R} _ _ _ _.

(* Every two-sided ideal is in particular a left ideal, so the refutation downstream is genuinely about the WEAKER notion. / 每个双边理想特别来说都是左理想，因此下游的反驳实际上是关于较弱的概念。 *)
Definition Ideal_LeftIdeal {R : RingObject} (I : Ideal R) : LeftIdeal R :=
  {| lidl_mem := idl_mem I
   ; lidl_resp := idl_resp I
   ; lidl_zero := idl_zero I
   ; lidl_plus := idl_plus I
   ; lidl_absorb_l := idl_absorb_l I |}.

(* Saturation in the argument-implicit shape the proofs below want. / 下面的证明所需要的论证隐含形式中的饱和度。 *)
Definition idl_at {R : RingObject} (I : Ideal R)
  {a b : carrier (rig_setoid R)} (Hab : a ≈ b) (Ha : idl_mem I a) :
  idl_mem I b := idl_resp I a b Hab Ha.

Definition lidl_at {R : RingObject} (L : LeftIdeal R)
  {a b : carrier (rig_setoid R)} (Hab : a ≈ b) (Ha : lidl_mem L a) :
  lidl_mem L b := lidl_resp L a b Hab Ha.

(* THE SIXTH FIELD THAT IS NOT A FIELD: closure under negation, because -a is (-1)·a. Only LEFT absorption is spent. / 第六个不是一个域的领域：关于取反的封闭性，因为 -a 等于 (-1)·a。只有左吸收性被使用。 *)
Lemma idl_neg {R : RingObject} (I : Ideal R) (a : carrier (rig_setoid R)) :
  idl_mem I a → idl_mem I (ring_neg R a).
Proof.
  intro Ha.
  apply (idl_at I (a := rig_mul R (ring_neg R (rig_one R)) a)).
  - apply rig_mul_neg_one.
  - exact (idl_absorb_l I _ _ Ha).
Qed.

Lemma idl_sub {R : RingObject} (I : Ideal R)
  (a b : carrier (rig_setoid R)) :
  idl_mem I a → idl_mem I b → idl_mem I (ab_sub (ring_ab R) a b).
Proof.
  intros Ha Hb.
  exact (idl_plus I _ _ Ha (idl_neg I _ Hb)).
Qed.

(*
   * ** Multiplication against subtraction

   The three lemmas the multiplicative congruence costs.  None is in
   the tree at [RingObject] level: Instance/Matr/Determinant.v
   has [ring_neg_mul_l] and [ring_neg_mul_r], but over its own section
   variable [K] and behind that file's notation, and requiring a
   1742-line determinant development for two three-line lemmas is not
   a trade worth making.  They are restated here with different names, so
   that a file importing both does not shadow. 

   --------
   * ** 乘法与减法的对比

   三个引理涉及乘法同余。 在树的  [RingObject]  层级中没有出现：
   Instance/Matr/Determinant.v 文件中有  [ring_neg_mul_l]  和  [ring_neg_mul_r] ，但在其自身的节变量
   [K]  以及该文件的记号之后，并且为了两个三行引理而进行 1742 行的行列式展开
   并不值得做。这些引理在这里以不同的名称重新陈述，以便导入两个文件时不会产生覆盖。
*)

Lemma rng_neg_mul_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_r.
  rewrite (ring_neg_l R a).
  apply rig_mul_zero_l.
Qed.

Lemma rng_neg_mul_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_l.
  rewrite (ring_neg_l R b).
  apply rig_mul_zero_r.
Qed.

Lemma rig_mul_sub_l (R : RingObject) (a b c : carrier (rig_setoid R)) :
  rig_mul R a (ab_sub (ring_ab R) b c)
    ≈ ab_sub (ring_ab R) (rig_mul R a b) (rig_mul R a c).
Proof.
  unfold ab_sub; simpl.
  rewrite rig_distr_l.
  now rewrite rng_neg_mul_r.
Qed.

Lemma rig_mul_sub_r (R : RingObject) (a b c : carrier (rig_setoid R)) :
  rig_mul R (ab_sub (ring_ab R) a b) c
    ≈ ab_sub (ring_ab R) (rig_mul R a c) (rig_mul R b c).
Proof.
  unfold ab_sub; simpl.
  rewrite rig_distr_r.
  now rewrite rng_neg_mul_l.
Qed.

(*
 A ring homomorphism commutes with subtraction.  [RigHom_neg]
 (Theory/Algebra/Rig.v) supplies the negation half; nothing here is
 new mathematics, but the shape is what the descent step below wants
 and Instance/Ab/Subtract.v's [ab_map_sub] is stated for an [AbHom],
 which a [RigHom] is only after transport through [Rng_Forget_Ab]. 

 --------
 环同态与减法交换。[RigHom_neg]（理论/代数/Rig.v）提供了取负的一半；这里没有新的数学内容，但其形式正是下面下降步骤所需要的，而Instance/Ab/Subtract.v 的 [ab_map_sub] 是为一个 [AbHom] 陈述的，一个 [RigHom] 只有在通过 [Rng_Forget_Ab] 传输后才成立。
*)
Lemma rig_map_sub {R S : RingObject} (f : R ~{Rng}~> S)
  (x y : carrier (rig_setoid R)) :
  rig_map f (ab_sub (ring_ab R) x y)
    ≈ ab_sub (ring_ab S) (rig_map f x) (rig_map f y).
Proof.
  unfold ab_sub; simpl.
  rewrite (rig_map_add f).
  apply rig_add_respects; [ reflexivity |].
  apply (RigHom_neg R S f).
Qed.

(*
 THE IDENTITY THAT FORCES TWO-SIDEDNESS:
 x·y - x'·y' ≈ x·(y - y') + (x - x')·y'
 The first summand is absorbed on the LEFT, the second on the RIGHT.
 Neither absorption law can cover the other summand, which is why a
 one-sided ideal is not enough. 

 --------
 迫使双面性的恒等式：
 x·y - x'·y' ≈ x·(y - y') + (x - x')·y'
 第一个加数在左边被吸收，第二个在右边被吸收。
 没有吸收律可以覆盖另一个加数，这就是为什么单侧理想是不够的。
*)
Lemma rig_mul_sub_expand (R : RingObject)
  (x y x' y' : carrier (rig_setoid R)) :
  ab_sub (ring_ab R) (rig_mul R x y) (rig_mul R x' y')
    ≈ rig_add R (rig_mul R x (ab_sub (ring_ab R) y y'))
                (rig_mul R (ab_sub (ring_ab R) x x') y').
Proof.
  rewrite rig_mul_sub_l, rig_mul_sub_r.
  symmetry.
  exact (ab_sub_trans (ring_ab R) (rig_mul R x y) (rig_mul R x y')
                      (rig_mul R x' y')).
Qed.

(** ** The quotient relation / ** 商关系 *)

(*
 Since the PR "algebraic carriers are sets" (2026-09-17) the quotient is a
 [RingObject] and so owes [rig_prop], which forces its equality to be a
 [Prop].  [idl_mem] STAYS [Type]-valued -- see the note on [Ideal] above --
 and the relation is its PROPOSITIONAL TRUNCATION.  [inhabited] is the
 truncation; [pequiv_elim_inhabited] (Lib/Setoid/Propositional.v) is what
 gets back out, and the seven congruence lemmas below each gain one
 [destruct … as [K]] going in and one [constructor] coming out. 

 --------
 自从 PR “代数载体是集合” (2026-09-17) 以来，商是一个 [RingObject]，因此欠 [rig_prop]，这迫使它的相等性是一个 [Prop]。[idl_mem] 保持 [Type] 值——参见上文关于 [Ideal] 的注释——并且该关系是它的命题截断。[inhabited] 是截断；[pequiv_elim_inhabited]（Lib/Setoid/Propositional.v）是得到的结果，而下面的七个同余引理，每个进入获得一个 [destruct … as [K]，出来获得一个 [constructor]。
*)
Definition rquot_rel {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) : Prop :=
  inhabited (idl_mem I (ab_sub (ring_ab R) x y)).

Section QuotientRelation.

Context {R : RingObject}.
Context (I : Ideal R).

Lemma rquot_rel_of_equiv (x y : carrier (rig_setoid R)) :
  x ≈ y → rquot_rel I x y.
Proof.
  intro Hxy; unfold rquot_rel.
  constructor.
  apply (idl_at I (a := rig_zero R)); [| exact (idl_zero I) ].
  change (rig_zero R) with (cmon_zero (ring_ab R)).
  rewrite <- Hxy.
  symmetry; apply (ab_sub_self (ring_ab R)).
Qed.

Lemma rquot_rel_refl (x : carrier (rig_setoid R)) : rquot_rel I x x.
Proof. apply rquot_rel_of_equiv; reflexivity. Qed.

Lemma rquot_rel_sym (x y : carrier (rig_setoid R)) :
  rquot_rel I x y → rquot_rel I y x.
Proof.
  unfold rquot_rel; intros [K].
  constructor.
  apply (idl_at I (a := ring_neg R (ab_sub (ring_ab R) x y))).
  - apply (ab_sub_neg (ring_ab R)).
  - exact (idl_neg I _ K).
Qed.

Lemma rquot_rel_trans (x y z : carrier (rig_setoid R)) :
  rquot_rel I x y → rquot_rel I y z → rquot_rel I x z.
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I (a := rig_add R (ab_sub (ring_ab R) x y)
                                 (ab_sub (ring_ab R) y z))).
  - apply (ab_sub_trans (ring_ab R)).
  - exact (idl_plus I _ _ K1 K2).
Qed.

Lemma rquot_rel_add (x x' y y' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I y y' →
  rquot_rel I (rig_add R x y) (rig_add R x' y').
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I (a := rig_add R (ab_sub (ring_ab R) x x')
                                 (ab_sub (ring_ab R) y y'))).
  - apply (ab_sub_plus (ring_ab R)).
  - exact (idl_plus I _ _ K1 K2).
Qed.

Lemma rquot_rel_neg (x x' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I (ring_neg R x) (ring_neg R x').
Proof.
  unfold rquot_rel; intros [K].
  constructor.
  apply (idl_at I (a := ring_neg R (ab_sub (ring_ab R) x x'))).
  - rewrite (ab_sub_neg (ring_ab R)).
    (*
 [exact] rather than [apply]: [ab_neg (ring_ab R)] and
 [ring_neg R] are convertible but not syntactically equal, and
 unification will not invert the projection under a metavariable. 

 --------
 [exact] 而不是 [apply]：[ab_neg (ring_ab R)] 和 [ring_neg R] 是可转换的但在语法上不相等，并且合一不会在元变量下反转投影。
*)
    symmetry; exact (ab_sub_neg_neg (ring_ab R) x x').
  - exact (idl_neg I _ K).
Qed.

(* THE PLACE BOTH ABSORPTION LAWS ARE SPENT, one apiece. / 两个吸收定律都被消耗的地方，每个各一个。 *)
Lemma rquot_rel_mul (x x' y y' : carrier (rig_setoid R)) :
  rquot_rel I x x' → rquot_rel I y y' →
  rquot_rel I (rig_mul R x y) (rig_mul R x' y').
Proof.
  unfold rquot_rel; intros [K1] [K2].
  constructor.
  apply (idl_at I
           (a := rig_add R (rig_mul R x (ab_sub (ring_ab R) y y'))
                           (rig_mul R (ab_sub (ring_ab R) x x') y'))).
  - symmetry; apply rig_mul_sub_expand.
  - apply idl_plus.
    + exact (idl_absorb_l I x _ K2).
    + exact (idl_absorb_r I _ y' K1).
Qed.

(*
 Membership IS congruence to zero, in both directions -- up to the
 truncation.

 AN EARLIER REVISION stated the right-hand side as the bare [idl_mem I x].
 Since the PR "algebraic carriers are sets" (2026-09-17) [rquot_rel] is the
 propositional truncation of membership, so the LEFT-to-right direction is
 an elimination of a [Prop] into a [Type] and is refused; the biconditional
 is stated up to [inhabited], which is its exact content.  The direction
 that loses nothing -- membership implies congruence to zero, which is what
 every consumer in the tree actually uses -- is kept separately as
 [rquot_rel_of_mem] below, with its [Type]-valued hypothesis intact. 

 --------
 成员资格在两个方向上都与零同余——直到截断。

 早期的修订将右侧表示为单纯的 [idl_mem I x]。由于 PR “代数载体是集合”（2026-09-17） [rquot_rel] 是成员资格的命题截断，因此从左到右的方向是将 [Prop] 消去为 [Type] 并被拒绝；双条件在 [inhabited] 范围内陈述，这是其确切内容。失去任何信息的方向——成员资格蕴含与零同余，这是树中的每个使用者实际上使用的——在下文中以 [rquot_rel_of_mem] 单独保留，其 [Type] 值的假设保持不变。
*)
Lemma rquot_rel_zero_iff (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ inhabited (idl_mem I x).
Proof.
  split; intros [K]; unfold rquot_rel in *; constructor.
  - exact (idl_at I (ab_sub_zero_r (ring_ab R) x) K).
  - exact (idl_at I (symmetry (ab_sub_zero_r (ring_ab R) x)) K).
Qed.

(*
 The half of the biconditional that keeps its [Type]-valued hypothesis:
 nothing is truncated on the way in. 

 --------
 保持其 [Type] 值假设的双条件的另一半：输入过程中没有任何东西被截断。
*)
Lemma rquot_rel_of_mem (x : carrier (rig_setoid R)) :
  idl_mem I x → rquot_rel I x (rig_zero R).
Proof.
  intro K; unfold rquot_rel; constructor.
  exact (idl_at I (symmetry (ab_sub_zero_r (ring_ab R) x)) K).
Qed.

Program Definition rquot_setoid : Setoid (carrier (rig_setoid R)) := {|
  equiv := rquot_rel I
|}.
Next Obligation.
  constructor.
  - exact rquot_rel_refl.
  - exact rquot_rel_sym.
  - exact rquot_rel_trans.
Qed.

End QuotientRelation.

Arguments rquot_setoid {R} I.

(* The property the two-sided condition buys, named so that Instance/Rng/Quotient/OneSided.v can refute it for the one-sided notion. / 这种双向条件所带来的性质，因此命名，以便 Instance/Rng/Quotient/OneSided.v 可以针对单向概念反驳它。 *)
Definition IdealMulCongruence {R : RingObject} (I : Ideal R) : Type :=
  ∀ x x' y y' : carrier (rig_setoid R),
    rquot_rel I x x' → rquot_rel I y y' →
    rquot_rel I (rig_mul R x y) (rig_mul R x' y').

Definition ideal_mul_congruence {R : RingObject} (I : Ideal R) :
  IdealMulCongruence I := rquot_rel_mul I.

(*
 The same relation, read off a LEFT ideal, and the same property.  The
 relation is definitionally the two-sided one at [Ideal_LeftIdeal I]
 -- recorded by convertibility, which is what makes the refutation
 downstream a statement about this very construction. 

 --------
 相同的关系，从左理想读取，并具有相同的性质。该关系在 [Ideal_LeftIdeal I] 上从定义上就是双边关系——通过可转换性记录，这正是使得下游的反驳成为关于这一构造本身的陈述的原因。
*)
(*
 Truncated in lockstep with [rquot_rel], and for the same reason: the
 convertibility recorded by [lquot_rel_is_rquot_rel] below is what makes
 the refutation in Instance/Rng/Quotient/OneSided.v a statement about THIS
 construction, and two relations of different SORT could not be
 convertible.  An earlier revision wrote both without the [inhabited]. 

 --------
 与 [rquot_rel] 同步截断，原因相同：下面 [lquot_rel_is_rquot_rel] 记录的可转换性使得 Instance/Rng/Quotient/OneSided.v 中的反驳成为关于此构造的陈述，而且两种不同类型的关系不可能是可转换的。早期的修订在没有 [inhabited] 的情况下写了两者。
*)
Definition lquot_rel {R : RingObject} (L : LeftIdeal R)
  (x y : carrier (rig_setoid R)) : Prop :=
  inhabited (lidl_mem L (ab_sub (ring_ab R) x y)).

Definition LeftIdealMulCongruence {R : RingObject} (L : LeftIdeal R) : Type :=
  ∀ x x' y y' : carrier (rig_setoid R),
    lquot_rel L x x' → lquot_rel L y y' →
    lquot_rel L (rig_mul R x y) (rig_mul R x' y').

Example lquot_rel_is_rquot_rel {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y.
Proof. reflexivity. Qed.

(* * ** The quotient ring and its projection / * ** 商环及其投射 *)

Definition QuotientRing {R : RingObject} (I : Ideal R) : RingObject.
Proof.
  unshelve notypeclasses refine {|
    ring_rig := {| rig_setoid := {| carrier := carrier (rig_setoid R)
                                  ; is_setoid := rquot_setoid I |}
                 ; rig_zero := rig_zero R
                 ; rig_add := rig_add R
                 ; rig_one := rig_one R
                 ; rig_mul := rig_mul R |};
    ring_neg := ring_neg R
  |}.
  - (* rig_add_respects / 致敬 *)
    intros x x' Hx y y' Hy; now apply rquot_rel_add.
  - (* rig_mul_respects / 刚性乘法尊重 *)
    intros x x' Hx y y' Hy; now apply rquot_rel_mul.
  - (* rig_add_assoc / 环加法结合律 *)
    intros a b c; apply rquot_rel_of_equiv, rig_add_assoc.
  - (* rig_add_comm / rig_add_comm *)
    intros a b; apply rquot_rel_of_equiv, rig_add_comm.
  - (* rig_add_zero_l / rig_add_zero_l *)
    intros a; apply rquot_rel_of_equiv, rig_add_zero_l.
  - (* rig_mul_assoc / 环乘法结合律 *)
    intros a b c; apply rquot_rel_of_equiv, rig_mul_assoc.
  - (* rig_mul_one_l / rig_mul_one_l *)
    intros a; apply rquot_rel_of_equiv, rig_mul_one_l.
  - (* rig_mul_one_r / rig_乘以_一_r *)
    intros a; apply rquot_rel_of_equiv, rig_mul_one_r.
  - (* rig_distr_l / 刚性分布_l *)
    intros a b c; apply rquot_rel_of_equiv, rig_distr_l.
  - (* rig_distr_r / 刚性分布_r *)
    intros a b c; apply rquot_rel_of_equiv, rig_distr_r.
  - (* rig_mul_zero_l / 环_乘_零_左 *)
    intros a; apply rquot_rel_of_equiv, rig_mul_zero_l.
  - (* rig_mul_zero_r / 环_乘_零_右 *)
    intros a; apply rquot_rel_of_equiv, rig_mul_zero_r.
  - (* rig_prop. The quotient's `≈` IS [rquot_rel I], which since the PR "algebraic carriers are sets" (2026-09-17) is already a [Prop], so the ring is its own [Prop] mirror and both implications are the identity. / rig_prop。商的 `≈` 是 [rquot_rel I]，鉴于 PR ‘代数载体是集合’（2026-09-17），它已经是一个 [Prop]，因此这个环是它自己的 [Prop] 镜像，两者的蕴含都是恒等的。 *)
    exact (@PropEquiv_of_relation _ (rquot_setoid I) (rquot_rel I)
             (fun _ _ h => h) (fun _ _ h => h)).
  - (* ring_neg_respects / 未尊重戒指 *)
    intros x y Hxy; now apply rquot_rel_neg.
  - (* ring_neg_l / 铃声_负_L *)
    intros a; apply rquot_rel_of_equiv, ring_neg_l.
Defined.

(*
 NO NOTATION for the quotient, for the reason Instance/Grp/Quotient.v
 gives: an unscoped infix [/] at level 40 would compete with the
 stdlib's scope-bound division notations in every importing file. 

 --------
 商没有记号，原因是在文件 Instance/Grp/Quotient.v 中显示：一个未限定的中缀 [/] 在等级 40 会与标准库中在每个导入文件中的作用域绑定除法记号产生冲突。
*)

Program Definition rquot_proj {R : RingObject} (I : Ideal R) :
  R ~{Rng}~> QuotientRing I := {|
  rig_map := {| morphism := fun x : carrier (rig_setoid R) => x |}
|}.
Next Obligation. intros R I x y Hxy; apply rquot_rel_of_equiv, Hxy. Qed.
Next Obligation. intros R I; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I x y; simpl; apply rquot_rel_refl. Qed.

Lemma rquot_proj_kills {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  idl_mem I x → rig_map (rquot_proj I) x ≈ rig_zero (QuotientRing I).
Proof.
  intro Hx; simpl.
  (* The [Type]-valued direction: [rquot_rel_of_mem] rather than the truncated biconditional, so nothing is lost on the way in. / [Type] 值的方向：[rquot_rel_of_mem]，而不是截断的双条件，所以途中没有任何损失。 *)
  exact (rquot_rel_of_mem I x Hx).
Qed.

(*
 Conversely: the projection's kernel is exactly I, as a biconditional --
 up to the truncation.  AN EARLIER REVISION stated the right-hand side as
 the bare [idl_mem I x]; since the PR "algebraic carriers are sets"
 (2026-09-17) the quotient's `≈` is [rquot_rel], the propositional
 truncation of membership, so the forward direction would be a [Prop] into
 a [Type] and the biconditional is stated up to [inhabited].
 [rquot_proj_kills] above is the untruncated direction. 

 --------
 反之：投影的核正好是 I，作为双条件——
 直到截断为止。早期的修订版本将右侧写为
 纯粹的 [idl_mem I x]；由于 PR“代数承载体是集合”
 （2026-09-17），商的 `≈` 是 [rquot_rel]，即成员资格的命题截断，因此正向方向将是一个 [Prop] 到
 一个 [Type]，并且双条件被表述为直到 [inhabited]。
 上述 [rquot_proj_kills] 是未截断方向。
*)
Lemma rquot_proj_kernel {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rig_map (rquot_proj I) x ≈ rig_zero (QuotientRing I) ↔ inhabited (idl_mem I x).
Proof. exact (rquot_rel_zero_iff I x). Qed.

Lemma rquot_proj_surjective {R : RingObject} (I : Ideal R) :
  ∀ b : carrier (rig_setoid (QuotientRing I)),
    ∃ a, rig_map (rquot_proj I) a ≈ b.
Proof. intro x; exists x; simpl; apply rquot_rel_refl. Qed.

Lemma rquot_proj_epic {R : RingObject} (I : Ideal R) :
  Epic (rquot_proj I).
Proof. apply rng_surjective_epic, rquot_proj_surjective. Qed.

(* * ** The functor of homomorphisms killing I / * ** 使 I 消失的同态函子 *)

Definition RKills {R : RingObject} (I : Ideal R) (K : RingObject) : Type :=
  { h : R ~{Rng}~> K
  & ∀ a : carrier (rig_setoid R), idl_mem I a →
      rig_map h a ≈ rig_zero K }.

Program Definition RKills_Setoid {R : RingObject} (I : Ideal R)
  (K : RingObject) : Setoid (RKills I K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R I K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q u Hpq Hqu; now transitivity (`1 q).
Qed.

Lemma RKills_post {R : RingObject} (I : Ideal R) {K K' : RingObject}
  (k : K ~{Rng}~> K') (p : RKills I K) (a : carrier (rig_setoid R)) :
  idl_mem I a → rig_map (k ∘ `1 p) a ≈ rig_zero K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (rig_map_zero k).
Qed.

Program Definition RKillsFunctor {R : RingObject} (I : Ideal R) :
  Rng ⟶ Sets := {|
  fobj := fun K => {| carrier := RKills I K
                    ; is_setoid := RKills_Setoid I K |};
  fmap := fun K K' k =>
    {| morphism := fun p : RKills I K =>
         existT _ (k ∘ `1 p) (RKills_post I k p) |}
|}.
Next Obligation.
  intros R I K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros R I K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros R I K p a; simpl; reflexivity. Qed.
Next Obligation. intros R I K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism / ** 中介同态 *)

Section Mediator.

Context {R : RingObject}.
Context (I : Ideal R).
Context {K : RingObject}.
Context (p : RKills I K).

(*
 Descent: a homomorphism killing I cannot tell I-congruent elements
 apart.  From I (x - y) one gets h x - h y ≈ 0, whence h x ≈ h y.  This
 is the ONE computation the quotient's universal property costs. 

 --------
 下降：一个同态将无法区分的 I-合同元素消灭。从 I (x - y) 可以得到 h x - h y ≈ 0，因此 h x ≈ h y。这就是商的泛性质所需的唯一计算。
*)
Lemma rkills_descends (x y : carrier (rig_setoid R)) :
  rquot_rel I x y → rig_map (`1 p) x ≈ rig_map (`1 p) y.
Proof.
  intro Hxy.
  (*
 Since the PR "algebraic carriers are sets" (2026-09-17) [rquot_rel] is
 a truncation, so [Hxy] is a [Prop] and cannot be destructed into the
 [Type]-valued goal `≈`.  [pequiv_to] at the TARGET ring K puts a [Prop]
 goal in front of the elimination; [pequiv_from] returns, and the
 computation below is unchanged. 

 --------
 自从 PR “代数载体是集合”（2026-09-17） [rquot_rel] 是一个截断，因此 [Hxy] 是一个 [Prop]，不能被拆解成 [Type] 值的目标 `≈`。 [pequiv_to] 在目标环 K 上放置一个 [Prop] 目标在消解前；[pequiv_from] 返回，并且下面的计算保持不变。
*)
  apply pequiv_to.
  destruct Hxy as [Hxy].
  apply pequiv_from.
  apply (fst (ab_sub_eq_zero_iff (ring_ab K) _ _)).
  rewrite <- (rig_map_sub (`1 p) x y).
  exact (`2 p _ Hxy).
Qed.

Program Definition rquot_med : QuotientRing I ~{Rng}~> K := {|
  rig_map := {| morphism := fun x : carrier (rig_setoid (QuotientRing I)) =>
                              rig_map (`1 p) x |}
|}.
Next Obligation. intros x y Hxy; exact (rkills_descends x y Hxy). Qed.
Next Obligation. simpl; apply (rig_map_zero (`1 p)). Qed.
Next Obligation. intros x y; simpl; apply (rig_map_add (`1 p)). Qed.
Next Obligation. simpl; apply (rig_map_one (`1 p)). Qed.
Next Obligation. intros x y; simpl; apply (rig_map_mul (`1 p)). Qed.

Lemma rquot_med_commutes : rquot_med ∘ rquot_proj I ≈ `1 p.
Proof. intro x; simpl; reflexivity. Qed.

Lemma rquot_med_unique (v : QuotientRing I ~{Rng}~> K)
  (Hv : v ∘ rquot_proj I ≈ `1 p) : rquot_med ≈ v.
Proof. intro x; simpl; symmetry; exact (Hv x). Qed.

End Mediator.

Arguments rquot_med {R} I {K} p.

(* * ** Mac Lane §III.1 Exercise 6: ⟨R/I, p⟩ is a universal element / * ** 麦克·莱恩 §III.1 练习 6：⟨R/I, p⟩ 是一个泛元 *)

Definition rquot_elem {R : RingObject} (I : Ideal R) :
  RKills I (QuotientRing I) :=
  existT _ (rquot_proj I) (rquot_proj_kills I).

Program Definition rquot_universal_element {R : RingObject} (I : Ideal R) :
  AUniversalElement (RKillsFunctor I) (QuotientRing I) := {|
  aue_elem := rquot_elem I
|}.
Next Obligation.
  intros R I K x.
  unshelve refine {| unique_obj := rquot_med I x |}.
  - exact (rquot_med_commutes I x).
  - intros v Hv; simpl in *.
    exact (rquot_med_unique I x v Hv).
Defined.

(*
 The universal element's underlying homomorphism IS the projection, by
 convertibility -- the [eq_refl] exception to the `≈` discipline, and
 the check that the packaging did not silently rebuild it. 

 --------
 通用元素的基础同态是投影，通过可转换性 —— [eq_refl] 对 `≈` 规范的例外，以及检查包装是否没有悄悄重建它。
*)
Example rquot_universal_elem_is_proj {R : RingObject} (I : Ideal R) :
  `1 (@aue_elem _ (RKillsFunctor I) (QuotientRing I)
        (rquot_universal_element I)) = rquot_proj I.
Proof. reflexivity. Qed.

Example rquot_universal_med_is_rquot_med {R : RingObject} (I : Ideal R)
  {K : RingObject} (x : RKills I K) :
  unique_obj (@aue_universal _ (RKillsFunctor I) (QuotientRing I)
                (rquot_universal_element I) K x)
    = rquot_med I x.
Proof. reflexivity. Qed.

(* * ** The homomorphism theorem, as a biconditional / * ** 同态定理，作为一个双条件 *)

Theorem ring_hom_theorem {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K) :
  (∀ a : carrier (rig_setoid R), idl_mem I a → rig_map h a ≈ rig_zero K)
    ↔ (∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : R ~{Rng}~> K =>
                         ∀ a : carrier (rig_setoid R), idl_mem I a →
                           rig_map h a ≈ rig_zero K) h Hkill).
    unshelve refine {| unique_obj := rquot_med I x |}.
    + exact (rquot_med_commutes I x).
    + intros v Hv.
      exact (rquot_med_unique I x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (rig_map u (rig_map (rquot_proj I) a)).
    + symmetry; exact (Hu a).
    + transitivity (rig_map u (rig_zero (QuotientRing I))).
      * apply proper_morphism.
        exact (rquot_proj_kills I a Ha).
      * exact (rig_map_zero u).
Qed.

Definition ring_hom_theorem_factor {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K)
  (Hkill : ∀ a : carrier (rig_setoid R), idl_mem I a →
             rig_map h a ≈ rig_zero K) :
  ∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h :=
  fst (ring_hom_theorem I h) Hkill.

Definition ring_hom_theorem_kills {R K : RingObject} (I : Ideal R)
  (h : R ~{Rng}~> K)
  (Hfac : ∃! u : QuotientRing I ~{Rng}~> K, u ∘ rquot_proj I ≈ h) :
  ∀ a : carrier (rig_setoid R), idl_mem I a → rig_map h a ≈ rig_zero K :=
  snd (ring_hom_theorem I h) Hfac.

(*
   * ** The kernel of a ring homomorphism is a two-sided ideal

   Both absorption laws come from the SAME clause, [rig_map_mul],
   together with the two annihilation laws; that they are available on
   both sides is what makes a kernel two-sided without any hypothesis on
   R.  (The IMAGE, by contrast, is a subring and not an ideal -- which
   is why this file stops short of a first isomorphism theorem.) 

   --------
   * ** 环同态的核是一个双边理想

   两个吸收律都来源于同一个条款，[rig_map_mul]，
   以及两个消去律；它们在两边都适用，这就是为什么核在不假设 R 的情况下也是双边的。（相比之下，像象像是一个子环而不是理想——这也是本文件为什么没有达到第一同构定理的原因。）
*)

Program Definition KernelIdeal {R S : RingObject} (f : R ~{Rng}~> S) :
  Ideal R := {|
  idl_mem := fun a : carrier (rig_setoid R) => rig_map f a ≈ rig_zero S
|}.
Next Obligation.
  intros R S f a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation. intros R S f; simpl; apply (rig_map_zero f). Qed.
Next Obligation.
  intros R S f a b Ha Hb; simpl in *.
  rewrite (rig_map_add f), Ha, Hb.
  apply rig_add_zero_l.
Qed.
Next Obligation.
  intros R S f r a Ha; simpl in *.
  rewrite (rig_map_mul f), Ha.
  apply rig_mul_zero_r.
Qed.
Next Obligation.
  intros R S f a r Ha; simpl in *.
  rewrite (rig_map_mul f), Ha.
  apply rig_mul_zero_l.
Qed.

Example KernelIdeal_mem {R S : RingObject} (f : R ~{Rng}~> S)
  (a : carrier (rig_setoid R)) :
  idl_mem (KernelIdeal f) a = (rig_map f a ≈ rig_zero S).
Proof. reflexivity. Qed.

(* * ** Quotients by coextensive ideals agree / * ** 通过共延理想的商是一致的 *)

(*
 Since the PR "algebraic carriers are sets" (2026-09-17) [rquot_rel] is a
 truncation, and an [inhabited] cannot be destructed while the goal still
 wears the [Type] ascription that [@equiv] carries.  This lemma does the
 shuffle once, between two statements whose sort is [Prop] by declaration,
 so the two respectfulness obligations of [rquot_congr] stay one-liners. 

 --------
 自从 PR “代数载体是集合”（2026-09-17）以来，[rquot_rel] 是一个截断，而 [inhabited] 无法被析构，同时目标仍然带有 [Type] 的类型说明，这个类型说明是 [@equiv] 所携带的。这个引理只进行了一次交换，在两个声明中，其类型由声明是 [Prop]，因此 [rquot_congr] 的两个尊重义务仍然是一行代码。
*)
Lemma rquot_rel_mono {R : RingObject} (I I' : Ideal R)
  (H : ∀ a : carrier (rig_setoid R), idl_mem I a → idl_mem I' a)
  (x y : carrier (rig_setoid R)) : rquot_rel I x y → rquot_rel I' x y.
Proof. intros [K]; constructor; exact (H _ K). Qed.

Program Definition rquot_congr {R : RingObject} (I I' : Ideal R)
  (H1 : ∀ a : carrier (rig_setoid R), idl_mem I a → idl_mem I' a)
  (H2 : ∀ a : carrier (rig_setoid R), idl_mem I' a → idl_mem I a) :
  QuotientRing I ≅[Rng] QuotientRing I' := {|
  to := {| rig_map := {| morphism :=
    fun x : carrier (rig_setoid (QuotientRing I)) => x |} |};
  from := {| rig_map := {| morphism :=
    fun x : carrier (rig_setoid (QuotientRing I')) => x |} |}
|}.
Next Obligation.
  intros R I I' H1 H2 x y Hxy; exact (rquot_rel_mono I I' H1 x y Hxy).
Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation.
  intros R I I' H1 H2 x y Hxy; exact (rquot_rel_mono I' I H2 x y Hxy).
Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x y; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x; simpl; apply rquot_rel_refl. Qed.
Next Obligation. intros R I I' H1 H2 x; simpl; apply rquot_rel_refl. Qed.

(* * ** The degenerate ideals, named and separated / * ** 堕落的理想，被命名并分开 *)

Program Definition TrivialIdeal (R : RingObject) : Ideal R := {|
  idl_mem := fun a : carrier (rig_setoid R) => a ≈ rig_zero R
|}.
Next Obligation.
  intros R a b Hab Ha; simpl in *; now rewrite <- Hab.
Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation.
  intros R a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply rig_add_zero_l.
Qed.
Next Obligation.
  intros R r a Ha; simpl in *.
  rewrite Ha; apply rig_mul_zero_r.
Qed.
Next Obligation.
  intros R a r Ha; simpl in *.
  rewrite Ha; apply rig_mul_zero_l.
Qed.

Program Definition TotalIdeal (R : RingObject) : Ideal R := {|
  idl_mem := fun _ : carrier (rig_setoid R) => poly_unit
|}.
Next Obligation. intros R a b Hab Ha; exact ttt. Qed.
Next Obligation. intros R; exact ttt. Qed.
Next Obligation. intros R a b Ha Hb; exact ttt. Qed.
Next Obligation. intros R r a Ha; exact ttt. Qed.
Next Obligation. intros R a r Ha; exact ttt. Qed.

(*
 BOTH directions survive the truncation here, and the statement is
 unchanged.  [TrivialIdeal]'s membership is itself an `≈` on R's carrier,
 so the [inhabited] in front of it is eliminated by
 [pequiv_elim_inhabited] through R's own [rig_prop] -- no strength is
 lost, in contrast with [rquot_rel_zero_iff] at a general ideal.  AN
 EARLIER REVISION discharged the whole biconditional with one [exact]. 

 --------
 这里两边的方向都保留了截断，且该陈述保持不变。[TrivialIdeal] 的成员本身就是 R 的载体上的一个 `≈`，因此其前面的 [inhabited] 被 [pequiv_elim_inhabited] 通过 R 自身的 [rig_prop] 消除——没有任何强度损失，这与一般理想上的 [rquot_rel_zero_iff] 不同。早期的修订用一个 [exact] 就消除了整个双条件。
*)
Lemma rquot_trivial_iff (R : RingObject) (x y : carrier (rig_setoid R)) :
  rquot_rel (TrivialIdeal R) x y ↔ x ≈ y.
Proof.
  split.
  - intro K.
    apply (fst (ab_sub_eq_zero_iff (ring_ab R) x y)).
    exact (pequiv_elim_inhabited _ _ K).
  - intro Hxy.
    constructor.
    exact (snd (ab_sub_eq_zero_iff (ring_ab R) x y) Hxy).
Qed.

Lemma rquot_total_collapses (R : RingObject)
  (x y : carrier (rig_setoid R)) : rquot_rel (TotalIdeal R) x y.
Proof. constructor; exact ttt. Qed.

(* Quotienting by the whole ring gives a ring in which 1 ≈ 0, which is the zero ring up to the identification [rquot_total_collapses] supplies. / 将整个环取商会得到一个在其中 1 ≈ 0 的环，这就是零环，直到 [rquot_total_collapses] 提供的同一性为止。 *)
Lemma rquot_total_one_is_zero (R : RingObject) :
  rig_one (QuotientRing (TotalIdeal R))
    ≈ rig_zero (QuotientRing (TotalIdeal R)).
Proof. exact (rquot_total_collapses R _ _). Qed.

(*
   * ** Non-vacuity: ℤ modulo 2ℤ

   Everything above holds for every ring, so nothing yet shows the
   quotient does not collapse.  ℤ (Theory/Algebra/Rig.v's [Int_Ring])
   with the even integers is the smallest witness with a PROPER
   NONTRIVIAL ideal, and ℤ's setoid is Leibniz equality
   ([Z_eqT]), so every check below is a computation.

   NOTE that this ideal is NOT the module-level [EvenSub] of
   Instance/Mod/Quotient.v with a name changed: that one is a submodule
   of [Int_RMod] and closes under the SCALAR action only, while this one
   is an ideal of [Int_Ring] and closes under multiplication on both
   sides.  Over a commutative ring the two conditions coincide, but the
   records are different types over different objects, and this file
   does not depend on that one. 

   --------
   * ** 非空性: ℤ 模 2ℤ

   上述内容对每一个环都成立，因此目前还没有显示该商环会塌缩。ℤ（Theory/Algebra/Rig.v 的 [Int_Ring]）与偶整数是具有**恰当非平凡理想**的最小示例，并且 ℤ 的集合论等价为 Leibniz 等式（[Z_eqT]），因此下面的每一个检查都是一次计算。

   注意，这个理想 **不是** Instance/Mod/Quotient.v 中模块级别的 [EvenSub]，只是名字变了：那个是 [Int_RMod] 的一个子模，并且只在标量作用下封闭，而这个是 [Int_Ring] 的理想，并且在两边的乘法下都封闭。在交换环上，这两个条件是一致的，但记录是不同对象的不同类型，而本文件不依赖于那个文件。
*)

(* ℤ's ring operations, pinned by convertibility -- what lets [ring] and [lia] see the goals below, neither tactic seeing through [carrier]. / ℤ 的环运算，由可转换性固定——是什么让 [ring] 和 [lia] 看到下面的目标，而没有策略能看穿 [carrier]。 *)
Example zring_zero_is_0 : rig_zero Int_Ring = 0%Z := eq_refl.
Example zring_one_is_1 : rig_one Int_Ring = 1%Z := eq_refl.
Example zring_add_is_add (a b : Z) : rig_add Int_Ring a b = (a + b)%Z :=
  eq_refl.
Example zring_mul_is_mul (a b : Z) : rig_mul Int_Ring a b = (a * b)%Z :=
  eq_refl.
Example zring_neg_is_opp (a : Z) : ring_neg Int_Ring a = (- a)%Z := eq_refl.
Example zring_sub_is_minus (a b : Z) :
  ab_sub (ring_ab Int_Ring) a b = (a - b)%Z := eq_refl.

Definition ZEven (a : Z) : Type := { k : Z & a = (2 * k)%Z }.

Program Definition EvenIdeal : Ideal Int_Ring := {| idl_mem := ZEven |}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite zring_add_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.
Next Obligation.
  intros a r [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (k * r)%Z; ring.
Qed.

(* 2ℤ is PROPER: 1 is not even, so ℤ/2ℤ is not the zero ring. / 2ℤ 是真子集：1 不是偶数，所以 ℤ/2ℤ 不是零环。 *)
Theorem EvenIdeal_proper : idl_mem EvenIdeal 1%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 2ℤ is NONTRIVIAL: it contains 2, which is not zero. / 2ℤ 是非平凡的：它包含 2，而 2 不是零。 *)
Theorem EvenIdeal_nontrivial :
  idl_mem EvenIdeal 2%Z
  * ((2%Z : carrier (rig_setoid Int_Ring)) ≈ rig_zero Int_Ring → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - simpl; discriminate.
Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: 1 stays apart from 0 in ℤ/2ℤ, i.e. ℤ/2ℤ is not the zero ring. / 商环不退化：1在ℤ/2ℤ中仍然与0分开，即ℤ/2ℤ不是零环。 *)
Theorem Z2_ring_not_collapsed : rquot_rel EvenIdeal 1%Z 0%Z → False.
Proof.
  (* One extra layer since the PR "algebraic carriers are sets" (2026-09-17): [rquot_rel] is the truncation of membership, and the goal [False] is a [Prop], so the elimination is allowed. / 自从 PR “代数承载是集合” (2026-09-17) 后增加了一层：[rquot_rel] 是成员资格的截断，目标 [False] 是一个 [Prop]，因此允许消去。 *)
  intros [[k Hk]].
  assert (Hz : (1 - 0 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z2_ring_nonzero :
  rig_one (QuotientRing EvenIdeal) ≈ rig_zero (QuotientRing EvenIdeal)
    → False.
Proof. exact Z2_ring_not_collapsed. Qed.

(* ...but it does collapse 2 into 0, so the projection is not injective and the quotient is a genuine quotient rather than a relabelling. / ...但它确实将 2 压缩为 0，因此投影不是单射，商是一个真正的商，而不是重新标记。 *)
Theorem Z2_ring_collapses_two :
  rig_map (rquot_proj EvenIdeal) 2%Z ≈ rig_map (rquot_proj EvenIdeal) 0%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem rquot_proj_EvenIdeal_not_injective :
  (∀ a b : carrier (rig_setoid Int_Ring),
     rig_map (rquot_proj EvenIdeal) a ≈ rig_map (rquot_proj EvenIdeal) b
       → a ≈ b) → False.
Proof.
  intro Hinj.
  pose proof (Hinj 2%Z 0%Z Z2_ring_collapses_two) as E.
  discriminate E.
Qed.

(* ℤ/2ℤ's ARITHMETIC, computed: 1 + 1 ≈ 0 and 1 · 1 ≈ 1, so the MULTIPLICATIVE structure survives the quotient nondegenerately and the ring is not merely an abelian group in disguise. / ℤ/2ℤ 的算术，计算得出：1 + 1 ≈ 0 且 1 · 1 ≈ 1，因此乘法结构在商上非退化地保留下来，并且这个环不仅仅是伪装成阿贝尔群的结构。 *)
Theorem Z2_ring_one_plus_one :
  rig_add (QuotientRing EvenIdeal) 1%Z 1%Z
    ≈ rig_zero (QuotientRing EvenIdeal).
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem Z2_ring_one_times_one :
  rig_mul (QuotientRing EvenIdeal) 1%Z 1%Z
    ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 0%Z; reflexivity. Qed.

Theorem Z2_ring_three_is_one :
  rig_map (rquot_proj EvenIdeal) 3%Z ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 1%Z; reflexivity. Qed.

(*
 The kernel of the projection is exactly 2ℤ, in both directions -- up to
 the truncation.  AN EARLIER REVISION stated the right-hand side as the
 bare [idl_mem EvenIdeal a]; since the PR "algebraic carriers are sets"
 (2026-09-17) the left-hand side is a [Prop] (the kernel's membership IS
 the quotient's `≈`, which is [rquot_rel]), so the statement is up to
 [inhabited], exactly as [rquot_proj_kernel] is. 

 --------
 投影的核在两个方向上恰好是 2ℤ —— 直到截断。早期的修订将右侧写为裸的 [idl_mem EvenIdeal a]；自从 PR“代数承载是集合”（2026-09-17）以来，左侧是 [Prop]（核的成员资格就是商的 `≈`，即 [rquot_rel]），所以这个陈述直到 [inhabited]，与 [rquot_proj_kernel] 完全相同。
*)
Lemma EvenIdeal_is_kernel_of_proj (a : Z) :
  idl_mem (KernelIdeal (rquot_proj EvenIdeal)) a
    ↔ inhabited (idl_mem EvenIdeal a).
Proof. exact (rquot_proj_kernel EvenIdeal a). Qed.

(*
   * *** The universal property, exercised

   6ℤ ⊆ 2ℤ, so the projection ℤ ↠ ℤ/2ℤ kills 6ℤ and therefore factors
   uniquely through ℤ/6ℤ.  The mediator produced by
   [rquot_universal_element] is applied below and its value COMPUTED --
   this is what makes the universal property a working tool here rather
   than an unexercised statement. 

   --------
   * *** 通用性质的应用

   6ℤ ⊆ 2ℤ，因此投影 ℤ ↠ ℤ/2ℤ 消去 6ℤ，因此可以唯一地通过 ℤ/6ℤ 进行分解。下面应用了由
   [rquot_universal_element]  产生的中介者并计算了其值 --
   这正是使得通用性质在此成为可操作工具而不是未使用陈述的原因。
*)

Definition ZSix (a : Z) : Type := { k : Z & a = (6 * k)%Z }.

Program Definition SixIdeal : Ideal Int_Ring := {| idl_mem := ZSix |}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite zring_add_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.
Next Obligation.
  intros a r [k Hk].
  rewrite zring_mul_is_mul, Hk.
  exists (k * r)%Z; ring.
Qed.

Lemma six_kills_two (a : Z) :
  idl_mem SixIdeal a →
  rig_map (rquot_proj EvenIdeal) a ≈ rig_zero (QuotientRing EvenIdeal).
Proof.
  intros [k Hk].
  constructor.
  exists (3 * k)%Z.
  (* The membership equation is CONVERTIBLE to one about plain ℤ, and [exact] is what performs the conversion; [lia] and [ring] see through neither [carrier] nor [rig_zero]. / 成员方程可以转换为一个关于普通 ℤ 的方程，而 [exact] 是执行转换的工具；[lia] 和 [ring] 看不到 [carrier] 或 [rig_zero]。 *)
  assert (Hz : (a - 0 = 2 * (3 * k))%Z) by lia.
  exact Hz.
Qed.

Definition six_to_two : RKills SixIdeal (QuotientRing EvenIdeal) :=
  existT _ (rquot_proj EvenIdeal) six_kills_two.

Definition Z6_to_Z2 : QuotientRing SixIdeal ~{Rng}~> QuotientRing EvenIdeal :=
  rquot_med SixIdeal six_to_two.

(* The mediator is the one the CLASS produces, by convertibility. / 调解人是由 CLASS 产生的，通过可转换性。 *)
Example Z6_to_Z2_is_the_mediator :
  unique_obj (@aue_universal _ (RKillsFunctor SixIdeal)
                (QuotientRing SixIdeal) (rquot_universal_element SixIdeal)
                (QuotientRing EvenIdeal) six_to_two)
    = Z6_to_Z2.
Proof. reflexivity. Qed.

(* Its triangle, and its value: the class of 5 in ℤ/6ℤ goes to the class of 1 in ℤ/2ℤ, and not to 0. / 它的三角形及其值：在 ℤ/6ℤ 中的 5 类映射到 ℤ/2ℤ 中的 1 类，而不是映射到 0。 *)
Lemma Z6_to_Z2_triangle : Z6_to_Z2 ∘ rquot_proj SixIdeal
    ≈ rquot_proj EvenIdeal.
Proof. exact (rquot_med_commutes SixIdeal six_to_two). Qed.

Theorem Z6_to_Z2_five_is_one :
  rig_map Z6_to_Z2 5%Z ≈ rig_one (QuotientRing EvenIdeal).
Proof. constructor; exists 2%Z; reflexivity. Qed.

Theorem Z6_to_Z2_five_not_zero :
  rig_map Z6_to_Z2 5%Z ≈ rig_zero (QuotientRing EvenIdeal) → False.
Proof.
  intros [[k Hk]].
  assert (Hz : (5 - 0 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

(* And the mediator is NOT injective: 3 and 1 are apart in ℤ/6ℤ but agree in ℤ/2ℤ, so the factorization is genuinely a further quotient. / 并且中介映射不是单射：3 和 1 在 ℤ/6ℤ 中是不同的，但在 ℤ/2ℤ 中相同，所以这个分解实际上是进一步的商映射。 *)
Theorem Z6_three_apart_from_one : rquot_rel SixIdeal 3%Z 1%Z → False.
Proof.
  intros [[k Hk]].
  assert (Hz : (3 - 1 = 6 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z6_to_Z2_identifies_three_and_one :
  rig_map Z6_to_Z2 3%Z ≈ rig_map Z6_to_Z2 1%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.
