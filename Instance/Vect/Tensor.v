(*
 [Coq.QArith.QArith] is imported FIRST, before [Category.Lib]: it exports
 an [equiv] that shadows [Setoid]'s otherwise.  This is the import-order
 discipline Instance/FdVect.v records at its own head. 

 --------
 [Coq.QArith.QArith] 首先被导入，在 [Category.Lib] 之前：它导出一个 [equiv]，该 [equiv] 遮盖了 [Setoid] 的其他部分。这是 Instance/FdVect.v 在其本身开头记录的导入顺序规范。
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The tensor product of vector spaces, as a universal element

   nLab:      https://ncatlab.org/nlab/show/tensor+product
   nLab:      https://ncatlab.org/nlab/show/universal+element
   Wikipedia: https://en.wikipedia.org/wiki/Tensor_product
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §III.1, printed p. 58 — maclane:III.1:construction6
   Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed
   p. 58 — riehl:2.3:example8

   THE HEADLINE.  Mac Lane's §III.1 and Riehl's §2.3 both state the
   tensor product for VECTOR SPACES: the functor carrying a space W to
   the set of bilinear maps V × V' → W is represented by V ⊗ V', with
   universal element the canonical bilinear map ⊗.  That statement is
   [vct_tensor_universal_element] below.

   WHERE THE WORK IS.  Instance/FdVect.v defines
   [Vct_F F := RMod (field_ring F)]: a vector space over F IS an
   F-module, by DEFINITION and not by an isomorphism of categories.  So
   the construction uses nothing about fields and is carried out over an
   arbitrary [RingObject] in Instance/Mod/Tensor.v — the formal-
   expression carrier, the bilinear-maps functor, the mediator, the
   universal element and the non-degeneracy results all live there.
   This file is the vector-space reading, and because the two categories
   are the same term, every specialization below is a CONVERSION: each
   definition is stated with its [Vct_F]-level type and inhabited by the
   [RMod]-level term, so the kernel checks the identification rather
   than a transport doing it.  Nothing here reproves anything.

   WHAT THE FIELD LAYER BUYS, EXACTLY.  Not the universal property:
   Instance/Mod/Tensor.v proves that over an arbitrary ring, and
   commutativity is a hypothesis of none of the construction, the
   functor or the universal element there (that file's GENERALITY
   section states it exactly, including the one general lemma that DOES
   assume it).  What commutativity buys is that
   the tensor product does not collapse further than the classical
   construction does.  The engine file's [rbl_commutator] shows that
   every commutator of the scalar ring annihilates the image of every
   bilinear map, so over a non-commutative ring V ⊗ V' is smaller than a
   reader of the commutative case expects; [vct_commutator_vacuous]
   below is the record that over a field that identity is empty,
   obtained from [field_comm] alone.  Read the direction carefully: the
   hypothesis is absent upstream because the conclusion degenerates
   without it, NOT because the theorem is stronger than the classical
   one.

   Nothing below spends [finv] or [field_one_neq_zero].  A proper
   fraction does appear in both argument positions — as a VECTOR in
   [q_tensor_half_distinct] (½ ⊗ 1 is not 1 ⊗ 1) and as a SCALAR in
   [q_tensor_smul_half] and [q_tensor_smul_half_moves] (the action of ½
   moves 1 ⊗ 1) — so the witnesses do exercise ℚ rather than its prime
   subring; but nothing is ever inverted, and no claim is made here that
   the multiplicative-inverse structure is exercised.

   WHAT THE ℚ WITNESSES ADD OVER THE ℤ ONES.  Instance/Mod/Tensor.v
   already measures the construction at ℤ.  The point of repeating the
   measurement here is that ℤ's setoid equality is Leibniz [=], so the
   ℤ witnesses exercise no quotient at the SCALAR level; ℚ's is [Qeq],
   a genuine quotient (the terms [4#2] and [2#1] are distinct and
   [Qeq]-equal), so [Q_tensor_iso] is the only place in these two files
   where the tensor product is pinned over a scalar setoid that
   identifies distinct terms.  Test/ProbeModTensor.v guards the
   consequence: over ℤ the mediator's value at a closed generator is a
   numeral by [eq_refl], over ℚ it is not.

   WHAT IS NOT DELIVERED.  Everything the engine file's own
   WHAT IS NOT DELIVERED section lists — no bifunctoriality, no monoidal
   structure on [Vct_F F], no coefficient uniqueness, no comparison with
   Instance/Ab/Tensor.v — plus two readings specific to this level: no
   dimension theory (nothing here says dim(V ⊗ V') = dim V · dim V',
   and no connection to Instance/FdVect.v's based spaces or to
   Instance/FdVect/Tensor.v's [TensorSq], which is the diagonal square
   endofunctor of Riehl Ex 1.4.4(vii) and not a tensor product of two
   spaces at all), and no bilinear-forms specialization. 

   --------
   * * 向量空间的张量积，作为一个泛元素

   nLab:       https://ncatlab.org/nlab/show/tensor+product 
   nLab:       https://ncatlab.org/nlab/show/universal+element 
   Wikipedia:  https://en.wikipedia.org/wiki/Tensor_product 
   书籍: Mac Lane，《为工作数学家而作的范畴论》，第2版，
   GTM 5，第III.1节，第58页印刷版 — maclane:III.1:construction6
   书籍: Riehl，《语境中的范畴论》，Dover 2016，第2.3节，第58页印刷版
   — riehl:2.3:example8

   主要内容.  Mac Lane的第III.1节和Riehl的第2.3节都说明了
   向量空间的张量积：将空间W映射到双线性映射集V × V' → W的函子
   由V ⊗ V'表示，其泛元素为标准双线性映射⊗。该陈述
   在下面为[vct_tensor_universal_element]。工作的地方。Instance/FdVect.v 定义了 
   [Vct_F F := RMod (field_ring F)] ：一个 F 上的向量空间，是一个 
   F-模，这是根据定义而非范畴同构得出的。所以
   该构造不涉及域的内容，并且可以在任意 
   [RingObject] 上进行——在 Instance/Mod/Tensor.v 中——形式表达承载者、双线性映射函子、中介器、普遍元素以及非退化性结果都在这里。
   这个文件是向量空间的解读，因为这两个范畴是相同的项，下面的每个特化都是一次转换：每个定义都是以其 [Vct_F] 级别类型来陈述，并由 [RMod] 级别项填充，因此内核检查的是识别而不是通过传输来实现它。这里没有重新证明任何内容。字段层究竟提供了什么，而不是通用性质：
   Instance/Mod/Tensor.v 证明了在任意环上，并且交换律不是任何构造、函子或通用元素的假设（该文件的 GENERALITY 部分准确说明了这一点，包括唯一一个确实假设交换律的一般引理）。交换律带来的好处是张量积不会比经典构造进一步坍缩。引擎文件的 [rbl_commutator] 表明标量环的每个交换子都会消去每个双线性映射的像，因此在非交换环上，V ⊗ V' 比读者在交换情况下预期的要小；下面的 [vct_commutator_vacuous] 记录了在一个域上该恒等式为空，仅从 [field_comm] 得到。仔细阅读说明：假设在上游缺失是因为没有它结论会退化，而不是因为该定理比经典定理更强。

   下面没有使用 [finv] 或 [field_one_neq_zero]。一个适当的分数确实出现在两个论证位置——在 [q_tensor_half_distinct] 中作为一个向量（½ ⊗ 1 不是 1 ⊗ 1），并在 [q_tensor_smul_half] 和 [q_tensor_smul_half_moves] 中作为一个标量（½ 的作用移动 1 ⊗ 1）——所以这些见证确实使用 ℚ 而不是它的素数子环；但是没有任何东西被取逆，也没有声称在这里使用了乘法逆元结构。ℚ 证人在 ℤ 证人之上的补充。Instance/Mod/Tensor.v 已经在 ℤ 上测量了该构造。在这里重复测量的目的是 ℤ 的集合等价是 Leibniz  [=]，因此 ℤ 证人在标量级别上不涉及商；而 ℚ 的集合等价是 [Qeq]，一个真正的商（术语 [4#2] 和 [2#1] 是不同的，并且 [Qeq] 相等），因此 [Q_tensor_iso] 是这两个文件中唯一一个张量积固定在能够区分不同术语的标量集合等价的位置。Test/ProbeModTensor.v 保护其结果：在 ℤ 上，封闭生成元处介值是一个 [eq_refl] 的数值，而在 ℚ 上则不是。未提供的内容。引擎文件自身的“未提供内容”部分列出的所有内容——没有双函子性，没有在  [Vct_F F] 上的幺半群结构，没有系数唯一性，没有与 Instance/Ab/Tensor.v 的比较——以及两个针对该级别的特定说明：没有维度理论（这里没有说明 dim(V ⊗ V') = dim V · dim V'，也没有与 Instance/FdVect.v 的基空间或 Instance/FdVect/Tensor.v 的 [TensorSq] 相关联，后者是 Riehl 第 1.4.4(vii) 题的对角平方自函子，而根本不是两个空间的张量积），也没有双线性形式的特化。
*)

Section VectTensor.

Context (F : FieldObject).

(* * ** Bilinear maps of vector spaces / * ** 向量空间的双线性映射 *)

(*
   * The bilinear maps V × V' → W, at the vector-space level.  This is
   Instance/Mod/Tensor.v's [RBilinear] read through
   [Vct_F F = RMod (field_ring F)]. 

   --------
   * 在向量空间层面上的双线性映射 V × V' → W。这是 Instance/Mod/Tensor.v 的 [RBilinear]，通过 [Vct_F F = RMod (field_ring F)] 阅读。
*)
Definition VctBilinear (V V' W : Vct_F F) : Type := RBilinear V V' W.

Example VctBilinear_is_RBilinear (V V' W : Vct_F F) :
  VctBilinear V V' W = RBilinear V V' W := eq_refl.

(** The bilinear-maps FUNCTOR Bilin(V, V'; −) : Vct_F F ⟶ Sets. / 双线性映射函子 Bilin(V, V'; −) : Vct_F F ⟶ 集合。 *)
Definition VctBilin (V V' : Vct_F F) : Vct_F F ⟶ Sets := Bilin V V'.

(* * ** The tensor product, and its canonical bilinear map / * ** 张量积及其典型双线性映射 *)

Definition VctTensor (V V' : Vct_F F) : Vct_F F := TensorMod V V'.

Definition vct_tensor_gen (V V' : Vct_F F) :
  VctBilinear V V' (VctTensor V V') := tensor_gen.

(* * ** Mac Lane §III.1 / Riehl §2.3: ⟨V ⊗ V', ⊗⟩ is a universal element For every vector space W and every bilinear map β : V × V' → W there is one and only one linear map V ⊗ V' ⟶ W carrying ⊗ to β. / * ** Mac Lane §III.1 / Riehl §2.3：⟨V ⊗ V', ⊗⟩ 是一个泛元素 对于每一个向量空间 W 和每一个双线性映射 β : V × V' → W，都存在唯一一个线性映射 V ⊗ V' ⟶ W，将 ⊗ 映射到 β。 *)
Definition vct_tensor_universal_element (V V' : Vct_F F) :
  AUniversalElement (VctBilin V V') (VctTensor V V') :=
  tensor_universal_element V V'.

(** The same data as Mac Lane's pair ⟨r, e⟩. / 与 Mac Lane 的对 ⟨r, e⟩ 相同的数据。 *)
Definition vct_tensor_UniversalElement (V V' : Vct_F F) :
  UniversalElement (VctBilin V V') := tensor_UniversalElement V V'.

Example vct_tensor_UniversalElement_obj (V V' : Vct_F F) :
  @ue_obj (Vct_F F) (VctBilin V V') (vct_tensor_UniversalElement V V')
    = VctTensor V V' := eq_refl.

(* * ** Unique factorization, elementwise / * ** 唯一分解，每个元素 *)

Definition vct_tensor_factor {V V' W : Vct_F F} (β : VctBilinear V V' W) :
  VctTensor V V' ~{Vct_F F}~> W := tensor_factor β.

Lemma vct_tensor_factor_commutes {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (vct_tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof. exact (tensor_factor_commutes β v w). Qed.

Lemma vct_tensor_factor_unique {V V' W : Vct_F F} (β : VctBilinear V V' W)
  (k : VctTensor V V' ~{Vct_F F}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  vct_tensor_factor β ≈ k.
Proof. exact (tensor_factor_unique β k). Qed.

(*
   * ** What commutativity buys

   The engine file's collapse identity, at a field: its conclusion
   already follows from [field_comm], with no bilinear map in sight, so
   over a field it says nothing.  That is the precise sense in which the
   construction above is the classical tensor product of vector
   spaces. 

   --------
   * ** 交换性带来的好处

   引擎文件在一个域上的坍缩恒等式：它的结论已经可以从 [field_comm] 推出，而没有出现任何双线性映射，因此在域上它没有提供任何信息。这正是上述构造是向量空间经典张量积的精确意义。
*)
Lemma vct_commutator_vacuous (W : Vct_F F)
  (r s : carrier (rig_setoid (ring_rig (field_ring F))))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig (field_ring F)) r s) x
    ≈ rm_smul W (rig_mul (ring_rig (field_ring F)) s r) x.
Proof.
  exact (rbl_commutator_from_commutativity (field_comm F) W r s x).
Qed.

End VectTensor.

Arguments VctBilinear {F} V V' W.
Arguments VctBilin {F} V V'.
Arguments VctTensor {F} V V'.
Arguments vct_tensor_gen {F} V V'.
Arguments vct_tensor_universal_element {F} V V'.
Arguments vct_tensor_UniversalElement {F} V V'.
Arguments vct_tensor_factor {F V V' W} β.

(*
   * ** Non-degeneracy over ℚ

   The field as a one-dimensional space over itself, with multiplication
   as the archetypal bilinear map — the ℤ measurements of
   Instance/Mod/Tensor.v repeated over a scalar setoid whose [≈] is a
   genuine quotient. 

   --------
   * ** 在 ℚ 上的非退化性

   该域作为其自身的一维空间，以乘法作为原型双线性映射——Instance/Mod/Tensor.v 的 ℤ 测量在一个标量集合上重复，其 [≈] 是一个真正的商。
*)

Definition Q_Vct : Vct_F Q_Field := Ring_RMod (field_ring Q_Field).

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the constructor itself) — the device Instance/Mod/Free.v uses. / 索引参数仅提供一次，作为符号（因此每个符号展开为构造函数本身）——设备 Instance/Mod/Free.v 使用的方法。 *)
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qzero := (@mt_zero (field_ring Q_Field) Q_Vct Q_Vct).
Local Notation qsmul := (@mt_smul (field_ring Q_Field) Q_Vct Q_Vct).

Definition Q_mul_bilinear : VctBilinear Q_Vct Q_Vct Q_Vct.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear (field_ring Q_Field) Q_Vct Q_Vct Q_Vct Qmult
       _ _ _ _ _).
  - (* rbl_respects / rbl_尊重 *)
    intros a b Hab c d Hcd; simpl in *.
    now rewrite Hab, Hcd.
  - (* rbl_add_l *)
    intros v v' w; simpl; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; ring.
  - (* rbl_smul_l / rbl_smul_l *)
    intros r v w; simpl; ring.
  - (* rbl_smul_r: the clause that spends commutativity of ℚ / rbl_smul_r：花费有理数可交换性的子句 *)
    intros r v w; simpl; ring.
Defined.

(*
   * The factorization computes: the mediator is a fixpoint, so its value
   on a closed generator reduces — up to [≈], which here is [Qeq] and so
   is a genuine quotient step rather than a syntactic identity. 

   --------
   * 因式分解计算：中介是一个不动点，因此它在闭合生成元上的值简化——最多到 [≈]，这里是 [Qeq]，因此这是一个真正的商步骤，而不是语法上的恒等式。
*)
Example q_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

Example q_tensor_factor_computes :
  cmon_map (rm_hom (vct_tensor_factor Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. reflexivity. Qed.

(*
   * The quotient does not collapse, proved by mapping OUT through
   [tensor_med_respects]. 

   --------
   * 商不会塌缩，已通过将 OUT 映射到 [tensor_med_respects] 证明。
*)
Lemma q_tensor_gen_nonzero : mt_eq (qgen 1 1) qzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(*
   * The scalars really are ℚ: a proper fraction gives a generator
   distinct from the one at 1 — the counterpart of
   Instance/Vect/Free.v's [free_vect_half_not_one], and the one place
   below where a non-integer scalar does work. 

   --------
   * 标量确实是 ℚ：一个真分数会生成一个与 1 处不同的生成元 — 是 Instance/Vect/Free.v 中的 [free_vect_half_not_one] 的对应物，也是非整数标量生效的唯一位置下方。
*)
Lemma q_tensor_half_distinct : mt_eq (qgen (1#2) 1) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(*
   * The same fraction in SCALAR position.  The first is the action rule
   at r = ½ (the product ½·1 reducing to the term [1#2], so the
   statement typechecks by conversion); the second says the action of ½
   genuinely moves the generator, which is what makes the scalar side of
   the module structure non-degenerate over a field rather than merely
   over its prime subring. 

   --------
   * 在标量位置的相同分数。第一个是在 r = ½ 的作用规则（乘积 ½·1 化为项 [1#2]，因此通过转换语句类型检查）；第二个表示 ½ 的作用确实移动了生成元，这正是使得模结构的标量部分在域上非退化，而不仅仅是在其素子环上非退化的原因。
*)
Lemma q_tensor_smul_half : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen (1#2) 1).
Proof.
  exact (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct (1#2) 1 1).
Qed.

Lemma q_tensor_smul_half_moves : mt_eq (qsmul (1#2) (qgen 1 1)) (qgen 1 1) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Q_mul_bilinear _ _ He) as Hq.
  simpl in Hq; unfold Qeq in Hq; simpl in Hq.
  discriminate Hq.
Qed.

(*
   * ℚ ⊗_ℚ ℚ ≅ ℚ in [Vct_F Q_Field], by the same two legs as the ℤ case:
   multiplication one way, q ↦ q ⊗ 1 the other. 

   --------
   * ℚ ⊗_ℚ ℚ ≅ ℚ 在 [Vct_F Q_Field] 中，通过与 ℤ 情况相同的两条边：
   一条是乘法，另一条是 q ↦ q ⊗ 1。
*)
Program Definition q_tensor_unit :
  Q_Vct ~{Vct_F Q_Field}~> VctTensor Q_Vct Q_Vct := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun q => qgen q 1;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l (field_ring Q_Field) Q_Vct Q_Vct 1).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l (field_ring Q_Field) Q_Vct Q_Vct a b 1).
Qed.
Next Obligation.
  intros r q;
    exact (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct r q 1)).
Qed.

Program Definition Q_tensor_iso :
  @Isomorphism (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct) Q_Vct := {|
  to   := tensor_med Q_mul_bilinear;
  from := q_tensor_unit
|}.
Next Obligation.
  intro q; simpl; apply Qmult_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (q_tensor_unit ∘ tensor_med Q_mul_bilinear)
            (@id (Vct_F Q_Field) (VctTensor Q_Vct Q_Vct)) _).
  intros v w; simpl.
  (* (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w. / (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w。 *)
  refine (mte_trans (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
                       (Qmult_comm v w) (reflexivity 1)) _).
  refine (mte_trans
            (mte_sym (@mte_act_l (field_ring Q_Field) Q_Vct Q_Vct w v 1)) _).
  refine (mte_trans (@mte_act_r (field_ring Q_Field) Q_Vct Q_Vct w v 1) _).
  exact (@mte_gen (field_ring Q_Field) Q_Vct Q_Vct _ _ _ _
           (reflexivity v) (Qmult_1_r w)).
Qed.
