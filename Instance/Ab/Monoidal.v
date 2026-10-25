(* * * The symmetric monoidal category (Ab, ⊗, ℤ) / * * 对称单体范畴 (Ab, ⊗, ℤ) *)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §VII.1, printed pp. 163–164 (PDF pp. 171–172) —
 maclane:VII.1:remark1
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups
 nLab:      https://ncatlab.org/nlab/show/Ab
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 Mac Lane's §VII.1 names (Ab, ⊗, ℤ) as the motivating monoidal category:
 the tensor product of abelian groups is associative and unital only up to
 canonical isomorphism, and the coherence axioms were calibrated against
 exactly this example.  Instance/Ab/Tensor.v built the bifunctor
 [AbTensor_Functor : Ab ∏ Ab ⟶ Ab] together with the universal property of
 [AbTensor] and its consumable uniqueness half [tensor_hom_ext].  This file
 supplies the rest of the structure:

 - [ZAb]: the unit object ℤ, taken from the ring layer
 - [zsmul]: the ℤ-action on any abelian group, with its module laws
 - [Ab_lam]/[Ab_lam_inv], [Ab_rho]/[Ab_rho_inv]: the unitors
 - [Ab_assoc_to]/[Ab_assoc_from]: the associator
 - [Ab_Monoidal]: the monoidal structure, with both naturality
 directions for each structural isomorphism and the triangle and
 pentagon
 - [Ab_braid], [Ab_Braided], [Ab_Symmetric]: the symmetry, with both
 hexagons and the involution

 Design:

 1. THE ℤ-ACTION IS ITERATED ADDITION OVER [nat], NOT BINARY ARITHMETIC.
 [zsmul A n a] is defined by a sign split on [n] over the unary
 [nat_smul A k a] (a plain [Fixpoint] adding [a] to itself [k] times).
 Defining it directly over the binary representation would make every
 module law an induction entangled with carry propagation; over [nat]
 the laws are one-line inductions, and the only place binary structure
 surfaces is additivity in the scalar ([zsmul_add]), whose mixed-sign
 cases go through [Z.pos_sub_spec] and are closed by [lia] on the
 INDEX arithmetic alone — never on the group algebra, which stays
 entirely in `≈`.

 2. EVERY COHERENCE LAW IS A COMPUTATION ON GENERATORS.  The mediator of
 Tensor.v's universal property is a fixpoint on formal sums, so the
 structural maps compute: [Ab_assoc_to] sends [(a ⊗ b) ⊗ c] to
 [a ⊗ (b ⊗ c)] definitionally, and both routes of the pentagon send
 [((a ⊗ b) ⊗ c) ⊗ d] to the very same term.  What remains is to reach
 the generators of an ITERATED tensor, whose left factor is itself an
 arbitrary formal sum.  [AgreeOnL]/[AgreeOnR] package the three
 closure steps (zero, sum, negation) that a pair of homomorphisms out
 of a tensor always satisfies, and [tensor_hom_ext2],
 [tensor_hom_ext2r] and [tensor_hom_ext3] iterate them to depth two
 and three.  After that, associator round trips, associator
 naturality, the pentagon, braid naturality and both hexagons all
 close by [ts_refl]; the triangle closes by the one genuinely
 arithmetic fact, [ts_gen_zsmul_balance] — that a scalar may be moved
 across the tensor sign.

 3. THE UNIT IS REUSED, NOT REBUILT.  [ZAb] is Instance/Rng.v's
 [ring_ab] applied to Theory/Algebra/Rig.v's axiom-free [Int_Ring], so
 ℤ enters as the additive group of the integer ring already in tree
 rather than as a fresh record.  Its carrier setoid is `@eq Z`, which
 is why the scalar arguments of the unitors are handled by Leibniz
 reasoning ([ZAb_eq], [zsmul_int_one]) while everything else stays
 in `≈`.

 4. ONE MONOIDAL PATH ON [Ab].  Instance/Grp.v records the tree's
 policy: a [Monoidal] structure is registered as an instance only when
 it is the sole such path on its category, since a second registered
 path silently changes resolution elsewhere.  [@Monoidal Ab] has no
 other inhabitant in tree, so [Ab_Monoidal], [Ab_Braided] and
 [Ab_Symmetric] are exported instances.

 5. THE UNIVERSE ANNOTATIONS ARE LOAD-BEARING; DO NOT DROP THEM.  The
 target is [Ab_Monoidal@{s o} : Monoidal@{o s}] with BOTH levels bound
 parameters — [s] the hom/carrier level, [o] the object level, related
 by [s < o] exactly as [Ab] itself relates them.  Left to inference the
 instance instead comes out as [Monoidal@{u Set}]: nothing in a
 monoidal structure on [Ab] pushes the carrier level up, so the
 elaborator takes the least solution and [Ab] gets pinned to groups
 whose carriers live in [Set], which makes the enrichment of [Ab] over
 itself unusable for hom-objects above [Set].  Two things are needed,
 and each is necessary on its own:

 - Every definition feeding the instance carries an explicit
 declaration ([Ab_lam], [Ab_lam_inv], [Ab_rho], [Ab_rho_inv] at
 [@{s +}] over [AbObject@{s s s}]; the three isomorphisms and the
 instances at [@{s o + | s < o +}] over [Ab@{o s}]).  A declared
 universe cannot be minimized away.  The load-bearing [+] is the
 one in CONSTRAINT position: the bodies incur constraints beyond
 [s < o] (the auxiliary universes of [AbTensor], nine of them,
 and [AbTensor_Functor], EIGHT, relate to [s] and [o]), and
 without it elaboration stops with "Universe constraints are not
 implied by the ones declared".  The [+] after the universe list
 is inert here — dropping it still compiles — and is kept only
 for uniformity with the constraint one.
 (RE-MEASURED by [About] under [Set Printing Universes] after the
 PR "algebraic carriers are sets" (2026-09-17): [AbTensor] still
 binds nine universes, [AbTensor_Functor] now binds eight where
 an earlier revision of this sentence wrote seven.  Nothing else
 in the paragraph moved; the declarations it describes are
 unchanged and still load-bearing.)

 - [ZAb_one] exists so that no bare [1%Z] is elaborated at an
 UNRESOLVED [carrier ?G] position in this file.  (Where the
 [AbObject] is already pinned — as in Construction/Enriched/Ab.v's
 [@ts_gen ZAb …] applications — the projection reduces to [Z]
 before matching and a bare literal is harmless.)  The literal has sort [Set], and matching
 it against [Type@{s}] forces the rigid constraint [Set = s] rather
 than the cumulative [Set <= s] — which silently re-pins the whole
 instance even after every declaration above is in place.  The
 symptom is subtle: the type still PRINTS as [Monoidal@{o s}], with
 [Set = s] hidden in the constraint list.  [zsmul_int_one] and
 [nat_smul_int_one] are therefore stated over [ZAb_one] too.

 A related trap, should these ever be revisited: annotating the
 instance while leaving the helper definitions inferred does not break
 loudly.  [Program] silently inserts [eq_rect] transport obligations
 of the form [AbTensor ZAb x = fobj[AbTensor_Functor] (ZAb, x)],
 because the conversion those two rely on has been broken by the
 universe mismatch, and the coherence proofs then face transported
 terms instead of the generator computations of note 2.
 SCOPE.  §VII.1 also lists the sibling tensor-product monoidal
 categories — K-Mod over a commutative ring, K-algebras, graded and
 differential-graded modules, bimodules.  Each presupposes the module
 categories of issue #258 and is recorded on issue #265, not owed
 here; this file delivers the Ab case only. 

 --------
 书籍：Mac Lane, 《为实际工作的数学家分类》，第2版，§VII.1，第163–164页（PDF第171–172页）—
 maclane:VII.1:remark1
 nLab: https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups
 nLab: https://ncatlab.org/nlab/show/Ab
 维基百科: https://en.wikipedia.org/wiki/Monoidal_category

 Mac Lane 的 §VII.1 将 (Ab, ⊗, ℤ) 命名为激励的单体范畴：
 阿贝尔群的张量积仅在典范同构下具有结合性和单位元性，并且相干公理正是针对这个例子校准的。Instance/Ab/Tensor.v 构建了二值函子 [AbTensor_Functor : Ab ∏ Ab ⟶ Ab] 以及 [AbTensor] 的普遍性质和其可消耗唯一性的一半 [tensor_hom_ext]。该文件提供了其余的结构：-  [ZAb]：取自环层的单位对象ℤ
 -  [zsmul]：对任意阿贝尔群的ℤ作用，以及它的模律
 -  [Ab_lam] / [Ab_lam_inv]，[Ab_rho] / [Ab_rho_inv]：单位子
 -  [Ab_assoc_to] / [Ab_assoc_from]：结合子
 -  [Ab_Monoidal]：幺半结构，对于每个结构同构都有两个自然性方向，以及三角形和五边形
 -  [Ab_braid]，[Ab_Braided]，[Ab_Symmetric]：对称性，包含两个六边形和逆元

 设计：1. ℤ-作用是在 [nat] 上的迭代加法，而不是二进制算术。[zsmul A n a] 通过在一元的 [nat_smul A k a] 上对 [n] 进行符号分裂来定义（一个简单的 [Fixpoint]，将 [a] 自身加 [k] 次）。如果直接在二进制表示上定义它，每条模律都会成为与进位传播交织的归纳；在 [nat] 上，这些定律则是单行归纳，二进制结构唯一显现的地方是在标量（[zsmul_add]）的可加性中，其混合符号情况通过 [Z.pos_sub_spec] 处理，并且仅通过索引运算上的 [lia] 闭合——从不在群代数上闭合，群代数完全保持在 `≈` 中。2. 每一个相干律都是对生成元的运算。Tensor.v 的泛性性质的调解器是对形式和的一个不动点，因此结构映射计算如下：[Ab_assoc_to] 定义上将 [(a ⊗ b) ⊗ c] 映射到 [a ⊗ (b ⊗ c)]，并且五边形的两条路径都将 [((a ⊗ b) ⊗ c) ⊗ d] 映射到完全相同的项。剩下的任务是达到迭代张量的生成元，其左因子本身是任意形式和。[AgreeOnL] / [AgreeOnR] 打包了对张量的同态对总是满足的三步闭包操作（零，加法，取反），而 [tensor_hom_ext2]、[tensor_hom_ext2r] 和 [tensor_hom_ext3] 将它们迭代到二级和三级。之后，同调子往返、同调子自然性、五边形、编织自然性以及两个六边形都由 [ts_refl] 闭合；三角形则由唯一的真正算术事实 [ts_gen_zsmul_balance] 闭合——即标量可以通过张量符号移动。

 3. 单位被重用，而不是重建。[ZAb] 是 Instance/Rng.v 的 [ring_ab] 应用于 Theory/Algebra/Rig.v 的无公理 [Int_Ring]，因此 ℤ 作为整数环的加法群已经存在于树中，而不是作为一个新的记录。它的承载集合同构是 `@eq Z`，这就是为什么单位子的标量参数通过 Leibniz 推理 ([ZAb_eq], [zsmul_int_one]) 处理，而其他所有内容保持在 `≈` 中。4. 在 [Ab] 上的一个单一幺半群路径。Instance/Grp.v 记录了树的策略：只有当 [Monoidal] 结构在其类别上是唯一的此类路径时，它才被注册为实例，因为第二条注册路径会在其他地方静默地改变解析。[@Monoidal Ab] 在树中没有其他居民，因此 [Ab_Monoidal]、[Ab_Braided] 和 [Ab_Symmetric] 被导出为实例。5. 宇宙注释具有承重性；不要丢弃它们。目标是 [Ab_Monoidal@{s o} : Monoidal@{o s}]，具有绑定的双层参数——[s] 同态/承载层，[o] 对象层，通过 [s < o] 关联，正如 [Ab] 本身关联它们一样。如果让实例通过推断得到，它反而会成为 [Monoidal@{u Set}]：在 [Ab] 的幺半群结构中没有任何东西会提升承载层，所以展开器会取最小解，并且 [Ab] 会被固定到其承载者位于 [Set] 的群，这使得 [Ab] 对自身的强化在高于 [Set] 的同态对象中不可用。需要两件事，每一件都是必要的：- 每个为实例提供的定义都带有显式声明（[Ab_lam]、[Ab_lam_inv]、[Ab_rho]、[Ab_rho_inv] 在 [@{s +}] 上的 [AbObject@{s s s}]；三个同构和在 [@{s o + | s < o +}] 上的实例 [Ab@{o s}]）。声明的宇宙不能被最小化去掉。承重的 [+] 位于约束(CONSTRAINT)位置：这些主体会产生超出 [s < o] 的约束（[AbTensor] 的辅助宇宙，共九个，以及 [AbTensor_Functor]，八个，与 [s] 和 [o] 相关），没有它，展开将停止并显示“宇宙约束不由声明的约束推出”。宇宙列表之后的 [+] 在这里是惰性的——即使删除它仍然可以编译——保留它只是为了与约束部分的一致性。(由 [About] 在 [Set Printing Universes] 下重新测量，在 PR “代数载体是集合”（2026-09-17）之后：[AbTensor] 仍然绑定九个宇宙，[AbTensor_Functor] 现在绑定八个，而本句的早期版本写作七个。段落中的其他内容没有移动；它所描述的声明保持不变，仍然是支撑性的。)- [ZAb_one] 的存在是为了防止在此文件中未解决的 [carrier ?G] 位置上出现未展开的 [1%Z]。（当 [AbObject] 已经固定时——如在 Construction/Enriched/Ab.v 的 [@ts_gen ZAb …] 应用中——投影会在匹配前简化为 [Z]，裸字面量是无害的。）该字面量的类型为 [Set]，将其与 [Type@{s}] 匹配会强制 rigid 约束 [Set = s] 而不是累积约束 [Set <= s]——即使在上述所有声明都到位后，也会静默地重新固定整个实例。症状很微妙：类型仍然显示为 [Monoidal@{o s}]，约束列表中 [Set = s] 被隐藏。因此 [zsmul_int_one] 和 [nat_smul_int_one] 也被声明在 [ZAb_one] 上。一个相关的陷阱，如果这些问题将来再次被讨论：在注释实例时，如果保留辅助定义为推断形式，并不会立即产生错误。[Program] 会静默地插入 [eq_rect] 形式的传输义务 [AbTensor ZAb x = fobj[AbTensor_Functor] (ZAb, x)]，因为这两者依赖的转换已被宇宙不匹配破坏，然后相干性证明面对的是传输后的项，而不是注释 2 中的生成器计算。
 范围。§VII.1 同时列出了兄弟张量积单体范畴——在交换环上的 K-模、K-代数、分级和微分分级模、双模。每一个都假定了第 #258 号问题中的模范畴，并在第 #265 号问题中有记录，这里无需赘述；此文件仅提供 Ab 的情况。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** Elementary group calculations Four rearrangements used throughout. They are stated at [AbObject] so that they apply equally to a tensor product, which is one. / * ** 初等群计算 整个过程中使用了四种重排方法。它们在 [AbObject] 处给出，因此同样适用于张量积（即其中之一）。 *)

(* (x + y) - y ≈ x. *)
Lemma ab_add_neg_cancel (A : AbObject) (x y : carrier A) :
  cmon_plus A (cmon_plus A x y) (ab_neg A y) ≈ x.
Proof.
  rewrite cmon_plus_assoc, ab_neg_right.
  apply cmon_plus_zero_r.
Qed.

(* x - (y + x) ≈ -y. *)
Lemma ab_neg_add_cancel (A : AbObject) (x y : carrier A) :
  cmon_plus A x (ab_neg A (cmon_plus A y x)) ≈ ab_neg A y.
Proof.
  rewrite ab_neg_plus.
  rewrite (cmon_plus_comm A (ab_neg A y) (ab_neg A x)).
  rewrite <- cmon_plus_assoc.
  rewrite ab_neg_right.
  apply cmon_plus_zero_l.
Qed.

(*
   * ** The ℤ-action

   [nat_smul A k a] is [a] added to itself [k] times.  All the module laws
   are inductions on [k]; none of them mentions the integers.

   The [zsmul] laws below are the full module API — additivity in each
   argument, preservation of the unit, of zero and of negation, and
   compatibility with homomorphisms.  The coherence proofs of this file
   consume [zsmul_one], [zsmul_plus], [zsmul_add] and [zsmul_hom];
   [zsmul_zero_r] and [zsmul_neg_r] complete the set for callers, since
   this is the only place the action is defined. 

   --------
   * ** ℤ-作用

   [nat_smul A k a] 是将 [a] 加到自身 [k] 次。所有模律都是关于 [k] 的归纳；没有一个提到整数。

   下面的 [zsmul] 定律是完整的模 API — 对每个参数的加法性、单位元、零和取反的保持性，以及与同态的兼容性。此文件的相干性证明使用了 [zsmul_one]、[zsmul_plus]、[zsmul_add] 和 [zsmul_hom]；[zsmul_zero_r] 和 [zsmul_neg_r] 完成了调用者需要的集合，因为这是定义作用的唯一地方。
*)

Fixpoint nat_smul (A : AbObject) (k : nat) (a : carrier A) : carrier A :=
  match k with
  | O   => cmon_zero A
  | S j => cmon_plus A a (nat_smul A j a)
  end.

Lemma nat_smul_respects (A : AbObject) (k : nat) (a b : carrier A) :
  a ≈ b → nat_smul A k a ≈ nat_smul A k b.
Proof.
  intro Hab.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - exact (cmon_plus_respects A _ _ Hab _ _ IH).
Qed.

Lemma nat_smul_add (A : AbObject) (j k : nat) (a : carrier A) :
  nat_smul A (j + k) a
    ≈ cmon_plus A (nat_smul A j a) (nat_smul A k a).
Proof.
  induction j as [|j IH]; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - rewrite IH.
    symmetry; apply cmon_plus_assoc.
Qed.

Lemma nat_smul_plus (A : AbObject) (k : nat) (a b : carrier A) :
  nat_smul A k (cmon_plus A a b)
    ≈ cmon_plus A (nat_smul A k a) (nat_smul A k b).
Proof.
  induction k as [|j IH]; simpl.
  - symmetry; apply cmon_plus_zero_l.
  - rewrite IH.
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
Qed.

Lemma nat_smul_zero (A : AbObject) (k : nat) :
  nat_smul A k (cmon_zero A) ≈ cmon_zero A.
Proof.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - rewrite IH; apply cmon_plus_zero_l.
Qed.

Lemma nat_smul_neg (A : AbObject) (k : nat) (a : carrier A) :
  nat_smul A k (ab_neg A a) ≈ ab_neg A (nat_smul A k a).
Proof.
  induction k as [|j IH]; simpl.
  - symmetry; apply ab_neg_zero.
  - rewrite IH.
    symmetry; apply ab_neg_plus.
Qed.

Lemma nat_smul_hom {A B : AbObject} (f : AbHom A B) (k : nat)
      (a : carrier A) :
  cmon_map f (nat_smul A k a) ≈ nat_smul B k (cmon_map f a).
Proof.
  induction k as [|j IH]; simpl.
  - apply cmon_map_zero.
  - rewrite cmon_map_plus, IH; reflexivity.
Qed.

(* The integer action: iterate, then negate if the scalar is negative. / 整数操作：迭代，然后如果标量为负数则取反。 *)
Definition zsmul (A : AbObject) (n : Z) (a : carrier A) : carrier A :=
  match n with
  | Z0     => cmon_zero A
  | Zpos p => nat_smul A (Pos.to_nat p) a
  | Zneg p => ab_neg A (nat_smul A (Pos.to_nat p) a)
  end.

(* The three sign-case computations, so that later steps can rewrite with them rather than depend on how far [simpl] chooses to unfold. / 三个符号情况的计算，以便后续步骤可以用它们重写，而不是依赖于 [simpl] 选择展开的程度。 *)
Lemma zsmul_Z0 (A : AbObject) (a : carrier A) :
  zsmul A Z0 a ≈ cmon_zero A.
Proof. reflexivity. Qed.

Lemma zsmul_Zpos (A : AbObject) (p : positive) (a : carrier A) :
  zsmul A (Z.pos p) a ≈ nat_smul A (Pos.to_nat p) a.
Proof. reflexivity. Qed.

Lemma zsmul_Zneg (A : AbObject) (p : positive) (a : carrier A) :
  zsmul A (Z.neg p) a ≈ ab_neg A (nat_smul A (Pos.to_nat p) a).
Proof. reflexivity. Qed.

Lemma zsmul_respects (A : AbObject) (n : Z) (a b : carrier A) :
  a ≈ b → zsmul A n a ≈ zsmul A n b.
Proof.
  intro Hab.
  destruct n as [|p|p].
  - reflexivity.
  - exact (nat_smul_respects A (Pos.to_nat p) a b Hab).
  - exact (ab_neg_respects A _ _ (nat_smul_respects A (Pos.to_nat p) a b Hab)).
Qed.

Lemma zsmul_one (A : AbObject) (a : carrier A) : zsmul A 1%Z a ≈ a.
Proof. exact (cmon_plus_zero_r A a). Qed.

Lemma zsmul_plus (A : AbObject) (n : Z) (a b : carrier A) :
  zsmul A n (cmon_plus A a b)
    ≈ cmon_plus A (zsmul A n a) (zsmul A n b).
Proof.
  destruct n as [|p|p].
  - symmetry; exact (cmon_plus_zero_l A (cmon_zero A)).
  - exact (nat_smul_plus A (Pos.to_nat p) a b).
  - refine (transitivity
              (ab_neg_respects A _ _ (nat_smul_plus A (Pos.to_nat p) a b)) _).
    exact (ab_neg_plus A _ _).
Qed.

Lemma zsmul_zero_r (A : AbObject) (n : Z) :
  zsmul A n (cmon_zero A) ≈ cmon_zero A.
Proof.
  destruct n as [|p|p].
  - reflexivity.
  - exact (nat_smul_zero A (Pos.to_nat p)).
  - refine (transitivity
              (ab_neg_respects A _ _ (nat_smul_zero A (Pos.to_nat p))) _).
    exact (ab_neg_zero A).
Qed.

Lemma zsmul_neg_r (A : AbObject) (n : Z) (a : carrier A) :
  zsmul A n (ab_neg A a) ≈ ab_neg A (zsmul A n a).
Proof.
  destruct n as [|p|p].
  - symmetry; exact (ab_neg_zero A).
  - exact (nat_smul_neg A (Pos.to_nat p) a).
  - exact (ab_neg_respects A _ _ (nat_smul_neg A (Pos.to_nat p) a)).
Qed.

Lemma zsmul_hom {A B : AbObject} (f : AbHom A B) (n : Z) (a : carrier A) :
  cmon_map f (zsmul A n a) ≈ zsmul B n (cmon_map f a).
Proof.
  destruct n as [|p|p].
  - apply cmon_map_zero.
  - exact (nat_smul_hom f (Pos.to_nat p) a).
  - refine (transitivity (ab_map_neg f _) _).
    exact (ab_neg_respects B _ _ (nat_smul_hom f (Pos.to_nat p) a)).
Qed.

(*
 The mixed-sign heart of additivity in the scalar: [Z.pos_sub p q] acts as
 the difference of the two iterated sums.  The three comparison cases are
 settled by the corresponding [nat] splitting plus one cancellation. 

 --------
 标量中可加性的混合符号心：[Z.pos_sub p q] 表现为两个迭代和的差异。三种比较情况通过对应的 [nat] 拆分加一次消去来解决。
*)
Lemma zsmul_pos_sub (A : AbObject) (p q : positive) (a : carrier A) :
  zsmul A (Z.pos_sub p q) a
    ≈ cmon_plus A (nat_smul A (Pos.to_nat p) a)
                  (ab_neg A (nat_smul A (Pos.to_nat q) a)).
Proof.
  (* The comparison is split on the [comparison] value rather than through [Pos.compare_spec]: the latter is a [Prop], and this goal lives in [Type], where a [Prop] may not be eliminated. / 比较是基于[comparison]值进行的，而不是通过[Pos.compare_spec]：后者是一个[Prop]，并且这个目标存在于[Type]，其中[Prop]可能无法被消除。 *)
  rewrite Z.pos_sub_spec.
  destruct (p ?= q)%positive eqn:Hcmp.
  - assert (Heq : p = q) by (apply Pos.compare_eq; exact Hcmp).
    subst q.
    rewrite zsmul_Z0.
    symmetry; apply ab_neg_right.
  - (* p < q: the difference is negative / p < q：差值为负 *)
    assert (Hlt : (p < q)%positive)
      by (apply Pos.compare_lt_iff; exact Hcmp).
    rewrite zsmul_Zneg.
    rewrite (Pos2Nat.inj_sub q p Hlt).
    assert (Hidx : ((Pos.to_nat q - Pos.to_nat p) + Pos.to_nat p
                      = Pos.to_nat q)%nat).
    { assert (Hn : (Pos.to_nat p < Pos.to_nat q)%nat)
        by (apply Pos2Nat.inj_lt; exact Hlt).
      lia. }
    assert (Hsplit : nat_smul A (Pos.to_nat q) a
              ≈ cmon_plus A (nat_smul A (Pos.to_nat q - Pos.to_nat p) a)
                            (nat_smul A (Pos.to_nat p) a)).
    { transitivity (nat_smul A
                      ((Pos.to_nat q - Pos.to_nat p) + Pos.to_nat p) a).
      - rewrite Hidx; reflexivity.
      - apply nat_smul_add. }
    symmetry.
    rewrite Hsplit.
    apply ab_neg_add_cancel.
  - (* q < p: the difference is positive / q < p：差值为正 *)
    assert (Hgt : (q < p)%positive)
      by (apply Pos.compare_gt_iff; exact Hcmp).
    rewrite zsmul_Zpos.
    rewrite (Pos2Nat.inj_sub p q Hgt).
    assert (Hidx : ((Pos.to_nat p - Pos.to_nat q) + Pos.to_nat q
                      = Pos.to_nat p)%nat).
    { assert (Hn : (Pos.to_nat q < Pos.to_nat p)%nat)
        by (apply Pos2Nat.inj_lt; exact Hgt).
      lia. }
    assert (Hsplit : nat_smul A (Pos.to_nat p) a
              ≈ cmon_plus A (nat_smul A (Pos.to_nat p - Pos.to_nat q) a)
                            (nat_smul A (Pos.to_nat q) a)).
    { transitivity (nat_smul A
                      ((Pos.to_nat p - Pos.to_nat q) + Pos.to_nat q) a).
      - rewrite Hidx; reflexivity.
      - apply nat_smul_add. }
    symmetry.
    rewrite Hsplit.
    apply ab_add_neg_cancel.
Qed.

Lemma zsmul_add (A : AbObject) (n m : Z) (a : carrier A) :
  zsmul A (n + m)%Z a ≈ cmon_plus A (zsmul A n a) (zsmul A m a).
Proof.
  destruct n as [|p|p]; destruct m as [|q|q].
  - symmetry; exact (cmon_plus_zero_l A (cmon_zero A)).
  - symmetry; exact (cmon_plus_zero_l A _).
  - symmetry; exact (cmon_plus_zero_l A _).
  - symmetry; exact (cmon_plus_zero_r A _).
  - (* both positive / 两者都是正面的 *)
    transitivity (nat_smul A (Pos.to_nat p + Pos.to_nat q) a).
    + rewrite <- Pos2Nat.inj_add.
      exact (zsmul_Zpos A (p + q) a).
    + exact (nat_smul_add A (Pos.to_nat p) (Pos.to_nat q) a).
  - (* positive plus negative / 正加负 *)
    exact (zsmul_pos_sub A p q a).
  - symmetry; exact (cmon_plus_zero_r A _).
  - (* negative plus positive / 负加正 *)
    refine (transitivity (zsmul_pos_sub A q p a) _).
    apply cmon_plus_comm.
  - (* both negative / 两者都是负面的 *)
    transitivity (ab_neg A (nat_smul A (Pos.to_nat p + Pos.to_nat q) a)).
    + rewrite <- Pos2Nat.inj_add.
      exact (zsmul_Zneg A (p + q) a).
    + refine (transitivity
                (ab_neg_respects A _ _
                   (nat_smul_add A (Pos.to_nat p) (Pos.to_nat q) a)) _).
      exact (ab_neg_plus A _ _).
Qed.

(*
   * ** The unit object ℤ

   Instance/Rng.v's [ring_ab] applied to Theory/Algebra/Rig.v's [Int_Ring]:
   the additive group of the integer ring, already in tree and axiom-free.
   Its hom-setoid equality is Leibniz `=` on [Z], which is the one place in
   this file where `=` is the right relation on carrier elements. 

   --------
   * ** 单位对象 ℤ

   Instance/Rng.v 的 [ring_ab] 应用于 Theory/Algebra/Rig.v 的 [Int_Ring]：
   整数环的加法群，已经是树状且无公理。
   它的同态集合等式是 [Z] 上的 Leibniz `=`，这是此文件中唯一
   `=` 是载体元素上的正确关系的地方。
*)

Definition ZAb : AbObject := ring_ab Int_Ring.

(*
 The generator of ℤ, named rather than written inline.  A bare [1%Z] at a
 [carrier ZAb] position carries sort [Set] and pins the carrier universe
 to it (design note 5); routed through this constant the level stays a
 bound parameter. 

 --------
 ℤ 的生成元，被命名而不是内联书写。在 [carrier ZAb] 位置的一个裸 [1%Z] 承载 [Set] 类型并将载体宇宙固定到它（设计说明 5）；通过这个常数路由时，级别保持为绑定参数。
*)
Definition ZAb_one : carrier ZAb := 1%Z.

Lemma ZAb_eq (n m : carrier ZAb) : n ≈ m → n = m.
Proof. intro Hn; exact Hn. Qed.

(* Iterating 1 in ℤ counts. / 在 ℤ 中迭代 1 是有效的。 *)
Lemma nat_smul_int_one (k : nat) : nat_smul ZAb k ZAb_one = Z.of_nat k.
Proof.
  induction k as [|j IH].
  - reflexivity.
  - (* [change] rather than [simpl]: the addition of [ZAb] is [Z.add] only after unfolding through [ring_ab] and [rig_cmon], and [lia] needs to see it. / [change] 而不是 [simpl]：只有在通过 [ring_ab] 和 [rig_cmon] 展开后，[ZAb] 的添加才是 [Z.add]，并且 [lia] 需要看到它。 *)
    change (nat_smul ZAb (S j) ZAb_one)
      with (Z.add 1%Z (nat_smul ZAb j ZAb_one)).
    rewrite IH.
    lia.
Qed.

(*
 The ℤ-action on ℤ itself at the generator 1 is the identity: this is what
 makes the unitors mutually inverse. 

 --------
 在生成元 1 上，ℤ 对 ℤ 本身的作用是恒等的：这就是使单元元互为逆的原因。
*)
Lemma zsmul_int_one (n : Z) : zsmul ZAb n ZAb_one = n.
Proof.
  destruct n as [|p|p].
  - reflexivity.
  - change (zsmul ZAb (Z.pos p) ZAb_one)
      with (nat_smul ZAb (Pos.to_nat p) ZAb_one).
    rewrite nat_smul_int_one.
    apply positive_nat_Z.
  - change (zsmul ZAb (Z.neg p) ZAb_one)
      with (Z.opp (nat_smul ZAb (Pos.to_nat p) ZAb_one)).
    rewrite nat_smul_int_one, positive_nat_Z.
    reflexivity.
Qed.

(*
   * ** Calculations inside a tensor product

   Every statement here is phrased with [ts_eq] and proved from the
   constructors of Tensor.v's quotient, so that no conversion between the
   relation and the ambient `≈` is ever needed. 

   --------
   * ** 张量积中的计算

   这里的每个陈述都使用 [ts_eq] 表述，并从 Tensor.v 的商的构造函数中证明，因此从未需要在该关系与周围的 `≈` 之间进行转换。
*)

Section TensorCalculus.

Context {G H : AbObject}.

(* In a group, an idempotent element is zero. / 在一个群中，一个幂等元素是零。 *)
Lemma ts_idem_zero (s : tsum G H) :
  ts_eq (ts_plus s s) s → ts_eq s ts_zero.
Proof.
  intro Hs.
  refine (te_trans (te_sym (te_zero_l s)) _).
  refine (te_trans (te_plus (te_sym (te_neg_l s)) (ts_refl s)) _).
  refine (te_trans (te_assoc _ _ _) _).
  refine (te_trans (te_plus (ts_refl (ts_neg s)) Hs) _).
  exact (te_neg_l s).
Qed.

(* Additive inverses are determined. / 加法逆元已确定。 *)
Lemma ts_neg_unique (s t : tsum G H) :
  ts_eq (ts_plus t s) ts_zero → ts_eq t (ts_neg s).
Proof.
  intro Hts.
  refine (te_sym _).
  refine (te_trans (te_sym (te_zero_l (ts_neg s))) _).
  refine (te_trans (te_plus (te_sym Hts) (ts_refl (ts_neg s))) _).
  refine (te_trans (te_assoc t s (ts_neg s)) _).
  refine (te_trans (te_plus (ts_refl t)
                     (te_trans (te_comm s (ts_neg s)) (te_neg_l s))) _).
  exact (te_trans (te_comm t ts_zero) (te_zero_l t)).
Qed.

(* Middle-four exchange. / 中四交换 *)
Lemma ts_interchange (s t u v : tsum G H) :
  ts_eq (ts_plus (ts_plus s t) (ts_plus u v))
        (ts_plus (ts_plus s u) (ts_plus t v)).
Proof.
  refine (te_trans (te_assoc s t (ts_plus u v)) _).
  refine (te_trans (te_plus (ts_refl s) (te_sym (te_assoc t u v))) _).
  refine (te_trans (te_plus (ts_refl s)
                     (te_plus (te_comm t u) (ts_refl v))) _).
  refine (te_trans (te_plus (ts_refl s) (te_assoc u t v)) _).
  exact (te_sym (te_assoc s u (ts_plus t v))).
Qed.

Lemma ts_neg_plus (s t : tsum G H) :
  ts_eq (ts_neg (ts_plus s t)) (ts_plus (ts_neg s) (ts_neg t)).
Proof.
  refine (te_sym (ts_neg_unique _ _ _)).
  refine (te_trans (ts_interchange (ts_neg s) (ts_neg t) s t) _).
  refine (te_trans (te_plus (te_neg_l s) (te_neg_l t)) _).
  exact (te_zero_l ts_zero).
Qed.

(* A generator with a zero component is zero: the bilinearity rule makes it idempotent. / 一个具有零分量的生成器就是零：双线性规则使其幂等。 *)
Lemma ts_gen_zero_l (h : carrier H) :
  ts_eq (@ts_gen G H (cmon_zero G) h) ts_zero.
Proof.
  apply ts_idem_zero.
  refine (te_trans (te_sym (te_bilin_l (cmon_zero G) (cmon_zero G) h)) _).
  exact (te_gen (cmon_plus_zero_l G (cmon_zero G)) (reflexivity h)).
Qed.

Lemma ts_gen_zero_r (g : carrier G) :
  ts_eq (@ts_gen G H g (cmon_zero H)) ts_zero.
Proof.
  apply ts_idem_zero.
  refine (te_trans (te_sym (te_bilin_r g (cmon_zero H) (cmon_zero H))) _).
  exact (te_gen (reflexivity g) (cmon_plus_zero_l H (cmon_zero H))).
Qed.

(* Negation may be moved out of either component. / 否定可以从任一组成部分中移出。 *)
Lemma ts_gen_neg_l (g : carrier G) (h : carrier H) :
  ts_eq (ts_gen (ab_neg G g) h) (ts_neg (ts_gen g h)).
Proof.
  apply ts_neg_unique.
  refine (te_trans (te_sym (te_bilin_l (ab_neg G g) g h)) _).
  refine (te_trans (te_gen (ab_neg_left G g) (reflexivity h)) _).
  exact (ts_gen_zero_l h).
Qed.

Lemma ts_gen_neg_r (g : carrier G) (h : carrier H) :
  ts_eq (ts_gen g (ab_neg H h)) (ts_neg (ts_gen g h)).
Proof.
  apply ts_neg_unique.
  refine (te_trans (te_sym (te_bilin_r g (ab_neg H h) h)) _).
  refine (te_trans (te_gen (reflexivity g) (ab_neg_left H h)) _).
  exact (ts_gen_zero_r g).
Qed.

(* Iterated addition may be moved out of either component. / 迭代加法可以移出任一组件。 *)
Lemma ts_gen_nat_smul_l (k : nat) (g : carrier G) (h : carrier H) :
  ts_eq (ts_gen (nat_smul G k g) h)
        (nat_smul (AbTensor G H) k (ts_gen g h)).
Proof.
  induction k as [|j IH].
  - exact (ts_gen_zero_l h).
  - refine (te_trans (te_bilin_l g (nat_smul G j g) h) _).
    exact (te_plus (ts_refl (ts_gen g h)) IH).
Qed.

Lemma ts_gen_nat_smul_r (k : nat) (g : carrier G) (h : carrier H) :
  ts_eq (ts_gen g (nat_smul H k h))
        (nat_smul (AbTensor G H) k (ts_gen g h)).
Proof.
  induction k as [|j IH].
  - exact (ts_gen_zero_r g).
  - refine (te_trans (te_bilin_r g h (nat_smul H j h)) _).
    exact (te_plus (ts_refl (ts_gen g h)) IH).
Qed.

(*
 The one genuinely arithmetic coherence fact: a scalar crosses the tensor
 sign.  This is what proves the triangle identity. 

 --------
 唯一真正的算术一致性事实：一个标量穿过张量符号。这就是证明三角恒等式的原因。
*)
Lemma ts_gen_zsmul_balance (n : Z) (g : carrier G) (h : carrier H) :
  ts_eq (ts_gen (zsmul G n g) h) (ts_gen g (zsmul H n h)).
Proof.
  destruct n as [|p|p].
  - refine (te_trans (ts_gen_zero_l h) _).
    exact (te_sym (ts_gen_zero_r g)).
  - refine (te_trans (ts_gen_nat_smul_l (Pos.to_nat p) g h) _).
    exact (te_sym (ts_gen_nat_smul_r (Pos.to_nat p) g h)).
  - refine (te_trans (ts_gen_neg_l (nat_smul G (Pos.to_nat p) g) h) _).
    refine (te_trans (te_neg (ts_gen_nat_smul_l (Pos.to_nat p) g h)) _).
    refine (te_trans
              (te_neg (te_sym (ts_gen_nat_smul_r (Pos.to_nat p) g h))) _).
    exact (te_sym (ts_gen_neg_r g (nat_smul H (Pos.to_nat p) h))).
Qed.

End TensorCalculus.

(*
   * ** Reaching the generators of an iterated tensor

   [tensor_hom_ext] reduces an equation between homomorphisms out of
   [AbTensor G H] to the generators [ts_gen x h] — but [x] ranges over all
   of [G], and when [G] is itself a tensor its elements are arbitrary
   formal sums.  The predicate "the two homomorphisms agree on generators
   with left component [x]" is closed under zero, sum and negation, which
   is exactly what lets an induction descend one level.  Recording those
   three steps once makes the depth-two and depth-three extensionality
   principles short. 

   --------
   * ** 到达迭代张量的生成元

   [tensor_hom_ext] 将一个关于同态的方程简化为 [AbTensor G H] 的生成元 [ts_gen x h] — 但是 [x] 在整个 [G] 中变化，当 [G] 本身是一个张量时，它的元素是任意形式的和。谓词“两个同态在左分量为 [x] 的生成元上相等”在零、求和和取负下是封闭的，这正是让归纳可以下降一层的原因。只记录这三个步骤一次，就可以使二层和三层的外延性原理简洁。
*)

Section GeneratorClosure.

Context {G H K : AbObject}.
Context (f g : AbHom (AbTensor G H) K).

Definition AgreeOnL (x : carrier G) : Type :=
  ∀ h : carrier H, cmon_map f (ts_gen x h) ≈ cmon_map g (ts_gen x h).

Definition AgreeOnR (u : carrier H) : Type :=
  ∀ x : carrier G, cmon_map f (ts_gen x u) ≈ cmon_map g (ts_gen x u).

Lemma agreeL_respects (x y : carrier G) : x ≈ y → AgreeOnL x → AgreeOnL y.
Proof.
  intros Hxy Hx h.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (te_gen (symmetry Hxy) (reflexivity h))) _).
  refine (transitivity (Hx h) _).
  exact (proper_morphism (cmon_map g) _ _
           (te_gen Hxy (reflexivity h))).
Qed.

Lemma agreeL_zero : AgreeOnL (cmon_zero G).
Proof.
  intro h.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (ts_gen_zero_l h)) _).
  refine (transitivity (cmon_map_zero f) _).
  refine (transitivity (symmetry (cmon_map_zero g)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (ts_gen_zero_l h))).
Qed.

Lemma agreeL_plus (x y : carrier G) :
  AgreeOnL x → AgreeOnL y → AgreeOnL (cmon_plus G x y).
Proof.
  intros Hx Hy h.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (te_bilin_l x y h)) _).
  refine (transitivity (cmon_map_plus f _ _) _).
  refine (transitivity (cmon_plus_respects K _ _ (Hx h) _ _ (Hy h)) _).
  refine (transitivity (symmetry (cmon_map_plus g _ _)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (te_bilin_l x y h))).
Qed.

Lemma agreeL_neg (x : carrier G) : AgreeOnL x → AgreeOnL (ab_neg G x).
Proof.
  intros Hx h.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (ts_gen_neg_l x h)) _).
  refine (transitivity (ab_map_neg f _) _).
  refine (transitivity (ab_neg_respects K _ _ (Hx h)) _).
  refine (transitivity (symmetry (ab_map_neg g _)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (ts_gen_neg_l x h))).
Qed.

Lemma agreeR_respects (u v : carrier H) : u ≈ v → AgreeOnR u → AgreeOnR v.
Proof.
  intros Huv Hu x.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (te_gen (reflexivity x) (symmetry Huv))) _).
  refine (transitivity (Hu x) _).
  exact (proper_morphism (cmon_map g) _ _
           (te_gen (reflexivity x) Huv)).
Qed.

Lemma agreeR_zero : AgreeOnR (cmon_zero H).
Proof.
  intro x.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (ts_gen_zero_r x)) _).
  refine (transitivity (cmon_map_zero f) _).
  refine (transitivity (symmetry (cmon_map_zero g)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (ts_gen_zero_r x))).
Qed.

Lemma agreeR_plus (u v : carrier H) :
  AgreeOnR u → AgreeOnR v → AgreeOnR (cmon_plus H u v).
Proof.
  intros Hu Hv x.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (te_bilin_r x u v)) _).
  refine (transitivity (cmon_map_plus f _ _) _).
  refine (transitivity (cmon_plus_respects K _ _ (Hu x) _ _ (Hv x)) _).
  refine (transitivity (symmetry (cmon_map_plus g _ _)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (te_bilin_r x u v))).
Qed.

Lemma agreeR_neg (u : carrier H) : AgreeOnR u → AgreeOnR (ab_neg H u).
Proof.
  intros Hu x.
  refine (transitivity (proper_morphism (cmon_map f) _ _
                          (ts_gen_neg_r x u)) _).
  refine (transitivity (ab_map_neg f _) _).
  refine (transitivity (ab_neg_respects K _ _ (Hu x)) _).
  refine (transitivity (symmetry (ab_map_neg g _)) _).
  exact (proper_morphism (cmon_map g) _ _ (te_sym (ts_gen_neg_r x u))).
Qed.

End GeneratorClosure.

Arguments AgreeOnL {G H K} f g x.
Arguments AgreeOnR {G H K} f g u.

(*
 Depth two, left-nested: agreeing on [(a ⊗ b) ⊗ c] suffices.  The outer
 [ts_gen] carries its indices explicitly: with them implicit, the inner
 generator would be elaborated at [tsum X Y] before the outer tensor is
 known, and [carrier ?G] does not unify with a bare [tsum]. 

 --------
 深度为二，左嵌套：同意 [(a ⊗ b) ⊗ c] 就足够了。外层 [ts_gen] 明确携带其索引：如果索引是隐式的，内部生成器将在外层张量已知之前在 [tsum X Y] 处展开，并且 [carrier ?G] 无法与裸 [tsum] 统一。
*)
Lemma tensor_hom_ext2 {X Y Z K : AbObject}
      (f g : AbHom (AbTensor (AbTensor X Y) Z) K) :
  (∀ (a : carrier X) (b : carrier Y) (c : carrier Z),
      cmon_map f (@ts_gen (AbTensor X Y) Z (ts_gen a b) c)
        ≈ cmon_map g (@ts_gen (AbTensor X Y) Z (ts_gen a b) c)) →
  ∀ s, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen.
  apply (tensor_hom_ext f g).
  intros x c; revert c.
  change (AgreeOnL f g x).
  induction x as [a b| |x1 IH1 x2 IH2|x IH].
  - intro c; exact (Hgen a b c).
  - exact (agreeL_zero f g).
  - exact (agreeL_plus f g x1 x2 IH1 IH2).
  - exact (agreeL_neg f g x IH).
Qed.

(* Depth two, right-nested: agreeing on [a ⊗ (b ⊗ c)] suffices. / 深度二，右嵌套：同意 [a ⊗ (b ⊗ c)] 就足够了。 *)
Lemma tensor_hom_ext2r {X Y Z K : AbObject}
      (f g : AbHom (AbTensor X (AbTensor Y Z)) K) :
  (∀ (a : carrier X) (b : carrier Y) (c : carrier Z),
      cmon_map f (@ts_gen X (AbTensor Y Z) a (ts_gen b c))
        ≈ cmon_map g (@ts_gen X (AbTensor Y Z) a (ts_gen b c))) →
  ∀ s, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen.
  apply (tensor_hom_ext f g).
  intros a u; revert a.
  change (AgreeOnR f g u).
  induction u as [b c| |u1 IH1 u2 IH2|u IH].
  - intro a; exact (Hgen a b c).
  - exact (agreeR_zero f g).
  - exact (agreeR_plus f g u1 u2 IH1 IH2).
  - exact (agreeR_neg f g u IH).
Qed.

(* Depth three, fully left-nested: what the pentagon needs. / 深度三，完全左嵌套：五角大楼所需要的。 *)
Lemma tensor_hom_ext3 {X Y Z W K : AbObject}
      (f g : AbHom (AbTensor (AbTensor (AbTensor X Y) Z) W) K) :
  (∀ (a : carrier X) (b : carrier Y) (c : carrier Z) (d : carrier W),
      cmon_map f (@ts_gen (AbTensor (AbTensor X Y) Z) W
                    (@ts_gen (AbTensor X Y) Z (ts_gen a b) c) d)
        ≈ cmon_map g (@ts_gen (AbTensor (AbTensor X Y) Z) W
                        (@ts_gen (AbTensor X Y) Z (ts_gen a b) c) d)) →
  ∀ s, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen.
  apply (tensor_hom_ext f g).
  intros t d; revert d.
  change (AgreeOnL f g t).
  induction t as [s c| |t1 IH1 t2 IH2|t IH].
  - induction s as [a b| |s1 IHs1 s2 IHs2|s IHs].
    + intro d; exact (Hgen a b c d).
    + exact (agreeL_respects f g _ _
               (te_sym (@ts_gen_zero_l (AbTensor X Y) Z c))
               (agreeL_zero f g)).
    + exact (agreeL_respects f g _ _
               (te_sym (@te_bilin_l (AbTensor X Y) Z s1 s2 c))
               (agreeL_plus f g _ _ IHs1 IHs2)).
    + exact (agreeL_respects f g _ _
               (te_sym (@ts_gen_neg_l (AbTensor X Y) Z s c))
               (agreeL_neg f g _ IHs)).
  - exact (agreeL_zero f g).
  - exact (agreeL_plus f g t1 t2 IH1 IH2).
  - exact (agreeL_neg f g t IH).
Qed.

(*
   * ** The unitors

   [Ab_lam] is the factorization of the bilinear map (n, a) ↦ n·a through
   the tensor; its inverse sends a to 1 ⊗ a.  One round trip is
   [zsmul_one]; the other is [ts_gen_zsmul_balance] together with
   [zsmul_int_one].

   From here to the end of the file the universe declarations are part of
   the statements, not decoration: see design note 5.  Objects of [Ab] are
   [AbObject@{s s s}] and the category itself is [Ab@{o s}] with [s < o]. 

   --------
   * ** 单位元器

   [Ab_lam] 是二线性映射 (n, a) ↦ n·a 通过张量的分解；它的逆将 a 发送到 1 ⊗ a。一次往返是
   [zsmul_one]；另一次是 [ts_gen_zsmul_balance] 以及
   [zsmul_int_one]。

   从这里到文件末尾，宇宙声明是语句的一部分，而不是装饰：参见设计说明 5。[Ab] 的对象是
   [AbObject@{s s s}]，并且该范畴本身是 [Ab@{o s}]，带有 [s < o]。
*)

Program Definition Ab_lam@{s +} (A : AbObject@{s s s}) :
  AbHom (AbTensor ZAb@{s s s} A) A :=
  tensor_ump (@Build_Bilinear ZAb@{s s s} A A (fun n a => zsmul A n a) _ _ _).
Next Obligation.
  intros A n n' Hn a a' Ha.
  pose proof (ZAb_eq n n' Hn) as Hn'.
  rewrite <- Hn'.
  exact (zsmul_respects A n a a' Ha).
Qed.
Next Obligation.
  intros A n n' a.
  exact (zsmul_add A n n' a).
Qed.
Next Obligation.
  intros A n a a'.
  exact (zsmul_plus A n a a').
Qed.

Program Definition Ab_lam_inv@{s +} (A : AbObject@{s s s}) :
  AbHom A (AbTensor ZAb@{s s s} A) := {|
  cmon_map := {| morphism := fun a : carrier A => @ts_gen ZAb@{s s s} A ZAb_one a |}
|}.
Next Obligation.
  intros A a a' Ha.
  exact (te_gen (reflexivity ZAb_one) Ha).
Qed.
Next Obligation.
  intros A.
  exact (ts_gen_zero_r ZAb_one).
Qed.
Next Obligation.
  intros A a b.
  exact (te_bilin_r ZAb_one a b).
Qed.

Program Definition Ab_rho@{s +} (A : AbObject@{s s s}) :
  AbHom (AbTensor A ZAb@{s s s}) A :=
  tensor_ump (@Build_Bilinear A ZAb@{s s s} A (fun a n => zsmul A n a) _ _ _).
Next Obligation.
  intros A a a' Ha n n' Hn.
  pose proof (ZAb_eq n n' Hn) as Hn'.
  rewrite <- Hn'.
  exact (zsmul_respects A n a a' Ha).
Qed.
Next Obligation.
  intros A a a' n.
  exact (zsmul_plus A n a a').
Qed.
Next Obligation.
  intros A a n n'.
  exact (zsmul_add A n n' a).
Qed.

Program Definition Ab_rho_inv@{s +} (A : AbObject@{s s s}) :
  AbHom A (AbTensor A ZAb@{s s s}) := {|
  cmon_map := {| morphism := fun a : carrier A => @ts_gen A ZAb@{s s s} a ZAb_one |}
|}.
Next Obligation.
  intros A a a' Ha.
  exact (te_gen Ha (reflexivity ZAb_one)).
Qed.
Next Obligation.
  intros A.
  exact (ts_gen_zero_l ZAb_one).
Qed.
Next Obligation.
  intros A a b.
  exact (te_bilin_l a b ZAb_one).
Qed.

(*
   * ** The associator

   Built in two stages.  For a fixed [c] the inner mediator sends
   [a ⊗ b] to [a ⊗ (b ⊗ c)]; the outer mediator then sends [s ⊗ c] to
   the value of the inner one at [s].  Bilinearity of the outer map in
   [c] is not a computation on generators — it is an induction over the
   formal sum [s], since [s] is what the inner mediator consumes. 

   --------
   * ** 结合器

   分为两个阶段构建。对于固定的 [c]，内部中介将 [a ⊗ b] 发送到 [a ⊗ (b ⊗ c)]；然后外部中介将 [s ⊗ c] 发送到内部中介在 [s] 的值。外部映射在 [c] 上的双线性不是对生成元的计算——它是对形式和 [s] 的归纳，因为 [s] 是内部中介所消耗的。
*)

Program Definition Ab_assoc_inner (X Y Z : AbObject) (c : carrier Z) :
  AbHom (AbTensor X Y) (AbTensor X (AbTensor Y Z)) :=
  tensor_ump (@Build_Bilinear X Y (AbTensor X (AbTensor Y Z))
    (fun a b => @ts_gen X (AbTensor Y Z) a (ts_gen b c)) _ _ _).
Next Obligation.
  intros X Y Z c a a' Ha b b' Hb.
  exact (@te_gen X (AbTensor Y Z) a a' (ts_gen b c) (ts_gen b' c)
           Ha (te_gen Hb (reflexivity c))).
Qed.
Next Obligation.
  intros X Y Z c a a' b.
  exact (@te_bilin_l X (AbTensor Y Z) a a' (ts_gen b c)).
Qed.
Next Obligation.
  intros X Y Z c a b b'.
  refine (te_trans
            (@te_gen X (AbTensor Y Z)
               a a
               (ts_gen (cmon_plus Y b b') c)
               (cmon_plus (AbTensor Y Z) (ts_gen b c) (ts_gen b' c))
               (reflexivity a) (te_bilin_l b b' c)) _).
  exact (@te_bilin_r X (AbTensor Y Z) a (ts_gen b c) (ts_gen b' c)).
Qed.

Lemma Ab_assoc_inner_respects (X Y Z : AbObject) (c c' : carrier Z) :
  c ≈ c' →
  ∀ s : carrier (AbTensor X Y),
    cmon_map (Ab_assoc_inner X Y Z c) s
      ≈ cmon_map (Ab_assoc_inner X Y Z c') s.
Proof.
  intros Hc.
  apply (tensor_hom_ext (Ab_assoc_inner X Y Z c) (Ab_assoc_inner X Y Z c')).
  intros a b; simpl.
  exact (@te_gen X (AbTensor Y Z) a a (ts_gen b c) (ts_gen b c')
           (reflexivity a) (te_gen (reflexivity b) Hc)).
Qed.

Lemma Ab_assoc_inner_add_r (X Y Z : AbObject) (c c' : carrier Z)
      (s : carrier (AbTensor X Y)) :
  cmon_map (Ab_assoc_inner X Y Z (cmon_plus Z c c')) s
    ≈ cmon_plus (AbTensor X (AbTensor Y Z))
        (cmon_map (Ab_assoc_inner X Y Z c) s)
        (cmon_map (Ab_assoc_inner X Y Z c') s).
Proof.
  induction s as [a b| |s1 IH1 s2 IH2|s IH]; simpl.
  - refine (te_trans
              (@te_gen X (AbTensor Y Z)
                 a a
                 (ts_gen b (cmon_plus Z c c'))
                 (cmon_plus (AbTensor Y Z) (ts_gen b c) (ts_gen b c'))
                 (reflexivity a) (te_bilin_r b c c')) _).
    exact (@te_bilin_r X (AbTensor Y Z) a (ts_gen b c) (ts_gen b c')).
  - exact (te_sym (te_zero_l ts_zero)).
  - refine (te_trans (te_plus IH1 IH2) _).
    exact (ts_interchange _ _ _ _).
  - refine (te_trans (te_neg IH) _).
    exact (ts_neg_plus _ _).
Qed.

Program Definition Ab_assoc_to (X Y Z : AbObject) :
  AbHom (AbTensor (AbTensor X Y) Z) (AbTensor X (AbTensor Y Z)) :=
  tensor_ump (@Build_Bilinear (AbTensor X Y) Z (AbTensor X (AbTensor Y Z))
    (fun s c => cmon_map (Ab_assoc_inner X Y Z c) s) _ _ _).
Next Obligation.
  intros X Y Z s s' Hs c c' Hc.
  refine (transitivity
            (proper_morphism (cmon_map (Ab_assoc_inner X Y Z c)) _ _ Hs) _).
  exact (Ab_assoc_inner_respects X Y Z c c' Hc s').
Qed.
Next Obligation.
  intros X Y Z s s' c.
  exact (cmon_map_plus (Ab_assoc_inner X Y Z c) s s').
Qed.
Next Obligation.
  intros X Y Z s c c'.
  exact (Ab_assoc_inner_add_r X Y Z c c' s).
Qed.

Program Definition Ab_assoc_from_inner (X Y Z : AbObject) (a : carrier X) :
  AbHom (AbTensor Y Z) (AbTensor (AbTensor X Y) Z) :=
  tensor_ump (@Build_Bilinear Y Z (AbTensor (AbTensor X Y) Z)
    (fun b c => @ts_gen (AbTensor X Y) Z (ts_gen a b) c) _ _ _).
Next Obligation.
  intros X Y Z a b b' Hb c c' Hc.
  exact (@te_gen (AbTensor X Y) Z (ts_gen a b) (ts_gen a b') c c'
           (te_gen (reflexivity a) Hb) Hc).
Qed.
Next Obligation.
  intros X Y Z a b b' c.
  refine (te_trans
            (@te_gen (AbTensor X Y) Z
               (ts_gen a (cmon_plus Y b b'))
               (cmon_plus (AbTensor X Y) (ts_gen a b) (ts_gen a b'))
               c c
               (te_bilin_r a b b') (reflexivity c)) _).
  exact (@te_bilin_l (AbTensor X Y) Z (ts_gen a b) (ts_gen a b') c).
Qed.
Next Obligation.
  intros X Y Z a b c c'.
  exact (@te_bilin_r (AbTensor X Y) Z (ts_gen a b) c c').
Qed.

Lemma Ab_assoc_from_inner_respects (X Y Z : AbObject) (a a' : carrier X) :
  a ≈ a' →
  ∀ u : carrier (AbTensor Y Z),
    cmon_map (Ab_assoc_from_inner X Y Z a) u
      ≈ cmon_map (Ab_assoc_from_inner X Y Z a') u.
Proof.
  intros Ha.
  apply (tensor_hom_ext (Ab_assoc_from_inner X Y Z a)
                        (Ab_assoc_from_inner X Y Z a')).
  intros b c; simpl.
  exact (@te_gen (AbTensor X Y) Z (ts_gen a b) (ts_gen a' b) c c
           (te_gen Ha (reflexivity b)) (reflexivity c)).
Qed.

Lemma Ab_assoc_from_inner_add_l (X Y Z : AbObject) (a a' : carrier X)
      (u : carrier (AbTensor Y Z)) :
  cmon_map (Ab_assoc_from_inner X Y Z (cmon_plus X a a')) u
    ≈ cmon_plus (AbTensor (AbTensor X Y) Z)
        (cmon_map (Ab_assoc_from_inner X Y Z a) u)
        (cmon_map (Ab_assoc_from_inner X Y Z a') u).
Proof.
  induction u as [b c| |u1 IH1 u2 IH2|u IH]; simpl.
  - refine (te_trans
              (@te_gen (AbTensor X Y) Z
                 (ts_gen (cmon_plus X a a') b)
                 (cmon_plus (AbTensor X Y) (ts_gen a b) (ts_gen a' b))
                 c c
                 (te_bilin_l a a' b) (reflexivity c)) _).
    exact (@te_bilin_l (AbTensor X Y) Z (ts_gen a b) (ts_gen a' b) c).
  - exact (te_sym (te_zero_l ts_zero)).
  - refine (te_trans (te_plus IH1 IH2) _).
    exact (ts_interchange _ _ _ _).
  - refine (te_trans (te_neg IH) _).
    exact (ts_neg_plus _ _).
Qed.

Program Definition Ab_assoc_from (X Y Z : AbObject) :
  AbHom (AbTensor X (AbTensor Y Z)) (AbTensor (AbTensor X Y) Z) :=
  tensor_ump (@Build_Bilinear X (AbTensor Y Z) (AbTensor (AbTensor X Y) Z)
    (fun a u => cmon_map (Ab_assoc_from_inner X Y Z a) u) _ _ _).
Next Obligation.
  intros X Y Z a a' Ha u u' Hu.
  refine (transitivity
            (proper_morphism (cmon_map (Ab_assoc_from_inner X Y Z a))
               _ _ Hu) _).
  exact (Ab_assoc_from_inner_respects X Y Z a a' Ha u').
Qed.
Next Obligation.
  intros X Y Z a a' u.
  exact (Ab_assoc_from_inner_add_l X Y Z a a' u).
Qed.
Next Obligation.
  intros X Y Z a u u'.
  exact (cmon_map_plus (Ab_assoc_from_inner X Y Z a) u u').
Qed.

(** ** The structural isomorphisms / ** 结构同构 *)

Program Definition Ab_unit_left_iso@{s o + | s < o +} (x : AbObject@{s s s}) :
  @Isomorphism Ab@{o s} (AbTensor ZAb@{s s s} x) x := {|
  to   := Ab_lam x;
  from := Ab_lam_inv x
|}.
Next Obligation.
  intros x a; simpl.
  exact (zsmul_one x a).
Qed.
Next Obligation.
  intros x s; revert s.
  apply tensor_hom_ext.
  intros n a; simpl.
  refine (te_trans (te_sym (@ts_gen_zsmul_balance ZAb x n ZAb_one a)) _).
  rewrite (zsmul_int_one n).
  exact (ts_refl _).
Qed.

Program Definition Ab_unit_right_iso@{s o + | s < o +} (x : AbObject@{s s s}) :
  @Isomorphism Ab@{o s} (AbTensor x ZAb@{s s s}) x := {|
  to   := Ab_rho x;
  from := Ab_rho_inv x
|}.
Next Obligation.
  intros x a; simpl.
  exact (zsmul_one x a).
Qed.
Next Obligation.
  intros x s; revert s.
  apply tensor_hom_ext.
  intros a n; simpl.
  refine (te_trans (@ts_gen_zsmul_balance x ZAb n a ZAb_one) _).
  rewrite (zsmul_int_one n).
  exact (ts_refl _).
Qed.

Program Definition Ab_tensor_assoc_iso@{s o + | s < o +} (x y z : AbObject@{s s s}) :
  @Isomorphism Ab@{o s} (AbTensor (AbTensor x y) z) (AbTensor x (AbTensor y z)) := {|
  to   := Ab_assoc_to x y z;
  from := Ab_assoc_from x y z
|}.
Next Obligation.
  intros x y z s; revert s.
  apply tensor_hom_ext2r.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  intros x y z s; revert s.
  apply tensor_hom_ext2.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.

(*
   * ** The monoidal structure

   Each naturality square and each coherence law reduces, through the
   extensionality principles above, to a computation on generators. 

   --------
   * ** 单体结构

   每个自然性方阵和每个相干律都通过上述外延性原理归结为对生成元的计算。
*)

#[export] Program Instance Ab_Monoidal@{s o + | s < o +} :
  @Monoidal Ab@{o s} := {|
  I            := ZAb;
  tensor       := AbTensor_Functor;
  unit_left    := Ab_unit_left_iso;
  unit_right   := Ab_unit_right_iso;
  tensor_assoc := Ab_tensor_assoc_iso
|}.
Next Obligation.
  (* to_unit_left_natural / 向左单位自然 *)
  intros x y g s; revert s.
  apply tensor_hom_ext.
  intros n a; simpl.
  exact (zsmul_hom g n a).
Qed.
Next Obligation.
  (* from_unit_left_natural / 来自左侧的单位，自然 *)
  intros x y g a; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* to_unit_right_natural / 向右自然移动单位 *)
  intros x y g s; revert s.
  apply tensor_hom_ext.
  intros a n; simpl.
  exact (zsmul_hom g n a).
Qed.
Next Obligation.
  (* from_unit_right_natural / 来自右侧的自然单位 *)
  intros x y g a; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* to_tensor_assoc_natural / 到张量关联自然 *)
  intros x y z w v u g h i s; revert s.
  apply tensor_hom_ext2.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* from_tensor_assoc_natural / 来自张量关联自然 *)
  intros x y z w v u g h i s; revert s.
  apply tensor_hom_ext2r.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* triangle_identity / 三角恒等式 *)
  intros x y s; revert s.
  apply tensor_hom_ext2.
  intros a n b; simpl.
  exact (@ts_gen_zsmul_balance x y n a b).
Qed.
Next Obligation.
  (* pentagon_identity / 五边形恒等式 *)
  intros x y z w s; revert s.
  apply tensor_hom_ext3.
  intros a b c d; simpl.
  exact (ts_refl _).
Qed.

(*
   * ** The symmetry

   The braiding is the factorization of (a, b) ↦ b ⊗ a.  Its naturality,
   its involutivity and both hexagons are generator computations: each
   side sends a generator to the same term. 

   --------
   * ** 对称性

   编织是 (a, b) ↦ b ⊗ a 的分解。它的自然性、它的自反性以及两个六边形都是生成元计算：每一边都会将一个生成元映射到相同的项。
*)

Program Definition Ab_braid (A B : AbObject) :
  AbHom (AbTensor A B) (AbTensor B A) :=
  tensor_ump (@Build_Bilinear A B (AbTensor B A)
    (fun a b => ts_gen b a) _ _ _).
Next Obligation.
  intros A B a a' Ha b b' Hb.
  exact (te_gen Hb Ha).
Qed.
Next Obligation.
  intros A B a a' b.
  exact (te_bilin_r b a a').
Qed.
Next Obligation.
  intros A B a b b'.
  exact (te_bilin_l b b' a).
Qed.

#[export] Program Instance Ab_Braided@{s o + | s < o +} :
  @BraidedMonoidal Ab@{o s} := {|
  braided_is_monoidal := Ab_Monoidal;
  braid               := Ab_braid
|}.
Next Obligation.
  (* braid_natural / 自然编辫 *)
  intros x y g z w h s; revert s.
  apply tensor_hom_ext.
  intros a c; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* hexagon_identity / 六边形身份 *)
  intros x y z s; revert s.
  apply tensor_hom_ext2.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  (* hexagon_identity_sym / 六边形身份符 *)
  intros x y z s; revert s.
  apply tensor_hom_ext2r.
  intros a b c; simpl.
  exact (ts_refl _).
Qed.

#[export] Program Instance Ab_Symmetric@{s o + | s < o +} :
  @SymmetricMonoidal Ab@{o s} := {|
  symmetric_is_braided := Ab_Braided
|}.
Next Obligation.
  (* braid_invol / 辫子卷入 *)
  intros x y s; revert s.
  apply tensor_hom_ext.
  intros a b; simpl.
  exact (ts_refl _).
Qed.
