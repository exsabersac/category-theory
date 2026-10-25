Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * Compact closed categories / * 紧闭范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/compact+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Compact_closed_category

 A compact closed category is a symmetric monoidal category in which every
 object [X] has a (chosen) dual [X^*], i.e. it is a rigid (autonomous)
 symmetric monoidal category. Symmetry forces the left and right duals to
 coincide, so a single dual [X^*] suffices. The structure comprises:

 dual X       X^*                         (the chosen dual object)
 cc_unit X    η_X : I ~> X^* ⨂ X          (unit / coevaluation / "cup")
 cc_counit X  ε_X : X ⨂ X^* ~> I          (counit / evaluation / "cap")

 subject to the two snake / zigzag (triangle, "yanking") identities. In this
 library's notation, with λ = [unit_left], ρ = [unit_right], α =
 [tensor_assoc], and [to]/[from] the forward/inverse iso components:

 snake_left  (= id[X]):
 λ_X ∘ (ε ⨂ id) ∘ α⁻¹_{X,X^*,X} ∘ (id ⨂ η) ∘ ρ⁻¹_X

 snake_right (= id[X^*]):
 ρ_{X^*} ∘ (id ⨂ ε) ∘ α_{X^*,X,X^*} ∘ (η ⨂ id) ∘ λ⁻¹_{X^*}

 These match the Wikipedia statements λ ∘ (ε⊗id) ∘ α⁻¹ ∘ (id⊗η) ∘ ρ⁻¹ = id_A
 and ρ ∘ (id⊗ε) ∘ α ∘ (η⊗id) ∘ λ⁻¹ = id_{A^*}; the unitors here are folded
 into the identity rather than written as a separate [λ ∘ ρ⁻¹] coherence.

 Compact closed categories are the setting for finite-dimensional vector
 spaces (FdVect), the category Rel of relations, and — once a compatible
 dagger is added (a dagger-compact category) — the ZX-calculus.

 Hypergraph categories are a special case: every object is its own dual via
 [X^* := X], with unit and counit built from the special commutative
 Frobenius (SCFA) structure as [η := δ ∘ η_X] and [ε := ε_X ∘ μ]. 

 --------
 nLab：  https://ncatlab.org/nlab/show/compact+closed+category 
 维基百科：  https://en.wikipedia.org/wiki/Compact_closed_category 

 紧闭范畴是一个对称幺半范畴，其中每个对象  [X]  都有一个（选定的）对偶  [X^*] ，即它是一个刚性（自律）对称幺半范畴。对称性要求左对偶和右对偶一致，因此单个对偶  [X^*]  就足够了。该结构包括：

 对偶 X       X^*                         （选定的对偶对象）
 cc_unit X    η_X : I ~> X^* ⨂ X          （单位 / 协评 / “杯”）
 cc_counit X  ε_X : X ⨂ X^* ~> I          （余单位 / 评估 / “帽”）

 服从两个蛇形 / 锯齿形（三角形，“拉回”）恒等式。在本库的符号中，λ =  [unit_left] ，ρ =  [unit_right] ，α = [tensor_assoc] ，以及 [to] / [from] 为正向/逆向同构分量：snake_left (= id [X])：
 λ_X ∘ (ε ⨂ id) ∘ α⁻¹_{X,X^*,X} ∘ (id ⨂ η) ∘ ρ⁻¹_X

 snake_right (= id [X^*])：
 ρ_{X^*} ∘ (id ⨂ ε) ∘ α_{X^*,X,X^*} ∘ (η ⨂ id) ∘ λ⁻¹_{X^*}

 这些与维基百科中的陈述相符 λ ∘ (ε⊗id) ∘ α⁻¹ ∘ (id⊗η) ∘ ρ⁻¹ = id_A
 和 ρ ∘ (id⊗ε) ∘ α ∘ (η⊗id) ∘ λ⁻¹ = id_{A^*}；这里的单位子被合并
 成恒等映射，而不是写成单独的 [λ ∘ ρ⁻¹] 一致性。

 紧致闭合范畴是有限维向量空间（FdVect）、关系范畴 Rel 的适用环境，
 并且——一旦加入兼容的 dagger（即 dagger-紧致范畴）——
 可以用于 ZX-演算。超图范畴是一个特例：每个对象通过 [X^* := X] 都是其自身的对偶，单位和余单位由特殊交换 Frobenius (SCFA) 结构构建为 [η := δ ∘ η_X] 和 [ε := ε_X ∘ μ]。
*)

(*
 Duals as internal adjunctions: history, applications, and neighbours

 nLab:  https://ncatlab.org/nlab/show/compact+closed+category
 Paper: Kelly, "Many-variable functorial calculus. I.", in Coherence
 in Categories, Springer LNM 281, 1972
 Paper: Kelly, Laplaza, "Coherence for compact closed categories",
 Journal of Pure and Applied Algebra 19, 1980
 Paper: Abramsky, Coecke, "A categorical semantics of quantum
 protocols", LiCS 2004

 The content of the definition is that every object is an adjoint:
 [cc_unit] and [cc_counit] are the unit and counit of an adjunction
 X ⊣ X^* internal to the monoidal structure, and [snake_left] and
 [snake_right] are its triangle identities.  It follows that the
 category is closed: maps C ⨂ A ~> B correspond naturally to maps
 C ~> B ⨂ A^*, so the internal hom of A and B is representable as
 B ⨂ A^* — the closure the name records (nLab).  The same adjunction
 yields map–state duality: the name of f : A ~> B is the state
 ⌜f⌝ := (id ⨂ f) ∘ η_A : I ~> A^* ⨂ B; every morphism of that type
 is the name of a unique map A ~> B, and duality extends to a
 contravariant functor with A^{**} naturally isomorphic to A
 (Abramsky–Coecke 2004).  A compact closed category is thereby the
 degenerate star-autonomous category whose dualizing object is the
 tensor unit itself (nLab), the model of multiplicative linear logic
 in which ⊗ and ⅋ coincide; the general dualizing-object picture is
 developed in Structure/Monoidal/StarAutonomous.v.

 The notion is due to Kelly (1972, above); its coherence theory is
 Kelly–Laplaza (1980): a well-formed equation in the language of
 compact closed categories follows from the axioms precisely when
 both sides have isomorphic string diagrams.  Selinger's survey ("A
 survey of graphical languages for monoidal categories", 2009)
 states this as its Theorem 4.33, and the caveat after it records
 that Kelly–Laplaza proved the simple-signature case and that the
 fully general case does not appear in the literature.  Coherence is
 what licenses the bent-wire calculus: [cc_unit] creates a pair of
 oppositely oriented wires, [cc_counit] joins such a pair, and the
 snake identities say a bent wire may be pulled straight — whence
 "yanking".  Concretely, in Rel every object is its own dual and η_X
 relates the sole element of the unit to each pair (x, x); in
 FdVect, η_V sends 1 to Σ ē_i ⊗ e_i against a chosen basis, and
 names are exactly the passage between matrices and vectors
 (Abramsky–Coecke 2004).  Dualizability is a finiteness condition:
 FdVect and FdHilb are compact closed while their
 infinite-dimensional counterparts are not even autonomous, and the
 cobordism category under disjoint union is compact closed with
 duals given by orientation reversal (Selinger 2009).

 Every compact closed category carries a canonical trace, and
 conversely the Int construction of Joyal, Street and Verity
 ("Traced monoidal categories", Math. Proc. Camb. Phil. Soc. 119,
 1996) freely completes a traced monoidal category to a compact
 closed one, with composition given by tracing — the categorical
 backbone of Girard's Geometry of Interaction (Abramsky, Haghverdi,
 Scott, "Geometry of Interaction and Linear Combinatory Algebras",
 MSCS 12(5), 2002).  The traced interface in this library is
 Structure/Monoidal/Traced.v; neither bridge is formalized in-tree
 yet.

 The applications track these readings.  Abramsky and Coecke (2004)
 express teleportation and entanglement swapping in any compact
 closed category with biproducts, reading preparation of an
 entangled state as a name and an observational branch as a coname;
 adding a compatible dagger yields the dagger-compact setting named
 by Selinger ("Dagger compact closed categories and completely
 positive maps", ENTCS 170, 2007).  The DisCoCat model of
 natural-language meaning (Coecke, Sadrzadeh, Clark, "Mathematical
 Foundations for a Compositional Distributional Model of Meaning",
 2010) lifts Lambek pregroup type reductions to morphisms
 transforming FdVect word vectors into the meaning of the whole
 sentence.  The structure is also rigid: finite products in a
 compact closed category are automatically biproducts (Houston,
 "Finite products are biproducts in a compact closed category",
 JPAA 212, 2008), and in this library Structure/Monoidal/Collapse.v
 assumes [CompactClosed] over a relevance monoidal category to prove
 Abramsky's no-cloning collapse — uniform copying forces the
 braiding to be the identity.  Downstream of the derivation below,
 Construction/Cospan/Hypergraph.v points its clients at
 [Hypergraph_CompactClosed] for their cups and caps. 

 --------
 作为内部伴随的对偶：历史、应用及邻域

 nLab：https://ncatlab.org/nlab/show/compact+closed+category
 论文：Kelly，《多变量函子演算 I》，收录于《范畴中的相干性》，Springer LNM 281，1972
 论文：Kelly, Laplaza，《紧闭范畴的相干性》，《纯粹与应用代数杂志》19，1980
 论文：Abramsky, Coecke，《量子协议的范畴语义》，LiCS 2004定义的内容是每个对象都是一个伴随：
 [cc_unit] 和 [cc_counit] 是伴随的单位和余单位
 X ⊣ X^* 在幺半群结构内部，并且 [snake_left] 和 [snake_right] 是它的三角恒等式。由此可得该范畴是闭合的：映射 C ⨂ A ~> B 自然对应于映射 C ~> B ⨂ A^*，因此 A 和 B 的内部同态可以表示为 B ⨂ A^* —— 闭合性由名称记录（nLab）。相同的伴随关系也产生映射–态对偶：f : A ~> B 的名称是态 ⌜f⌝ := (id ⨂ f) ∘ η_A : I ~> A^* ⨂ B；每个该类型的态都是唯一映射 A ~> B 的名称，并且对偶性可以扩展为一个逆变函子，并且 A^{**} 与 A 自然同构（Abramsky–Coecke 2004）。紧闭范畴因此是退化的星自主范畴，其对偶化对象就是张量单位本身（nLab），这是乘法线性逻辑的模型，其中 ⊗ 和 ⅋ 重合；一般的对偶化对象图像在 Structure/Monoidal/StarAutonomous.v 中进行了展开。这个概念源自 Kelly（1972，上文）；其相干理论是 Kelly–Laplaza（1980）：仅当双方有同构的字符串图时，紧闭范畴语言中的一个良构方程才会从公理中推导出来。Selinger 的综述（《A survey of graphical languages for monoidal categories》，2009）将其作为定理 4.33 陈述，其后的注意事项记录了 Kelly–Laplaza 证明了简单签名的情况，而完全一般的情况尚未出现在文献中。相干性是允许弯曲线计算的依据：[cc_unit] 创建一对方向相反的导线，[cc_counit] 将这样的一对连接起来，而蛇形恒等式说明弯曲的导线可以拉直——因此有‘拉直’之称。具体来说，在 Rel 中，每个对象都是它自身的对偶，η_X 将单位的唯一元素与每一对 (x, x) 关联起来；在 FdVect 中，η_V 将 1 映射为 Σ ē_i ⊗ e_i（基于所选的基），而名字正是矩阵与向量之间的转换（Abramsky–Coecke 2004）。可对偶性是一种有限性条件：FdVect 和 FdHilb 是紧闭范畴，而它们的无限维对应物甚至都不是自治范畴，并且在不相交并集下的 cobordism 范畴是紧闭的，其对偶由取反定向给出（Selinger 2009）。每一个紧闭范畴都带有一个典型的踪迹，反过来，Joyal、Street 和 Verity 的 Int 构造（“Traced monoidal categories”，Math. Proc. Camb. Phil. Soc. 119, 1996）可以自由地将一个带追踪的幺半群范畴完成为一个紧闭范畴，其复合由追踪给出——这是 Girard《交互几何》的范畴学骨干（Abramsky, Haghverdi, Scott, “Geometry of Interaction and Linear Combinatory Algebras”, MSCS 12(5), 2002）。本库中的追踪接口在 Structure/Monoidal/Traced.v；目前两者的桥接尚未在树中形式化。这些应用程序会跟踪这些读数。Abramsky 和 Coecke (2004) 在任何带有二元积的紧闭范畴中表示量子传送和纠缠交换，将纠缠态的制备读取为一个名称，将观测分支读取为一个协名称；加入一个兼容的 dagger 后就得到了 Selinger 所命名的 dagger 紧闭环境（“Dagger 紧闭闭范畴与完全正映射”, ENTCS 170, 2007）。自然语言意义的 DisCoCat 模型（Coecke, Sadrzadeh, Clark，“组合分布式意义模型的数学基础”, 2010）将 Lambek 前群类型简约提升为将 FdVect 词向量转换为整个句子意义的态射。该结构也是刚性的：紧闭范畴中的有限积自动是双积（Houston，《有限积在紧闭范畴中是双积》，JPAA 212, 2008），在该库 Structure/Monoidal/Collapse.v 中，假设在相关单闪范畴上有 [CompactClosed]，以证明 Abramsky 的不可克隆崩塌——统一复制迫使编织为恒等。在下面推导的下游，Construction/Cospan/Hypergraph.v 指向它的客户端使用 [Hypergraph_CompactClosed] 来处理它们的杯和帽。
*)

Section CompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CompactClosed : Type := {
  (* The chosen dual object [X^*] of each object [X]. / 每个对象 [X] 的选定对偶对象 [X^*]。 *)
  dual : C -> C;

  (* Unit / coevaluation ("cup") η_X : I ~> X^* ⨂ X. / 单位 / 共评估（“杯”） η_X : I ~> X^* ⨂ X。 *)
  cc_unit   : forall X : C, I ~> dual X ⨂ X;
  (* Counit / evaluation ("cap") ε_X : X ⨂ X^* ~> I. / 余单位 / 评估（"帽"） ε_X : X ⨂ X^* ~> I。 *)
  cc_counit : forall X : C, X ⨂ dual X ~> I;

  (*
 Left snake / zigzag, "yanking" the X-strand straight:
 λ ∘ (ε ⨂ id) ∘ α⁻¹ ∘ (id ⨂ η) ∘ ρ⁻¹ ≈ id[X]. 

 --------
 左蛇形 / 锯齿形，“拉直” X-链：
 λ ∘ (ε ⨂ id) ∘ α⁻¹ ∘ (id ⨂ η) ∘ ρ⁻¹ ≈ id [X] 。
*)
  snake_left : forall X : C,
    to (@unit_left C _ X)
      ∘ bimap (cc_counit X) id[X]
      ∘ from (@tensor_assoc C _ X (dual X) X)
      ∘ bimap id[X] (cc_unit X)
      ∘ from (@unit_right C _ X)
    ≈ id[X];

  (*
 Right snake / zigzag, "yanking" the X^*-strand straight:
 ρ ∘ (id ⨂ ε) ∘ α ∘ (η ⨂ id) ∘ λ⁻¹ ≈ id[X^*]. 

 --------
 右蛇形 / 锯齿形，“拉直” X^*-链：
 ρ ∘ (id ⨂ ε) ∘ α ∘ (η ⨂ id) ∘ λ⁻¹ ≈ id [X^*] 。
*)
  snake_right : forall X : C,
    to (@unit_right C _ (dual X))
      ∘ bimap id[dual X] (cc_counit X)
      ∘ to (@tensor_assoc C _ (dual X) X (dual X))
      ∘ bimap (cc_unit X) id[dual X]
      ∘ from (@unit_left C _ (dual X))
    ≈ id[dual X]
}.

End CompactClosed.

Arguments CompactClosed C {S}.
Arguments dual {C S _} X.
Arguments cc_unit {C S _} X.
Arguments cc_counit {C S _} X.

(* * * Every hypergraph category is compact closed (self-dual) / * * 每个超图范畴都是紧闭的（自对偶的） *)

(*
 For [X^* := X] we set

 cc_unit X   := δ ∘ η : I ~> X ⨂ X
 cc_counit X := ε ∘ μ : X ⨂ X ~> I

 built from the special commutative Frobenius algebra carried by every
 object of a hypergraph category. The snake identities collapse via the
 Frobenius law together with the monoid unit and comonoid counit laws (see
 the worked proofs below); specialness ([μ ∘ δ ≈ id]) is not needed for the
 snake equations themselves. This construction is not exported as a [Global
 Instance], to avoid typeclass-search blowups: clients opt in via [Existing
 Instance Hypergraph_CompactClosed]. 

 --------
 对于 [X^* := X]，我们设置

 cc_unit X   := δ ∘ η : I ~> X ⨂ X
 cc_counit X := ε ∘ μ : X ⨂ X ~> I

 这些由超图范畴中每个对象所携带的特殊交换 Frobenius 代数构造而成。蛇形恒等式通过 Frobenius 定律以及单子单位和余单子余单位定律收缩（见下面的详细证明）；特殊性（[μ ∘ δ ≈ id]）对于蛇形方程本身不是必须的。此构造不会作为 [Global Instance] 导出，以避免类型类搜索膨胀：客户端通过 [Existing Instance Hypergraph_CompactClosed] 选择使用。
*)

Section HypergraphIsCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* Self-dual unit, given an SCFA on [X]. / 自对偶单位，给定在 [X] 上的 SCFA。 *)
Definition hcc_unit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : I ~> X ⨂ X := scfa_delta F ∘ scfa_eta F.

(* Self-dual counit, given an SCFA on [X]. / 自对偶余单位，给定 [X] 上的 SCFA。 *)
Definition hcc_counit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : X ⨂ X ~> I := scfa_epsilon F ∘ scfa_mu F.

End HypergraphIsCompactClosed.

(* * * The derivation [Hypergraph C -> CompactClosed C] / * * 推导 [Hypergraph C -> CompactClosed C] *)

(*
 Self-dual: [dual X := X], [cc_unit X := scfa_delta ∘ scfa_eta],
 [cc_counit X := scfa_epsilon ∘ scfa_mu].

 Both snake equations reduce by the same pattern:
 1. Distribute [bimap (ε∘μ) id ≈ bimap ε id ∘ bimap μ id] and dually
 [bimap id (δ∘η) ≈ bimap id δ ∘ bimap id η].
 2. Apply the Frobenius law [frob_law_left] (resp. [frob_law_right])
 to collapse [bimap μ id ∘ α⁻¹ ∘ bimap id δ] to [δ ∘ μ].
 3. Apply the monoid unit law [mu_unit_right] to collapse
 [μ ∘ bimap id η] to [unit_right], cancelling with [unit_right⁻¹].
 4. Apply the comonoid counit law [delta_counit_left] to collapse
 [bimap ε id ∘ δ] to [unit_left⁻¹], cancelling with [unit_left].

 Not exported as a [Global Instance] to avoid typeclass-search blowups;
 clients opt in with [Existing Instance Hypergraph_CompactClosed]. 

 --------
 自对偶：[dual X := X]，[cc_unit X := scfa_delta ∘ scfa_eta]，[cc_counit X := scfa_epsilon ∘ scfa_mu]。

 两条蛇形方程都按相同模式简化：
 1. 分配[bimap (ε∘μ) id ≈ bimap ε id ∘ bimap μ id]，并对偶地分配[bimap id (δ∘η) ≈ bimap id δ ∘ bimap id η]。
 2. 应用弗罗贝尼乌斯定律[frob_law_left]（或者[frob_law_right]），将[bimap μ id ∘ α⁻¹ ∘ bimap id δ]简化为[δ ∘ μ]。
 3. 应用幺半群单位律[mu_unit_right]，将[μ ∘ bimap id η]简化为[unit_right]，并与[unit_right⁻¹]抵消。
 4. 应用余半群余单位律[delta_counit_left]，将[bimap ε id ∘ δ]简化为[unit_left⁻¹]，并与[unit_left]抵消。

 未作为[Global Instance]导出，以避免类型类搜索膨胀；客户端可通过[Existing Instance Hypergraph_CompactClosed]选择启用。
*)

Section HypergraphToCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(* Re-expose the unfoldings of [cc_unit] / [cc_counit] for the self-dual construction; these isolate the [scfa_*] form for rewriting. / 重新暴露 [cc_unit] / [cc_counit] 的展开以用于自对偶构造；这些隔离出 [scfa_*] 形式以便重写。 *)
Lemma cc_unit_unfold (X : C) :
  hcc_unit X (F := scfa X) = scfa_delta (scfa X) ∘ scfa_eta (scfa X).
Proof. reflexivity. Qed.

Lemma cc_counit_unfold (X : C) :
  hcc_counit X (F := scfa X) = scfa_epsilon (scfa X) ∘ scfa_mu (scfa X).
Proof. reflexivity. Qed.

(* The snake-left calculation, abstracted away from the iso unfoldings. / 蛇形左侧的计算，从同构展开中抽象出来。 *)
Lemma hypergraph_snake_left (X : C) :
  to (@unit_left C _ X)
    ∘ bimap (hcc_counit X (F := scfa X)) id[X]
    ∘ from (@tensor_assoc C _ X X X)
    ∘ bimap id[X] (hcc_unit X (F := scfa X))
    ∘ from (@unit_right C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  (* Distribute bimap over the SCFA composites. / 将 bimap 分配到 SCFA 复合体上。 *)
  rewrite (bimap_comp_id_right (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_left (scfa_delta _) (scfa_eta _)).
  (* Bring frob_law_left into focus: bimap μ id ∘ α⁻¹ ∘ bimap id δ ≈ δ ∘ μ. / 将 frob_law_left 聚焦：bimap μ id ∘ α⁻¹ ∘ bimap id δ ≈ δ ∘ μ。 *)
  (*
 Currently: unit_left ∘ (bimap ε id ∘ bimap μ id) ∘ α⁻¹
 ∘ (bimap id δ ∘ bimap id η) ∘ unit_right⁻¹. 

 --------
 当前：unit_left ∘ (bimap ε id ∘ bimap μ id) ∘ α⁻¹ ∘ (bimap id δ ∘ bimap id η) ∘ unit_right⁻¹。
*)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap (scfa_mu _) id)).
  rewrite (comp_assoc (bimap (scfa_mu _) id ∘ from tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_left (Frobenius := scfa X)).
  (* Now: unit_left ∘ bimap ε id ∘ (δ ∘ μ) ∘ bimap id η ∘ unit_right⁻¹. / 现在：unit_left ∘ bimap ε id ∘ (δ ∘ μ) ∘ bimap id η ∘ unit_right⁻¹。 *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap id eta)).
  rewrite (mu_unit_right (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  (* Now: unit_left ∘ (bimap ε id ∘ δ) ≈ id. / 现在：unit_left ∘ (bimap ε id ∘ δ) ≈ id。 *)
  rewrite (delta_counit_left (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(* The snake-right calculation, symmetric to [snake_left] under [paws]. / 蛇形-右计算，在 [paws] 下对称于 [snake_left] 。 *)
Lemma hypergraph_snake_right (X : C) :
  to (@unit_right C _ X)
    ∘ bimap id[X] (hcc_counit X (F := scfa X))
    ∘ to (@tensor_assoc C _ X X X)
    ∘ bimap (hcc_unit X (F := scfa X)) id[X]
    ∘ from (@unit_left C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  rewrite (bimap_comp_id_left  (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_right (scfa_delta _) (scfa_eta _)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap id (scfa_mu _))).
  rewrite (comp_assoc (bimap id (scfa_mu _) ∘ to tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_right (Frobenius := scfa X)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap eta id)).
  rewrite (mu_unit_left (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  rewrite (delta_counit_right (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(*
 The derived compact-closed structure on a hypergraph category.

 [dual X := X] (self-dual), and [cc_unit] / [cc_counit] are the SCFA-derived
 morphisms [hcc_unit] / [hcc_counit]. The snake identities follow from
 [hypergraph_snake_left] and [hypergraph_snake_right]. 

 --------
 超图范畴上的派生紧闭结构。

 [dual X := X]（自对偶），以及 [cc_unit] / [cc_counit] 是由 SCFA 派生的态射 [hcc_unit] / [hcc_counit]。蛇形恒等式源自 [hypergraph_snake_left] 和 [hypergraph_snake_right]。
*)
Program Instance Hypergraph_CompactClosed : @CompactClosed C S := {|
  dual      := fun X => X;
  cc_unit   := fun X => hcc_unit X (F := scfa X);
  cc_counit := fun X => hcc_counit X (F := scfa X);

  snake_left  := hypergraph_snake_left;
  snake_right := hypergraph_snake_right
|}.

End HypergraphToCompactClosed.
