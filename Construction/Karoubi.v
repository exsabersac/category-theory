Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

(*
   * The Karoubi envelope (idempotent splitting completion) of a category. 

   --------
   * 一个范畴的 Karoubi 包络（幂等分裂完备）。
*)

(*
 nLab:      https://ncatlab.org/nlab/show/Karoubi+envelope
 Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

 The Karoubi envelope Split(C) of a category C — also called its idempotent
 splitting completion, or Cauchy completion — freely splits the idempotents
 of C.  An object is a pair (x, e) of an object x : C and an idempotent
 e : x ~> x with e ∘ e ≈ e; a morphism (x, e) ~> (y, e') is a morphism
 f : x ~> y of C absorbed by the idempotents on either side,

 e' ∘ f ≈ f      and      f ∘ e ≈ f,

 two such being equal exactly when their underlying C-morphisms are ≈, the
 absorption proofs being irrelevant.  The identity of (x, e) is e itself —
 not id[x], which need not be absorbed by e — and composition is
 composition in C, the absorption laws for a composite following from those
 of its outer factors.

 C embeds into Split(C) by x ↦ (x, id[x]) on objects and f ↦ f on
 morphisms (Karoubi_Embed); the embedding is full and faithful, both
 witnessed below by the identity on underlying morphisms.  The point of the
 construction is that in Split(C) every idempotent splits: an idempotent φ
 on (x, e) factors through the object (x, φ) as a retraction followed by a
 section, both carried by φ itself, with both triangle equations reducing
 to φ ∘ φ ≈ φ (karoubi_idem_splits, phrased via the SplitIdempotent class
 of Theory/Morphisms.v). 

 --------
 nLab：       https://ncatlab.org/nlab/show/Karoubi+envelope
 维基百科：  https://en.wikipedia.org/wiki/Karoubi_envelope

 一个范畴 C 的 Karoubi 包 Split(C) —— 也称为它的幂等元分解完成，或柯西完成 —— 自由地分解了 C 中的幂等元。一个对象是一个对 (x, e)，其中 x 是 C 的一个对象，e : x ~> x 是一个幂等元，满足 e ∘ e ≈ e；一个态射 (x, e) ~> (y, e') 是 C 中的一个态射 f : x ~> y，被两边的幂等元所吸收，即

 e' ∘ f ≈ f      且      f ∘ e ≈ f,

 两者相等当且仅当它们的基础 C 态射 ≈，吸收证明不相关。(x, e) 的恒等态射就是 e 本身 —— 而不是 id [x] ，它不一定被 e 吸收 —— 复合就是 C 中的复合，复合的吸收律由其外部因子的吸收律得到。C 通过 x ↦ (x, id [x]) 在对象上，f ↦ f 在态射上嵌入到 Split(C)（Karoubi_Embed）；该嵌入是满且忠实的，两者都由底层态射上的恒等映射体现。该构造的意义在于在 Split(C) 中每个幂等元都可以分裂：在 (x, e) 上的幂等元 φ 可以作为从对象 (x, φ) 的重traction（retraction）然后再到 section 的因子化，二者都由 φ 本身携带，且两个三角形方程简化为 φ ∘ φ ≈ φ（karoubi_idem_splits，通过 Theory/Morphisms.v 中的 SplitIdempotent 类表述）。
*)

(*
 Why idempotents are split, and where the completion is used

 nLab:  https://ncatlab.org/nlab/show/Karoubi+envelope
 nLab:  https://ncatlab.org/nlab/show/Cauchy+complete+category
 Paper: Karoubi, “K-Theory: An Introduction”, Springer 1978
 Paper: Hayashi, “Adjunction of semifunctors: categorical structures
 in nonextensional lambda calculus”, Theoretical Computer
 Science 41, 1985
 Paper: Lawvere, “Metric spaces, generalized logic, and closed
 categories”, Rendiconti del Seminario Matematico e Fisico di
 Milano 43, 1973
 Paper: Borceux, Dejean, “Cauchy completion in category theory”,
 Cahiers de Topologie et Géométrie Différentielle
 Catégoriques 27, 1986

 An idempotent e : x ~> x behaves like a projection onto a part of x,
 its image, yet in a bare category that image object need not be
 present.  The idempotent splits when there are an object y and maps
 r : x ~> y, s : y ~> x with s ∘ r ≈ e and r ∘ s ≈ id, and then y is
 the retract e carves out.  The envelope [Karoubi] adjoins exactly
 these missing retracts and nothing further: it is the universal
 enlargement of C closed under the splitting of idempotents, and
 [karoubi_idem_splits] establishes that closure within it.
 Construction/Karoubi/Universal.v records the universality — a functor
 into any idempotent-complete category extends along the embedding
 ([Karoubi_Extend]), uniquely up to isomorphism — so the envelope is a
 left-adjoint-style completion, determined up to equivalence (nLab,
 “Karoubi envelope”).

 The completion adds only structure that every functor already
 respects.  Splitting an idempotent is an absolute colimit, a colimit
 preserved by every functor out of the category, and for ordinary
 (Set-enriched) categories the conditions “idempotents split”, “all
 absolute colimits exist” and “Cauchy complete” coincide (nLab,
 “Cauchy complete category”).  The library records the last as
 [CauchyComplete], a synonym of [IdempotentsSplit], in
 Construction/Karoubi/Universal.v.  Two categories have equivalent
 presheaf categories precisely when their Cauchy completions agree,
 the content of Morita equivalence.  The tree's cone-level predicate
 for an absolute colimit is Structure/Limit/Absolute.v's
 [AbsoluteColimitCocone] (#477), beside Structure/Limit/Constant.v's
 apex-only [AbsoluteColimit]; exhibiting the splitting of an
 idempotent as one is issue #957, and is not done here.

 The two names trace a route through several subjects rather than one
 origin.  Max Karoubi split the idempotents of vector bundles in
 topological K-theory, where the pseudo-abelian, or Karoubian,
 completion of an additive category is the setting in which K-theory
 is framed (Karoubi, “K-Theory: An Introduction”, Springer 1978);
 that completion is again additive.  The term “Karoubi envelope” was
 coined not by Karoubi but by Hayashi, in a semantics of the lambda
 calculus (Hayashi, “Adjunction of semifunctors”, Theoretical
 Computer Science 41, 1985); the parallel name “Cauchy completion”
 is due to Lawvere, who read a metric space as a category enriched
 in the nonnegative reals ordered by ≥, whereupon the enriched
 Cauchy completion reproduces the ordinary completion by Cauchy
 sequences (Lawvere, 1973); that the Set-enriched instance is
 idempotent completion was settled by Borceux and Dejean (1986).

 The reach of the construction follows from the retract reading.  A
 model of the untyped lambda calculus is a reflexive object carrying
 its own function space as a retract, and the Karoubi envelope of an
 extensional lambda-model, taken as a one-object category, is
 cartesian closed (Wikipedia, “Karoubi envelope”).  That envelope is
 generated by such a reflexive object, the setting of Scott's
 representation theorem, machine-checked in (van der Leer et al.,
 “Scott's Representation Theorem and the Univalent Karoubi Envelope”,
 ITP 2025).  Read computationally, an idempotent is a normalizer, a
 program a second run leaves unchanged; splitting names the fixed
 points of that normalizer as a type of their own, the picture under
 which types are retracts of a universal object in domain-theoretic
 and realizability models.  Instance/Sets/Karoubi.v makes this
 concrete: the category of setoids is Cauchy complete ([Sets_Cauchy]),
 the splitting object of an idempotent being the sub-setoid of its
 fixed points ([sets_split_obj]).  The idempotent split here is an
 endomorphism, distinct from the idempotent monad [IdempotentMonad]
 of Construction/Reflective/Idempotent.v, which Theory/Equivalence.v
 groups beside this completion. 

 --------
 为什么幂等元是分裂的，以及完成在哪里使用

 nLab:   https://ncatlab.org/nlab/show/Karoubi+envelope 
 nLab:   https://ncatlab.org/nlab/show/Cauchy+complete+category 
 论文: Karoubi, 《K-理论：导论》，Springer 1978
 论文: Hayashi, 《半函子伴随：非外延 λ 演算中的范畴结构》，理论计算机科学 41, 1985
 论文: Lawvere, 《度量空间、广义逻辑和封闭范畴》，米兰数学与物理研讨会纪要 43, 1973
 论文: Borceux, Dejean, 《范畴论中的柯西完成》，范畴拓扑与微分几何笔记 27, 1986一个幂等元 e : x ~> x 的行为类似于将 x 投影到 x 的一部分，即它的像，但在一个裸范畴中，该像对象不一定存在。当存在一个对象 y 及映射 r : x ~> y, s : y ~> x，使得 s ∘ r ≈ e 且 r ∘ s ≈ id 时，幂等元就分裂了，那么 y 就是 e 所刻画的重截对象。包络 [Karoubi] 恰好附加这些缺失的重截，而不添加其他内容：它是 C 的幂等完备分裂下的泛增大对象，而 [karoubi_idem_splits] 在其中建立了该闭包。Construction/Karoubi/Universal.v 记录了这种普遍性——到任意幂等完备范畴的函子沿嵌入 ([Karoubi_Extend]) 唯一地（到同构）扩展——因此这个包络是一种类似左伴随的完备方式，其结果至等价唯一（nLab，“Karoubi 包络”）。完成仅添加每个函子已经遵守的结构。拆分幂等元是一个绝对余极限，一个由该范畴出的每个函子都保持的余极限，对于普通（Set-富集）范畴，条件“幂等元可拆分”、“所有绝对余极限存在”和“柯西完备”是一致的（nLab，“柯西完备范畴”）。库将最后一个记录为 [CauchyComplete]，它是 [IdempotentsSplit] 的同义词，在 Construction/Karoubi/Universal.v 中。当且仅当两个范畴的柯西完备化相同时，它们的预层范畴才是等价的，这就是 Morita 等价的内容。树的锥层谓词对于绝对余极限是 Structure/Limit/Absolute.v 的 [AbsoluteColimitCocone] (#477)，旁边是 Structure/Limit/Constant.v 的 apex-only [AbsoluteColimit]；显示了幂等的拆分作为问题 #957 的一个内容，这里没有完成。这两个名字沿着多个主题而非单一来源追溯。一点式向量丛的幂等元由Max Karoubi拆分，在拓扑K理论中，加性范畴的伪阿贝尔或Karoubian完备性是K理论构建的背景（Karoubi，《K-Theory: An Introduction》，Springer 1978）；该完备性仍然是加性的。“Karoubi 包”这一术语并非由 Karoubi 创造，而是由 Hayashi 在 λ 演算的语义中提出的（Hayashi，《半函子伴随》，理论计算机科学 41, 1985）；与之对应的名称“Cauchy 完备化”则归功于 Lawvere，他将度量空间视为以非负实数（按 ≥ 排序）为丰富对象的范畴，从而丰富的 Cauchy 完备化再现了通过 Cauchy 序列的普通完备化（Lawvere, 1973）；而 Set-丰富实例是幂等完备化这一结论，则由 Borceux 和 Dejean 在 1986 年确定。该构造的推广来源于重traction读法。无类型λ演算的模型是一个反射对象，它自身的函数空间作为一个重traction，而外延λ模型的Karoubi包络，如果作为一个单对象范畴来看，是笛卡尔闭合的（维基百科，《Karoubi envelope》）。该包络由这样的反射对象生成，这是Scott表示定理的背景，在(van der Leer 等，《Scott的表示定理与统一Karoubi包络》，ITP 2025)中经过机器检验。从计算的角度来看，一个幂等元是一个正规化器，一个程序第二次运行不会改变；分裂将该正规化器的固定点命名为它们自己的一种类型，其图景是在域理论和可实现性模型中类型作为一个通用对象的重traction。Instance/Sets/Karoubi.v 使这一点具体化：集合体范畴是柯西完备的（[Sets_Cauchy]），幂等元的分裂对象是其固定点的子集合体（[sets_split_obj]）。这里的幂等分裂是一个自同态，有别于 Construction/Reflective/Idempotent.v 中的幂等幺半群 [IdempotentMonad]，Theory/Equivalence.v 将其与这个完备性放在一起。
*)

#[local] Obligation Tactic := idtac.

Program Definition Karoubi (C : Category) : Category := {|
  obj := ∃ (x : C) (e : x ~> x), e ∘ e ≈ e;
  hom := fun X Y =>
    ∃ f : `1 X ~> `1 Y, (`1 (`2 Y) ∘ f ≈ f) ∧ (f ∘ `1 (`2 X) ≈ f);
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id := fun X => (`1 (`2 X); _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation.
  (* the hom-setoid: equivalence of the underlying C-morphisms / 同宿集：基础 C-态射的等价 *)
  intros C X Y.
  equivalence.
Qed.
Next Obligation.
  (*
 the identity on (x, e) is e; both absorption laws read e ∘ e ≈ e 

 --------
 在 (x, e) 上的恒等元是 e；两个吸收律都写作 e ∘ e ≈ e
*)
  intros C X.
  destruct X as [x [e He]]; simpl.
  split.
  - exact He.
  - exact He.
Qed.
Next Obligation.
  (*
 composition: each absorption law comes from the nearer factor 

 --------
 组成：每个吸收定律都来自较近的因素
*)
  intros C X Y Z f g.
  destruct f as [f [fl fr]], g as [g [gl gr]]; simpl in *.
  split.
  - rewrite comp_assoc, fl.
    reflexivity.
  - rewrite <- comp_assoc, gr.
    reflexivity.
Qed.
Next Obligation.
  (* compose respects ≈, inherited from C / 组成尊重 ≈，继承自 C *)
  intros C X Y Z f g Hfg h k Hhk; simpl in *.
  now rewrite Hfg, Hhk.
Qed.
Next Obligation.
  (* id_left: e_y ∘ f ≈ f is f's left absorption law / id_left: e_y ∘ f ≈ f 是 f 的左吸收律 *)
  intros C X Y f.
  destruct f as [f [fl fr]]; simpl.
  exact fl.
Qed.
Next Obligation.
  (*
 id_right: f ∘ e_x ≈ f is f's right absorption law 

 --------
 id_right：f ∘ e_x ≈ f 是 f 的右吸收律
*)
  intros C X Y f.
  destruct f as [f [fl fr]]; simpl.
  exact fr.
Qed.
Next Obligation.
  intros C X Y Z W f g h; simpl.
  apply comp_assoc.
Qed.
Next Obligation.
  intros C X Y Z W f g h; simpl.
  apply comp_assoc_sym.
Qed.

(*
 The canonical full and faithful embedding C ⟶ Split(C), sending x to the
 trivially split idempotent (x, id[x]) and acting as the identity on
 morphisms. 

 --------
 将 x 映射到平凡分裂幂等元 (x, id [x]) 并在态射上作为恒等映射的典范完全且忠实的嵌入 C ⟶ Split(C)。
*)
Program Definition Karoubi_Embed {C : Category} : C ⟶ Karoubi C := {|
  fobj := fun x => (x; (id[x]; _));
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation.
  intros C x; simpl.
  apply id_left.
Qed.
Next Obligation.
  intros C x y f; simpl.
  split.
  - apply id_left.
  - apply id_right.
Qed.
Next Obligation.
  intros C x y f g Hfg; simpl.
  exact Hfg.
Qed.
Next Obligation.
  intros C x; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; simpl.
  reflexivity.
Qed.

(*
 The embedding is full: a morphism (x, id) ~> (y, id) of Split(C) is
 carried by a C-morphism x ~> y, which is its own preimage. 

 --------
 嵌入是满的：Split(C) 的一个态射 (x, id) ~> (y, id) 由一个 C-态射 x ~> y 承载，该态射自身是它的原像。
*)
#[export] Program Instance Karoubi_Embed_Full {C : Category} :
  Full (@Karoubi_Embed C) := {
  prefmap := fun _ _ g => `1 g
}.
Next Obligation.
  intros C x y g; simpl.
  reflexivity.
Qed.

(*
 The embedding is faithful: equality of images is literally equality of the
 underlying morphisms. 

 --------
 嵌入是忠实的：图像的相等就是底层态射的字面相等。
*)
#[export] Program Instance Karoubi_Embed_Faithful {C : Category} :
  Faithful (@Karoubi_Embed C).
Next Obligation.
  intros C x y f g Hfg.
  exact Hfg.
Qed.

(*
 Every idempotent in the Karoubi envelope splits.  Given an idempotent φ on
 X = (x, e), the splitting object is (x, φ) — the underlying morphism of φ
 is itself an idempotent of C, absorbed on both sides by itself — and the
 retraction and section are both carried by φ, with s ∘ r ≈ φ and
 r ∘ s ≈ id[(x, φ)] each reducing to φ ∘ φ ≈ φ. 

 --------
 Karoubi 封闭中的每一个幂等元都是可分裂的。给定 X = (x, e) 上的幂等元 φ，其分裂对象是 (x, φ)——φ 的底层态射本身就是 C 中的一个幂等元，并且在两边都被自身吸收——收缩映射和截面映射都由 φ 承载，其中 s ∘ r ≈ φ，且 r ∘ s ≈ id [(x, φ)]，各自都可简化为 φ ∘ φ ≈ φ。
*)
Program Definition karoubi_idem_splits {C : Category} (X : Karoubi C)
        (φ : X ~{Karoubi C}~> X) (H : Idempotent φ) :
  @SplitIdempotent (Karoubi C) X (`1 X; (`1 φ; @idem _ _ _ H)) := {|
  split_idem   := φ;
  split_idem_r := (`1 φ; _);
  split_idem_s := (`1 φ; _)
|}.
Next Obligation.
  (*
 the retraction X ~> (x, φ): absorption by φ above, by e below 

 --------
 缩回 X ~> (x, φ)：φ 在上吸收，e 在下吸收
*)
  intros C X φ H; simpl.
  split.
  - exact (@idem _ _ _ H).
  - exact (snd (`2 φ)).
Qed.
Next Obligation.
  (*
 the section (x, φ) ~> X: absorption by e above, by φ below 

 --------
 该部分 (x, φ) ~> X：上方被 e 吸收，下方被 φ 吸收
*)
  intros C X φ H; simpl.
  split.
  - exact (fst (`2 φ)).
  - exact (@idem _ _ _ H).
Qed.
Next Obligation.
  (* s ∘ r ≈ φ, i.e. φ ∘ φ ≈ φ *)
  intros C X φ H; simpl.
  exact (@idem _ _ _ H).
Qed.
Next Obligation.
  (*
 r ∘ s ≈ id on (x, φ), whose identity is carried by φ 

 --------
 r ∘ s ≈ id 在 (x, φ) 上，其恒等由 φ 承载
*)
  intros C X φ H; simpl.
  exact (@idem _ _ _ H).
Qed.
