Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Instance.Fact.

Generalizable All Variables.

(*
 Orthogonal factorization systems.

 nLab:      https://ncatlab.org/nlab/show/orthogonal+factorization+system
 https://ncatlab.org/nlab/show/factorization+system
 Wikipedia: https://en.wikipedia.org/wiki/Factorization_system

 An (E, M)-factorization of a morphism f : x ~> y, for two classes of
 morphisms E and M on C, is a middle object together with an E-morphism
 followed by an M-morphism composing to f:

 x --e--> mid --m--> y,        m ∘ e ≈ f.

 An orthogonal factorization system (OFS) on C consists of two such
 classes E and M, each respecting the hom-setoid equivalence ≈, such that
 every morphism carries an (E, M)-factorization and every E-morphism is
 orthogonal to every M-morphism in the sense of Theory/Orthogonality.v:
 each commuting square with an E-morphism on the left and an M-morphism
 on the right has a unique diagonal filler.

 The classical consequences developed here:

 - [factorization_unique]: any two (E, M)-factorizations of the same
 morphism are connected by an isomorphism of middle objects commuting
 with both legs, so factorizations are unique up to isomorphism.

 - [ofs_m_char] / [ofs_e_char]: a morphism orthogonal on the appropriate
 side against one whole class belongs to the other class, granted an
 explicit closure hypothesis discussed at the statements.

 - [factorization_fact_iso]: the comparison isomorphism, read inside the
 factorization category Fact f of Instance/Fact.v, connects the two
 factorizations as objects of Fact f. 

 --------
 正交分解系统。

 nLab:       https://ncatlab.org/nlab/show/orthogonal+factorization+system 
 https://ncatlab.org/nlab/show/factorization+system 
 维基百科:  https://en.wikipedia.org/wiki/Factorization_system 

 对于在 C 上的两类态射 E 和 M，一个态射 f : x ~> y 的 (E, M)-分解是一个中间对象以及一个 E 态射随后一个 M 态射，它们的复合等于 f：

 x --e--> 中间 --m--> y,        m ∘ e ≈ f。

 在 C 上的正交分解系统 (OFS) 由两类这样的态射 E 和 M 组成，每类都遵守 Hom-集同构关系 ≈，使得每个态射都有一个 (E, M)-分解，并且每个 E 态射对每个 M 态射都是正交的，其意义见 Theory/Orthogonality.v：每个以 E 态射在左、M 态射在右形成的交换方形都有唯一的对角填充。

 这里发展出的经典结果：-  [factorization_unique]：同一个态射的任意两个 (E, M)-分解通过中间对象的一个同构相互连接，该同构与两条腿都可交换，因此分解在同构意义下是唯一的。

 -  [ofs_m_char] / [ofs_e_char]：一个在适当一侧与整类正交的态射属于另一类，前提是满足在命题中讨论的明确闭包假设。

 -  [factorization_fact_iso]：比较同构，在 Instance/Fact.v 的分解范畴 Fact f 中读取，把两个分解作为 Fact f 的对象连接起来。
*)

(*
 The image paradigm, its history, and its reach

 nLab:      https://ncatlab.org/nlab/show/weak+factorization+system
 Wikipedia: https://en.wikipedia.org/wiki/Lifting_property
 Blog:      Bartosz Milewski, "(Weak) Factorization Systems", 2025

 A factorization system equips an arbitrary category with a canonical
 notion of image along its arrows.  The guiding template is elementary
 set theory: a function f is in general neither injective nor
 surjective, and inserting its image between source and target
 separates the two defects, for the map onto the image is surjective
 and carries all the non-injectivity, while the inclusion of the image
 is injective and carries all the non-surjectivity (Milewski, "(Weak)
 Factorization Systems", 2025).  Abstracting "surjection" to a left
 class E and "injection" to a right class M, and asking that every
 morphism factor as an M-morphism after an E-morphism ([ofs_factor]),
 with every E-morphism orthogonal to every M-morphism ([ofs_orth]),
 yields the (E, M) system of [OFS].  The uniqueness of the diagonal
 filler is decisive: it forces any two factorizations of a morphism
 to be joined by a unique isomorphism of middle objects, exactly
 [factorization_unique].

 Two classical facts sit in the background, neither proved here.  Each
 class determines the other by orthogonality: E is the class of all
 morphisms left-orthogonal to M and M the class right-orthogonal to E,
 a Galois connection on arrow classes whose closed pairs are the
 prefactorization systems, and the intersection E ∩ M consists of
 exactly the isomorphisms (nLab, "orthogonal factorization system").
 In one phrase, an OFS is a weak factorization system whose lifts
 happen to be unique (nLab, "weak factorization system").

 The structure has been rediscovered under several names.  Mac Lane
 gave the earliest study, under the now-clashing name "bicategory" and
 with side conditions since dropped (Mac Lane, "Duality for groups",
 Bull. Amer. Math. Soc. 56, 1950).  The orthogonal notion in its
 modern form is due to Freyd and Kelly ("Categories of continuous
 functors, I", J. Pure Appl. Algebra 2, 1972); the name "factorization
 system" and the reflective constructions to Bousfield
 ("Constructions of factorization systems in categories", J. Pure
 Appl. Algebra 9, 1977); and the tie to reflective subcategories and
 localization to Cassidy, Hébert and Kelly (J. Austral. Math. Soc. Ser.
 A 38, 1985).  A later reading presents an OFS as an Eilenberg-Moore
 algebra, suitably defined, for the monad of the squaring endofunctor
 K ↦ K² on Cat (Korostenski, Tholen, J. Pure Appl. Algebra 85, 1993);
 Construction/Arrow.v records the same lineage.

 Instances recur across the classical domains.  In a regular category
 the (regular epi, mono) system and in an abelian category the (epi,
 mono) system are image factorizations, the middle object being the
 categorical image; the library packages these as [Regular_OFS] in
 Structure/Regular/Factorization.v and [Abelian_OFS] in
 Structure/Abelian.v, with the setoid archetype
 [Sets_Image_Factorization] in Instance/Sets/Image.v.  In Cat the
 (bijective-on-objects, fully-faithful) and comprehensive (final
 functor, discrete fibration) systems arise, and reflective
 factorization systems correspond to reflective subcategories and
 localizations, the reflector inverting the left class (Cassidy,
 Hébert, Kelly, 1985; see Construction/Localization/Universal.v).  In
 homotopy theory the weak variant is load-bearing: a Quillen model
 structure is two interlocking weak factorization systems with a class
 of weak equivalences (Quillen, "Homotopical Algebra", LNM 43, 1967).

 Computationally, the image factorization splits a function into its
 surjective and injective parts and names the canonical range that
 lies between them, the shape a typed program uses to give an arbitrary
 map an image type.  Whether the lift is unique is the decisive
 distinction.  The reverse assignment, an injection before a
 surjection, is only a weak factorization system, and its diagonal
 fillers rest on the axiom of choice, so they are not canonical
 (Milewski, 2025).  A lifting problem, the completion of a commuting
 square by a diagonal, is the abstract shape of many search and
 synthesis tasks; orthogonality is the case where the completion
 exists and is forced, so it may be computed as data, not merely
 asserted.  That is why Theory/Orthogonality.v packages the filler as
 a Type-valued unique-existence record, and why the proofs here read
 its witness [unique_obj] out of the orthogonality of [fact_e] against
 [fact_m] to build the comparison isomorphism. 

 --------
 图像范式、它的历史及其影响范围

 nLab:       https://ncatlab.org/nlab/show/weak+factorization+system 
 维基百科:  https://en.wikipedia.org/wiki/Lifting_property 
 博客:      Bartosz Milewski, “（弱）分解系统”, 2025一个分解系统为任意范畴提供了沿其箭头的像的规范概念。指导模板是初等集合论：一个函数 f 通常既不是单射也不是满射，将其像插入源和目标之间可以分离这两种缺陷，因为到像的映射是满射并携带所有非单射性，而像的包含映射是单射并携带所有非满射性（Milewski，《(弱)分解系统》，2025 年）。将“满射”抽象为左类 E，将“单射”抽象为右类 M，并要求每个态射都可以分解为先经过 E 态射再经过 M 态射 ([ofs_factor])，并且每个 E 态射与每个 M 态射正交 ([ofs_orth])，就得到 [OFS] 的 (E, M) 系统。对角填充的唯一性是决定性的：它迫使任意两个态射的分解通过唯一的中间对象同构相连，正是 [factorization_unique]。

 两个经典事实作为背景存在，这里未加证明。每个类通过正交性决定另一个类：E 是所有左正交于 M 的态射的类，而 M 是右正交于 E 的类，这是箭头类上的一个伽罗瓦联系，其闭合对是预分解系统，并且交集 E ∩ M 恰好由同构组成（nLab，“正交分解系统”）。一句话来说，OFS 是一种弱分解系统，其提升恰好是唯一的（nLab，“弱分解系统”）。这个结构已经以几个名称被重新发现。Mac Lane 给出了最早的研究，当时使用现在相冲突的名称“二范畴”，并附带已被废弃的附加条件（Mac Lane，《群的对偶性》，美洲数学会通报 56, 1950）。现代形式的正交概念归功于 Freyd 和 Kelly（《连续函子范畴，I》，纯应用代数杂志 2, 1972）；“分解系统”这一名称及反射构造归功于 Bousfield（《范畴中分解系统的构造》，纯应用代数杂志 9, 1977）；而与反射子范畴及局部化的关联则归功于 Cassidy、Hébert 和 Kelly（澳大利亚数学学会杂志 A 系列 38, 1985）。后来的一个读法将一个OFS呈现为一个Eilenberg-Moore代数，适当地定义，用于Cat上平方自函子K ↦ K²的monad（Korostenski, Tholen, J. Pure Appl. Algebra 85, 1993）；Construction/Arrow.v记录了相同的来源。实例在经典范畴中反复出现。在一个正规范畴中，(正规满射, 单射) 系统，以及在阿贝尔范畴中，(满射, 单射) 系统都是像分解，其中中间对象是范畴像；库将这些作为 [Regular_OFS] 在 Structure/Regular/Factorization.v 和 [Abelian_OFS] 在 Structure/Abelian.v 中打包，集合等价原型 [Sets_Image_Factorization] 在 Instance/Sets/Image.v 中。在 Cat 中，(对象上双射, 全忠实) 和全覆盖 (最终函子, 零散纤维) 系统出现，而反射分解系统对应于反射子范畴和局部化，反射器使左类元素逆转（Cassidy, Hébert, Kelly, 1985；参见 Construction/Localization/Universal.v）。在同伦论中，弱变体是承重的：一个Quillen模型结构是由两组相互交错的弱分解系统以及一类弱等价构成的（Quillen，《同伦代数》，LNM 43，1967）。在计算上，图像分解将一个函数拆分为其满射部分和单射部分，并命名位于它们之间的规范值域，即类型化程序用来赋予任意映射一个图像类型的形状。提升是否唯一是决定性区别。逆向赋值，即在满射之前进行单射，仅是一个弱分解系统，其对角线填充依赖于选择公理，因此它们不是规范的（Milewski, 2025）。提升问题，即通过对角线完成一个交换方格，是许多搜索和综合任务的抽象形状；正交性是完成存在且被强制的情况，因此它可以作为数据被计算，而不仅仅是被断言。这就是为什么 Theory/Orthogonality.v 将填充包装为一个类型值的唯一存在记录，以及为什么这里的证明从 [fact_e] 对 [fact_m] 的正交性中读取它的证明者 [unique_obj] 来构建比较同构。
*)

(*
 An (E, M)-factorization of f : x ~> y: a middle object [fact_mid], a
 left leg [fact_e] belonging to E, and a right leg [fact_m] belonging to
 M, with [fact_m ∘ fact_e ≈ f]. 

 --------
 函数 f : x ~> y 的 (E, M)-分解：一个中间对象 [fact_mid]，一个属于 E 的左边支 [fact_e]，以及一个属于 M 的右边支 [fact_m]，其中 [fact_m ∘ fact_e ≈ f] 。
*)
Record Factorization {C : Category} {x y : C} (f : x ~> y)
  (E M : MorphismClass C) := {
  fact_mid  : C;
  fact_e    : x ~> fact_mid;
  fact_e_in : E _ _ fact_e;
  fact_m    : fact_mid ~> y;
  fact_m_in : M _ _ fact_m;
  fact_comm : fact_m ∘ fact_e ≈ f
}.

Arguments fact_mid  {C x y f E M} _.
Arguments fact_e    {C x y f E M} _.
Arguments fact_e_in {C x y f E M} _.
Arguments fact_m    {C x y f E M} _.
Arguments fact_m_in {C x y f E M} _.
Arguments fact_comm {C x y f E M} _.

(*
 An orthogonal factorization system: two morphism classes closed under ≈,
 a factorization of every morphism, and orthogonality of E against M. 

 --------
 正交分解系统：两个在≈下封闭的态射类，每个态射的分解，以及E相对于M的正交性。
*)
Class OFS {C : Category} (E M : MorphismClass C) := {
  ofs_e_respects {x y} (f g : x ~> y) : f ≈ g → E x y f → E x y g;
  ofs_m_respects {x y} (f g : x ~> y) : f ≈ g → M x y f → M x y g;
  ofs_factor {x y} (f : x ~> y) : Factorization f E M;
  ofs_orth {a b x y} (e : a ~> b) (m : x ~> y) :
    E a b e → M x y m → e ⫫ m
}.

Section FactorizationSystem.

Context {C : Category}.
Context {E M : MorphismClass C}.

(*
 Two factorizations of one morphism bound the same commuting square: the
 two composites are both ≈ f, hence ≈ each other. 

 --------
 一个态射的两个分解限定了同一个交换方形：这两个复合都约等于 f，因此也约等于彼此。
*)
Lemma factorization_square {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘ fact_e F1.
Proof.
  rewrite (fact_comm F2).
  rewrite (fact_comm F1).
  reflexivity.
Qed.

(*
 The comparison morphism between two factorizations of f: the unique
 diagonal filler of the square [fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘
 fact_e F1], obtained from (fact_e F1) ⫫ (fact_m F2). 

 --------
 两个 f 的分解之间的比较态射：方形 [fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘ fact_e F1] 的唯一对角填充，由 (fact_e F1) ⫫ (fact_m F2) 得到。
*)
Lemma factorization_lift {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ d : fact_mid F1 ~> fact_mid F2,
    (d ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ d ≈ fact_m F1).
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  exact (unique_obj U; unique_property U).
Qed.

(*
 Any two comparison morphisms between the same pair of factorizations
 agree: both fill the same orthogonality square, whose filler is unique. 

 --------
 同一对分解之间的任意两个比较态射是相同的：它们都填充相同的正交方形，该方形的填充是唯一的。
*)
Lemma factorization_lift_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) (d d' : fact_mid F1 ~> fact_mid F2)
  (de : d ∘ fact_e F1 ≈ fact_e F2) (md : fact_m F2 ∘ d ≈ fact_m F1)
  (d'e : d' ∘ fact_e F1 ≈ fact_e F2) (md' : fact_m F2 ∘ d' ≈ fact_m F1) :
  d ≈ d'.
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  assert (H1 : unique_obj U ≈ d). {
    apply (uniqueness U).
    split.
    - exact de.
    - exact md.
  }
  assert (H2 : unique_obj U ≈ d'). {
    apply (uniqueness U).
    split.
    - exact d'e.
    - exact md'.
  }
  rewrite <- H1.
  exact H2.
Qed.

(*
 Uniqueness of factorizations: any two (E, M)-factorizations of the same
 morphism have isomorphic middle objects, through a comparison morphism
 commuting with both legs.  The forward comparison and its inverse are the
 two diagonal fillers, and both round trips agree with the identity by
 uniqueness of the filler of each self-square. 

 --------
 分解的唯一性：同一态射的任意两个 (E, M)-分解具有同构的中间对象，通过一个与两条箭头交换的比较态射。前向比较及其逆是两个对角填充，而两次往返通过每个自方形填充的唯一性与恒等映射一致。
*)
Theorem factorization_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ i : fact_mid F1 ≅ fact_mid F2,
    (to i ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ to i ≈ fact_m F1).
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  exists {| to := d; from := d'; iso_to_from := dd'; iso_from_to := d'd |}.
  split.
  - exact de.
  - exact md.
Qed.

(*
 The easy direction of the characterization of M: every M-morphism is
 right orthogonal to every E-morphism.  This is [ofs_orth] restated with
 the arguments in the order matching [ofs_m_char] below. 

 --------
 M 的特征的简单方向：每个 M-态射都与每个 E-态射右正交。这是 [ofs_orth] 的重新表述，参数顺序与下面的 [ofs_m_char] 相匹配。
*)
Corollary ofs_m_orth {O : OFS E M} {x y : C} (m : x ~> y) :
  M x y m → ∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m.
Proof.
  intros Hm a b e He.
  exact (ofs_orth e m He Hm).
Qed.

(* Dually, every E-morphism is left orthogonal to every M-morphism. / 同样，每个 E-态射都与每个 M-态射左正交。 *)
Corollary ofs_e_orth {O : OFS E M} {x y : C} (e : x ~> y) :
  E x y e → ∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m.
Proof.
  intros He a b m Hm.
  exact (ofs_orth e m He Hm).
Qed.

(*
 Characterization of M, hypothesis form.  Classically, m belongs to M as
 soon as e ⫫ m for every e ∈ E.  The argument factors m as m' ∘ e' and
 shows that e' is an isomorphism, exhibiting m (up to ≈) as an M-morphism
 precomposed with an isomorphism — so it needs M to be closed under
 precomposition with isomorphisms.  Nothing in the four fields of [OFS]
 supplies that closure, so the statement takes it as the explicit
 hypothesis [Mclosed] rather than silently strengthening the class. 

 --------
 M 的特征化，假设形式。按照经典方法，一旦对于每个 e ∈ E 都有 e ⫫ m，则 m 属于 M。论证将 m 分解为 m' ∘ e' 并表明 e' 是一个同构，从而展示 m（在 ≈ 意义下）作为与一个同构前组合的 M-态射——因此它需要 M 在与同构前组合下是封闭的。[OFS] 的四个领域中没有任何内容提供这种封闭性，因此该陈述将其作为显式假设 [Mclosed]，而不是默默地加强该类。
*)
Theorem ofs_m_char {O : OFS E M}
  (Mclosed : ∀ (x y z : C) (i : x ~> y) (m : y ~> z),
      IsIsomorphism i → M y z m → M x z (m ∘ i))
  {x y : C} (m : x ~> y) :
  (∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m) → M x y m.
Proof.
  intros H.
  destruct (ofs_factor m) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m ∘ id ≈ m' ∘ e' through e' ⫫ m. / 通过 e' ⫫ m，将平方 m ∘ id ≈ m' ∘ e' 提升。 *)
  assert (comm1 : m ∘ id ≈ m' ∘ e'). {
    rewrite id_right.
    symmetry.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m (H _ _ e' He') id m' comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e' ≈ id, mD : m ∘ unique_obj U ≈ m'. / dE ： unique_obj U ∘ e' ≈ id， mD ： m ∘ unique_obj U ≈ m'。 *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* Both e' ∘ (unique_obj U) and id fill the self-square of (e', m'). / e' ∘ (unique_obj U) 和 id 都填充了 (e', m') 的自我方格。 *)
  assert (Hu1 : unique_obj Uself ≈ e' ∘ unique_obj U). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite dE.
      cat.
    - rewrite comp_assoc.
      rewrite comm'.
      exact mD.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (ed : e' ∘ unique_obj U ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism e'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := ed;
             is_left_inverse   := dE |}.
  }
  apply (ofs_m_respects (m' ∘ e') m comm').
  exact (Mclosed _ _ _ e' m' Hiso Hm').
Qed.

(*
 Characterization of E, hypothesis form, dual to [ofs_m_char]: e belongs
 to E as soon as e ⫫ m for every m ∈ M, granted that E is closed under
 postcomposition with isomorphisms ([Eclosed]). 

 --------
 E 的特征化，假设形式，[ofs_m_char] 的对偶：只要 e ⫫ m 对于每个 m ∈ M 成立，则 e 属于 E，前提是 E 在与同构的后合成下封闭（[Eclosed]）。
*)
Theorem ofs_e_char {O : OFS E M}
  (Eclosed : ∀ (x y z : C) (e : x ~> y) (i : y ~> z),
      IsIsomorphism i → E x y e → E x z (i ∘ e))
  {x y : C} (e : x ~> y) :
  (∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m) → E x y e.
Proof.
  intros H.
  destruct (ofs_factor e) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m' ∘ e' ≈ id ∘ e through e ⫫ m'. / 通过 e ⫫ m' 提升平方 m' ∘ e' ≈ id ∘ e。 *)
  assert (comm1 : m' ∘ e' ≈ id ∘ e). {
    rewrite id_left.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e m' (H _ _ m' Hm') e' id comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e ≈ e', mD : m' ∘ unique_obj U ≈ id. / dE：unique_obj U ∘ e ≈ e'， mD：m' ∘ unique_obj U ≈ id。 *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* Both (unique_obj U) ∘ m' and id fill the self-square of (e', m'). / Both (unique_obj U) ∘ m' 和 id 填充了 (e', m') 的自方格。 *)
  assert (Hu1 : unique_obj Uself ≈ unique_obj U ∘ m'). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite comm'.
      exact dE.
    - rewrite comp_assoc.
      rewrite mD.
      cat.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (dm : unique_obj U ∘ m' ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism m'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := mD;
             is_left_inverse   := dm |}.
  }
  apply (ofs_e_respects (m' ∘ e') e comm').
  exact (Eclosed _ _ _ e' m' Hiso He').
Qed.

(*
 Every (E, M)-factorization of f is in particular an object of the
 factorization category Fact f of Instance/Fact.v: keep the middle object
 and the two legs, discarding the class memberships. 

 --------
 f 的每一个 (E, M)-分解特别是 Instance/Fact.v 中分解范畴 Fact f 的一个对象：保留中间对象和两个边，丢弃类别成员资格。
*)
Definition factorization_to_fact {x y : C} (f : x ~> y)
  (F1 : Factorization f E M) : Fact f.
Proof.
  refine (fact_mid F1; (fact_e F1; (fact_m F1; _))).
  symmetry.
  exact (fact_comm F1).
Defined.

(*
 The comparison morphism of [factorization_unique] is precisely a
 morphism of Fact f — its two triangles are Fact's two commuting
 conditions — and Fact's homs compare underlying C-morphisms only, so the
 two round-trip identities transfer.  Hence two (E, M)-factorizations of
 f are isomorphic as objects of Fact f. 

 --------
 [factorization_unique] 的比较态射恰好是 Fact f 的一个态射 —— 它的两个三角形就是 Fact 的两个交换条件 —— 而 Fact 的同态仅比较底层的 C-态射，所以两个往返恒等式得以传递。因此 f 的两个 (E, M)-分解作为 Fact f 的对象是同构的。
*)
Theorem factorization_fact_iso {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  factorization_to_fact f F1 ≅[Fact f] factorization_to_fact f F2.
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  unshelve refine {| to := _; from := _ |}.
  - refine (d; _).
    split.
    + exact de.
    + exact md.
  - refine (d'; _).
    split.
    + exact d'e.
    + exact md'.
  - exact dd'.
  - exact d'd.
Qed.

End FactorizationSystem.
