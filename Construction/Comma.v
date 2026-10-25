Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Comma.

Context {A B C : Category}.

Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

(*
   * The comma category (S ↓ T) of two functors with common codomain. 

   --------
   * 具有共同余域的两个函子之间的逗号范畴 (S ↓ T)。
*)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Given functors S : A ⟶ C and T : B ⟶ C, the comma category S ↓ T has as
 objects the triples (a, b, h) of objects a : A and b : B together with a
 morphism h : S a ~> T b in C; here a triple is encoded as the dependent
 pair (∃ p : A ∏ B, S (fst p) ~> T (snd p)), so `1 x is the pair (a, b) and
 `2 x is the mediating morphism h. A morphism (a, b, h) ~> (a', b', h') is a
 pair of morphisms (f : a ~> a' in A, g : b ~> b' in B) making the square

 S a  --h-->  T b
 |            |
 S f           T g           commute, i.e.  h' ∘ S f ≈ T g ∘ h.
 v            v
 S a' --h'--> T b'

 Identity is (id, id) and composition is componentwise, (f, g) ∘ (f', g') :=
 (f ∘ f', g ∘ g'); both laws hold because they hold in A and B. Equivalence
 of morphisms is the componentwise conjunction of ≈ in A and ≈ in B (the
 commuting-square proof component is irrelevant to equality).

 The construction is due to Lawvere (1963), who used a comma punctuation mark
 for it; the name persists even though the modern notation is the arrow ↓.

 Special cases: taking S = T = Id[C] gives the arrow category C^→, whose
 objects are the morphisms of C and whose morphisms are commuting squares;
 taking S = Id[C] and T = Δ(c) the constant functor at c : C gives the slice
 C/c (see Construction/Slice.v, where C ̸ c ≅ (Id ↓ =(c)) is proven); dually
 S = Δ(c), T = Id[C] gives the coslice c/C. The projection functors below,
 comma_proj1 : S ↓ T ⟶ A and comma_proj2 : S ↓ T ⟶ B, recover a and b, and
 comma_proj_nat is the natural transformation S ◯ comma_proj1 ⟹ T ◯
 comma_proj2 whose component at (a, b, h) is h. Comma categories characterize
 adjunctions and universal arrows: a universal arrow from S to T is an
 initial object of the appropriate comma category. 

 --------
 nLab: https://ncatlab.org/nlab/show/comma+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 给定函子 S : A ⟶ C 和 T : B ⟶ C，逗号范畴 S ↓ T 的对象是由对象 a : A 和 b : B 以及在 C 中的态射 h : S a ~> T b 组成的三元组 (a, b, h)；这里三元组被编码为依赖对 (∃ p : A ∏ B, S (fst p) ~> T (snd p))，所以 `1 x 是对 (a, b) 而 `2 x 是中介态射 h。一个态射 (a, b, h) ~> (a', b', h') 是一对态射 (f : a ~> a' 在 A 中, g : b ~> b' 在 B 中)，使得下方的图表

 S a  --h-->  T b
 |            |
 S f           T g
 v            v
 S a' --h'--> T b'

 交换，即 h' ∘ S f ≈ T g ∘ h。恒等映射是 (id, id)，复合运算按分量进行，即 (f, g) ∘ (f', g') := (f ∘ f', g ∘ g')；这两个律成立，因为它们在 A 和 B 中成立。态射的等价性是 A 中的 ≈ 与 B 中的 ≈ 的分量结合（交换方形证明部分与等式无关）。

 该构造由劳维尔（Lawvere, 1963）提出，他为此使用了逗号标点符号；即使现代符号已改为箭头 ↓，该名称仍然沿用。特殊情况：取 S = T = Id [C]，会得到箭头范畴 C^→，其对象是 C 的态射，其态射是交换图形；取 S = Id [C] 且 T = Δ(c) 为常值函子在 c : C 上，则得到切片 C/c（参见 Construction/Slice.v，其中证明了 C ̸ c ≅ (Id ↓ =(c))）；对偶地，S = Δ(c)，T = Id [C] 则给出余切片 c/C。下面的投射函子，comma_proj1 : S ↓ T ⟶ A 和 comma_proj2 : S ↓ T ⟶ B，恢复了 a 和 b，而 comma_proj_nat 是自然变换 S ◯ comma_proj1 ⟹ T ◯ comma_proj2，其在 (a, b, h) 处的分量是 h。逗号范畴刻画了伴随与泛箭：从 S 到 T 的泛箭是相应逗号范畴的初对象。
*)

(*
 Reification, the adjoint functor theorems, and gluing

 nLab: https://ncatlab.org/nlab/show/comma+object
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab: https://ncatlab.org/nlab/show/scone

 The construction first appeared as an unnamed auxiliary device in
 Lawvere's thesis (Lawvere, "Functorial Semantics of Algebraic Theories",
 Columbia University PhD thesis 1963; summarized in Proc. Nat. Acad. Sci.
 50 (1963), 869-872; republished with an author's commentary as Reprints
 in Theory and Applications of Categories 5, 2004), where it serves to
 characterize adjoint functors.  The original notation (S, T) generalizes
 the hom-set notation C(x, y), and the nLab records that the name is a
 holdover from that punctuation.  Wikipedia notes that the device became
 generally known only many years later; its textbook treatment is
 section II.6 of Mac Lane, "Categories for the Working Mathematician"
 (Springer GTM 5; 2nd ed. 1998).

 What the definition provides is reification.  A morphism between an
 S-image and a T-image becomes an OBJECT of the category [Comma], so that
 universal properties quantified over morphisms become initial-object
 properties quantified over objects, where the general machinery of this
 library applies.  Beyond the special cases named above, the category of
 cones over a diagram F is the comma Δ ↓ F (Instance/Cones/Comma.v), the
 product category A ∏ B is the comma of two functors into the terminal
 category (Construction/Product/Comma.v), and natural transformations
 S ⟹ T correspond to functors A ⟶ (S ↓ T) sectioning both projections —
 an observation Wikipedia credits to Huq, an exercise in Mac Lane —
 formalized in Construction/Comma/Natural/Transformation.v.  Invariance
 of S ↓ T under natural isomorphism of S and T is
 Construction/Comma/Isomorphism.v.

 The adjunction story that motivated the definition is carried through
 in-tree at each of its historical layers.  A universal arrow from d to U
 is an initial object of =(d) ↓ U, and a family of them assembles into an
 adjunction (Theory/Universal/Arrow.v, [AdjunctionFromUniversalArrows]).
 Lawvere's own criterion — F ⊣ G precisely when (F ↓ Id) ≅ (Id ↓ G)
 compatibly with the projections, which Wikipedia reports as the original
 motivation for the construction — is packaged as [lawvere_equiv] in
 Construction/Comma/Adjunction.v.  Freyd's General Adjoint Functor
 Theorem (Freyd, "Abelian Categories", Harper & Row 1964, exercises of
 chapter 3; reprinted as TAC Reprints 3, 2003) reduces the existence of a
 left adjoint to U to an initial object in each =(d) ↓ U; the library
 executes exactly this route in Adjunction/GAFT.v ([GAFT_from_initials],
 [GAFT]), with completeness of the comma category supplied by
 [Comma_Complete] in Construction/Comma/Limit.v, where the projection
 [comma_proj2] creates the limits.  Creation of limits in comma
 categories was studied early by Pellegrino (two papers, Riv. Mat. Univ.
 Parma 3 and Atti Sem. Mat. Fis. Univ. Modena 23, both 1974).

 Two further readings locate the construction in the wider theory.
 Viewed 2-categorically, [Comma] is the strict comma object of the
 cospan A ⟶ C ⟵ B in Cat — the instance that gives the general notion
 its name — and comma objects are PIE-limits, constructible from
 pullbacks and the power C^2 (nLab, "comma object").  Viewed logically,
 the Freyd cover, or scone, of a category T is the comma Set ↓ Γ over
 the global-sections functor Γ := T(1, −); gluing arguments through it
 prove the disjunction and existence properties of intuitionistic
 higher-order logic (Lambek and Scott 1980; Freyd and Scedrov,
 "Categories, Allegories", North-Holland 1990; Johnstone, "Sketches of
 an Elephant", C3.6), and Artin gluing generalizes this: when a functor
 f between topoi preserves pullbacks, the comma category Id ↓ f is
 again a topos (nLab, "comma category").  In programming-language
 theory the same gluing underlies logical-relations proofs.  Finally,
 Rydeheard and Burstall ("Computational Category Theory", Prentice Hall
 1988, section 5.2) read the comma category as a program-construction
 device: given code once for [Comma], colimit algorithms for derived
 categories such as graphs are inherited from colimit algorithms for
 their ingredients. 

 --------
 具体化、伴随函子定理与拼接

 nLab:  https://ncatlab.org/nlab/show/comma+object 
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem 
 nLab:  https://ncatlab.org/nlab/show/scone这种构造最初出现在Lawvere的论文中，作为一个未命名的辅助工具（Lawvere，《代数理论的函子语义》，哥伦比亚大学博士论文 1963；在《美国国家科学院院刊》50 (1963), 869-872 有总结；并在《范畴理论与应用文集》5, 2004 中复印发表并附作者评论），它用于刻画伴随函子。最初的符号 (S, T) 是对同态集记号 C(x, y) 的推广，nLab 记录指出这个名字是从那个标点符号延续下来的。Wikipedia 指出，这一工具直到多年后才为大众所知；在教材中的讨论见 Mac Lane 《为工作数学家准备的范畴论》第二章第6节（Springer GTM 5；第2版，1998）。定义所提供的是具体化。一个 S-图像与 T-图像之间的态射成为类别 [Comma] 的一个对象，因此对态射量化的泛性质变为对对象量化的初始对象性质，并且该库的一般机制适用。除了上述特殊情况之外，一个图 F 上的圆锥类别是逗号 Δ ↓ F（Instance/Cones/Comma.v），积类别 A ∏ B 是两个函子到终端类别的逗号（Construction/Product/Comma.v），自然变换 S ⟹ T 对应于函子 A ⟶ (S ↓ T) 来分解两个投影——这是 Wikipedia 归功于 Huq 的一个观察，是 Mac Lane 的一个练习——在 Construction/Comma/Natural/Transformation.v 中形式化。在自然同构下 S↓T 的不变性 对于 S 和 T 是 Construction/Comma/Isomorphism.v。激励定义的伴随故事在每一个历史层次的树中都得以延续。从 d 到 U 的一个泛箭头是 =(d) ↓ U 的一个初始对象，而它们的一族组合成一个伴随关系（Theory/Universal/Arrow.v，[AdjunctionFromUniversalArrows]）。Lawvere 自身的标准——当且仅当 (F ↓ Id) ≅ (Id ↓ G) 并与投影兼容时 F ⊣ G，维基百科将其报道为该构造的最初动机——在 Construction/Comma/Adjunction.v 中以 [lawvere_equiv] 的形式打包。弗雷德的一般伴随函子定理（Freyd，《Abelian Categories》，Harper & Row 1964，第3章练习；重印于 TAC Reprints 3, 2003）将左伴随函子 U 的存在性归结为每一个 =(d) ↓ U 中初始对象的存在；库在 Adjunction/GAFT.v（[GAFT_from_initials]，[GAFT]）中正是采用了这一路径，逗号范畴的完备性由 Construction/Comma/Limit.v 中的 [Comma_Complete] 提供，其中投影 [comma_proj2] 生成极限。逗号范畴中极限的生成早期由 Pellegrino 研究（两篇论文，Riv. Mat. Univ. Parma 3 和 Atti Sem. Mat. Fis. Univ. Modena 23，均为 1974 年）。另外两种解读将该构造归于更广泛的理论中。从2-范畴角度看，[Comma] 是
 在Cat中cospan A ⟶ C ⟵ B——给出一般概念的实例
 其名称——逗号对象是PIE极限，可由
 拉回和幂C^2（nLab，“逗号对象”）。从逻辑上看，一个范畴 T 的 Freyd 覆盖或饼状物，是全局截面函子 Γ := T(1, −) 上的逗号范畴 Set ↓ Γ；通过它的粘合论证可证明直觉主义高阶逻辑的析取性和存在性（Lambek 和 Scott 1980；Freyd 和 Scedrov，《范畴，寓言》，North-Holland 1990；Johnstone，《大象的草图》，C3.6），而 Artin 粘合则将其推广：当两个拓扑范畴之间的函子 f 保持拉回时，逗号范畴 Id ↓ f 仍是一个拓扑范畴（nLab，“逗号范畴”）。在程序设计语言理论中，相同的粘合方法构成逻辑关系证明的基础。最后，Rydeheard 和 Burstall（《计算范畴论》，Prentice Hall 1988，第5.2节）将逗号范畴解读为一种程序构造工具：给定一次 [Comma] 的代码，派生范畴（如图）的余极限算法就可以继承其组成部分的余极限算法。
*)

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

(*
   【Comma 范畴定义展开】/ Comma walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      给定 S : A ⟶ C、T : B ⟶ C，逗号范畴 S ↓ T 把「S 像到 T 像之间的一条箭头」
      提升成对象，把交换方块提升成态射。
      Objects = mediating arrows h : S a ~> T b; morphisms = commuting squares.
      名字来自 Lawvere 原记号里的逗号；(S, T) → 现代写成 S ↓ T。

   2) 编码（本文件）/ Encoding here
      - obj := ∃ p : A ∏ B, S (fst p) ~> T (snd p)
        `1 x = (a,b)，`2 x = h
      - hom := ∃ (f,g),  `2 y ∘ S f ≈ T g ∘ `2 x   （交换方）
      - ≈ 只看 (f,g) 的分量 ≈，方块证明不参与相等
        / ≈ ignores the square proof (irrelevant)

   3) 特殊情形 / Special cases
      Id ↓ Id = 箭头范畴 Arrow；Id ↓ Δ(c) ≃ 切片 C/c；Δ(c) ↓ Id ≃ 余切片。
      Arrow / Slice / Coslice are commas.

   4) 投影 / Projections
      comma_proj1 / comma_proj2 找回 a、b；comma_proj_nat 的分量就是那条 h。

   阅读：三元组 (a,b,h) → 交换方 (f,g) → 分量 ≈ → 投影。
   Read: triples → commuting pairs → componentwise ≈ → projections.
*)

Program Definition Comma : Category := {|
  (* objects: triples (a, b, h : S a ~> T b) / 对象：三元组 (a, b, h : S a ~> T b) *)
  obj     := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p);
  (*
 morphisms: pairs (f, g) with the commuting square h' ∘ S f ≈ T g ∘ h 

 --------
 态射：成对 (f, g) 的元组，满足交换图 h' ∘ S f ≈ T g ∘ h
*)
  hom     := fun x y =>
    ∃ f : (fst (`1 x) ~{A}~> fst (`1 y)) * (snd (`1 x) ~{B}~> snd (`1 y)),
      `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x;
  (*
 equivalence: componentwise ≈ in A and B (square proof is irrelevant) 

 --------
 等价性：A 和 B 中按分量近似（平方证明无关紧要）
*)
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);    (* identity (id_a, id_b) / 身份 (id_a, id_b) *)
  (* composition is componentwise (f ∘ f', g ∘ g') / 组合是逐分量的 (f ∘ f', g ∘ g') *)
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros.
  simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ?; simpl.
  intros [[]] [[]]; simpl in *.
  rewrite !fmap_comp.
  rewrite comp_assoc.
  rewrites.
  rewrite <- !comp_assoc.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation.
  intros; simpl.
  split; now rewrite id_left.
Qed.
Next Obligation.
  intros. simpl.
  split; now rewrite id_right.
Qed.
Next Obligation.
  intros.
  simpl.
  split; apply comp_assoc.
Qed.
Next Obligation.
  intros. simpl.
  split; apply comp_assoc_sym.
Qed.

Program Instance comma_proj  : Comma ⟶ A ∏ B := {|
  fobj := fun x => ``x;
  fmap := fun _ _ f => ``f
|}.
Next Obligation.
  intros ? ? ? ? [e0 e1].
  now split.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj1 : Comma ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj2 : Comma ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

#[local] Obligation Tactic := cat_simpl.

Program Instance comma_proj_nat : S ◯ comma_proj1 ⟹ T ◯ comma_proj2.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_mor_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y → `1 x ≅[A ∏ B] `1 y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Defined.

Theorem comma_proj_com_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  ∀ iso : x ≅ y,
    `2 x ≈ fmap[T] (snd `1 (from iso)) ∘ `2 y ∘ fmap[S] (fst `1 (to iso)).
Proof.
  intros.
  pose proof (iso_from_to iso); simpl in X.
  destruct (from iso), x0; simpl in *.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst X).
  cat.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(*
 The "cocomma" defined here is the comma category formed in the opposite
 categories, @Comma (B^op) (A^op) (C^op) (T^op) (S^op). Since the comma of
 opposite functors is the opposite of the comma, this is (S ↓ T)^op up to
 isomorphism: it dualizes S ↓ T by reversing every arrow. Note this is the
 pointwise/op dual and is NOT the cocomma *object* of nLab (the colimit-side
 dual, a.k.a. the collage), which is a genuinely different construction. 

 --------
 这里定义的“协逗号”是由对偶范畴形成的逗号范畴，@Comma (B^op) (A^op) (C^op) (T^op) (S^op)。由于对偶函子之间的逗号是逗号的对偶，因此它在同构意义下是 (S ↓ T)^op：它通过反转每一条箭头来对 S ↓ T 进行对偶。注意这只是逐点/对偶对偶，并不是 nLab 中的协逗号*对象*（即余极限端的对偶，也称为拼接物），那是一个真正不同的构造。
*)
Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
