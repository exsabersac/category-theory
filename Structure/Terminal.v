Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Category with a terminal object / * 具有终对象的范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/terminal+object
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 A terminal object `1` in a category C is an object such that for every
 object `x` there is exactly one morphism `! : x ~> 1`. "Exactly one" splits
 into existence (the morphism [one]) and uniqueness (any two morphisms into
 `1` agree under `≈`, the law [one_unique]). Equivalently, every hom-setoid
 `x ~> 1` is contractible (a singleton up to `≈`). A terminal object is the
 dual of an initial object — it is initial in `C^op` — and is the limit of
 the empty diagram; see Structure/Initial.v, which derives initial objects
 from this file by duality. Terminal objects are unique up to (unique)
 isomorphism whenever they exist: [terminal_unique] below builds the
 isomorphism, [terminal_arrow_unique] shows it is the only arrow at all
 between the two objects, and [terminal_unique_up_to_unique_iso] packages
 the two as a single [Unique]. 

 --------
 nLab: https://ncatlab.org/nlab/show/terminal+object
 维基百科: https://en.wikipedia.org/wiki/Initial_and_terminal_objects范畴 C 中的终对象 `1` 是这样一个对象：对于每一个对象 `x`，存在唯一的态射 `! : x ~> 1`。“唯一的”可拆分为存在性（该态射 [one]）和唯一性（任意两个指向 `1` 的态射在 `≈` 下一致，即定律 [one_unique]）。等价地，每个同态集合 `x ~> 1` 都是可收缩的（在 `≈` 下是单例）。终对象是初对象的对偶——在 `C^op` 中它是初的——并且是空图的极限；参考 Structure/Initial.v，该文件通过对偶性推导出初对象。终结对象在其存在时至多唯一（唯一同构）：下面的 [terminal_unique] 构建了同构，[terminal_arrow_unique] 显示它是在两个对象之间的唯一箭头，而 [terminal_unique_up_to_unique_iso] 将两者打包为单个 [Unique]。
*)

(*
 Where terminal objects come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/global+element
 nLab:  https://ncatlab.org/nlab/show/unit+type
 Paper: Samuel, "On universal mappings and free topological groups",
 Bulletin of the AMS 54(6), 1948
 Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950
 Paper: Lawvere, "An elementary theory of the category of sets",
 PNAS 52, 1964

 The terminal object is the simplest universal property.  Universal
 mapping properties enter mathematics with Samuel (1948), whose
 treatment of free topological groups the Bourbaki group then extended
 to free groups, tensor products and limits (the history is traced in
 Dubuc, "Categorías. Los 30 primeros años", arXiv:1404.6240, 2014);
 terminality is the nullary, degenerate case, a universal property with
 no auxiliary data whatsoever.  It follows that the contractibility of
 each hom-setoid `x ~> 1` is the prototype for every
 uniqueness-up-to-unique-isomorphism argument downstream, with
 [one_unique] as its entire content.  Mac Lane's duality program
 (1950), which recast group theory in terms of homomorphisms and
 composition so that reversing arrows would exchange paired notions,
 supplies the other half of the design: initial and terminal objects
 are the model dual pair, and Structure/Initial.v realizes the pairing
 literally — `Initial C` is notation for `Terminal (C^op)`, with
 [zero] and [zero_unique] mere projections of [one] and [one_unique],
 and [zero_comp] the dual reading of [one_comp].

 Terminality is also the shape to which every limit reduces.  The
 header's remark that `1` is the limit of the empty diagram is proved
 in both directions as [Terminal_Limit] in Structure/Limit/Terminal.v;
 conversely, a limit of any diagram is precisely a terminal object in
 its category of cones (Wikipedia, "Initial and terminal objects");
 [Limit_Cones] in Instance/Cones/Limit.v builds the limit from the
 terminal cone.  Even GAFT bottoms out here: Theory/WeaklyInitial.v
 builds its initial object as a [Build_Terminal] on the opposite
 category.

 The purpose the definition serves is to say "element" without
 mentioning elements.  A morphism `1 ~> x` is a global element of `x`
 — in the nLab's phrasing, a generalized element at stage of definition
 `1`: in Set it picks out an ordinary element, in Cat a functor from
 the terminal category singles out an object, and in a topos a global
 element of the subobject classifier is a truth value (nLab, "global
 element").  Lawvere's elementary theory of the category of sets
 (1964) rests on this reading: its categories are well-pointed,
 meaning `1` is a generator — two morphisms `a ~> b` agreeing on every
 global element of `a` already satisfy ≈ (nLab, "well-pointed topos").
 In this library the reading surfaces as [truth : 1 ~> Ω] in
 Structure/SubobjectClassifier.v and as the [Constant] class of
 Structure/Constant.v, a family of global elements embedding the
 values of a Coq type.

 Computationally, `1` is the unit type.  The nLab's unit-type article
 aligns the proposition "true", the singleton set, the terminal object
 and the unit type in a single row, the unit type being contractible
 exactly as the header describes the hom-setoids here.  In a category
 of types and pure functions there is one and only one function from
 any type to the unit type; Milewski's Bool counterexample — two
 distinct constant functions into Bool exist, so Bool is not terminal —
 shows the uniqueness half of the definition carrying all the weight
 (Milewski, "Products and Coproducts", 2015).  The computable witnesses
 are [Coq_Terminal] in Instance/Coq.v and [Sets_Terminal] in
 Instance/Sets.v; [const] below factors any constant map through `1`.

 Read in a monoidal category whose unit is terminal, [one] becomes the
 discard map and terminality becomes a causality principle.  Coecke
 and Lal define a causal category as a symmetric, partially monoidal
 category whose unit is terminal, and show that classical or quantum
 correlations force that terminality (Coecke, Lal, "Causal categories:
 relativistically interacting processes", Foundations of Physics 43,
 2013); Kissinger, Hoban and Coecke state the principle as process
 terminality — when the output of a process is discarded, the process
 itself may as well be discarded — and prove it equivalent to
 relativistic causal structure (Kissinger, Hoban, Coecke, "Equivalence
 of relativistic causal structure and process terminality", 2017).
 Concretely: probability distributions are normalized, quantum
 channels preserve trace, and [one_comp] is the slogan's algebraic
 kernel — discarding after computing is just discarding.
 Structure/Monoidal/Semicartesian/Terminal.v packages the
 correspondence as a [Terminal] structure with `one := eliminate`. 

 --------
 终端对象的来源以及它们的用途

 nLab:   https://ncatlab.org/nlab/show/global+element 
 nLab:   https://ncatlab.org/nlab/show/unit+type 
 论文: Samuel, 《论泛映射与自由拓扑群》, 
 美国数学学会公报 54(6), 1948
 论文: Mac Lane, 《群的对偶性》, 美国数学学会公报 56, 1950
 论文: Lawvere, 《集合范畴的初等理论》, 
 美国国家科学院院刊 52, 1964终端对象是最简单的泛性质。泛映射性质通过 Samuel (1948) 引入数学，他对自由拓扑群的处理随后被 Bourbaki 小组扩展到自由群、张量积和极限（历史可追溯见 Dubuc，《Categorías. Los 30 primeros años》，arXiv:1404.6240, 2014）；终端性是零元、退化的情况，是一种没有任何辅助数据的泛性质。因此，每个同态集 `x ~> 1` 的可收缩性是下游每个“唯一性至唯一同构”的论证的原型，而 [one_unique] 则构成其全部内容。麦克·莱恩的对偶计划（1950年），将群论重新表述为同态和组合的形式，以便反转箭头可以交换成对的概念，提供了设计的另一半：初始对象和终结对象是模型对偶对，而 Structure/Initial.v 则将这种配对实现为字面上的 — `Initial C` 是 `Terminal (C^op)` 的符号表示，[zero] 和 [zero_unique] 只是 [one] 和 [one_unique] 的投影，[zero_comp] 则是 [one_comp] 的对偶读法。终结性也是每个极限归约的形态。标题中提到的 `1` 是空图的极限，这在 Structure/Limit/Terminal.v 中以两个方向证明，作为 [Terminal_Limit]；反过来，任何图的极限正是其锥类别中的终端对象（维基百科，“初始对象和终端对象”）；Instance/Cones/Limit.v 中的 [Limit_Cones] 从终端锥构建极限。即使是 GAFT 也在这里触底：Theory/WeaklyInitial.v 在对立类别上将其初始对象构建为 [Build_Terminal]。定义的目的在于在不提及元素的情况下表达“元素”。一个态射 `1 ~> x` 是 `x` 的全局元素——用 nLab 的表述方式，在定义阶段的广义元素：在 Set 中，它选出一个普通元素，在 Cat 中，一个来自终端范畴的函子选出一个对象，而在一个拓扑体中，子对象分类器的全局元素就是一个真值（nLab，“全局元素”）。Lawvere 的集合范畴的初等理论（1964）基于这种解读：它的范畴是良点化的，这意味着 `1` 是一个生成元——两个态射 `a ~> b` 在 `a` 的每个全局元素上都一致，那么它们已经满足 ≈（nLab，“良点化拓扑体”）。在这个库中，读取在 Structure/SubobjectClassifier.v 中显示为 [truth : 1 ~> Ω]，在 Structure/Constant.v 中显示为 [Constant] 类，这是一组嵌入 Coq 类型值的全局元素。在计算上，`1` 是单位类型。nLab 的单位类型文章将命题“真”、单例集合、终对象和单位类型排列在同一行，单位类型正如标题在此处描述的 hom-setoids 一样是可收缩的。在类型和纯函数的范畴中，从任意类型到单位类型只有一个函数；Milewski 的 Bool 反例——存在两个不同的恒定函数映射到 Bool，因此 Bool 不是终对象——展示了定义中唯一性这一半承载了全部重量（Milewski，《乘积与余积》，2015）。可计算的证明者是 Instance/Coq.v 中的 [Coq_Terminal] 和 Instance/Sets.v 中的 [Sets_Terminal]；下面的 [const] 将任何恒定映射通过 `1` 因式分解。在一个单位对象为终结对象的单模范畴中，[one] 变成了丢弃映射，而终结性变成了一个因果原则。Coecke 和 Lal 将因果范畴定义为一个对称的、部分单模的范畴，其单位对象为终结对象，并且表明经典或量子关联会强制该终结性（Coecke, Lal, “Causal categories: relativistically interacting processes”, Foundations of Physics 43, 2013）；Kissinger、Hoban 和 Coecke 将该原则表述为过程终结性——当一个过程的输出被丢弃时，该过程本身也可以被丢弃——并证明其与相对论因果结构等价（Kissinger, Hoban, Coecke, “Equivalence of relativistic causal structure and process terminality”, 2017）。具体来说：概率分布是归一化的，量子通道保持迹，[one_comp] 是该口号的代数核 —— 计算后丢弃就是丢弃。Structure/Monoidal/Semicartesian/Terminal.v 将对应关系打包为一个带有 `one := eliminate` 的 [Terminal] 结构。
*)

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;                     (* the terminal object 1 / 终对象 1 *)
  one {x} : x ~> terminal_obj;          (* the morphism ! : x ~> 1 / 态射 ! : x ~> 1 *)

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g  (* ! is unique up to ≈ / ! 是唯一的，约等于 ≈ *)
}.

End Terminal.

Notation "1" := terminal_obj : object_scope.

(* Precomposing the unique map collapses: ! ∘ f ≈ !, since both land in `1`. / 将唯一映射进行预合成会塌缩：! ∘ f ≈ !，因为两者都落在 `1` 中。 *)
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

(* `one[x]` names the morphism `! : x ~> 1` at an explicit Terminal instance. / `one [x]ZZ ` 在一个明确的 Terminal 实例上命名了态射 `! : x ~> 1`。 *)
Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.

(*
 A "constant" map `x ~> y` factoring through `1`: pick `f : 1 ~> y`, then
 precompose with `! : x ~> 1`, so the result ignores its argument's data. 

 --------
 一个“常量”映射 `x ~> y` 通过 `1` 分解：选择 `f : 1 ~> y`，然后与 `! : x ~> 1` 进行前合成，这样结果就会忽略其参数的数据。
*)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].

(*
 Uniqueness of the terminal object (Mac Lane, CWM 2nd ed., §I.5, p. 20).

 Two [Terminal] structures on the same category need not choose the same
 object -- nothing in the class forces that -- but their chosen objects are
 canonically isomorphic. Each supplies the unique arrow into the other's
 object, and both round trips are arrows into a terminal object, so
 [one_unique] identifies them with the identity. This is the sense in which
 "the" terminal object is well defined, and it is what licenses the informal
 practice of speaking of *the* object `1`. 

 --------
 终对象的唯一性（Mac Lane，《范畴论概论》第二版，第I.5节，第20页）。

 在同一个范畴上，两个  [Terminal]  结构不必选择相同的对象——类中没有任何东西强制要求如此——但是它们所选择的对象是自然同构的。每个结构都会提供唯一的箭头指向对方的对象，并且两次往返都是指向终对象的箭头，因此  [one_unique]  将它们识别为恒等箭头。这就是“终对象”定义良好的意义，也是允许非正式地称之为 *the* 对象  `1` 的依据。
*)
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.

(*
 The isomorphism above is moreover the ONLY one, and indeed the only arrow
 at all between the two objects: every arrow into a terminal object is
 already pinned down by [one_unique]. Mac Lane states uniqueness of the
 object "up to a unique isomorphism"; this corollary is the "unique" half,
 and it makes [terminal_unique] canonical rather than merely one choice. 

 --------
 上面的同构此外还是唯一的，实际上也是两个对象之间唯一的箭头：每一个指向终对象的箭头都已经被 [one_unique] 固定了。Mac Lane 说对象的唯一性是“直到唯一同构”，这个推论就是“唯一性”的一半，它使得 [terminal_unique] 成为规范的，而不仅仅是一个选择。
*)
Corollary terminal_arrow_unique {C : Category} (T1 T2 : @Terminal C)
      (f g : @terminal_obj C T1 ~> @terminal_obj C T2) : f ≈ g.
Proof. apply (@one_unique C T2). Qed.

(*
 The object-level form of terminality (Riehl, CTiC, Def. 1.6.1).  The
 bundled [Terminal] class both *chooses* an object and asserts the
 universal property; when the object is already fixed -- as it is when
 terminality is used as a PREDICATE, e.g. to span a subcategory or to
 transport along an isomorphism -- the choice gets in the way.  Stated
 with [Unique] (Lib/Setoid.v), "there is exactly one arrow x ~> c" is
 literally "the hom-setoid x ~> c is contractible", the phrasing of the
 header of this file.  [Terminal_from_IsTerminalObj] and
 [IsTerminalObj_from_Terminal] convert in both directions, the latter
 landing on [terminal_obj] definitionally. 

 --------
 终端性的对象层面形式（Riehl，CTiC，定义 1.6.1）。捆绑的 [Terminal] 类既*选择*一个对象，又断言该对象具备广义性质；当对象已经固定时——例如当终端性作为谓词使用时，如用于生成一个子范畴或沿同构进行传输——选择反而成为障碍。用 [Unique]（Lib/Setoid.v）表述，“恰好存在一个箭头 x ~> c”字面意思是“同态集 x ~> c 是可收缩的”，这是该文件头部用语的表述。[Terminal_from_IsTerminalObj] 和 [IsTerminalObj_from_Terminal] 在两个方向上进行转换，后者在定义上落到 [terminal_obj]。
*)
Definition IsTerminalObj {C : Category} (c : C) : Type :=
  ∀ x : C, Unique (fun _ : x ~> c => True).

(* The unique arrow x ~> c supplied by the predicate. / 由谓词提供的唯一箭头 x ~> c。 *)
Definition is_terminal_one {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} : x ~> c := unique_obj (H x).

(* ... and its uniqueness, in the two-arrow form used by [one_unique]: both arrows agree with the chosen witness, hence with each other. / ...及其独特性，在 [one_unique] 使用的双箭头形式中：两根箭头都与所选的见证一致，因此也彼此一致。 *)
Lemma is_terminal_unique {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} (f g : x ~> c) : f ≈ g.
Proof.
  pose proof (uniqueness (H x) f I) as Hf.
  pose proof (uniqueness (H x) g I) as Hg.
  now rewrite <- Hf, <- Hg.
Qed.

(* Bundling: the predicate at c yields a [Terminal] structure choosing c. / 捆绑：在 c 的谓词产生了一个 [Terminal] 结构，选择 c。 *)
Program Definition Terminal_from_IsTerminalObj {C : Category} {c : C}
  (H : IsTerminalObj c) : @Terminal C := {|
  terminal_obj := c;
  one := fun x => @is_terminal_one C c H x
|}.
Next Obligation. now apply (is_terminal_unique H). Qed.

(* ... and conversely, unbundling at the chosen object. / ... 相反，在所选对象处进行拆包。 *)
Program Definition IsTerminalObj_from_Terminal {C : Category}
  (T : @Terminal C) : IsTerminalObj (@terminal_obj C T) := fun x =>
  {| unique_obj := @one C T x
   ; unique_property := I |}.
Next Obligation. now apply (@one_unique C T). Qed.

(*
 Riehl, CTiC, Exercise 1.6.ii(i): terminality is isomorphism-invariant.
 Any object isomorphic to a terminal object is itself terminal.  The
 arrow into y is the arrow into 1 followed across the isomorphism, and
 uniqueness transports back: two arrows into y agree as soon as their
 [from i] translates agree, which they do by [one_unique].  The result
 chooses y ON THE NOSE -- see [Terminal_iso_obj] in Block B -- so this
 is a genuine transport of structure, not merely an existence claim. 

 --------
 Riehl, CTiC, 练习 1.6.ii(i)：终对象性在同构下是不变的。任何与终对象同构的对象本身也是终对象。指向 y 的箭头是通过同构从指向 1 的箭头得到的，并且唯一性会传回：一旦它们的 [from i] 翻译一致，指向 y 的两个箭头就会一致，而它们确实通过 [one_unique] 一致。结果精确选择 y -- 见 Block B 中的 [Terminal_iso_obj] -- 因此这是结构的真实传递，而不仅仅是存在性的声明。
*)
Program Definition Terminal_iso {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @Terminal C := {|
  terminal_obj := y;
  one := fun x => to i ∘ @one C T x
|}.
Next Obligation.
  assert (Hf : to i ∘ (from i ∘ f) ≈ f)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  assert (Hg : to i ∘ (from i ∘ g) ≈ g)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  transitivity (to i ∘ (from i ∘ f)).
  - now symmetry.
  - now rewrite (@one_unique C T _ (from i ∘ f) (from i ∘ g)).
Qed.

(*
 Seven Sketches, Remark 3.85 ("unique up to unique isomorphism"), packaged as
 a single result rather than an existence lemma plus a separate appeal to
 [terminal_arrow_unique].

 The statement is [Unique] over the setoid [iso_setoid] of isomorphisms
 `1₁ ≅ 1₂`, whose equivalence [iso_equiv] compares BOTH the `to` and the
 `from` component.  So the three fields say, in order: such an isomorphism
 exists; the trivial predicate holds of it; and every isomorphism between
 the two objects is equal to it, in both directions.  Together that is
 exactly "there is exactly one isomorphism 1₁ ≅ 1₂" -- the predicate is
 [True] precisely so that the uniqueness clause quantifies over ALL
 isomorphisms and not merely over those satisfying some side condition. 

 --------
 《七个素描》，备注 3.85（“唯一性到唯一同构”），打包为一个单一结果，而不是作为一个存在引理加上对 [terminal_arrow_unique] 的单独引用。

 该陈述是在同构的集合 [iso_setoid] 上的 [Unique]，其等价关系 [iso_equiv] 比较 `to` 和 `from` 两个分量。因此，这三个字段依次说明：存在这样的同构；它满足平凡谓词；并且两个对象之间的每个同构都等于它，在两个方向上。组合在一起，这正是“恰好存在一个同构 1₁ ≅ 1₂”——谓词是 [True]，正是为了使唯一性条款对所有同构进行量化，而不仅仅是对满足某些附加条件的同构进行量化。
*)
Program Definition terminal_unique_up_to_unique_iso {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) := {|
  unique_obj := terminal_unique T1 T2;
  unique_property := I
|}.
Next Obligation.
  split.
  - apply (@one_unique C T2).
  - apply (@one_unique C T1).
Qed.

(*
 The sharper fact behind it: not only is the isomorphism unique, the
 underlying morphism is the unique morphism of its hom-setoid.  This is
 [terminal_arrow_unique] packaged as a [Unique], and it implies the
 isomorphism statement above. 

 --------
 更尖锐的事实是：不仅同构是唯一的，其底层态射也是其同态集合的唯一态射。这是以 [terminal_arrow_unique] 的形式封装为 [Unique]，并且它意味着上述同构声明。
*)
Program Definition terminal_hom_unique {C : Category} (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ~> @terminal_obj C T2 => True) := {|
  unique_obj := @one C T2 (@terminal_obj C T1);
  unique_property := I
|}.
Next Obligation. apply (@one_unique C T2). Qed.
