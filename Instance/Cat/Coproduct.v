(** * Cat has set-indexed coproducts / * 范畴具有集合下标的余积 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.
Require Category.Instance.StrictCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := program_simpl.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §III.5 Exercise 4, printed p. 74 (PDF p. 84) —
 maclane:III.5:ex4
 Book:      Riehl, “Category Theory in Context”, 2nd ed., §3.6 —
 riehl:3.6:construction-cat-coproducts

 The [Cat]-level packaging of Construction/Coproduct/Indexed.v: the
 disjoint-union category [SigmaCat C] of a family [C : I → Category],
 with its injections, IS the indexed coproduct of that family in
 [Cat], and [Cat] therefore has all set-indexed coproducts.

 - [SigmaCat_IsIndexedCoproduct]: the ELEMENTARY, apex-pinned form
 of Structure/Limit/Coproduct.v, supplied by [:=] with no tactic
 — the [∃!] of [SigmaCat_ump] IS that record's [desc] field, the
 [∘] of [Cat] being [Compose] and its [≈] being [Functor_Setoid],
 both definitionally
 - [Cat_HasIndexedCoproducts]: the class instance, likewise a [:=]

 1. THE ELEMENTARY FORM IS TAKEN FIRST, AND THE [Colimit] READING IS
 NOT DELIVERED.  Structure/Limit/Coproduct.v offers two shapes: the
 elementary [IsIndexedCoproduct f p inj], which mentions no
 diagram, and [icoprod]/[icoprod_ump], which read a
 [Limit (@DiscreteCat_Functor A (C^op) f)].  Only the first is
 used, and the second is not derived, for two reasons that are
 worth keeping apart.

 (i) RECORDED CORRECTION, AND THIS REASON NO LONGER HOLDS.  An
 earlier revision of this paragraph read: “[DiscreteCat_Functor]
 (Instance/Discrete.v) is declared with NO universe binders, so
 minimization instantiates [DiscreteCat@{u Set Set}] and routing
 through it pins the ambient category's hom and proof universes to
 [Set].  At [C := Cat], whose objects are categories, that would
 confine the result to categories-of-categories with [Set]-sized
 homs — a measured defect of the FUNCTOR, not of [DiscreteCat],
 which is properly annotated [@{o h p}].”  The diagnosis was right,
 and the defect was repaired: the functor was annotated in place at
 Instance/Discrete.v in the PR “algebraic carriers are sets”
 (2026-09-17), so it now leaves the ambient hom and proof universes
 free and confines nothing at [C := Cat].  Reason (ii) below is
 untouched by that repair and is on its own sufficient, which is why
 the passage is still not derived.  The same measurement is recorded
 in docs/INDEX.md for issues #331 and #335.

 (ii) Independently of universes, the passage does not exist: the
 tree carries [colimit_is_indexed_coproduct], which reads a
 [Limit] AS an [IsIndexedCoproduct], and no converse.  So a
 [Colimit] reading is not one step away from what is proved here;
 it would need a [Limit] of the discrete diagram built by hand.
 Neither is attempted.

 2. THE SMALLNESS SIDE CONDITION IS CARRIED BY UNIVERSES, NOT BY A
 HYPOTHESIS.  [HasIndexedCoproducts] quantifies [{A : Type}] as a
 universe PARAMETER of the class, and the instance below
 instantiates it AS STATED, with no variant.  The constraint that
 CARRIES THE MATHEMATICS is that the index type sits at or below
 [Cat]'s OBJECT universe — the universe at which the summand
 categories' own objects live — which is exactly Mac Lane's
 “small” index set.  Read that as the load-bearing one and not as
 the whole block: the block also carries [Projections.*] bounds on
 the index and on the summands' hom universe, inherited from the
 monomorphic stdlib [projT1]/[projT2], which are nothing to do
 with smallness (Construction/Coproduct/Indexed.v's header point 4
 records them).
 That is the discipline Instance/Sets/Products.v established for
 [Sets_HasIndexedProducts], and the reader is referred to that
 file's header for the general statement.  The condition BITES,
 and the section [Smallness] below pins where: at an index type as
 large as [obj[Cat]] itself, the CONSTRUCTION still elaborates —
 that is the positive control — but its result sits one universe
 up from the summands, so the elementary indexed-coproduct
 statement about it is rejected as a universe inconsistency.  This
 is the same phenomenon Theory/Size.v's erratum records for
 [Check (Cat : obj[Cat])]: written unpinned it succeeds only
 because the two occurrences are instantiated at different levels,
 and the honest test pins the instance.

 What the instance inherits and cannot shed is the identification
 of hom with proof universes in the summands and in the target,
 which Construction/Coproduct/Indexed.v measures and attributes to
 [Functor_Setoid] (Theory/Functor.v).  The CONSTRUCTION is
 free of it — [SigmaCat] keeps those universes apart — but the
 universal property is stated with [≈] on functors, which IS that
 setoid, so the instance carries it.  Not introduced here, and not
 claimed unavoidable.

 3. THE BINARY CASE, MEASURED STRICT-FIRST.  At [I := bool] the
 comparison with Construction/Coproduct.v's [C ∐ D] reaches
 ISOMORPHISM OF CATEGORIES: [SigmaBool_strict_iso] inhabits
 [SigmaCat (BoolFam C D) ≅[StrictCat] C ∐ D], both round trips
 holding at [Functor_StrictEq_Setoid] with every object component
 [eq_refl], and [SigmaBool_iso] is the DERIVED [≅[Cat]] reading —
 which in this library is only an EQUIVALENCE of categories
 (Instance/Cat.v's hom-setoid is [Functor_Setoid]), so the two
 must not be quoted interchangeably.  No stronger identification
 is ACHIEVED -- what is established is that [eq_refl] does not
 typecheck, a conversion failure; no impossibility of a Leibniz
 equality is proved -- and the two attempts are pinned rather than
 asserted: the underlying object types are not the same type
 ([∃ b : bool, BoolFam C D b] against [obj[C] + obj[D]]), so
 neither the objects nor the two [Category] records are Leibniz
 equal.  The comparison is between the two coproduct CATEGORIES;
 no relation between the two universal properties as records, and
 none with [Cat_Cocartesian], is claimed.  [Instance/StrictCat.v]
 is [Require]d WITHOUT [Import] and [StrictCat] named by its
 qualified path, deliberately: importing it puts a second
 [Category] instance in scope and instance resolution then picks
 it up in [Cat_HasIndexedCoproducts], which stops elaborating.

 4. THE NEGATIVE RESULT INSTANTIATED.  [inj_Full_forces_UIP_at_One]
 feeds the terminal category to
 Construction/Coproduct/Indexed.v's [sigma_inj_Full_forces_UIP]:
 if the injection into [∐_{i:I} 1] at [i] is full, then every loop
 at [i] is [eq_refl].  [_1] is the right witness because its
 hom-family [fun _ _ => poly_unit] does not depend on its
 endpoints, so the hypothesis that the relevant hom-sets are
 inhabited is discharged by [ttt] with no case analysis.

 THE COMPANION PROBE is Test/ProbeCatCoproduct338.v.  It pins the
 three boundaries neither target can state — the load-bearing
 universe binders and the [Functor_Setoid] localization (both
 FORMABILITY, both needing a section that declares levels strictly
 apart) and the binary object-type refutation (CONVERSION) — and it
 compiles the inhabitedness half of the encoding-(c) refutation that
 this file's header can only argue.

 WHAT IS NOT DELIVERED.  No [Colimit] or [DiscreteCat_Functor]
 reading (point 1).  No [Cocomplete Cat] and no other colimit in
 [Cat].  No comparison with [Cat_Cocartesian] as a STRUCTURE — the
 binary comparison below is between the two coproduct CATEGORIES, and
 nothing relates the two universal properties as records.  No
 [Initial]-vs-empty-index statement beyond [SigmaCat_empty_no_obj] —
 in particular [SigmaCat] over the empty index is not exhibited as
 [Instance/Zero.v]'s [_0], only shown to have no objects.  No
 distributivity of [Cat]'s products over these coproducts.  No
 [HasIndexedProducts Cat], which would be the dual packaging of
 Construction/Product/Indexed.v's [PiCat] and is untouched here. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，§III.5 练习4，印刷版第74页（PDF第84页）—— maclane:III.5:ex4
 书籍：Riehl，《上下文中的范畴论》，第2版，§3.6 —— riehl:3.6:construction-cat-coproducts

 Construction/Coproduct/Indexed.v 的 [Cat] 级别封装：一族 [C : I → Category] 的不交并范畴 [SigmaCat C] ，及其注入，是该族在 [Cat] 中的索引余积，因此 [Cat] 具有所有集合索引的余积。-  [SigmaCat_IsIndexedCoproduct]：Structure/Limit/Coproduct.v 的基础、顶点固定形式，由 [:=] 提供，无策略  
 — [∃!] 的 [SigmaCat_ump] 是该记录的 [desc] 字段，[Cat] 的 [∘] 是 [Compose]，其 [≈] 是 [Functor_Setoid]，  
 两者都是定义性的  
 -  [Cat_HasIndexedCoproducts]：类实例，同样是一个 [:=]  

 1. 首先采用基础形式，并且 [Colimit] 的读取未被提供。Structure/Limit/Coproduct.v 提供两种形态：  
 基础的 [IsIndexedCoproduct f p inj]，不提及任何图表，以及 [icoprod] / [icoprod_ump]，它读取一个 [Limit (@DiscreteCat_Functor A (C^op) f)]。  
 仅使用第一种，第二种未被推导，有两个原因，这两个原因值得区分开来。(i) 已记录的更正，因此此理由不再成立。该段落的早期修订版本写道：“[DiscreteCat_Functor]（Instance/Discrete.v）声明时没有宇宙绑定，因此最小化会实例化 [DiscreteCat@{u Set Set}]，并且通过它的路由会将环境类别的 Hom 和证明宇宙固定为 [Set]。”在 [C := Cat] 中，其对象是范畴，这会将结果限制在具有 [Set] 大小的同态的范畴的范畴——这是函子（FUNCTOR）的一个可测缺陷，而不是 [DiscreteCat] 的缺陷，后者正确地标注为 [@{o h p}]。诊断是正确的，缺陷已被修复：函子在 PR “algebraic carriers are sets”（2026-09-17）的 Instance/Discrete.v 中已就地标注，因此现在它不限制周围的同态和证明宇宙，并且在 [C := Cat] 处没有任何限制。下面的原因 (ii) 没有受到该修复的影响，并且本身就足够，这就是为什么该段落仍未被导出。同样的测量也记录在 docs/INDEX.md 中，针对问题 #331 和 #335。(ii) 独立于宇宙，该段落不存在：树携带 [colimit_is_indexed_coproduct]，其将 [Limit] 读取为 [IsIndexedCoproduct]，而不存在相反情况。因此，[Colimit] 的读取并不是与此处证明的内容相差一步；它将需要手工构建的离散图的 [Limit]。也未尝试过。2. 小性条件是由宇宙承担的，而不是由假设承担的。[HasIndexedCoproducts] 将 [{A : Type}] 量化为类的宇宙参数，下面的实例按所述实例化它，没有任何变体。承载数学的约束是索引类型位于或低于 [Cat] 的对象宇宙——这是求和类别自身对象所在的宇宙——这正是 Mac Lane 所说的“较小”的索引集合。将其理解为承载主要负荷的部分，而不是整个区块：该区块还承载 [Projections.*] 对索引和求和对象的同态宇宙的界限，这些界限继承自单态标准库 [projT1] / [projT2]，与小性无关（Construction/Coproduct/Indexed.v 的标题第 4 点记录了它们）。这是为 [Sets_HasIndexedProducts] 建立的学科 Instance/Sets/Products.v，读者可参阅该文件的头部以获取一般说明。条件 BITES，以及下面的部分 [Smallness] 指明了位置：在与 [obj[Cat] 本身一样大的索引类型上，CONSTRUCTION 仍然会展开——也就是说，这是正控制——但其结果位于比求和项高一个宇宙层次的位置，因此关于它的基本索引余积陈述被作为宇宙不一致而拒绝。这与 Theory/Size.v 的勘误所记录的 [Check (Cat : obj[Cat] 的现象相同）：未固定书写时，它仅因两处出现被实例化于不同层次而成功，而正确的测试会固定该实例。实例继承而无法去掉的是同构与求和项及目标中的证明宇宙的标识，Construction/Coproduct/Indexed.v 测量并归因于 [Functor_Setoid]（Theory/Functor.v）。构造本身不受其影响 — [SigmaCat] 将那些宇宙分开 — 但普遍性质是通过 [≈] 在函子上表述的，而这就是该集合等价关系，因此实例携带它。这里没有引入，也不声称不可避免。3. 二元情况，优先严格测量。在 [I := bool] 处，与 Construction/Coproduct.v 的 [C ∐ D] 比较达到范畴同构：[SigmaBool_strict_iso] 属于 [SigmaCat (BoolFam C D) ≅[StrictCat] C ∐ D]，两个往返在 [Functor_StrictEq_Setoid] 处对每个对象分量 [eq_refl] 都成立，并且 [SigmaBool_iso] 是 DERIVED [≅[Cat]] 的解读——在这个库中，这只是范畴的等价（Instance/Cat.v 的 hom-setoid 是 [Functor_Setoid]），因此两者不能互换引用。没有更强的等同实现——确定的是 [eq_refl] 无法进行类型检查，这是一个转换失败；没有证明莱布尼茨等式的不可能性——这两个尝试是固定的而非断言的：底层对象类型不是相同的类型（[∃ b : bool, BoolFam C D b] 对比 [obj[C] + 对象 [D]），所以对象以及两个 [Category] 记录都不是莱布尼茨等同的。比较的是两个余积类别；没有声称作为记录的两个泛性质之间存在关系，也没有与 [Cat_Cocartesian] 存在关系。[Instance/StrictCat.v] 是 [Require] d 没有 [Import] 和 [StrictCat]，通过其限定路径命名的，有意如此：导入它会在作用域中放置第二个 [Category] 实例，然后实例解析会在 [Cat_HasIndexedCoproducts] 中选择它，这会停止展开。

 4. 负结果被实例化。[inj_Full_forces_UIP_at_One] 将终端范畴提供给 Construction/Coproduct/Indexed.v 的 [sigma_inj_Full_forces_UIP]：如果在 [i] 处注入到 [∐_{i:I} 1] 是满的，那么在 [i] 的每个循环都是 [eq_refl]。[_1] 是正确的证明，因为它的同态族 [fun _ _ => poly_unit] 不依赖于它的端点，因此相关同态集有元素的假设由 [ttt] 消除，无需案例分析。伴随探针是 Test/ProbeCatCoproduct338.v。它固定了两个目标都无法陈述的三个边界——承重的宇宙绑定器和 [Functor_Setoid] 定位（两者都是可成型性，都需要一个严格区分级别的部分）以及二进制对象类型的驳斥（转换）——并且它编译了编码-(c) 驳斥中有住性的一半，而该文件的头只能对此进行论证。未交付内容。没有 [Colimit] 或 [DiscreteCat_Functor] 的读取（第1点）。没有 [Cocomplete Cat]，也没有 [Cat] 中的其他余积。没有将 [Cat_Cocartesian] 作为结构进行比较——下面的二进制比较是在两个余积范畴之间进行的，没有任何内容将这两个作为记录的泛性质联系起来。没有 [Initial] 对空索引的声明，除了 [SigmaCat_empty_no_obj] ——特别是 [SigmaCat] 在空索引上的情况没有作为 [Instance/Zero.v] 的 [_0] 展示，仅显示没有对象。没有 [Cat] 的乘积在这些余积上的分配性。没有 [HasIndexedProducts Cat]，它将是 Construction/Product/Indexed.v 的 [PiCat] 的对偶封装，这里未涉及。
*)

(** ** The indexed coproduct in Cat / ** Cat 中的索引余积 *)

(* Both of these are [:=] with no tactic: [SigmaCat_ump]'s [∃!] is literally the [desc] field the elementary record asks for. / 这两者都是 [:=]，没有策略：[SigmaCat_ump] 的 [∃!] 字段就是基本记录所要求的 [desc] 字段。 *)
Definition SigmaCat_IsIndexedCoproduct {I : Type} (C : I → Cat) :
  IsIndexedCoproduct C (SigmaCat C) (SigmaCat_inj C) :=
  Build_IsIndexedCoproduct C (SigmaCat C) (SigmaCat_inj C)
    (fun D F => SigmaCat_ump F).

#[export]
Instance Cat_HasIndexedCoproducts : @HasIndexedCoproducts Cat :=
  Build_HasIndexedCoproducts
    (fun A C => SigmaCat C)
    (fun A C a => SigmaCat_inj C a)
    (fun A C => SigmaCat_IsIndexedCoproduct C).

(* * ** Fullness of the injections forces UIP on the index / * ** 注射的充盈使UIP作用于指标 *)

(*
 The terminal category's homs do not depend on their endpoints, so
 the inhabitation hypothesis of [sigma_inj_Full_forces_UIP] is
 discharged by [ttt]. 

 --------
 终端范畴的 Hom 不依赖于它们的端点，因此 [sigma_inj_Full_forces_UIP] 的充足性假设被 [ttt] 消解。
*)
Theorem inj_Full_forces_UIP_at_One {I : Type} (i : I)
  (H : Full (SigmaCat_inj (fun _ : I => _1) i)) :
  ∀ e : i = i, e = eq_refl.
Proof.
  exact (sigma_inj_Full_forces_UIP (fun _ : I => _1) i ttt (fun _ => ttt) H).
Qed.

(** ** The singleton index / ** 单例索引 *)

Program Definition SigmaCat_unit_iso (D : Category) :
  SigmaCat (fun _ : poly_unit => D) ≅[Cat] D := {|
  to := SigmaCat_unit_collapse;
  from := SigmaCat_unit_expand;
  iso_to_from := SigmaCat_unit_round_l;
  iso_from_to := SigmaCat_unit_round_r
|}.

(* * ** Two summands: the construction is not degenerate / * ** 两个加数：构造不是退化的 *)

Definition BoolFam (C D : Category) (b : bool) : Category :=
  if b then C else D.

(* Across summands the hom is empty. / 在各个加数间，同态是空的。 *)
Lemma bool_cross_empty_lr (C D : Category) (x : C) (y : D) :
  ((true; x) ~{SigmaCat (BoolFam C D)}~> (false; y)) → False.
Proof. apply sigma_hom_cross_empty; simpl; discriminate. Qed.

Lemma bool_cross_empty_rl (C D : Category) (x : D) (y : C) :
  ((false; x) ~{SigmaCat (BoolFam C D)}~> (true; y)) → False.
Proof. apply sigma_hom_cross_empty; simpl; discriminate. Qed.

(*
 …so objects of different summands are not isomorphic: the summands
 are not merged. 

 --------
 …因此不同加数的对象不是同构的：这些加数没有合并。
*)
Lemma bool_summands_not_isomorphic (C D : Category) (x : C) (y : D) :
  @Isomorphism (SigmaCat (BoolFam C D)) (true; x) (false; y) → False.
Proof. intros iso; exact (bool_cross_empty_lr C D x y (to iso)). Qed.

(*
 The case functor genuinely does case analysis: over the two-object
 family it takes the two summands to two DIFFERENT objects of the
 target, by computation. 

 --------
 case 函子真正执行了 case 分析：在两对象族上，它通过计算将两个子项映射到目标的两个不同对象。
*)
Program Definition PointX : _1 ⟶ _2 := {|
  fobj := fun _ => TwoX;
  fmap := fun _ _ _ => id
|}.

Program Definition PointY : _1 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Definition TwoPointFuns (b : bool) : BoolFam _1 _1 b ⟶ _2 :=
  if b as b0 return (BoolFam _1 _1 b0 ⟶ _2) then PointX else PointY.

Example case_at_true :
  SigmaCat_case TwoPointFuns (true; ttt) = TwoX := eq_refl.

Example case_at_false :
  SigmaCat_case TwoPointFuns (false; ttt) = TwoY := eq_refl.

Lemma case_separates_summands :
  fobj[SigmaCat_case TwoPointFuns] (true; ttt)
    ≠ fobj[SigmaCat_case TwoPointFuns] (false; ttt).
Proof. discriminate. Qed.

(* * ** Comparison with the binary coproduct / * ** 与二元余积的比较 *)

(*
 The object and arrow actions of the comparison, factored out so that
 the [bool] case analysis happens once. 

 --------
 比较的对象和箭头操作被抽取出来，以便 [bool] 的情况分析只发生一次。
*)
Definition bool_to_obj (C D : Category) (b : bool) :
  BoolFam C D b → obj[C ∐ D] :=
  match b as b0 return BoolFam C D b0 → obj[C ∐ D] with
  | true => Datatypes.inl
  | false => Datatypes.inr
  end.

Definition bool_to_map (C D : Category) (b : bool) (x y : BoolFam C D b)
  (f : x ~> y) : bool_to_obj C D b x ~> bool_to_obj C D b y :=
  (match b as b0 return
     ∀ x0 y0 : BoolFam C D b0, (x0 ~> y0) →
       (bool_to_obj C D b0 x0 ~> bool_to_obj C D b0 y0)
   with
   | true => fun _ _ h => h
   | false => fun _ _ h => h
   end) x y f.

Definition sb_map (C D : Category)
  {X Y : sigma_obj (BoolFam C D)} (f : sigma_hom X Y) :
  bool_to_obj C D (`1 X) (`2 X) ~> bool_to_obj C D (`1 Y) (`2 Y) :=
  (match `1 f as e0 in _ = m return
     ∀ y0 : BoolFam C D m, (ob_cast (BoolFam C D) e0 (`2 X) ~> y0) →
       (bool_to_obj C D (`1 X) (`2 X) ~> bool_to_obj C D m y0)
   with
   | eq_refl => fun y0 h => bool_to_map C D (`1 X) (`2 X) y0 h
   end) (`2 Y) (`2 f).

#[local] Obligation Tactic := idtac.

Program Definition SigmaBool_to (C D : Category) :
  SigmaCat (BoolFam C D) ⟶ C ∐ D := {|
  fobj := fun X => bool_to_obj C D (`1 X) (`2 X);
  fmap := fun X Y f => sb_map C D f
|}.
Next Obligation.
  intros C D [b x] [c y]; simpl.
  intros [e1 f] [e2 g] [p Hp]; simpl in *.
  destruct p; simpl in *.
  destruct e1; simpl in *.
  destruct b; simpl in *; exact Hp.
Qed.
Next Obligation.
  intros C D [b x]; destruct b; simpl; reflexivity.
Qed.
Next Obligation.
  intros C D [b x] [c y] [d z] [e1 f] [e2 g]; simpl in *.
  destruct e1, e2; simpl in *.
  destruct b; simpl; reflexivity.
Qed.

Definition sb_from_obj (C D : Category) (x : obj[C] + obj[D]) :
  sigma_obj (BoolFam C D) :=
  match x with
  | Datatypes.inl c => (true; c)
  | Datatypes.inr d => (false; d)
  end.

(*
 Written as an explicit nested dependent match rather than left to
 [Program]: [Program]'s equation-passing match compilation blocks the
 conversions [inl c ~> inl c'] ≡ [c ~> c'] and
 [inl c ~> inr d] ≡ [False] that this definition lives on. 

 --------
 写成一个显式的嵌套依赖匹配，而不是交给 [Program] : [Program] 的方程传递匹配编译，这阻止了该定义所依赖的转换 [inl c ~> inl c'] ≡ [c ~> c'] 和 [inl c ~> inr d] ≡ [False]。
*)
Definition sb_from_map (C D : Category) (x y : obj[C] + obj[D])
  (f : x ~{C ∐ D}~> y) :
  sigma_hom (sb_from_obj C D x) (sb_from_obj C D y) :=
  (match x as x0 return
     ∀ f0 : x0 ~{C ∐ D}~> y,
       sigma_hom (sb_from_obj C D x0) (sb_from_obj C D y)
   with
   | Datatypes.inl c =>
     (match y as y0 return
        ∀ f0 : Datatypes.inl c ~{C ∐ D}~> y0,
          sigma_hom (sb_from_obj C D (Datatypes.inl c))
                    (sb_from_obj C D y0)
      with
      | Datatypes.inl c' => fun f0 => (eq_refl; f0)
      | Datatypes.inr d' => fun f0 => False_rect _ f0
      end)
   | Datatypes.inr d =>
     (match y as y0 return
        ∀ f0 : Datatypes.inr d ~{C ∐ D}~> y0,
          sigma_hom (sb_from_obj C D (Datatypes.inr d))
                    (sb_from_obj C D y0)
      with
      | Datatypes.inl c' => fun f0 => False_rect _ f0
      | Datatypes.inr d' => fun f0 => (eq_refl; f0)
      end)
   end) f.

Program Definition SigmaBool_from (C D : Category) :
  C ∐ D ⟶ SigmaCat (BoolFam C D) := {|
  fobj := sb_from_obj C D;
  fmap := sb_from_map C D
|}.
Next Obligation.
  intros C D x y f g H.
  destruct x, y; simpl in *; try contradiction;
  exists eq_refl; exact H.
Qed.
Next Obligation.
  intros C D x; destruct x; simpl; exists eq_refl; reflexivity.
Qed.
Next Obligation.
  intros C D x y z f g.
  destruct x, y, z; simpl in *; try contradiction;
  exists eq_refl; reflexivity.
Qed.

#[local] Obligation Tactic := program_simpl.

Lemma SigmaBool_round_to (C D : Category) :
  SigmaBool_to C D ◯ SigmaBool_from C D ≈ Id[C ∐ D].
Proof.
  unshelve eexists.
  - intros [c|d]; exact iso_id.
  - intros [c|d] [c'|d'] f; simpl in *; try contradiction;
    rewrite id_left, id_right; reflexivity.
Qed.

Lemma SigmaBool_round_from (C D : Category) :
  SigmaBool_from C D ◯ SigmaBool_to C D ≈ Id[SigmaCat (BoolFam C D)].
Proof.
  unshelve eexists.
  - intros [b x]; destruct b; exact iso_id.
  - intros [b x] [c y] [e f]; simpl in *.
    destruct e; simpl in *.
    destruct b; simpl in *; exists eq_refl; simpl;
    rewrite id_left, id_right; reflexivity.
Qed.

Program Definition SigmaBool_iso (C D : Category) :
  SigmaCat (BoolFam C D) ≅[Cat] C ∐ D := {|
  to := SigmaBool_to C D;
  from := SigmaBool_from C D;
  iso_to_from := SigmaBool_round_to C D;
  iso_from_to := SigmaBool_round_from C D
|}.

(*
 The comparison is STRICT: both round trips hold at
 [Functor_StrictEq_Setoid], with every object component [eq_refl], so
 the two categories are ISOMORPHIC and not merely equivalent. 

 --------
 比较是严格的：两个往返都保持在 [Functor_StrictEq_Setoid]，每个对象组件都在 [eq_refl]，所以这两个范畴是同构的，而不仅仅是等价的。
*)
Lemma SigmaBool_strict_to (C D : Category) :
  @equiv _ Functor_StrictEq_Setoid
    (SigmaBool_to C D ◯ SigmaBool_from C D) (Id[C ∐ D]).
Proof.
  unshelve eexists.
  - intros [c|d]; exact eq_refl.
  - intros [c|d] [c'|d'] f; simpl in *; try contradiction; reflexivity.
Qed.

Lemma SigmaBool_strict_from (C D : Category) :
  @equiv _ Functor_StrictEq_Setoid
    (SigmaBool_from C D ◯ SigmaBool_to C D)
    (Id[SigmaCat (BoolFam C D)]).
Proof.
  unshelve eexists.
  - intros [b x]; destruct b; exact eq_refl.
  - intros [b x] [c y] [e f]; simpl in *.
    destruct e; simpl in *.
    destruct b; simpl in *; exists eq_refl; reflexivity.
Qed.

Program Definition SigmaBool_strict_iso (C D : Category) :
  SigmaCat (BoolFam C D) ≅[Category.Instance.StrictCat.StrictCat] C ∐ D
  := {|
  to := SigmaBool_to C D;
  from := SigmaBool_from C D;
  iso_to_from := SigmaBool_strict_to C D;
  iso_from_to := SigmaBool_strict_from C D
|}.

(*
 …but no stronger identification is achieved.  The two categories are
 NOT the same record, and not even on the same object type:
 [∃ b : bool, BoolFam C D b] against [obj[C] + obj[D]].  Both
 refutations are CONVERSION failures, pinned here rather than
 asserted -- each was stripped and its error read.

 NOTE THE PARENTHESES in the second, and note WHY they are there: [∐]
 binds looser than [=], so the unparenthesised
 [SigmaCat (BoolFam C D) = C ∐ D] parses as
 [(SigmaCat (BoolFam C D) = C) ∐ D] and the [Fail] then fires on a
 TYPE error about [∐]'s argument -- certifying nothing.  This file
 shipped that FALSE PASS in an earlier revision, with this very
 comment asserting a conversion failure it did not have. 

 --------
 …但没有获得更强的识别。这两类不是同一记录，甚至不是同一对象类型：
 [∃ b : bool, BoolFam C D b] 对 [obj[C] + obj [D]]。两者的驳斥都是转换失败，这里被固定而不是断言——每个都被剥离并读取其错误。

 注意第二个中的括号，并注意它们存在的原因：[∐] 的绑定比 [=] 弱，因此未加括号的 [SigmaCat (BoolFam C D) = C ∐ D] 解析为 [(SigmaCat (BoolFam C D) = C) ∐ D]，然后 [Fail] 在 [∐] 的参数上触发类型错误——没有进行任何验证。这个文件在早期版本中就以这个错误通过了，并带有这条评论来断言它本不具有的转换失败。
*)
Fail Example SigmaBool_obj_strict (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = obj[C ∐ D] := eq_refl.

Fail Example SigmaBool_cat_strict (C D : Category) :
  SigmaCat (BoolFam C D) = (C ∐ D) := eq_refl.

(* * ** The smallness side condition, measured / * ** 小尺寸的侧条件，测量 *)

(*
 Over an index type as large as the OBJECTS of the very [Cat] the
 coproduct is to live in, the CONSTRUCTION still exists — but it
 lands one universe up, at [Category@{a e e}] where the summands are
 [Category@{d e e}] with [d < a] — so it is not an object of that
 [Cat], and the elementary indexed-coproduct statement about it is a
 universe inconsistency (“Cannot enforce d = _ because d < a <= _”).
 The [Check] immediately below is the positive control that the
 rejection is about the SIZE and not about the expression. 

 --------
 在一个像  [Cat]  这样大的索引类型上，余积仍然存在——但它落到上一个宇宙中，即  [Category@{a e e}] ，其中求和项是  [Category@{d e e}] ，带有  [d < a] ——所以它不是那个  [Cat] 的对象，而且关于它的基本索引余积声明是一个宇宙不一致性（“无法强制 d = _ 因为 d < a <= _”）。紧接在下面的  [Check] 是正向控制，表明被拒绝的是大小，而不是表达式。
*)
Section Smallness.
  Universe a b c d e.

  Check (fun (C : obj[Cat@{a b c d e}] → obj[Cat@{a b c d e}]) =>
           SigmaCat C).

  Fail Check (fun (C : obj[Cat@{a b c d e}] → obj[Cat@{a b c d e}]) =>
                SigmaCat_IsIndexedCoproduct C).
End Smallness.
