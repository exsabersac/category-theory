(* * * Functor categories over discrete shapes / * * 离散形状上的函子范畴 *)

Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.4, printed pp. 40–42 (PDF 50–52) — maclane:II.4:remark1,
 maclane:II.4:ex2, maclane:II.4:remark2
 Book:      Fong & Spivak, “Seven Sketches in Compositionality” (CUP,
 2019), §3.3.4 Examples 3.53 and 3.56, printed p. 96 (PDF
 p. 108) — 7sketches:3.3.4:example3.53,
 7sketches:3.3.4:example3.56
 nLab:      https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Functor_category

 Functor categories out of discrete shapes are function spaces.  Over
 the terminal category the functor category recovers the target; over
 a discrete set it is a power of the target, with NO naturality
 constraint anywhere — a morphism of diagrams over a discrete shape is
 a bare indexed family; over a two-element discrete target it computes
 characteristic functions, which is also how the functor category
 escapes a fixed universe when the domain is as large as the universe
 (Cantor's diagonal).

 - [Discrete_Transform]/[Discrete_hom_iso]: a bare family
 [∀ a, F a ~> G a] IS a natural transformation over a discrete
 shape (naturality is free), and the whole hom-setoid is
 componentwise — [Discrete_hom_iso] states it as a hom-setoid
 isomorphism in Sets, the discrete-shape analogue of
 [One_hom_iso] below
 - [Fun_Discrete_PiCat]: [DiscreteCat A, B] ≅ the indexed product
 [PiCat (fun _ : A => B)] in Cat — “B^A is an A-fold power of B”,
 for ANY index type A
 - [Fun_Discrete_power]: for finite shapes,
 [DiscreteCat (Fin.t n), B] ≅ [Pow B n], the n-fold iterated
 binary product B ∏ (B ∏ (… ∏ 1)) — Mac Lane's Exercise II.4.2
 - [Fun_Discrete_bool_subsets]: functors [DiscreteCat X] ⟶
 [DiscreteCat bool], up to natural isomorphism, are exactly the
 characteristic functions X → bool — the power-set computation
 - [cantor_predicates]/[cantor_bool]/[Fun_Discrete_no_surjection]:
 the diagonal argument, and with it the size half of Mac Lane's
 remark: no family of functors indexed by the domain's objects
 exhausts [DiscreteCat X, DiscreteCat bool]
 - [One_hom_iso]: the morphism half of [1, B] ≅ B as a hom-setoid
 isomorphism in Sets (Seven Sketches Example 3.53, stated for any
 B and instantiated at B := Sets)

 Design:

 1. THE OBJECT HALF OF [1, B] ≅ B IS ALREADY IN THE TREE.  Theory/
 Shapes.v proves [One_Fun_iso : [_1, C] ≅[Cat] C], and
 Instance/One.v and Instance/One/Diagonal.v already cite it; this
 file does not rebuild it.  What Seven Sketches Example 3.53 adds
 is the MORPHISM half stated at the hom-setoid level, [One_hom_iso]
 below.  Example 3.56 states the object half as an *equivalence*
 of categories; the in-tree statement is an isomorphism in [Cat],
 which by Instance/Cat.v's convention (hom-setoid = natural
 isomorphism of functors) IS equivalence-strength, so the stronger
 packaging costs nothing and is what is reported.

 2. EVERYTHING FACTORS THROUGH THE INDEXED PRODUCT.  The finite-power
 statement is proven once at the level of families
 ([Fun_Discrete_PiCat], for any index type) and then by induction
 on n entirely inside [PiCat], where morphisms are componentwise
 and no naturality obligation ever arises: [PiCat_Fin_zero] peels
 the empty case to the terminal category, [PiCat_Fin_succ] peels
 one component off [Fin.t (S n)] via [Fin.caseS'], and the local
 congruence isomorphism [second_iso] (from [Cartesian]'s [second]
 calculus) transports the induction hypothesis across [B ∏ −].
 The n-fold power [Pow B n] takes the nullary case to be the
 terminal category [_1], the standard empty product, so Exercise
 II.4.2's “finite power” reads uniformly for all n.  The
 trailing terminal factor can be collapsed with the right
 unitor [prod_one_r]; [Fun_Discrete_power_two_flat] exhibits
 the collapse at n = 2, giving the book's literal “B ∏ B” — at
 general n the collapse would iterate [second_iso] down the
 spine (the [_1] sits innermost), and that general flat form is
 not stated here.

 3. THE POWER-SET COMPUTATION IS CONSTRUCTIVE, SO IT LANDS ON
 DECIDABLE SUBSETS.  A functor [DiscreteCat X ⟶ DiscreteCat bool]
 is, up to the ambient natural isomorphism, exactly a
 characteristic function X → bool ([Fun_Discrete_bool_subsets] —
 isomorphisms in [DiscreteCat bool] are equality proofs, so the
 Functor_Setoid equivalence collapses to pointwise equality).
 Classically X → bool is the power set of X; constructively it is
 the DECIDABLE subsets, the same reading as
 Instance/FinSet/Classifier.v's Ω := 2, and the classical power
 set would instead take values in a [Prop]-valued target one
 universe up (Instance/Sets/Classifier.v's [PropSetoid]).  Mac
 Lane's two-object case is stated for bool, where his counting
 remark is exact.

 4. THE SIZE REMARK IS A THEOREM, NOT A UNIVERSE INCIDENT.  Mac
 Lane's second remark — for a universe-sized discrete domain the
 functor category outgrows the universe — is rendered structurally
 by the library's universe discipline ([Category@{o h p}] with
 [Cat]'s objects one level down; Instance/Cat.v's size note).
 What CAN be said inside a single universe is the diagonal
 argument behind it: [cantor_predicates] (no family of predicates
 indexed by A is extensionally surjective onto A → Prop) and
 [cantor_bool] (likewise for A → bool), both bare inductions with
 no axioms; [Fun_Discrete_no_surjection] then connects the bool
 form through the characteristic-function correspondence: no
 X-indexed family of functors exhausts
 [DiscreteCat X, DiscreteCat bool] up to natural isomorphism —
 “B^X is strictly bigger than X” at the smallest interesting B. 

 --------
 书籍：      Mac Lane，《为工作数学家准备的范畴论》，第2版，
 §II.4，印刷页40–42（PDF 50–52）—— maclane:II.4:remark1,
 maclane:II.4:ex2, maclane:II.4:remark2
 书籍：      Fong & Spivak，《组合性中的七个范例》（CUP，
 2019），§3.3.4 示例3.53和3.56，印刷页96（PDF
 页108）—— 7sketches:3.3.4:example3.53,
 7sketches:3.3.4:example3.56
 nLab：       https://ncatlab.org/nlab/show/functor+category 
 维基百科：  https://en.wikipedia.org/wiki/Functor_category从离散形状出的函子范畴是函数空间。在终结范畴上，函子范畴恢复目标；在离散集合上，它是目标的幂，没有任何自然性约束——在离散形状上的图的态射只是一个单纯的带下标族；在一个两元素离散目标上，它计算特征函数，这也是当定义域与宇宙一样大时，函子范畴如何突破固定宇宙（康托尔对角线法）。-  [Discrete_Transform] / [Discrete_hom_iso]：一个裸族
 [∀ a, F a ~> G a] 是一个在离散形上的自然变换（自然性是免费的），并且整个同态集合是按分量计算的——[Discrete_hom_iso] 将其描述为集合中的同态集合同构，是下面 [One_hom_iso] 的离散形类比
 -  [Fun_Discrete_PiCat]：[DiscreteCat A, B] ≅ Cat 中的索引积 [PiCat (fun _ : A => B)] ——“B^A 是 B 的 A 倍幂”，对于任何索引类型 A
 -  [Fun_Discrete_power]：对于有限形，[DiscreteCat (Fin.t n), B] ≅ [Pow B n]，即 n 重迭代二元积 B ∏ (B ∏ (… ∏ 1)) —— Mac Lane 练习 II.4.2
 -  [Fun_Discrete_bool_subsets]：函子 [DiscreteCat X] ⟶ [DiscreteCat bool]，在自然同构下，正好是特征函数 X → bool —— 幂集计算
 -  [cantor_predicates] / [cantor_bool] / [Fun_Discrete_no_surjection]：对角论证，以及 wi它是 Mac Lane 评论大小的一半：没有一个由该域对象索引的函子族可以穷尽 [DiscreteCat X, DiscreteCat bool]
 - [One_hom_iso]：作为 Sets 中同集体同构的 [1, B] 的态射的一半 ≅ B（《七个草图》示例 3.53，对任意 B 说明，并在 B := Sets 时实例化）设计：

 1. [1, B] ≅ B 的对象部分已经在树中。Theory/Shapes.v 证明了 [One_Fun_iso : [_1, C] ≅ [Cat] C]，并且 Instance/One.v 和 Instance/One/Diagonal.v 已经引用了它；这个文件没有重新构建它。七个示例 3.53 添加的是在 hom-setoid 级别声明的同态部分 [One_hom_iso]。示例 3.56 将对象部分表示为类别的等价；树中的声明是在 [Cat] 中的同构，根据 Instance/Cat.v 的约定（hom-setoid = 函子自然同构）就是等价强度，因此更强的封装不增加任何成本，并且就是报告的内容。2. 一切通过索引积进行因式分解。有限次幂的陈述在族层面上（[Fun_Discrete_PiCat]，对于任意索引类型）被证明成立，然后在 [PiCat] 中完全通过关于 n 的归纳进行证明，在这里态射是逐分量的，并且不会出现任何自然性义务：[PiCat_Fin_zero] 将空情况剥离到终端范畴，[PiCat_Fin_succ] 通过 [Fin.caseS'] 从 [Fin.t (S n)] 剥离一个分量，本地合同同构 [second_iso]（来源于 [Cartesian] 的 [second] 演算）将归纳假设沿 [B ∏ −] 传递。n 重幂 [Pow B n] 将零元情况视为终端范畴 [_1]，即标准空积，因此练习 II.4.2 的“有限次幂”对所有 n 的读法都是一致的。尾端末端因子可以与右结合子 [prod_one_r] 合并；[Fun_Discrete_power_two_flat] 在 n = 2 时表现出合并，给出书中的字面 “B ∏ B” —— 在一般 n 下，合并会沿着书脊重复 [second_iso] （[_1] 位于最内侧），这里没有说明这种一般的平展形式。3. 幂集计算是构造性的，因此它落在可判定子集上。函子 [DiscreteCat X ⟶ DiscreteCat bool]，在总体自然同构下，恰好是一个特征函数 X → bool（[Fun_Discrete_bool_subsets] — [DiscreteCat bool] 中的同构是相等性证明，所以 Functor_Setoid 等价退化为逐点相等）。从经典角度来看，X → bool 是 X 的幂集；从构造性角度来看，它是可判定子集，与 Instance/FinSet/Classifier.v 中 Ω := 2 的解读相同，而经典的幂集则会取值于一 [Prop] 值的目标单一宇宙上（Instance/Sets/Classifier.v 的 [PropSetoid]）。Mac Lane 的双对象情况是针对 bool 陈述的，他关于计数的备注是精确的。4. 关于大小的评论是一个定理，而不是宇宙事件。Mac Lane 的第二条评论——对于一个宇宙大小的离散域，函子范畴会超出该宇宙——通过库的宇宙规范被结构化地体现出来（[Category@{o h p}] 与 [Cat] 的对象降低一级；Instance/Cat.v 的大小注释）。在单一宇宙内可以说的是其背后的对角论证：[cantor_predicates]（没有以 A 为索引的谓词族在外延上是 A → Prop 的满射）以及 [cantor_bool]（对 A → bool 同样适用），都是无公理的基本归纳；然后 [Fun_Discrete_no_surjection] 通过特征函数对应将布尔形式联系起来：没有以 X 为索引的函子族能够穷尽 [DiscreteCat X, DiscreteCat bool]，直到自然同构——在最小有趣的 B 上，“B^X 比 X 严格更大”。
*)

(* * ** Natural transformations over a discrete shape are bare families / * ** 在离散形状上的自然变换是裸族 *)

(*
 Over a discrete domain, naturality is free: the only morphisms are
 equality proofs, and both functors send them into the conjugates of
 identities.  So a transformation is exactly a family of components. 

 --------
 在离散域上，自然性是免费的：唯一的态射是等式证明，并且两个函子都将它们映射到恒等式的共轭。因此，变换恰好是一族分量。
*)
Program Definition Discrete_Transform {A : Type} {B : Category}
        {F G : DiscreteCat A ⟶ B} (η : ∀ a : A, F a ~> G a) : F ⟹ G := {|
  transform := η
|}.
Next Obligation.
  intros A B F G η x y e; destruct e; simpl.
  assert (HF : fmap[F] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ F x).
  assert (HG : fmap[G] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ G x).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros A B F G η x y e; destruct e; simpl.
  assert (HF : fmap[F] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ F x).
  assert (HG : fmap[G] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ G x).
  rewrite HF, HG; cat.
Qed.

(*
 The characterization as a hom-setoid isomorphism in Sets: over a
 discrete shape the transformation setoid IS the setoid of
 componentwise families — the discrete-shape analogue of
 [One_hom_iso], and the morphism half of [Fun_Discrete_PiCat]. 

 --------
 在集合中的同类集等价范畴同构的表述：在离散形状上，变换等价集就是逐分量族的等价集——[One_hom_iso] 的离散形状类比，以及 [Fun_Discrete_PiCat] 的态射部分。
*)
Program Definition Discrete_hom_iso {A : Type} {B : Category}
        (F G : DiscreteCat A ⟶ B) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid (DiscreteCat A) B F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := ∀ a : A, F a ~> G a;
     is_setoid := {| equiv := fun η θ => ∀ a : A, η a ≈ θ a |} |} := {|
  to   := {| morphism := fun η a => η a |};
  from := {| morphism := fun η => Discrete_Transform η |}
|}.
Next Obligation.
  intros A B F G; constructor.
  - intros η a; reflexivity.
  - intros η θ Hηθ a; symmetry; exact (Hηθ a).
  - intros η θ ρ H1 H2 a; transitivity (θ a); [ exact (H1 a) | exact (H2 a) ].
Qed.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B F G η a; reflexivity.
Qed.
Next Obligation.
  intros A B F G η a; reflexivity.
Qed.

(* * ** The functor category over a discrete shape is an indexed product / * ** 离散形状上的函子范畴是一个索引积 *)

Program Definition Fun_Discrete_to {A : Type} {B : Category} :
  [DiscreteCat A, B] ⟶ PiCat (fun _ : A => B) := {|
  fobj := fun F a => F a;
  fmap := fun F G η a => η a
|}.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  (* the Fun identity's component at a is [fmap[F] eq_refl] / 在 a 处的 Fun 恒等式的分量是 [fmap[F] eq_refl] *)
  intros A B F a; exact (@fmap_id _ _ F a).
Qed.
Next Obligation.
  intros A B F G H η θ a; reflexivity.
Qed.

Program Definition Fun_Discrete_from {A : Type} {B : Category} :
  PiCat (fun _ : A => B) ⟶ [DiscreteCat A, B] := {|
  fobj := fun f => DiscreteCat_Functor f;
  fmap := fun f g η => Discrete_Transform (F:=DiscreteCat_Functor f)
                                          (G:=DiscreteCat_Functor g) η
|}.
Next Obligation.
  intros A B f g η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B f a; reflexivity.
Qed.
Next Obligation.
  intros A B f g h η θ a; reflexivity.
Qed.

(*
 The comparison functor [Fun_Discrete_from ◯ Fun_Discrete_to] rebuilds a
 functor from its object function; the rebuilt functor is naturally
 isomorphic to the original with identity components. 

 --------
 比较函子 [Fun_Discrete_from ◯ Fun_Discrete_to] 从其对象函数重建一个函子；重建的函子自然同构于原来的函子，其分量是恒等映射。
*)
Program Definition DiscreteCat_Functor_iso {A : Type} {B : Category}
        (F : DiscreteCat A ⟶ B) :
  @Isomorphism ([DiscreteCat A, B]) (DiscreteCat_Functor (fobj[F])) F := {|
  to   := Discrete_Transform (F:=DiscreteCat_Functor (fobj[F])) (G:=F)
                             (fun a => id);
  from := Discrete_Transform (F:=F) (G:=DiscreteCat_Functor (fobj[F]))
                             (fun a => id)
|}.
Next Obligation.
  intros A B F a; simpl; cat.
Qed.
Next Obligation.
  intros A B F a; simpl; cat.
Qed.

Program Definition Fun_Discrete_PiCat {A : Type} {B : Category} :
  [DiscreteCat A, B] ≅[Cat] PiCat (fun _ : A => B) := {|
  to   := Fun_Discrete_to;
  from := Fun_Discrete_from
|}.
Next Obligation.
  intros A B.
  exists (fun f => iso_id).
  intros f g η a; simpl; cat.
Qed.
Next Obligation.
  intros A B.
  exists (fun F => DiscreteCat_Functor_iso F).
  intros F G η x; simpl; cat.
Qed.

(** ** Finite powers / ** 有限幂 *)

(*
 The n-fold power of a category, as an iterated binary product with the
 terminal category as the empty product. 

 --------
 一个范畴的n次幂，作为与终结范畴的迭代二元积的迭代积，将其视为空积。
*)
Fixpoint Pow (B : Category) (n : nat) : Category :=
  match n with
  | O => _1
  | S m => B ∏ Pow B m
  end.

(*
 [Cartesian]'s [second] calculus makes [z × −] carry isomorphisms; at
 [Cat] this transports the induction hypothesis across [B ∏ −]. 

 --------
 [Cartesian] 的 [second] 微积分使 [z × −] 承载同构；在 [Cat] 处，这将归纳假设传递到 [B ∏ −] 上。
*)
Program Definition second_iso {C : Category} `{@Cartesian C}
        {z x y : C} (f : x ≅ y) : z × x ≅ z × y := {|
  to   := second (to f);
  from := second (from f)
|}.
Next Obligation.
  intros C H z x y f.
  rewrite <- second_comp.
  rewrite iso_to_from.
  apply second_id.
Qed.
Next Obligation.
  intros C H z x y f.
  rewrite <- second_comp.
  rewrite iso_from_to.
  apply second_id.
Qed.

(* Any two choice functions on the empty shape are isomorphic in the product, with vacuous components. / 在空形上的任意两个选择函数在积中都是同构的，并且具有空的分量。 *)
Program Definition PiCat_Fin_zero_component (B : Category)
        (f : obj[PiCat (fun _ : Fin.t 0 => B)]) :
  @Isomorphism (PiCat (fun _ : Fin.t 0 => B))
               (fun i => Fin.case0 (fun _ => B) i) f := {|
  to   := fun i =>
    Fin.case0 (fun i' => Fin.case0 (fun _ => B) i' ~> f i') i;
  from := fun i =>
    Fin.case0 (fun i' => f i' ~> Fin.case0 (fun _ => B) i') i
|}.
Next Obligation.
  intros B f i; inversion i.
Qed.
Next Obligation.
  intros B f i; inversion i.
Qed.

(* The empty power: no components, so the product collapses to the point. / 空的力量：没有组件，所以产品崩溃到那个点。 *)
Program Definition PiCat_Fin_zero (B : Category) :
  PiCat (fun _ : Fin.t 0 => B) ≅[Cat] _1 := {|
  to   := Erase _;
  from := {| fobj := fun _ i => Fin.case0 (fun _ => B) i;
             fmap := fun _ _ _ i =>
               Fin.case0 (fun i' => Fin.case0 (fun _ => B) i'
                                      ~> Fin.case0 (fun _ => B) i') i |}
|}.
Next Obligation.
  intros B x i; inversion i.
Qed.
Next Obligation.
  intros B x y z f g i; inversion i.
Qed.
Next Obligation.
  intros B.
  unshelve eexists.
  - intro x; destruct x; exact iso_id.
  - intros x y f; destruct x, y, f; simpl; reflexivity.
Qed.
Next Obligation.
  intros B.
  exists (fun f => PiCat_Fin_zero_component B f).
  intros f g η i; inversion i.
Qed.

(*
 Splitting a pair into its components and repairing is the identity up
 to an identity-component isomorphism (pair eta is not definitional). 

 --------
 将一对拆分为其组成部分并进行修复是在一个单位-分量同构下的恒等（对的 eta 不是定义性的）。
*)
Program Definition PiCat_Fin_succ_component (B : Category) (n : nat)
        (p : obj[B ∏ PiCat (fun _ : Fin.t n => B)]) :
  @Isomorphism (B ∏ PiCat (fun _ : Fin.t n => B))
               (fst p, fun i => snd p i) p := {|
  to   := (id, fun i => id);
  from := (id, fun i => id)
|}.
Next Obligation.
  intros B n p; split; [ simpl; cat | intro i; simpl; cat ].
Qed.
Next Obligation.
  intros B n p; split; [ simpl; cat | intro i; simpl; cat ].
Qed.

(*
 Rebuilding a choice function on [Fin.t (S n)] from its head and tail
 is the identity componentwise. 

 --------
 从其头部和尾部重建 [Fin.t (S n)] 上的选择函数是按分量的恒等映射。
*)
Program Definition PiCat_Fin_succ_rebuild (B : Category) (n : nat)
        (f : obj[PiCat (fun _ : Fin.t (S n) => B)]) :
  @Isomorphism (PiCat (fun _ : Fin.t (S n) => B))
               (fun i => Fin.caseS' i (fun _ => B) (f Fin.F1)
                           (fun j => f (Fin.FS j))) f := {|
  to   := fun i => Fin.caseS' i
            (fun i' => Fin.caseS' i' (fun _ => B) (f Fin.F1)
                         (fun j => f (Fin.FS j)) ~> f i')
            id (fun j => id);
  from := fun i => Fin.caseS' i
            (fun i' => f i' ~> Fin.caseS' i' (fun _ => B) (f Fin.F1)
                                (fun j => f (Fin.FS j)))
            id (fun j => id)
|}.
Next Obligation.
  intros B n f i.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.
Next Obligation.
  intros B n f i.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.

(* Peeling one component off a finite power. / 从有限幂中剥离一个分量。 *)
Program Definition PiCat_Fin_succ (B : Category) (n : nat) :
  PiCat (fun _ : Fin.t (S n) => B) ≅[Cat]
  B ∏ PiCat (fun _ : Fin.t n => B) := {|
  to   := {| fobj := fun f => (f Fin.F1, fun i => f (Fin.FS i));
             fmap := fun f g η => (η Fin.F1, fun i => η (Fin.FS i)) |};
  from := {| fobj := fun p i => Fin.caseS' i (fun _ => B) (fst p) (snd p);
             fmap := fun p q h i =>
               Fin.caseS' i (fun i' =>
                 Fin.caseS' i' (fun _ => B) (fst p) (snd p)
                   ~> Fin.caseS' i' (fun _ => B) (fst q) (snd q))
                 (fst h) (fun j => snd h j) |}
|}.
Next Obligation.
  intros B n f g η θ Hηθ; split.
  - exact (Hηθ Fin.F1).
  - intro i; exact (Hηθ (Fin.FS i)).
Qed.
Next Obligation.
  intros B n f; split; [ reflexivity | intro i; reflexivity ].
Qed.
Next Obligation.
  intros B n f g h η θ; split; [ reflexivity | intro i; reflexivity ].
Qed.
Next Obligation.
  intros B n p q h h' Hh i.
  pattern i; apply (Fin.caseS' i); simpl.
  - exact (fst Hh).
  - intro j; exact (snd Hh j).
Qed.
Next Obligation.
  intros B n p i.
  pattern i; apply (Fin.caseS' i); simpl.
  - reflexivity.
  - intro j; reflexivity.
Qed.
Next Obligation.
  intros B n p q r h h' i.
  pattern i; apply (Fin.caseS' i); simpl.
  - reflexivity.
  - intro j; reflexivity.
Qed.
Next Obligation.
  intros B n.
  exists (fun p => PiCat_Fin_succ_component B n p).
  intros p q h; split.
  - simpl; cat.
  - intro i; simpl; cat.
Qed.
Next Obligation.
  intros B n.
  exists (fun f => PiCat_Fin_succ_rebuild B n f).
  intros f g η i; simpl.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.

(* The finite power, by induction at the level of families. / 通过在家族层面的归纳有限的力量。 *)
Fixpoint PiCat_Fin_power (B : Category) (n : nat) :
  PiCat (fun _ : Fin.t n => B) ≅[Cat] Pow B n :=
  match n with
  | O => PiCat_Fin_zero B
  | S m => iso_compose (second_iso (PiCat_Fin_power B m)) (PiCat_Fin_succ B m)
  end.

(*
 Mac Lane Exercise II.4.2: for a finite discrete shape, the functor
 category is a finite power of the target. 

 --------
 Mac Lane 练习 II.4.2：对于一个有限离散的形状，函子范畴是目标的有限冥次方。
*)
Definition Fun_Discrete_power (B : Category) (n : nat) :
  [DiscreteCat (Fin.t n), B] ≅[Cat] Pow B n :=
  iso_compose (PiCat_Fin_power B n) Fun_Discrete_PiCat.

(* The shape of the first interesting instance, for the record. / 作为记录，第一个有趣实例的形状。 *)
Example Fun_Discrete_power_two (B : Category) :
  [DiscreteCat (Fin.t 2), B] ≅[Cat] B ∏ (B ∏ _1) :=
  Fun_Discrete_power B 2.

(* Collapsing the trailing terminal factor by the right unitor recovers the book's literal n-fold shape: at n = 2, “B ∏ B”. / 通过右单位元塌缩尾端终端因子，可以恢复书中的字面 n 重形状：当 n = 2 时，“B ∏ B”。 *)
Example Fun_Discrete_power_two_flat (B : Category) :
  [DiscreteCat (Fin.t 2), B] ≅[Cat] B ∏ B :=
  iso_compose (second_iso prod_one_r) (Fun_Discrete_power B 2).

(** ** The power-set computation / ** 幂集计算 *)

(* An equality of objects of a discrete category, as an isomorphism. / 作为同构的离散范畴对象的等式。 *)
Program Definition Discrete_iso_of_eq {A : Type} {x y : A} (e : x = y) :
  @Isomorphism (DiscreteCat A) x y := {|
  to := e; from := eq_sym e
|}.
Next Obligation.
  intros A x y e; destruct e; reflexivity.
Qed.
Next Obligation.
  intros A x y e; destruct e; reflexivity.
Qed.

(*
 The setoid of objects of a functor category — functors up to the
 ambient natural isomorphism — packaged as an object of Sets. 

 --------
 函子范畴的对象的集合 —— 在环境自然同构下的函子 —— 包装为 Sets 的一个对象。
*)
Definition Fun_objects_setoid (C D : Category) : SetoidObject := {|
  carrier := C ⟶ D;
  is_setoid := @Functor_Setoid C D
|}.

(* Characteristic functions X → bool under pointwise equality. / 特征函数 X → bool 在逐点相等下。 *)
Program Definition CharFun_setoid (X : Type) : SetoidObject := {|
  carrier := X → bool;
  is_setoid := {| equiv := fun f g => ∀ x : X, f x = g x |}
|}.
Next Obligation.
  intro X; equivalence.
  now rewrite H, H0.
Qed.

(*
 Functors from a discrete shape into the discrete two-object target,
 up to natural isomorphism, are exactly characteristic functions: an
 isomorphism in [DiscreteCat bool] IS an equality proof, so the
 Functor_Setoid equivalence collapses to pointwise equality. 

 --------
 从离散形状到离散双对象目标的函子，直到自然同构，正好是特征函数：在  [DiscreteCat bool] 中，一个同构就是一个等式证明，因此 Functor_Setoid 等价简化为逐点等式。
*)
Program Definition Fun_Discrete_bool_subsets (X : Type) :
  Fun_objects_setoid (DiscreteCat X) (DiscreteCat bool) ≅[Sets]
  CharFun_setoid X := {|
  to   := {| morphism := fun F x => F x |};
  from := {| morphism := fun f : X → bool =>
               @DiscreteCat_Functor X (DiscreteCat bool) f |}
|}.
Next Obligation.
  intros X F G HFG x.
  exact (to (`1 HFG x)).
Qed.
Next Obligation.
  intros X f g Hfg.
  exists (fun x => Discrete_iso_of_eq (Hfg x)).
  intros x y e; destruct e; simpl.
  now destruct (Hfg x).
Qed.
Next Obligation.
  intros X f x; reflexivity.
Qed.
Next Obligation.
  intros X F.
  exists (fun x => iso_id).
  intros x y e; destruct e; simpl.
  assert (E : fmap[F] (@eq_refl X x) = @eq_refl bool (F x))
    by apply (@fmap_id _ _ F x).
  rewrite E; reflexivity.
Qed.

(** ** The diagonal argument / ** 对角线论证 *)

(*
 No family of predicates indexed by A is extensionally surjective onto
 the predicates on A: the diagonal predicate [fun x => ¬ f x x]
 differs from every member of the family at its own index.  Fully
 constructive — the biconditional at the diagonal point is already a
 contradiction. 

 --------
 没有一个以 A 为索引的谓词族在外延上可以满射到 A 上的谓词：对角谓词 [fun x => ¬ f x x] 在其自身索引处与族中的每个成员都不同。完全构造性 —— 对角点处的双条件语句已经是一个矛盾。
*)
Theorem cantor_predicates {A : Type} (f : A → A → Prop) :
  ¬ (∀ P : A → Prop, ∃ a : A, ∀ x : A, f a x ↔ P x).
Proof.
  intro H.
  destruct (H (fun x => ¬ f x x)) as [a Ha].
  specialize (Ha a).
  destruct Ha as [Hto Hfrom].
  assert (Hn : ¬ f a a) by (intro h; exact (Hto h h)).
  exact (Hn (Hfrom Hn)).
Qed.

(* The boolean form: the diagonal flips its own value. / 布尔形式：对角线翻转其自身的值。 *)
Theorem cantor_bool {A : Type} (f : A → A → bool) :
  ¬ (∀ g : A → bool, ∃ a : A, ∀ x : A, f a x = g x).
Proof.
  intro H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  specialize (Ha a).
  destruct (f a a); discriminate.
Qed.

(*
 The size half of Mac Lane's remark, through the characteristic-function
 correspondence: no X-indexed family of functors exhausts
 [DiscreteCat X, DiscreteCat bool] up to natural isomorphism.  The
 two-valued target is the smallest at which the functor category
 already outgrows the shape; for a universe-sized discrete shape the
 escape is structural (Instance/Cat.v's size note). 

 --------
 通过特征函数对应，麦克莱恩评论的一半大小：没有 X 索引的函子族能够将 [DiscreteCat X, DiscreteCat bool] 完全涵盖到自然同构为止。双值目标是函子范畴已经超过形状的最小值；对于一个宇宙大小的离散形状，这种逃逸是结构性的（Instance/Cat.v 的大小说明）。
*)
Theorem Fun_Discrete_no_surjection {X : Type}
        (Φ : X → (DiscreteCat X ⟶ DiscreteCat bool)) :
  ¬ (∀ G : DiscreteCat X ⟶ DiscreteCat bool,
       ∃ a : X, Φ a ≈ G).
Proof.
  intro H.
  apply (cantor_bool (fun a x => Φ a x)).
  intro g.
  destruct (H (@DiscreteCat_Functor X (DiscreteCat bool) g)) as [a Ha].
  exists a.
  intro x.
  exact (to (`1 Ha x)).
Qed.

(* * ** The morphism half of [1, B] ≅ B (Seven Sketches, Example 3.53) / * ** [1, B] 的态射一半 ≅ B（《七个草图》，例 3.53） *)

(*
 Between two functors from the terminal category, a natural
 transformation is exactly a morphism between their values: the only
 morphism of [1] is its identity, so naturality is the vacuous square
 conjugated by [fmap_id].  Stated as a hom-setoid isomorphism in Sets,
 so the identification is not left at the object level.  The object
 half is Theory/Shapes.v's [One_Fun_iso]. 

 --------
 在从终端范畴到两个函子之间，自然变换恰好是它们值之间的态射：  [1] 的唯一态射是它的恒等态射，所以自然性就是由 [fmap_id] 伴随的虚空方框。以 Sets 中的一个同构集的形式表述，因此这种对应并不仅停留在对象层面。对象部分是 Theory/Shapes.v 的 [One_Fun_iso]。
*)
Program Definition One_hom_iso {B : Category} (F G : _1 ⟶ B) :
  ({| carrier := F ⟹ G; is_setoid := @Transform_Setoid _1 B F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := F ttt ~> G ttt; is_setoid := @homset B (F ttt) (G ttt) |} := {|
  to   := {| morphism := fun η => η ttt |};
  from := {| morphism := fun h =>
    {| transform := fun a => match a with ttt => h end |} |}
|}.
Next Obligation.
  intros B F G η θ Hηθ; exact (Hηθ ttt).
Qed.
Next Obligation.
  intros B F G h x y f; destruct x, y, f; simpl.
  assert (HF : fmap[F] ttt ≈ id) by apply (@fmap_id _ _ F ttt).
  assert (HG : fmap[G] ttt ≈ id) by apply (@fmap_id _ _ G ttt).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros B F G h x y f; destruct x, y, f; simpl.
  assert (HF : fmap[F] ttt ≈ id) by apply (@fmap_id _ _ F ttt).
  assert (HG : fmap[G] ttt ≈ id) by apply (@fmap_id _ _ G ttt).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros B F G h h' Hh a; destruct a; exact Hh.
Qed.
Next Obligation.
  intros B F G h; reflexivity.
Qed.
Next Obligation.
  intros B F G η a; destruct a; reflexivity.
Qed.

(*
 Seven Sketches states Example 3.53 at B := Sets: a natural
 transformation between two functors [1 ⟶ Sets] is just a function
 between their value setoids. 

 --------
 《七个素描》在 B := 集合中陈述了例 3.53：两个函子之间的自然变换 [1 ⟶ Sets] 只是它们值集合之间的一个函数。
*)
Example One_hom_iso_Sets (F G : _1 ⟶ Sets) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid _1 Sets F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := F ttt ~> G ttt;
     is_setoid := @homset Sets (F ttt) (G ttt) |} :=
  One_hom_iso F G.
