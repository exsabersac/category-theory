Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Square.

Require Import Coq.Lists.List.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(*
   * * The walking commutative square as 2 × 2

   Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
   Example 1.6.6, printed p. 41
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   §II.8, Exercise 1, printed p. 52

   Riehl introduces the walking commutative square not by generators
   and relations but as a PRODUCT: the shape 2 × 2, two copies of the
   walking arrow.  That presentation makes the arrow count immediate —
   an arrow of a product of thin categories is a pair of arrows, and
   the walking arrow has three (two identities and the map between
   them), so 3 × 3 = 9 — while Mac Lane's presentation makes the
   UNIVERSAL PROPERTY immediate.  This file proves the two shapes are
   the same category, so each reading is available for the other.

   WHAT IS DELIVERED.  (1) the comparison functors both ways,
   [Square_to_22] (built through [Instance/Square.v]'s
   [SquareFunctor], so it IS the universal property applied to the
   evident commutative square in 2 × 2) and [Square_of_22] (built by
   hand, its three functor laws discharged by thinness); (2) their
   object actions, mutually inverse at LEIBNIZ equality
   ([square_22_node_round], [square_22_obj_round] — proved by case
   analysis, not by [eq_refl] uniformly: both maps are matches, and on
   the 2 × 2 side the argument must additionally be exposed as a pair,
   [prod] carrying no eta); (3) the identification
   [Square_2x2_iso : Square ≅[StrictCat] _2 ∏ _2];
   (4) the arrow count of 2 × 2, proved independently of
   [Instance/Square.v]'s count, and the cross-check that the two agree
   ([square_22_counts_agree]).

   THE STRENGTH IS [StrictCat], and that is the strong reading, not the
   weak one.  [Instance/Cat.v] gives [Cat] the hom-setoid
   [Functor_Setoid], which identifies naturally isomorphic functors, so
   an isomorphism [C ≅[Cat] D] in this library is an EQUIVALENCE of
   categories and says strictly less.  [≅[StrictCat]] is the genuine
   isomorphism of categories: the two round trips are equalities of
   functors in [Functor_StrictEq_Setoid], Leibniz on objects and a
   [hom_cast] conjugation on morphisms.  The [Cat] reading is derived
   from it ([Square_2x2_Cat_iso]) rather than stated in its place.

   An isomorphism of categories, rather than a mere equivalence, is
   available here for two reasons, both cheap: the categories are thin,
   so the morphism half of each round trip is an equation between
   parallel arrows and discharges outright; and the two object maps are
   mutually inverse by case analysis on four constructors, so no
   half-adjoint correction and no object-UIP hypothesis is needed.
   (Contrast [Theory/Skeleton.v]'s
   [skeletal_equivalence_is_isomorphism], where turning an equivalence
   into a [StrictCat] isomorphism does need the HoTT half-adjoint
   correction; nothing of the sort is used below, because the two
   functors are written down rather than extracted.)

   WHAT IS NOT DELIVERED.  No claim that the two categories are equal
   as records — their object types are [SquareNode] and
   [TwoObj * TwoObj], distinct inductive types, so no Leibniz equality
   of categories is available or attempted.  No comparison with
   [Construction/Funny.v]'s [_2 □ _2]: that is a DIFFERENT category
   (the funny tensor imposes no interchange law, so its two diagonals
   stay apart — [funny_diagonals_distinct]), and it is the free square
   rather than the commutative one; the tree carries no comparison
   functor and none is built here.  The count below is proved directly
   rather than transported along the isomorphism: the library has no
   machinery for transporting an arrow count along a comparison
   functor, and proving it twice is what makes it a CROSS-CHECK. 

   --------
   * * 步行交换平方作为 2 × 2

   书籍：Riehl，《语境中的范畴论》，Dover 2016，第1.6节，第1.6.6例，印刷页 41
   书籍：Mac Lane，《工作数学家的范畴》，第2版，第II.8节，练习1，印刷页 52

   Riehl 引入步行交换平方不是通过生成元和关系，而是作为一个积：形状 2 × 2，即两个步行箭头的副本。这种表述使箭头数量一目了然——薄范畴的积的箭头是箭头对，而步行箭头有三个（两个身份箭头以及它们之间的映射），所以 3 × 3 = 9——而 Mac Lane 的表述则使得泛性质显而易见。该文件证明了这两种形状是相同的范畴，因此每种解读都可用于另一种。交付内容是什么。(1) 双向比较函子，[Square_to_22]（通过[Instance/Square.v]的[SquareFunctor]构建，所以它是应用于2×2中明显交换图的普遍性质）和[Square_of_22]（手工构建，其三个函子定律通过薄化得到满足）；(2) 它们对对象的作用，在莱布尼茨等式下互为逆（[square_22_node_round], [square_22_obj_round]——通过案例分析证明，而非通过[eq_refl]统一：两个映射都是匹配映射，并且在2×2侧，参数还必须额外暴露为一对，[prod]不携带eta）；(3) 识别[Square_2x2_iso : Square ≅[StrictCat]_2∏_2；(4) 2×2的箭头数量，独立于[Instance/Square.v]的计数证明，并且交叉检查两者是否一致（[square_22_counts_agree]）。强度是 [StrictCat]，这是强读数，而不是弱读数。[Instance/Cat.v] 给 [Cat] 提供了同构集 [Functor_Setoid]，它自然地识别同构函子，因此在此库中，[C ≅[Cat] D] 的同构是范畴的等价，并且严格意义上表达的内容更少。[≅[StrictCat]] 是范畴的真正同构：两个往返是 [Functor_StrictEq_Setoid] 中函子的等式，对象上的莱布尼茨性以及态射上的 [hom_cast] 共轭。[Cat] 读法是从它（[Square_2x2_Cat_iso]）推导出来的，而不是在其位置直接陈述。这里可以得到范畴的同构，而不仅仅是一个等价，有两个原因，而且都很简单：范畴是稀薄的，因此每次往返的态射部分就是平行箭头之间的等式，并且可以直接消解；而且两个对象映射在四个构造子的情形分析下是互逆的，因此不需要半伴随修正，也不需要对象-UIP假设。（与 [Theory/Skeleton.v] 的 [skeletal_equivalence_is_isomorphism] 对比，在那里将等价变为 [StrictCat] 同构确实需要 HoTT 半伴随修正；下面没有使用类似的东西，因为这两个函子是直接写下来的，而不是提取的。）没有交付的内容。并未声称这两类记录是相等的——它们的对象类型是 [SquareNode] 和 [TwoObj * TwoObj]，属于不同的归纳类型，因此不存在也未尝试使用类别的莱布尼茨相等。也没有与 [Construction/Funny.v] 的 [_2 □ _2] 进行比较：那是一个不同的类别（有趣的张量不施加交换律，因此它的两条对角线保持分离——[funny_diagonals_distinct]），而且它是自由平方而非交换平方；树状结构没有携带比较函子，这里也没有构建比较函子。下面的计数是直接证明的，而不是沿同构关系传递的：库中没有沿比较函子传递箭头计数的机制，且证明两次正是为了作为交叉验证。
*)

(** ** Thinness of the product shape / ** 产品形状的纤薄 *)

(*
   * The walking arrow is thin.  Its hom-setoid is [Morphism_equality],
   so [≈] is Leibniz [=] and this is [ord_two_thin]
   ([Instance/Ordinal.v]) verbatim; it is cited rather than reproved. 

   --------
   * 这个行走箭头是细的。它的同类集合是  [Morphism_equality] ，  
   所以  [≈]  是 Leibniz  [=] ，而这是  [ord_two_thin]  
   （ [Instance/Ordinal.v] ）逐字；它被引用而不是重新证明。
*)
Lemma Two_Thin : Thin _2.
Proof. intros x y f g; exact (ord_two_thin f g). Qed.

Lemma Two2_Thin : Thin (_2 ∏ _2).
Proof. exact (Thin_Product Two_Thin Two_Thin). Qed.

(* * ** From 2 × 2 to the square The four corners. The first factor is the horizontal direction of the square (A → B and C → D), the second the vertical (A → C and B → D). / * ** 从 2 × 2 到平方 四个角。第一个因子是平方的水平方向（A → B 和 C → D），第二个因子是垂直方向（A → C 和 B → D）。 *)
Definition sq22_node (a b : TwoObj) : SquareNode :=
  match a, b with
  | TwoX, TwoX => Sq_A
  | TwoY, TwoX => Sq_B
  | TwoX, TwoY => Sq_C
  | TwoY, TwoY => Sq_D
  end.

Definition sq22_obj (x : TwoObj * TwoObj) : SquareNode :=
  sq22_node (fst x) (snd x).

(*
   * The nine arrows of 2 × 2, sent to the nine arrows of the square.
   The last line is the one with content: a pair of non-identity arrows
   goes to the DIAGONAL, which is where the imposed relation is spent —
   without it there would be two candidate images and no functor. 

   --------
   * 2 × 2的九条箭头，发送到方形的九条箭头。  
   最后一行是内容为：一对非恒等箭头  
   去到对角线，这是施加关系所消耗的地方——  
   没有它就会有两个候选像，而没有函子。
*)
Definition sq22_map {a b c d : TwoObj} (u : TwoHom a c) (v : TwoHom b d) :
  sq22_node a b ~{Square}~> sq22_node c d :=
  match u in TwoHom a0 c0, v in TwoHom b0 d0
    return sq22_node a0 b0 ~{Square}~> sq22_node c0 d0 with
  | TwoIdX, TwoIdX => id
  | TwoIdX, TwoIdY => id
  | TwoIdY, TwoIdX => id
  | TwoIdY, TwoIdY => id
  | TwoXY,  TwoIdX => square_f
  | TwoIdX, TwoXY  => square_g
  | TwoIdY, TwoXY  => square_h
  | TwoXY,  TwoIdY => square_k
  | TwoXY,  TwoXY  => square_diagonal
  end.

(*
   * All three functor laws are equations between parallel arrows of
   [Square], hence instances of [Square_Thin]. 

   --------
   * 所有三个函子定律都是 [Square] 的平行箭头之间的等式，因此是 [Square_Thin] 的实例。
*)
Definition Square_of_22 : (_2 ∏ _2) ⟶ Square :=
  Build_Functor (_2 ∏ _2) Square
    sq22_obj
    (fun x y f => sq22_map (fst f) (snd f))
    (fun x y f g _ => Square_Thin _ _ _ _)
    (fun x => Square_Thin _ _ _ _)
    (fun x y z f g => Square_Thin _ _ _ _).

(*
   * ** From the square to 2 × 2

   The evident commutative square in 2 × 2, and the functor the
   universal property of [Square] makes of it. 

   --------
   * ** 从方形到 2 × 2

   2 × 2 中明显的交换方，及函子的
   [Square] 的泛性质使其成为这样。
*)
Definition sq22_commuting : CommutingSquare (_2 ∏ _2) :=
  @Build_CommutingSquare (_2 ∏ _2)
    (TwoX, TwoX) (TwoY, TwoX) (TwoX, TwoY) (TwoY, TwoY)
    (TwoXY, TwoIdX) (TwoIdX, TwoXY) (TwoIdY, TwoXY) (TwoXY, TwoIdY)
    (Two2_Thin _ _ _ _).

Definition Square_to_22 : Square ⟶ (_2 ∏ _2) := SquareFunctor sq22_commuting.

(** Its object action, on the nose. / 它的对象动作，非常准确。 *)
Example Square_to_22_A : fobj[Square_to_22] Sq_A = (TwoX, TwoX) := eq_refl.
Example Square_to_22_B : fobj[Square_to_22] Sq_B = (TwoY, TwoX) := eq_refl.
Example Square_to_22_C : fobj[Square_to_22] Sq_C = (TwoX, TwoY) := eq_refl.
Example Square_to_22_D : fobj[Square_to_22] Sq_D = (TwoY, TwoY) := eq_refl.

(*
   * ** The two object actions are mutually inverse

   Leibniz equalities, but not [eq_refl] uniformly: both maps are
   matches, so they reduce only once their argument is a constructor,
   and on the 2 × 2 side the argument must additionally be exposed as a
   PAIR, [prod] carrying no eta. 

   --------
   * ** 这两个对象动作是相互逆的

   莱布尼茨等式，但不是 [eq_refl] 一致的：两个映射都是匹配的，
   因此它们仅在其参数是构造器时才减少，并且在 2 × 2 方面，参数还必须
   作为 PAIR 暴露，[prod] 不携带 eta。
*)
Lemma square_22_node_round (n : SquareNode) :
  sq22_obj (fobj[Square_to_22] n) = n.
Proof. destruct n; reflexivity. Qed.

Lemma square_22_obj_round (x : TwoObj * TwoObj) :
  fobj[Square_to_22] (sq22_obj x) = x.
Proof. destruct x as [a b]; destruct a, b; reflexivity. Qed.

(*
   * ** The identification

   Both round trips at [Functor_StrictEq_Setoid] strength: Leibniz on
   objects, and on morphisms a [hom_cast] conjugation which thinness
   discharges outright on either side. 

   --------
   * ** 识别

   在 [Functor_StrictEq_Setoid] 上的双程旅行强度：莱布尼茨关于对象，以及关于态射的 [hom_cast] 共轭，其稀薄性在任一侧都直接释放。
*)
Lemma Square_22_round : @equiv _ (@Functor_StrictEq_Setoid Square Square)
  (Square_of_22 ◯ Square_to_22) (Id[Square]).
Proof.
  apply (strict_of_hom_cast (Square_of_22 ◯ Square_to_22) (Id[Square])
           square_22_node_round).
  intros x y p; exact (Square_Thin _ _ _ _).
Qed.

Lemma Square_22_round' :
  @equiv _ (@Functor_StrictEq_Setoid (_2 ∏ _2) (_2 ∏ _2))
    (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2]).
Proof.
  apply (strict_of_hom_cast (Square_to_22 ◯ Square_of_22) (Id[_2 ∏ _2])
           square_22_obj_round).
  intros x y p; exact (Two2_Thin _ _ _ _).
Qed.

(*
   * Riehl §1.6 Example 1.6.6: the walking commutative square IS 2 × 2 —
   an isomorphism of categories, not merely an equivalence. 

   --------
   * Riehl §1.6 示例 1.6.6：步行交换方格是 2 × 2 — 一个范畴的同构，而不仅仅是等价。
*)
Definition Square_2x2_iso : Square ≅[StrictCat] (_2 ∏ _2) :=
  @Build_Isomorphism StrictCat Square (_2 ∏ _2)
    Square_to_22 Square_of_22 Square_22_round' Square_22_round.

(*
   * The weaker [Cat] reading, derived.  Recall that [≅[Cat]] in this
   library is an EQUIVALENCE of categories, [Cat]'s hom-setoid being
   [Functor_Setoid]; the [StrictCat] statement above is the strong
   one. 

   --------
   * 弱的 [Cat] 读数，派生的。回想一下，这个库中的 [≅[Cat] 是类别的等价，[Cat] 的同态集合是 [Functor_Setoid]；上面的 [StrictCat] 陈述是强的那个。
*)
Definition Square_2x2_Cat_iso : Square ≅[Cat] (_2 ∏ _2) :=
  @Build_Isomorphism Cat Square (_2 ∏ _2)
    Square_to_22 Square_of_22
    (strict_equiv_implies_fun_equiv _ _ Square_22_round')
    (strict_equiv_implies_fun_equiv _ _ Square_22_round).

(*
   * ** The arrow count of 2 × 2, independently

   An arrow of [_2 ∏ _2] is a pair of arrows of [_2], so the count is
   the square of the walking arrow's.  Proved here from scratch — not
   transported along [Square_2x2_iso] — so that it is a genuine
   cross-check on [Instance/Square.v]'s count rather than a restatement
   of it. 

   --------
   * ** 2 × 2 的箭头计数，独立计算

   [_2 ∏ _2] 的一个箭头是 [_2] 的一对箭头，因此计数是行走箭头计数的平方。在这里从零开始证明——不是沿着 [Square_2x2_iso] 转运——因此它是对 [Instance/Square.v] 计数的真正交叉验证，而不是对其的重新陈述。
*)

(*
   * The walking arrow has three arrows: [TwoHom] is inhabited except at
   (Y, X), and then by exactly one element. 

   --------
   * 行走箭头有三个箭头：[TwoHom] 被占据，除了在 (Y, X) 处，然后仅由一个元素占据。
*)
Definition two_homcount (a b : TwoObj) : nat :=
  match a, b with
  | TwoY, TwoX => 0
  | _, _ => 1
  end.

Lemma two_hom_empty (f : TwoHom TwoY TwoX) : False.
Proof. exact (TwoHom_Y_X_absurd f). Qed.

Lemma two_hom_inhabited (a b : TwoObj) :
  two_homcount a b = 1%nat → TwoHom a b.
Proof.
  destruct a, b; simpl; intro H;
    solve [ exact TwoIdX | exact TwoIdY | exact TwoXY | discriminate ].
Qed.

Definition two_objs : list TwoObj := TwoX :: TwoY :: nil.

Definition two_pairs : list (TwoObj * TwoObj) := list_prod two_objs two_objs.

Definition two_arrow_total : nat :=
  fold_right (fun q n => two_homcount (fst q) (snd q) + n)%nat 0%nat two_pairs.

Theorem two_arrow_total_3 : two_arrow_total = 3%nat.
Proof. reflexivity. Qed.

(*
   * In the product, the hom-set at a pair of endpoint pairs is the
   product of the two component hom-sets, so its count is the product
   of the two counts. 

   --------
   * 在积中，一对端点对的同态集是两个组成部分同态集的积，所以它的数量是两个数量的乘积。
*)
Definition prod22_homcount (x y : TwoObj * TwoObj) : nat :=
  (two_homcount (fst x) (fst y) * two_homcount (snd x) (snd y))%nat.

Definition prod22_pairs : list ((TwoObj * TwoObj) * (TwoObj * TwoObj)) :=
  list_prod two_pairs two_pairs.

Example prod22_pairs_16 : length prod22_pairs = 16%nat := eq_refl.

Definition prod22_arrow_total : nat :=
  fold_right (fun q n => prod22_homcount (fst q) (snd q) + n)%nat 0%nat
    prod22_pairs.

Theorem prod22_arrow_total_9 : prod22_arrow_total = 9%nat.
Proof. reflexivity. Qed.

Definition prod22_identity_total : nat :=
  fold_right (fun x n => prod22_homcount x x + n)%nat 0%nat two_pairs.

Theorem prod22_identity_total_4 : prod22_identity_total = 4%nat.
Proof. reflexivity. Qed.

Definition prod22_nonidentity_total : nat :=
  (prod22_arrow_total - prod22_identity_total)%nat.

Theorem prod22_nonidentity_total_5 : prod22_nonidentity_total = 5%nat.
Proof. reflexivity. Qed.

(*
   * The counting function is correct: it is 0 exactly where the hom-set
   is empty, and where it is 1 the hom-set is inhabited and thin.
   (Thinness is [Two2_Thin] and holds everywhere, so only inhabitation
   and emptiness are per-pair.) 

   --------
   * 计数函数是正确的：正是在同态集为空时为 0，而当它为 1 时，同态集是非空且稀疏的。（稀疏性是 [Two2_Thin] 并且在所有地方都成立，所以只有每对的非空性和空性是需要考虑的。）
*)
Theorem prod22_homcount_empty (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 0%nat → (x ~{_2 ∏ _2}~> y) → False.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl;
    solve [ intros H _; discriminate H
          | intros _ [u v]; solve [ exact (two_hom_empty u)
                                  | exact (two_hom_empty v) ] ].
Qed.

Theorem prod22_homcount_inhabited (x y : TwoObj * TwoObj) :
  prod22_homcount x y = 1%nat → x ~{_2 ∏ _2}~> y.
Proof.
  destruct x as [a b], y as [c d]; destruct a, b, c, d; simpl; intro H;
    solve [ discriminate H
          | exact (TwoIdX, TwoIdX) | exact (TwoIdX, TwoIdY)
          | exact (TwoIdX, TwoXY)  | exact (TwoIdY, TwoIdX)
          | exact (TwoIdY, TwoIdY) | exact (TwoIdY, TwoXY)
          | exact (TwoXY, TwoIdX)  | exact (TwoXY, TwoIdY)
          | exact (TwoXY, TwoXY) ].
Qed.

(*
   * The cross-check the two presentations owe each other: Mac Lane's
   count and Riehl's agree, arrow for arrow, identity for identity. 

   --------
   * 对这两个展示进行交叉检查：马赫·莱恩的计数和里尔的计数完全一致，一箭对一箭，一体对一体。
*)
Theorem square_22_counts_agree :
  ((square_arrow_total = prod22_arrow_total) *
   (square_identity_total = prod22_identity_total) *
   (square_nonidentity_total = prod22_nonidentity_total))%type.
Proof. repeat split; reflexivity. Qed.

(** ...and 9 = 3 × 3, which is the whole of Riehl's argument. / …而 9 = 3 × 3，这就是 Riehl 论证的全部内容。 *)
Example square_count_is_three_squared :
  square_arrow_total = (two_arrow_total * two_arrow_total)%nat := eq_refl.
