Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* * * Naturality of the exponential laws / * * 指数定律的自然性 *)

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/exponential+object
 nLab: https://ncatlab.org/nlab/show/natural+transformation

 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.5
 Exercise 2 (printed p. 44), asks that the familiar exponential laws

 z^(x × y) ≅ (z^y)^x,      (y × z)^x ≅ y^x × z^x,
 x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

 be shown NATURAL in each of their variables.  Riehl, "Category Theory in
 Context", §1.4 Example 1.4.11 (printed p. 29) reads the same four laws in
 the groupoid of finite sets and observes that applying the cardinality
 functor decategorifies them into the arithmetic identities
 z^(xy) = (z^y)^x, (yz)^x = y^x z^x, x(y+z) = xy + xz and x^(y+z) = x^y x^z;
 that half of the example is Instance/FinSet/Decategorify.v.

 The four isomorphisms themselves are already in the tree, as POINTWISE
 families indexed by three objects:

 - [exp_prod_l]     (Structure/Cartesian/Closed.v)  z^(x × y) ≅ (z^y)^x
 - [exp_prod_r]     (Structure/Cartesian/Closed.v)  (y × z)^x ≅ y^x × z^x
 - [prod_coprod_r]  (Structure/BiCCC.v)             x × (y+z) ≅ x×y + x×z
 - [exp_coprod]     (Structure/BiCCC.v)             x^(y+z) ≅ x^y × x^z

 What was missing is the statement that each family is a NATURAL
 isomorphism, i.e. an isomorphism in a functor category between the two
 sides read as functors of their three variables.  This file supplies that,
 as an UPGRADE and not as a replacement: every component of every
 transformation below is literally the [to] or [from] leg of the existing
 pointwise instance (recorded by the eight [_component] lemmas -- one per
 leg per law -- each of which holds by [reflexivity]), so nothing is rebuilt
 and the pointwise isos keep all their consumers.  The object action of
 each of the eight functors is likewise recorded by an [Example] holding by
 [eq_refl].

 ** Variances and domains

 Exponentiation is contravariant in the exponent and covariant in the base,
 so the four laws live over three different product categories.  The domains
 chosen here are

 - [exp_prod_l]     ((x, y), z) over ((C^op ∏ C^op) ∏ C)
 - [exp_prod_r]     (x, (y, z)) over (C^op ∏ (C ∏ C))
 - [prod_coprod_r]  (x, (y, z)) over (C ∏ (C ∏ C))
 - [exp_coprod]     ((y, z), x) over ((C^op ∏ C^op) ∏ C)

 with the bracketing of each domain matching the bracketing of the objects
 in the corresponding statement.  In each case both sides are given as
 DIRECT functor records (concrete [fobj] and [fmap]) rather than as
 composites of the internal-hom and product bifunctors; this keeps the
 naturality squares stated in the curry/eval calculus of
 Structure/Cartesian/Closed.v with no opposite-of-a-product bookkeeping.

 The arrow actions of the eight functors are built from three combinators:
 [ihom] below -- the action of the internal hom, exactly the [fmap] of
 [InternalHomFunctor] (Functor/Hom/Internal.v) written in C with no [op]
 coercion, an identification machine-checked below at Leibniz [eq_refl]
 ([ihom_is_InternalHomFunctor_fmap]) -- together with [split]
 (Structure/Cartesian.v) and [cover] (Structure/Cocartesian.v) for the
 product and coproduct actions.  The two Law-3 functors, whose statement
 has no exponentials, use only the latter two.

 ** The transpose triangle

 The final section relates the internal law [exp_prod_l] to the EXTERNAL
 currying bijection [exp_iso : x × y ~> z ≊ x ~> z^y] of
 Structure/Cartesian/Closed.v, whose two legs are [curry] and [uncurry]:
 postcomposition by [to exp_prod_l] computes, on an arbitrary generalized
 element f : w ~> z^(x × y), as a composite of [exp_iso] transposes -- one
 [uncurry], then two [curry]s -- through the associator, and dually for
 [from exp_prod_l].  So the
 internal iso is CARRIED by the external bijection; see
 [exp_prod_l_transpose] and [exp_prod_l_untranspose]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/cartesian+closed+category 
 nLab:  https://ncatlab.org/nlab/show/exponential+object 
 nLab:  https://ncatlab.org/nlab/show/natural+transformation 

 Mac Lane，《为工作数学家而写的范畴论》，第二版，§II.5
 练习2（印刷页44）要求证明熟悉的指数律

 z^(x × y) ≅ (z^y)^x,      (y × z)^x ≅ y^x × z^x,
 x × (y + z) ≅ x × y + x × z,   x^(y + z) ≅ x^y × x^z

 在每个变量上是自然的。Riehl，《语境中的范畴论》，§1.4 示例1.4.11（印刷页29）在有限集合的群类中读同样的四条律，并观察应用基数函子将它们去范畴化为算术恒等式
 z^(xy) = (z^y)^x, (yz)^x = y^x z^x, x(y+z) = xy + xz 和 x^(y+z) = x^y x^z；
 示例的一半位于 Instance/FinSet/Decategorify.v。四个同构自身已经在树中，作为以三个对象为索引的逐点族：

 -  [exp_prod_l]      (Structure/Cartesian/Closed.v)  z^(x × y) ≅ (z^y)^x
 -  [exp_prod_r]      (Structure/Cartesian/Closed.v)  (y × z)^x ≅ y^x × z^x
 -  [prod_coprod_r]   (Structure/BiCCC.v)             x × (y+z) ≅ x×y + x×z
 -  [exp_coprod]      (Structure/BiCCC.v)             x^(y+z) ≅ x^y × x^z缺失的是声明每个族都是一个自然同构，即在函子范畴中在其三个变量的函子视角下，两边之间的同构。这个文件提供了这一点，作为升级而非替代：下面每个变换的每个分量实际上都是现有逐点实例的 [to] 或 [from] 部分（由八个 [_component] 引理记录——每个定律每条腿一个——每个都由 [reflexivity] 成立），所以没有重建任何内容，并且逐点同构保持其所有使用者。八个函子的每个对象动作同样由 [Example] 记录，并由 [eq_refl] 成立。

 ** 变异性与定义域指数运算在指数上是逆变的，在底数上是协变的，因此这四条定律存在于三种不同的乘积范畴上。这里选择的域为：

 - [exp_prod_l]      ((x, y), z) 位于 ((C^op ∏ C^op) ∏ C) 上
 - [exp_prod_r]      (x, (y, z)) 位于 (C^op ∏ (C ∏ C)) 上
 - [prod_coprod_r]      (x, (y, z)) 位于 (C ∏ (C ∏ C)) 上
 - [exp_coprod]      ((y, z), x) 位于 ((C^op ∏ C^op) ∏ C) 上

 每个域的括号与相应陈述中对象的括号匹配。在每种情况下，双方都以直接函子记录（具体的 [fobj] 和 [fmap]）给出，而不是作为内部 Hom 和乘积双函子的复合；这保持了在 Structure/Cartesian/Closed.v 的 curry/eval 演算中，范自然性方格的表述，而无需进行乘积取对立的记录。八个函子的箭头作用是由三个组合子构建的：
 [ihom] 下面——内部 Hom 的作用，正好是
 [fmap] 的 [InternalHomFunctor] （Functor/Hom/Internal.v）用 C 写成且没有 [op] 强制转换，下面在 Leibniz [eq_refl] （[ihom_is_InternalHomFunctor_fmap]）中经过机器校验——以及 [split] （Structure/Cartesian.v）和 [cover] （Structure/Cocartesian.v）用于积和余积作用。没有指数的两个 Law-3 函子，仅使用后两个。

 ** 转置三角形最后一部分将内部律 [exp_prod_l] 与 Structure/Cartesian/Closed.v 的外部柯里化双射 [exp_iso : x × y ~> z ≊ x ~> z^y] 联系起来，其两条分支是 [curry] 和 [uncurry]：通过 [to exp_prod_l] 后合成计算任意广义元素 f : w ~> z^(x × y)，作为 [exp_iso] 转置的复合——先一个 [uncurry]，然后两个 [curry]——通过结合子，并且 [from exp_prod_l] 以对偶方式处理。因此，内部同构由外部双射携带；见 [exp_prod_l_transpose] 和 [exp_prod_l_untranspose]。
*)

(*
   * ** Packaging a pointwise family of isomorphisms as a natural isomorphism

   Each of the four laws below is already available as a family of pointwise
   isomorphisms; what has to be added is one naturality square.  The two
   lemmas here move a square between the [to] and the [from] orientation (so
   that whichever leg is easier to compute with may be the one proved), and
   [NaturalIso_of_pointwise] assembles the family and the square into an
   isomorphism of the functor category, with the components UNCHANGED. 

   --------
   * ** 将一个逐点同构的族打包为自然同构

   下面的四条定律中的每一条已经作为逐点同构的族存在；需要添加的是一个自然性方形。这里的两个引理在  [to]  和  [from]  方向之间移动方形（这样可以选择计算起来更容易的一条腿进行证明），并且  [NaturalIso_of_pointwise]  将该族和方形组合成函子范畴的同构，同时保持分量不变。
*)

Section PointwiseNatural.

Context {D E : Category}.
Context {F G : D ⟶ E}.

Lemma natural_flip_from (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m.
Proof.
  intros x y m.
  assert (HA : from (comp y) ∘ (fmap[G] m ∘ to (comp x)) ≈ fmap[F] m).
  { rewrite nat, comp_assoc, iso_from_to; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_to_from.
  now rewrite id_right.
Qed.

Lemma natural_flip_to (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m.
Proof.
  intros x y m.
  assert (HA : to (comp y) ∘ (fmap[F] m ∘ from (comp x)) ≈ fmap[G] m).
  { rewrite nat, comp_assoc, iso_to_from; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_from_to.
  now rewrite id_right.
Qed.

(* The components of both legs are the components of [comp], on the nose. / 两条腿的组成部分是[comp]的组成部分，就在鼻子上。 *)
Program Definition NaturalIso_of_pointwise (comp : ∀ p, F p ≅ G p)
        (nat : ∀ (x y : D) (m : x ~> y),
            fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  @Isomorphism ([D, E]) F G := {|
  to   := {| transform := fun p => to (comp p) |};
  from := {| transform := fun p => from (comp p) |}
|}.
(*
 The obligations are the naturality square of each leg in both
 orientations, together with whichever round trips the ambient obligation
 tactic has not already discharged.  [Program] neither fixes their order nor
 guarantees how many survive, so each is closed by one alternation: the
 square supplied, its flip, or invertibility of the component (the round
 trips arrive with the identity of [G] still written [fmap[G] id]). 

 --------
 这些约束是每条支腿在两种方向上的本征平方，以及环境约束策略尚未解除的任何往返。[Program] 既不固定它们的顺序，也不保证有多少存活，因此每个约束由一个交替方式闭合：提供的平方、其翻转，或者组件的可逆性（往返带有 [G] 的恒等，仍然写作 [fmap[G] id）。
*)
Ltac natiso_obligation :=
  intros;
  try rewrite fmap_id;
  first [ now apply nat
        | symmetry; now apply nat
        | now apply natural_flip_from
        | symmetry; now apply natural_flip_from
        | now apply iso_to_from
        | now apply iso_from_to ].
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.

End PointwiseNatural.

Section ExpNatural.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(* * ** The internal-hom action, and its functoriality / * ** 内同作用及其函子性 *)

(*
 [ihom f h : c^a ~> d^b] for f : b ~> a and h : c ~> d precomposes by f in
 the exponent and postcomposes by h in the base.  This is the [fmap] of
 Functor/Hom/Internal.v's [InternalHomFunctor] with the C^op arrow spelled
 as the underlying C arrow, so that no [op] re-reading occurs below -- an
 identification that holds at Leibniz [eq_refl], machine-checked after the
 laws ([ihom_is_InternalHomFunctor_fmap]).  The three lemmas that follow
 therefore re-prove that functor's three obligations in the [op]-free
 spelling rather than shadowing something weaker. 

 --------
 [ihom f h : c^a ~> d^b] 对于 f : b ~> a 和 h : c ~> d，在指数上进行前复合，在基上进行后复合。这是 Functor/Hom/Internal.v 中 [InternalHomFunctor] 的 [fmap]，C^op 箭头写作底层的 C 箭头，因此下面不会发生 [op] 的重新读取——这是一个在 Leibniz [eq_refl] 中成立的标识，经过定律 ([ihom_is_InternalHomFunctor_fmap]) 的机器验证。接下来的三个引理因此重新证明了函子的三个义务，在 [op]-无约束的写法中，而不是遮蔽某个较弱的东西。
*)
Definition ihom {a b c d : C} (f : b ~> a) (h : c ~> d) : c^a ~> d^b :=
  curry (h ∘ eval ∘ second f).

(*
 [simpl] is used below only to reduce the pair projections of a product
 category; it must not go on to unfold [ihom] into its transpose. 

 --------
 [simpl] 下面的使用仅仅是为了减少某个产品类别的配对投影；它不能继续将 [ihom] 展开成其转置。
*)
Arguments ihom : simpl never.

#[export] Program Instance ihom_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@ihom a b c d).
Next Obligation. proper; unfold ihom; now rewrites. Qed.

Lemma ihom_id {a c : C} : ihom (id[a]) (id[c]) ≈ id[c^a].
Proof. unfold ihom; unfork; cat. Qed.

Lemma ihom_comp {a b b' c d e : C}
      (f : b ~> a) (f' : b' ~> b) (h : c ~> d) (h' : d ~> e) :
  ihom f' h' ∘ ihom f h ≈ ihom (f ∘ f') (h' ∘ h).
Proof.
  unfold ihom.
  symmetry.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(*
 The identification asserted above, machine-checked: [ihom] IS the arrow
 action of [InternalHomFunctor], read in C, at Leibniz equality -- not
 merely up to [≈].  ((a, c) ~> (b, d) in C^op ∏ C is a pair of f : b ~> a
 in C and h : c ~> d.) 

 --------
 上述声明的识别，经机器检查：[ihom] 是箭头
 动作 [InternalHomFunctor]，在 C 中读取，于 Leibniz 等式 —— 不仅仅是到 [≈]。((a, c) ~> (b, d) 在 C^op ∏ C 中是一对 f : b ~> a
 在 C 中和 h : c ~> d。)
*)
Example ihom_is_InternalHomFunctor_fmap {a b c d : C} (f : b ~> a) (h : c ~> d) :
  @fmap _ _ (InternalHomFunctor C) (a, c) (b, d) (f, h) = ihom f h := eq_refl.

(* * ** Small [split] identities used to normalise arrow actions / * ** 用于规范箭头动作的小型 [split] 身份 *)

Lemma first_as_split {x y z : C} (f : x ~> y) : first (z:=z) f ≈ split f id.
Proof. unfold first, split; cat. Qed.

Lemma second_as_split {x y z : C} (f : x ~> y) : second (z:=z) f ≈ split id f.
Proof. unfold second, split; cat. Qed.

(*
   * ** Naturality of the associator

   Structure/Cartesian.v states the associator as a pointwise isomorphism
   only, with no naturality; the two general squares are supplied here for
   reuse.  The squares of Law 1 do not consume them directly -- their middle
   factor is an identity, and rewriting [first]/[second] into [split] form
   costs more than proving the two specialised shapes below outright -- so
   what the proofs actually use is [prod_assoc_second_first],
   [prod_assoc_first_first] and [prod_assoc_from_first]. 

   --------
   * **关联子的自然性

   Structure/Cartesian.v 仅将关联子表述为逐点同构，没有自然性；这里提供了两个通用的方形图以供复用。法则 1 的方形图并不直接使用它们——其中间因子是恒等映射，将 [first] / [second] 重写为 [split] 形式比直接证明下面两个专门的形状要麻烦——因此实际在证明中使用的是 [prod_assoc_second_first]、[prod_assoc_first_first] 和 [prod_assoc_from_first]。
*)

Lemma prod_assoc_to_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  to prod_assoc ∘ split (split f g) h ≈ split f (split g h) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_from_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  from prod_assoc ∘ split f (split g h) ≈ split (split f g) h ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

(*
 Two instances of associator naturality, in the exact shapes the squares
 below produce (the middle factor of each composite is an identity, so
 neither is a bare instance of [prod_assoc_to_natural]). 

 --------
 结合子自然性的两个实例，在下方方形所产生的完全相同的形状中（每个复合的中间因子都是恒等映射，因此都不是 [prod_assoc_to_natural] 的纯实例）。
*)
Lemma prod_assoc_second_first {a x y x' y' : C} (f : x' ~> x) (g : y' ~> y) :
  to prod_assoc ∘ (second g ∘ first (second (z:=a) f))
    ≈ second (split f g) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_first_first {a b x y : C} (k : a ~> b) :
  to prod_assoc ∘ first (z:=y) (first (z:=x) k) ≈ first (z:=x × y) k ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

(*
 [eval_first] under a further composite, so that no [comp_assoc] step has to
 be aimed by hand at one side of a naturality square. 

 --------
 [eval_first] 在一个更复杂的复合下，因此不必手动将 [comp_assoc] 步骤对准自然方形的一侧。
*)
Corollary eval_first_comp {a b c w : C} (k : a ~> c^b) (m : w ~> a × b) :
  eval ∘ (first k ∘ m) ≈ uncurry k ∘ m.
Proof. rewrite comp_assoc, eval_first; reflexivity. Qed.

(*
 Postcomposition by an internal-hom action, computed through a transpose:
 this is the single calculation every naturality square below reduces to. 

 --------
 通过内部同态作用的后合成，通过转置计算：这是下面每一个自然性方格化简到的唯一计算。
*)
Lemma ihom_curry {a b b' c c' : C} (f : b' ~> b) (h : c ~> c') (m : a × b ~> c) :
  ihom f h ∘ curry m ≈ curry (h ∘ m ∘ second f).
Proof.
  unfold ihom.
  rewrite curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- first_second.
  rewrite (comp_assoc eval).
  rewrite eval_first, uncurry_curry.
  now rewrite comp_assoc.
Qed.

(*
   * ** Reading a contravariant slot back in C

   [C^op] has the objects and the hom-sets of [C] (Construction/Opposite.v),
   so both maps below are the identity.  They are nevertheless written out:
   without them the elaborator sees a slot of the domain typed at [C^op] and
   goes looking for a [@Cartesian (C^op)] -- that is, a [Cocartesian C] --
   when resolving [×] or [split].  Applying [opobj]/[oparr] pins the ambient
   category to [C], and simultaneously records the variance in the source
   text: [oparr] reverses the arrow. 

   --------
   * ** 在 C 中读取逆变槽

   [C^op] 具有 [C]（Construction/Opposite.v）的对象和同态集，因此下面的两个映射都是恒等映射。它们仍然被写出：没有它们，展开器会看到域槽的类型为 [C^op]，并会去寻找一个 [@Cartesian (C^op)]——也就是一个 [Cocartesian C]——在解析 [×] 或 [split] 时。应用 [opobj] / [oparr] 将环境类别固定为 [C]，同时在源文本中记录了方差：[oparr] 反转箭头。
*)
Definition opobj (a : C^op) : C := a.
Definition oparr {a b : C^op} (f : a ~{C^op}~> b) : opobj b ~{C}~> opobj a := f.

(*
   * ** Law 1: z^(x × y) ≅ (z^y)^x, natural in x, y and z

   Domain ((C^op ∏ C^op) ∏ C).  The object ((x, y), z) goes to z^(x × y) on
   the left and to (z^y)^x on the right.  A morphism ((f, g), h) out of it is
   a pair of C-arrows f : x' ~> x and g : y' ~> y -- the two contravariant
   slots, read in C^op -- together with h : z ~> z'. 

   --------
   * ** 定律 1：z^(x × y) ≅ (z^y)^x，对 x、y 和 z 自然成立

   定义域 ((C^op ∏ C^op) ∏ C)。对象 ((x, y), z) 在左边映射为 z^(x × y)，在右边映射为 (z^y)^x。 从它出发的态射 ((f, g), h) 是一对 C 箭 f : x' ~> x 和 g : y' ~> y —— 这两个反变槽，在 C^op 中读取 —— 以及 h : z ~> z'。
*)

(* The [to] and [from] legs of [exp_prod_l], named so that the calculations below never depend on how [Program] elaborated the instance; both hold by [reflexivity]. / [exp_prod_l] 的 [to] 和 [from] 分支，这样命名是为了下面的计算永远不依赖于 [Program] 如何展开实例；两者都由 [reflexivity] 保持。 *)
Lemma exp_prod_l_to_unfold {x y z : C} :
  to (@exp_prod_l C _ _ x y z) ≈ curry (curry (eval ∘ to prod_assoc)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_from_unfold {x y z : C} :
  from (@exp_prod_l C _ _ x y z) ≈ curry (uncurry eval ∘ from prod_assoc).
Proof. reflexivity. Qed.

(*
 The object and arrow actions are given as ordinary definitions and only
 then assembled into a functor record.  Elaborating them inside the
 [Program Definition] would not do: [Program] defers an unresolved instance
 argument of [product_obj] into an OBLIGATION, which
 Lib/Foundation.v's [Unset Transparent Obligations] makes opaque, and the
 resulting [fobj] then converts with nothing -- in particular not with the
 endpoints of [exp_prod_l]. 

 --------
 对象和箭头操作作为普通定义给出，然后才组装成函子记录。在 [Program Definition] 内部展开它们是不行的：[Program] 将 [product_obj] 的未解决实例参数推迟为一个义务，Lib/Foundation.v 的 [Unset Transparent Obligations] 使其不透明，而结果 [fobj] 随后无任何转换——尤其不是使用 [exp_prod_l] 的端点。
*)
Definition expProdL_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) × opobj (snd (fst p))).

Definition expProdL_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_lhs x ~> expProdL_lhs y :=
  ihom (split (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpProdL_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_lhs;
  fmap := @expProdL_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdL_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  ((snd p)^(opobj (snd (fst p))))^(opobj (fst (fst p))).

Definition expProdL_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_rhs x ~> expProdL_rhs y :=
  ihom (oparr (fst (fst m))) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpProdL_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_rhs;
  fmap := @expProdL_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_id.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_comp.
Qed.

(*
 The two object actions, recorded so that the shape of each side of Law 1 is
 machine-checked rather than only asserted in the header. 

 --------
 这两个对象动作被记录下来，以便法律1的每一边的形状可以通过机器检查，而不仅仅是在标题中断言。
*)
Example ExpProdL_LHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_LHS] ((x, y), z) = z^(opobj x × opobj y) := eq_refl.

Example ExpProdL_RHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_RHS] ((x, y), z) = (z^(opobj y))^(opobj x) := eq_refl.

(*
 The naturality square proper.  Both sides normalise to a double transpose
 by [ihom_curry] and [curry_comp_l]; what remains under the two [curry]s is
 naturality of the associator. 

 --------
 自然性方形是合适的。两边通过 [ihom_curry] 和 [curry_comp_l] 规范化为双转置；在两个 [curry] 下剩下的是结合子的自然性。
*)
Lemma exp_prod_l_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y' ~> y) (h : z ~> z') :
  ihom f (ihom g h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x' y' z') ∘ ihom (split f g) h.
Proof.
  rewrite !exp_prod_l_to_unfold.
  rewrite !ihom_curry.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_second_first, prod_assoc_first_first.
  unfold ihom.
  rewrite eval_first_comp, uncurry_curry.
  now rewrite <- !comp_assoc.
Qed.

Definition exp_prod_l_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpProdL_LHS p ≅ ExpProdL_RHS p :=
  @exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p).

Definition exp_prod_l_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpProdL_LHS ExpProdL_RHS :=
  NaturalIso_of_pointwise exp_prod_l_iso
    (fun _ _ m => exp_prod_l_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

(* The transformation is the existing pointwise iso: its component at ((x, y), z) is [to exp_prod_l] on the nose, and dually for [from]. / 这个变换是现有的逐点同构：它在 ((x, y), z) 处的分量正是 [to exp_prod_l]，对 [from] 也同理。 *)
Lemma exp_prod_l_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_prod_l_natural] p
    ≈ to (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_prod_l_natural] p
    ≈ from (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

(* * ** Naturality of Law 1 in a single variable Instantiating the square at two identities leaves the square in the remaining variable; the base variable z is done here as the specimen. / * ** 单变量下的法律自然性 在两个恒等式上实例化该方格时，会在剩余变量中保留该方格；这里将基变量 z 作为示例完成。 *)
Corollary exp_prod_l_natural_in_base {x y z z' : C} (h : z ~> z') :
  ihom (id[x]) (ihom (id[y]) h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x y z') ∘ ihom (id[x × y]) h.
Proof.
  pose proof (exp_prod_l_square (id[x]) (id[y]) h) as HA.
  now rewrite split_id in HA.
Qed.

(*
   * ** The transpose triangle: the internal law is carried by [exp_iso]

   [exp_iso : x × y ~> z ≊ x ~> z^y] (Structure/Cartesian/Closed.v) is the
   EXTERNAL currying bijection of the product-exponential adjunction; [curry]
   and [uncurry] are its two legs.  The two statements below say that
   composing with the internal isomorphism [exp_prod_l] computes as a
   composite of [exp_iso] transposes taken through the associator: to
   transpose f : w ~> z^(x × y) across [to exp_prod_l], untranspose it once,
   reassociate, and transpose twice back.  They hold for EVERY generalized
   element f, not merely for the identity, which is what makes them a
   statement about the two bijections rather than about one value.

   [prod_assoc_from_first] is the associator naturality the second statement
   needs; the [to] orientation is [prod_assoc_first_first] above. 

   --------
   * ** 转置三角形：内部定律由 [exp_iso] 承载  

   [exp_iso : x × y ~> z ≊ x ~> z^y]（结构/笛卡尔/Closed.v）是积-指数伴随的外部柯里化双射；[curry] 和 [uncurry] 是它的两条边。下面的两个陈述说明，与内部同构 [exp_prod_l] 组成时，可以计算为通过结合子进行的 [exp_iso] 转置的复合：要将 f : w ~> z^(x × y) 转置通过 [to exp_prod_l]，先反转置一次，重新结合，然后再转置两次回来。它们适用于每个广义元素 f，而不仅仅是恒等，这使它们是关于这两个双射的陈述，而不是关于某个值的陈述。  

   [prod_assoc_from_first] 是第二个陈述所需的结合子自然变换；[to] 的方向是上面的 [prod_assoc_first_first]。
*)
Lemma prod_assoc_from_first {a b x y : C} (k : a ~> b) :
  from prod_assoc ∘ first (z:=x × y) k
    ≈ first (z:=y) (first (z:=x) k) ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

Lemma exp_prod_l_transpose {w x y z : C} (f : w ~> z^(x × y)) :
  to (@exp_prod_l C _ _ x y z) ∘ f ≈ curry (curry (uncurry f ∘ to prod_assoc)).
Proof.
  rewrite exp_prod_l_to_unfold.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_first_first.
  now rewrite eval_first_comp.
Qed.

Lemma exp_prod_l_untranspose {w x y z : C} (g : w ~> (z^y)^x) :
  from (@exp_prod_l C _ _ x y z) ∘ g
    ≈ curry (uncurry (uncurry g) ∘ from prod_assoc).
Proof.
  rewrite exp_prod_l_from_unfold.
  rewrite curry_comp_l.
  f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_from_first.
  rewrite comp_assoc.
  now rewrite <- uncurry_comp, eval_first.
Qed.

(*
   * ** Law 2: (y × z)^x ≅ y^x × z^x, natural in x, y and z

   Domain (C^op ∏ (C ∏ C)): the object (x, (y, z)) goes to (y × z)^x on the
   left and to y^x × z^x on the right.  Only the first slot is
   contravariant. 

   --------
   * ** 定律 2: (y × z)^x ≅ y^x × z^x，自然于 x、y 和 z

   定义域 (C^op ∏ (C ∏ C))：对象 (x, (y, z)) 映射到左边的 (y × z)^x 和右边的 y^x × z^x。只有第一个位置是逆变的。
*)

Lemma exp_prod_r_to_unfold {x y z : C} :
  to (@exp_prod_r C _ _ x y z) ≈ curry (exl ∘ eval) △ curry (exr ∘ eval).
Proof. reflexivity. Qed.

(*
 Two readings of [ihom] with one argument an identity, used to recognise the
 legs of [exp_prod_r] and [exp_coprod] as internal-hom actions. 

 --------
 [ihom] 的两种读法，其中一个参数是恒等式，用于识别 [exp_prod_r] 和 [exp_coprod] 的边作为内部同态作用。
*)
Lemma ihom_id_l {a c d : C} (k : c ~> d) : ihom (id[a]) k ≈ curry (k ∘ eval).
Proof. unfold ihom; now rewrite second_id, id_right. Qed.

Lemma ihom_id_r {a b c : C} (k : b ~> a) :
  ihom k (id[c]) ≈ curry (eval ∘ second k).
Proof. unfold ihom; now rewrite id_left. Qed.

Definition expProdR_lhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p) × snd (snd p))^(opobj (fst p)).

Definition expProdR_lhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_lhs x ~> expProdR_lhs y :=
  ihom (oparr (fst m)) (split (fst (snd m)) (snd (snd m))).

Program Definition ExpProdR_LHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_lhs;
  fmap := @expProdR_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdR_rhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p))^(opobj (fst p)) × (snd (snd p))^(opobj (fst p)).

Definition expProdR_rhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_rhs x ~> expProdR_rhs y :=
  split (ihom (oparr (fst m)) (fst (snd m))) (ihom (oparr (fst m)) (snd (snd m))).

Program Definition ExpProdR_RHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_rhs;
  fmap := @expProdR_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpProdR_LHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_LHS] (x, (y, z)) = (y × z)^(opobj x) := eq_refl.

Example ExpProdR_RHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_RHS] (x, (y, z)) = y^(opobj x) × z^(opobj x) := eq_refl.

(* Both sides are forks, so the square splits into its two components, and each component is one application of [ihom_comp] modulo [exl_split] or [exr_split]. / 两边都是分叉，因此方块分成它的两个组成部分，每个组成部分是 [ihom_comp] 在模 [exl_split] 或 [exr_split] 下的一次应用。 *)
Lemma exp_prod_r_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y ~> y') (h : z ~> z') :
  split (ihom f g) (ihom f h) ∘ to (@exp_prod_r C _ _ x y z)
    ≈ to (@exp_prod_r C _ _ x' y' z') ∘ ihom f (split g h).
Proof.
  rewrite !exp_prod_r_to_unfold.
  rewrite <- !ihom_id_l.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite exl_split | now rewrite exr_split ].
Qed.

Definition exp_prod_r_iso (p : C^op ∏ (C ∏ C)) :
  ExpProdR_LHS p ≅ ExpProdR_RHS p :=
  @exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p)).

Definition exp_prod_r_natural :
  @Isomorphism ([C^op ∏ (C ∏ C), C]) ExpProdR_LHS ExpProdR_RHS :=
  NaturalIso_of_pointwise exp_prod_r_iso
    (fun _ _ m => exp_prod_r_square (oparr (fst m)) (fst (snd m)) (snd (snd m))).

Lemma exp_prod_r_natural_component (p : C^op ∏ (C ∏ C)) :
  transform[to exp_prod_r_natural] p
    ≈ to (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma exp_prod_r_natural_component_from (p : C^op ∏ (C ∏ C)) :
  transform[from exp_prod_r_natural] p
    ≈ from (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(* * ** Laws 3 and 4 need coproducts as well / * ** 法则3和4也需要余积 *)

Context `{@Cocartesian C}.

(* Duals of [exl_split] and [exr_split]; Structure/Cocartesian.v carries the [left]/[right] versions but not these. / [exl_split] 和 [exr_split] 的对偶；Structure/Cocartesian.v 包含 [left] / [right] 版本，但不包含这些。 *)
Lemma cover_inl {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inl ≈ inl ∘ f.
Proof. unfold cover; now rewrite inl_merge. Qed.

Lemma cover_inr {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inr ≈ inr ∘ g.
Proof. unfold cover; now rewrite inr_merge. Qed.

(* * ** Law 3: x × (y + z) ≅ x × y + x × z, natural in x, y and z Domain (C ∏ (C ∏ C)); every slot is covariant. / * ** 定律 3：x × (y + z) ≅ x × y + x × z，对于 x、y 和 z 是自然的 定义域 (C ∏ (C ∏ C))；每个位置都是协变的。 *)

Lemma prod_coprod_r_from_unfold {x y z : C} :
  from (@prod_coprod_r C _ _ _ x y z) ≈ second inl ▽ second inr.
Proof. reflexivity. Qed.

Definition prodCoprodR_lhs (p : C ∏ (C ∏ C)) : C :=
  (fst p) × (fst (snd p) + snd (snd p)).

Definition prodCoprodR_lhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_lhs x ~> prodCoprodR_lhs y :=
  split (fst m) (cover (fst (snd m)) (snd (snd m))).

Program Definition ProdCoprodR_LHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_lhs;
  fmap := @prodCoprodR_lhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_lhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite cover_id, split_id.
Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite split_comp, cover_comp.
Qed.

Definition prodCoprodR_rhs (p : C ∏ (C ∏ C)) : C :=
  (fst p × fst (snd p)) + (fst p × snd (snd p)).

Definition prodCoprodR_rhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_rhs x ~> prodCoprodR_rhs y :=
  cover (split (fst m) (fst (snd m))) (split (fst m) (snd (snd m))).

Program Definition ProdCoprodR_RHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_rhs;
  fmap := @prodCoprodR_rhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_rhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite !split_id, cover_id.
Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite cover_comp, !split_comp.
Qed.

Example ProdCoprodR_LHS_obj (x y z : C) :
  fobj[ProdCoprodR_LHS] (x, (y, z)) = x × (y + z) := eq_refl.

Example ProdCoprodR_RHS_obj (x y z : C) :
  fobj[ProdCoprodR_RHS] (x, (y, z)) = x × y + x × z := eq_refl.

(* Proved in the [from] orientation -- where both sides are copairings and the whole calculation is [merge_comp] plus one projection law -- and turned round by [natural_flip_to]. / 在 [from] 定向中得到证明 —— 其中双方都是配对，并且整个计算是 [merge_comp] 加上一个投影定律 —— 并被 [natural_flip_to] 翻转。 *)
Lemma prod_coprod_r_from_square {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  split f (cover g h) ∘ from (@prod_coprod_r C _ _ _ x y z)
    ≈ from (@prod_coprod_r C _ _ _ x' y' z') ∘ cover (split f g) (split f h).
Proof.
  rewrite !prod_coprod_r_from_unfold.
  unfold cover.
  rewrite <- !merge_comp.
  apply merge_inv; split.
  - rewrite split_second, inl_merge.
    rewrite comp_assoc, inl_merge.
    now rewrite second_split.
  - rewrite split_second, inr_merge.
    rewrite comp_assoc, inr_merge.
    now rewrite second_split.
Qed.

Definition prod_coprod_r_iso (p : C ∏ (C ∏ C)) :
  ProdCoprodR_LHS p ≅ ProdCoprodR_RHS p :=
  @prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p)).

Definition prod_coprod_r_natural :
  @Isomorphism ([C ∏ (C ∏ C), C]) ProdCoprodR_LHS ProdCoprodR_RHS :=
  NaturalIso_of_pointwise prod_coprod_r_iso
    (natural_flip_to prod_coprod_r_iso
       (fun _ _ m => prod_coprod_r_from_square (fst m) (fst (snd m)) (snd (snd m)))).

Lemma prod_coprod_r_natural_component (p : C ∏ (C ∏ C)) :
  transform[to prod_coprod_r_natural] p
    ≈ to (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma prod_coprod_r_natural_component_from (p : C ∏ (C ∏ C)) :
  transform[from prod_coprod_r_natural] p
    ≈ from (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(*
   * ** Law 4: x^(y + z) ≅ x^y × x^z, natural in x, y and z

   Domain ((C^op ∏ C^op) ∏ C), as for Law 1, but now the two contravariant
   slots are the summands of the exponent: ((y, z), x) goes to x^(y + z) on
   the left and to x^y × x^z on the right. 

   --------
   * ** 定律 4：x^(y + z) ≅ x^y × x^z，对 x、y 和 z 自然成立

   定义域 ((C^op ∏ C^op) ∏ C)，与定律 1 相同，但现在两个逆变位置是指数的加数：((y, z), x) 在左边映射到 x^(y + z)，在右边映射到 x^y × x^z。
*)

Lemma exp_coprod_to_unfold {x y z : C} :
  to (@exp_coprod C _ _ _ x y z)
    ≈ curry (eval ∘ second inl) △ curry (eval ∘ second inr).
Proof. reflexivity. Qed.

Definition expCoprod_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) + opobj (snd (fst p))).

Definition expCoprod_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_lhs x ~> expCoprod_lhs y :=
  ihom (cover (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpCoprod_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_lhs;
  fmap := @expCoprod_lhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite cover_id, ihom_id.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite ihom_comp, cover_comp.
Qed.

Definition expCoprod_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p))) × (snd p)^(opobj (snd (fst p))).

Definition expCoprod_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_rhs x ~> expCoprod_rhs y :=
  split (ihom (oparr (fst (fst m))) (snd m)) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpCoprod_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_rhs;
  fmap := @expCoprod_rhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpCoprod_LHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_LHS] ((y, z), x) = x^(opobj y + opobj z) := eq_refl.

Example ExpCoprod_RHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_RHS] ((y, z), x) = x^(opobj y) × x^(opobj z) := eq_refl.

Lemma exp_coprod_square {x y z x' y' z' : C}
      (g : y' ~> y) (h : z' ~> z) (f : x ~> x') :
  split (ihom g f) (ihom h f) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x' y' z') ∘ ihom (cover g h) f.
Proof.
  rewrite !exp_coprod_to_unfold.
  rewrite <- !ihom_id_r.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite cover_inl | now rewrite cover_inr ].
Qed.

Definition exp_coprod_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpCoprod_LHS p ≅ ExpCoprod_RHS p :=
  @exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p))).

Definition exp_coprod_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpCoprod_LHS ExpCoprod_RHS :=
  NaturalIso_of_pointwise exp_coprod_iso
    (fun _ _ m => exp_coprod_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

Lemma exp_coprod_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_coprod_natural] p
    ≈ to (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

Lemma exp_coprod_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_coprod_natural] p
    ≈ from (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

(* The single-variable specimen for Law 4: naturality in the first summand. / 定律4的单变量样本：第一个和数中的自然性。 *)
Corollary exp_coprod_natural_in_first_summand {x y z y' : C} (g : y' ~> y) :
  split (ihom g (id[x])) (ihom (id[z]) (id[x])) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x y' z) ∘ ihom (cover g (id[z])) (id[x]).
Proof. exact (exp_coprod_square g (id[z]) (id[x])). Qed.

End ExpNatural.
