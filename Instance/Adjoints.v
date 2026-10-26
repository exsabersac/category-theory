Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category of adjunctions. / 伴随的范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors#Composition

 Adjunctions can be composed: the identity functor is self-adjoint
 (Id ⊣ Id, [adj_id]), and given F ⊣ U and F' ⊣ U' the composites are again
 adjoint, with the left adjoints composing covariantly and the right adjoints
 contravariantly,

 F ⊣ U  →  F' ⊣ U'  →  F ◯ F' ⊣ U' ◯ U     ([adj_comp]).

 (Recall F ◯ G applies G then F, so F ◯ F' is the left adjoint and U' ◯ U the
 right adjoint of the composite.) This is exactly what is needed to organize
 categories and adjunctions into a category [Adjoints]:

 objects        Categories
 arrows         Adjunctions F ⊣ U between categories
 identity       Id ⊣ Id
 composition    F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U

 Two adjunctions are identified when their left and right adjoints are
 correspondingly naturally isomorphic ([adj_morphism_setoid]).

 WHICH ADJOINT POINTS FORWARD.  The choice is arbitrary, but it has to be
 named correctly, and the code makes the opposite one from what this
 header used to claim.  [adj_morphism] below declares
 [free_functor : D ⟶ C] and [forgetful_functor : C ⟶ D], and [Adjoints]
 sets [hom := @adj_morphism]; so an arrow C ~> D of [Adjoints] carries
 its RIGHT adjoint pointing FORWARD, C ⟶ D, and its LEFT adjoint
 pointing BACKWARD, D ⟶ C.  Measured out of tree, this file carrying no
 probe: for f : X ~> Y in [Adjoints] the ascription
 [forgetful_functor f : X ⟶ Y] typechecks and [free_functor f : X ⟶ Y]
 is rejected.  The composition displayed above
 agrees: along A ~> B ~> C the right adjoints compose covariantly, to
 U' ◯ U : A ⟶ C, and the left adjoints contravariantly, to
 F ◯ F' : C ⟶ A.

 WHICH OF MAC LANE'S TWO ORIENTATIONS THIS IS.  §IV.7, book p. 101, meets
 the ANALOGOUS choice for the category of adjunctions between two FIXED
 categories -- analogous and not the same, his axis being which way a
 natural TRANSFORMATION runs and this one which way a FUNCTOR runs --
 and displays BOTH readings as forgetful
 functors: A^X ← A^(adj)X reads off the LEFT adjoints, covariantly, while
 [A^(adj)X]^op → X^A reads off the RIGHT adjoints and is therefore
 displayed on the OPPOSITE category.  So in his A^(adj)X the left adjoint
 is the forward one, and in [A^(adj)X]^op the right adjoint is.
 [Adjoints] is a different category -- its objects are categories, not
 adjunctions between one fixed pair -- but on this one axis it matches
 the SECOND: right adjoint forward, like [A^(adj)X]^op.  Mac Lane's
 A^(adj)X itself is Instance/Adj.v's [Adj C D], which takes the FIRST
 orientation, and the two functors he displays are
 Instance/Adj/Forgetful.v.  See the closing note on InvAdj for the
 involutive refinement that removes the choice altogether. 

 --------
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor 
 维基百科:  https://en.wikipedia.org/wiki/Adjoint_functors#Composition 

 拓扑可以组合：恒等函子是自伴随的
 (Id ⊣ Id,  [adj_id] )，并且给定 F ⊣ U 和 F' ⊣ U'，其复合仍然
 是伴随的，左伴随函子进行协变组合，右伴随函子进行逆变组合，

 F ⊣ U  →  F' ⊣ U'  →  F ◯ F' ⊣ U' ◯ U     ( [adj_comp] )。

 （回忆 F ◯ G 是先应用 G 再应用 F，因此 F ◯ F' 是复合的左伴随函子，U' ◯ U 是复合的右伴随函子。）这正是组织
 类别和伴随进入一个类别 [Adjoints] 所需要的：

 对象        类别
 箭头        类别间的伴随 F ⊣ U
 恒等        Id ⊣ Id
 组合        F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U当两个伴随的左伴随和右伴随分别自然同构时，这两个伴随被认为是相同的 ([adj_morphism_setoid])。哪一个伴随指向前方。选择是任意的，但必须正确命名，并且代码生成的与此头文件曾声明的相反。下面的 [adj_morphism] 声明了 [free_functor : D ⟶ C] 和 [forgetful_functor : C ⟶ D]，[Adjoints] 设置 [hom := @adj_morphism]；因此 [Adjoints] 中的箭头 C ~> D 的右伴随指向前方，C ⟶ D，而左伴随指向后方，D ⟶ C。脱离树结构测量时，该文件不带任何探针：对于 [Adjoints] 中的 f : X ~> Y，类型标注 [forgetful_functor f : X ⟶ Y] 可以通过类型检查，而 [free_functor f : X ⟶ Y] 会被拒绝。上面显示的组合是一致的：沿着 A ~> B ~> C，右伴随协变组合为 U' ◯ U : A ⟶ C，左伴随逆变组合为 F ◯ F' : C ⟶ A。这是麦克莱恩的两种取向中的哪一种。§IV.7, 书页 101，对应于两个固定范畴之间附加范畴的类似选择——类似但不相同，他的轴是自然变换的方向，而这个是函子运行的方向——并将两种解释都显示为遗忘函子：A^X ← A^(adj)X 列出左陪伴函子（协变方式），而 [A^(adj)X] ^op → X^A 列出右陪伴函子，因此显示在相反的范畴上。因此在他的 A^(adj)X 中，左陪伴函子是前向的，而在 [A^(adj)X] ^op 中，右陪伴函子是前向的。[Adjoints] 是一个不同的范畴——它的对象是范畴，而不是一对固定对象之间的附加关系——但在这个轴上它与第二种匹配：右陪伴函子前向，就像 [A^(adj)X] ^op 一样。Mac Lane 的
 A^(adj)X 本身是 Instance/Adj.v 的 [Adj C D]，它采用第一个方向，而他展示的两个函子是 Instance/Adj/Forgetful.v。参见 InvAdj 的结尾注释，了解完全去除选择的自反细化。
*)

(*
 The identity functor is its own left and right adjoint: the transpose iso
 F x ~> y ≅ x ~> U y is the identity on hom-sets when F = U = Id. 

 --------
 恒等函子是其自身的左伴随和右伴随：当 F = U = Id 时，换位同构 F x ~> y ≅ x ~> U y 在 homolog 集合上是恒等映射。
*)
#[export]
Program Instance adj_id {C : Category} : Id ⊣ Id := {
  adj := fun _ _ =>
    {| to   := {| morphism := _ |}
     ; from := {| morphism := _ |} |}
}.

(*
 Composite of two adjunctions. The transpose iso for F ◯ F' ⊣ U' ◯ U is the
 composite of the two component transposes,

 F (F' a) ~> b  ≅[X]  F' a ~> U b  ≅[Y]  a ~> U' (U b),

 so ⌊-⌋ of the composite is ⌊-⌋ ∘ ⌊-⌋ and its inverse runs the two ⌈-⌉ in the
 opposite order. 

 --------
 两个伴随的复合。对于 F ◯ F' ⊣ U' ◯ U 的转置同构是两个分量转置的复合，

 F (F' a) ~> b  ≅ [X]   F' a ~> U b  ≅ [Y]   a ~> U' (U b),

 因此复合的 ⌊-⌋ 是 ⌊-⌋ ∘ ⌊-⌋，其逆运行两个 ⌈-⌉ 的顺序相反。
*)
Program Definition adj_comp
        {C : Category} {D : Category} {E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ◯ F' ⊣ U' ◯ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => to adj (to adj f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj⁻¹ (adj⁻¹ f) |} |}
|}.
Next Obligation. proper. rewrites; reflexivity. Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  srewrite (@iso_to_from _ _ _ (@adj C D F U X (F' a) b)).
  sapply (@iso_to_from _ _ _ (@adj D E F' U' Y a (U b))).
Qed.
Next Obligation.
  srewrite (@iso_from_to _ _ _ (@adj D E F' U' Y a (U b))).
  sapply (@iso_from_to _ _ _ (@adj C D F U X (F' a) b)).
Qed.
Next Obligation. rewrite <- !to_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !to_adj_nat_r; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_r; reflexivity. Qed.

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 30, right associativity) : category_scope.

(*
 An arrow C ⇸ D in [Adjoints]: a left/right adjoint pair whose FORWARD
 direction is the RIGHT adjoint, [forgetful_functor : C ⟶ D]; the left
 adjoint (“free”) points backward, D ⟶ C.  See the header for how this
 sits against Mac Lane's two orientations.  Only this description is
 corrected here; the record itself is unchanged. 

 --------
 在 [Adjoints] 中的箭头 C ⇸ D：一个左/右伴随对，其正向方向是右伴随，[forgetful_functor : C ⟶ D]；左伴随（“自由”）指向后方，即 D ⟶ C。请参见页眉了解它如何与 Mac Lane 的两种取向对应。这里只有这个描述被更正；记录本身保持不变。
*)
Record adj_morphism {C : Category} {D : Category} := {
  free_functor : D ⟶ C;                       (* the left adjoint / 左伴随 *)
  forgetful_functor : C ⟶ D;                  (* the right adjoint / 右伴随 *)
  adjunction : free_functor ⊣ forgetful_functor
}.

Local Set Warnings "-intuition-auto-with-star".

(*
 Two adjunctions are equal when their left adjoints are naturally isomorphic
 and their right adjoints are naturally isomorphic (in the functor category
 [Fun]); the conjugate-pair correspondence then makes the choice coherent. 

 --------
 当两个伴随的左伴随函子自然同构且右伴随函子自然同构（在函子范畴 [Fun] 中）时，它们被认为是相等的；然后，共轭对对应使得该选择是一致的。
*)
#[export]
Program Instance adj_morphism_setoid {C : Category} {D : Category} :
  Setoid (@adj_morphism C D) := {
  equiv := fun f g =>
              (free_functor f ≅[Fun] free_functor g) *
              (forgetful_functor f ≅[Fun] forgetful_functor g)
}.
(*
 The relation is a pair of natural isomorphisms, so it is an equivalence
 componentwise, straight from [iso_equivalence] in [Theory.Isomorphism].
 Spelled out rather than left to [equivalence]: this obligation was proved
 by that tactic plus two transitivity bullets, and its reflexivity and
 symmetry components were being closed only because [equivalence] reached
 [solve_crelation], a pattern-less [Hint Extern] in the standard library's
 [crelations] database, through a wide [auto with *].  Which pattern-less
 hints a wide [auto] reaches, and in which order, is a property of the hint
 database rather than anything this library states; on Rocq master the
 reflexivity and symmetry components stopped being discharged, the first
 bullet landed on a symmetry goal instead of the transitivity one it was
 written for, and [assumption] had nothing to close
 [free_functor y ≅ free_functor y] with -- issue #213.  Proving the three
 laws directly removes the dependency.  See [Test/Issue213.v]. 

 --------
 这个关系是一对自然同构，因此它在每个组件上都是等价的，直接来自  [iso_equivalence]  在  [Theory.Isomorphism] 中。详细说明而不是留给  [equivalence]：通过该策略加两个传递性步骤证明了这个义务，其自反性和对称性组件之所以被闭合，仅仅是因为  [equivalence] 达到了 [solve_crelation]，这是标准库 [crelations] 数据库中一个无模式的 [Hint Extern]，通过一个广泛的 [auto with *]。哪种无模式提示了一个宽广的 [auto] 能够达到，以及按照什么顺序，是提示数据库的属性，而不是这个库所声明的；在 Rocq 主分支上，自反性和对称性组件停止被释放，第一个要点落在了一个对称性目标上，而不是它原本为之编写的传递性目标，并且 [assumption] 没有任何东西可以关闭 [free_functor y ≅ free_functor y] —— 问题 #213。直接证明这三个定律可以消除依赖。见 [Test/Issue213.v]。
*)
Next Obligation.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(*
 The category of Adjoints:

 objects                Categories
 arrows                 Adjunctions between categories
 identity               Id ⊣ Id
 composition            F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U 

 --------
 伴随的类别：

 对象                范畴
 箭头                范畴之间的伴随
 恒等                Id ⊣ Id
 复合                F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U
*)

Program Definition Adjoints : Category := {|
  obj     := Category;
  hom     := @adj_morphism;
  homset  := @adj_morphism_setoid;
  id      := fun X => {| free_functor      := Id[X]
                  ; forgetful_functor := Id[X] |};
  compose := fun A B C f g =>
    {| adjunction :=
         @adj_comp A B C (free_functor g) (forgetful_functor g)
                   (free_functor f) (forgetful_functor f)
                   (adjunction g) (adjunction f) |}
|}.
Next Obligation.
  proper; simpl.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to X] _) ∘ transform[to X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from X] _) ∘ transform[from X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_to_from; cat.
      destruct X0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_from_to; cat.
      destruct X0; simpl in *.
      rewrite iso_from_to0; cat.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to H] _) ∘ transform[to H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from H] _) ∘ transform[from H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_to_from; cat.
      destruct H0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_from_to; cat.
      destruct H0; simpl in *.
      rewrite iso_from_to0; cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.

(*
 The closing quote (Chris Heunen, on MathOverflow) describes InvAdj, the
 involutive refinement of [Adjoints] that removes the arbitrary forward/
 backward choice; it is defined in §3.1.8 of his thesis “Categorical Quantum
 Models and Logics”:
 https://homepages.inf.ed.ac.uk/cheunen/publications/2009/thesis/thesis.pdf
 This library implements only the plain [Adjoints] above, not InvAdj. 

 --------
 结尾引用（Chris Heunen，在 MathOverflow 上）描述了 InvAdj，即 [Adjoints] 的自反精炼，它消除了任意的前/后选择；它在他论文《范畴量子模型与逻辑》第 3.1.8 节中定义：
 https://homepages.inf.ed.ac.uk/cheunen/publications/2009/thesis/thesis.pdf
 该库仅实现了上述普通的 [Adjoints]，而不是 InvAdj。
*)

(*
 mathoverflow: “You will have to make an arbitrary choice for the direction
 of morphisms: is the left adjoint ”forward“ or ”backward“? To prevent that,
 you can add involutions. The resulting category [InvAdj] of involutive
 categories and adjunctions has a lot of interesting structure. It is a
 dagger category, and in fact the `mother of all dagger categories', as it
 universally embeds any dagger category. In particular, the full subcategory
 of (ortho)posets and Galois connections has dagger kernels, dagger
 biproducts, an an opclassifier. See these two papers. Now for the
 definition (from 3.1.8 of my thesis):

 A functor ∗ : C^op → C is called involutive when ∗ ∘ ∗ = Id. Define a
 category [InvAdj] as follows. Objects are pairs (C,∗) of a category with an
 involution. A morphism (C,∗) → (D,∗) is functor F : C^op → D that has a
 left adjoint, where two such functors are identified when they are
 naturally isomorphic. The identity morphism on (C,∗) is the functor ∗ :
 C^op → C ; its left adjoint is ∗^op : C → C^op. The composition of F : C^op
 → D and G : D^op → E is defined by G ∘ ∗^op ∘ F : C^op → E; its left
 adjoint is F′ ∘ ∗ ∘ G′, where F′ ⊣ F and G′ ⊣ G.

 (It is not arbitrary to require a left adjoint instead of a right one. A
 contravariant functor from C to D can be written both as a (covariant)
 functor F : C^op → D or as a (covariant) functor F^op : C → D^op. The
 latter version has a right adjoint precisely when the former version has a
 left adjoint.)” 

 --------
 mathoverflow：“你必须为方向做出任意选择
 态射：左伴随是“正向”还是“向后”？为了防止这种情况，
 你可以添加对应。得到的范畴[InvAdj]自反的
 范畴和伴随函有很多有趣的结构。它是
 匕首类别，实际上是“所有匕首类别之母”，因为它
 普遍地嵌入任意匕首范畴。特别地，完整子范畴
 （正交）偏序集和伽罗瓦联络的匕首核为匕首核
 双积，一个操作分类器。参见这两篇论文。现在来看
 定义（摘自我的论文3.1.8）：当函子 ∗ : C^op → C 满足 ∗ ∘ ∗ = Id 时，称其为自反的。定义一个类别 [InvAdj]，如下。对象是带有自反的类别对 (C,∗)。态射 (C,∗) → (D,∗) 是具有左伴随的函子 F : C^op → D，其中当两个这样的函子自然同构时，它们被视为相同。在 (C,∗) 上的恒等态射是函子 ∗ : C^op → C；它的左伴随为 ∗^op : C → C^op。函子 F : C^op → D 和 G : D^op → E 的复合定义为 G ∘ ∗^op ∘ F : C^op → E；它的左伴随为 F′ ∘ ∗ ∘ G′，其中 F′ ⊣ F 且 G′ ⊣ G。（要求左伴随而不是右伴随并非随意。一个从 C 到 D 的逆变函子可以既写作一个（协变）函子 F : C^op → D，也可以写作一个（协变）函子 F^op : C → D^op。当且仅当前者有左伴随时，后者才恰好有右伴随。）
*)
