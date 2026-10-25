Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Transform.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p1}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.

(*
nLab: https://ncatlab.org/nlab/show/natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation

   A natural transformation `transform : F ⟹ G` between functors
   `F G : C ⟶ D` is a family of morphisms `transform : F x ~> G x`, one per
   object `x : C` (its components), such that for every morphism `f : x ~> y`
   the naturality square commutes: `fmap[G] f ∘ transform ≈ transform ∘
   fmap[F] f` (i.e., `G f ∘ η_x ≈ η_y ∘ F f`). Intuitively, transforming a
   mapped object before or after applying the functorial action introduces no
   change in the effect of such mappings.

--------
nLab: https://ncatlab.org/nlab/show/natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation

   函子 `F G : C ⟶ D` 之间的自然变换 `transform : F ⟹ G` 是一族态射
   `transform : F x ~> G x`，每个对象 `x : C` 一个（其分量），使得对每个态射
   `f : x ~> y`，自然性方块交换：`fmap[G] f ∘ transform ≈ transform ∘
   fmap[F] f`（即 `G f ∘ η_x ≈ η_y ∘ F f`）。直观上，在应用函子作用之前或之后
   变换被映射的对象，不会改变此类映射的效果。
*)

(*
Where natural transformations come from, and why they come first

   nLab:  https://ncatlab.org/nlab/show/natural+transformation
   nLab:  https://ncatlab.org/nlab/show/Godement+product
   nLab:  https://ncatlab.org/nlab/show/Roger+Godement
   SEP:   https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "Natural isomorphisms in group theory",
          Proc. Natl. Acad. Sci. USA 28(12), 1942
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Trans. Amer. Math. Soc. 58(2), 1945

   The definition above is the concept category theory was invented to
   state.  Mathematicians had long called a map "natural" when it was
   defined uniformly, with no arbitrary choice of basis or of
   representatives, but the word had no precise content.  The 1942
   preliminary report proposed a definition confined to group theory;
   the 1945 paper generalized it, introducing categories, functors, and
   natural transformations together, and stands as the founding document
   of the subject.  Its opening example locates the boundary exactly
   where the naturality square does: a finite-dimensional vector space L
   is isomorphic to its dual, but no isomorphism can be exhibited until
   a basis is chosen, and different bases yield different isomorphisms,
   whereas the isomorphism of L with its double dual is given
   "simultaneously" for all such spaces, no basis being mentioned.  The
   pointwise isomorphisms with the dual exist, yet they cannot be
   assembled into a family commuting with every linear map; the
   double-dual family can, and the paper draws precisely this file's
   square on p. 233, calling its commutativity the "naturality" or
   "simultaneity" condition.

   The library's Category → Functor → Transform spine thus ends at its
   own point of origin.  The 1945 paper is explicit: "the whole concept
   of a category is essentially an auxiliary one; our basic concepts are
   essentially those of a functor and of a natural transformation" (§6,
   p. 247), and Mac Lane restates the point in "Categories for the
   Working Mathematician" (Springer 1998, §I.4): the category was
   defined in order to be able to define the functor, and the functor in
   order to be able to define the natural transformation.  The same §6
   already confronts the size problems posed by "the category of all
   sets" — the concern this library answers with the universe
   parameters visible in this file's Section.

   Natural transformations are likewise the 2-cells of the category of
   categories.  Vertical composition [nat_compose], together with the
   componentwise equivalence [Transform_Setoid], is the composition of
   the functor category [C, D] built in Instance/Fun.v; horizontal
   composition [nat_hcompose] is the Godement product, traced to the
   five rules of functorial calculus in Godement's 1958 sheaf-theory
   book; and the interchange law between the two makes Cat a strict
   2-category (nLab, "Godement product"), realized in this library as
   the motivating bicategory of Instance/Cat/Bicategory.v, with
   [whisker_left] and [whisker_right] the horizontal composites against
   an identity.  Everything downstream is phrased in these 2-cells: an
   adjunction is a unit and a counit subject to the triangle identities
   (Adjunction/Natural/Transformation.v), a monad is its η and μ
   (Theory/Monad.v), the Yoneda lemma computes a setoid of
   transformations out of a representable (Functor/Hom/Yoneda.v), and
   Kan extension universal properties are stated through whiskering
   (Theory/Kan/Extension.v).

   The computational reading identifies natural transformations with
   parametrically polymorphic functions.  Reynolds' abstraction theorem
   (Reynolds, "Types, Abstraction and Parametric Polymorphism",
   Information Processing 83, 1983) and the free theorems it yields
   (Wadler, "Theorems for free!", FPCA 1989) show that every polymorphic
   function from lists to lists commutes with map f for every f — the
   naturality square, obtained from the type alone, since such a
   function can only rearrange, duplicate, or drop elements, never
   inspect them.  Milewski makes the identification explicit for Haskell
   (Milewski, "Natural Transformations", 2015): a polymorphic function
   between functors is automatically natural.  A basis-dependent
   construction is a non-parametric one; the 1942 uniformity and the
   1983 uniformity are one idea.  Yet in this setoid setting naturality
   is not free: no parametricity theorem applies to a bare family
   ∀ x, F x ~> G x, so [naturality] is carried as genuine proof content
   — the Haskell reading explains what the law means, and the field is
   where it is paid for.  At V = Sets, the enriched transformations of
   Construction/Enriched/Sets.v recover exactly this file's
   [Transform].

--------
自然变换从何而来，以及为何它们排在第一位

   nLab:  https://ncatlab.org/nlab/show/natural+transformation
   nLab:  https://ncatlab.org/nlab/show/Godement+product
   SEP:   https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "Natural isomorphisms in group theory",
          Proc. Natl. Acad. Sci. USA 28(12), 1942
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Trans. Amer. Math. Soc. 58(2), 1945

   上文定义正是发明范畴论所要陈述的概念。数学家长久称映射「自然」当它被
   一致定义、无任意基或代表元选择时，但该词无精确内容。1942 年预备报告提出
   限于群论的定义；1945 年论文加以推广，同时引入范畴、函子与自然变换，并成为
   该学科的奠基文献。其开篇例子恰好把边界放在自然性方块所在之处：有限维向量
   空间 L 同构于其对偶，但在选定基之前无法展示同构，且不同基给出不同同构；
   而 L 与其双重对偶的同构对所有此类空间「同时」给出，无需提及基。与对偶的
   逐点同构存在，却不能组装成与每个线性映射交换的族；双重对偶族可以，论文在
   第 233 页画出恰为本文件的方块，称其交换性为「自然性」或「同时性」条件。

   因此库的 Category → Functor → Transform 脊柱终于其自身的起源点。1945 年论文
   写明：「范畴的整个概念本质上是辅助性的；我们的基本概念本质上是函子与自然变换」
   （§6, p. 247）。本文件定义分量与自然性方块；垂直复合、whiskering 与 Godement
   积见同目录后续。
*)

(*
The `naturality_sym` field records the symmetric orientation of the
   naturality square. It is logically derivable from `naturality` (see
   `Build_Transform'` below, which proves it from `naturality` alone), but is
   kept as a primitive field so that duality holds definitionally: the
   opposite of a [Transform] swaps `naturality` and `naturality_sym` without
   any rewriting, mirroring `comp_assoc`/`comp_assoc_sym` in [Category].

--------
`naturality_sym` 字段记录了自然性方格的对称方向。它在逻辑上可以从 `naturality` 推导出来（见下面的 `Build_Transform'`，它仅从 `naturality` 证明了这一点），但它仍被保留为一个基本字段，以便对偶性在定义上成立：[Transform] 的相反项会交换 `naturality` 和 `naturality_sym` 而无需任何重写，在 [Category] 中镜像 `comp_assoc`/`comp_assoc_sym`。
*)

Class Transform := {
  transform {x} : F x ~> G x;             (* the component at each object x / 每个对象 x 的组件 *)

  (* naturality square: `G f ∘ η_x ≈ η_y ∘ F f` / 自然性方程：`G f ∘ η_x ≈ η_y ∘ F f` *)
  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  (* the symmetric orientation of the naturality square (built-in dual) / 自然性方格的对称取向（内建对偶） *)
  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
  }.

(*
Smart constructor: build a [Transform] from the components together with the
   single (non-symmetric) naturality square, deriving `naturality_sym` by
   symmetry. This witnesses that `naturality_sym` carries no extra content.

--------
智能构造函数：从各个组件以及单个（非对称）自然性方块一起构建 [Transform]，通过对称性推导出 `naturality_sym`。这证明了 `naturality_sym` 不包含额外内容。
*)

Definition Build_Transform'
  (transform' : forall x, F x ~> G x)
  (natural : forall x y (f : x ~> y), fmap[G] f ∘ transform' x ≈ transform' y ∘ fmap[F] f)
  :  Transform.
Proof.
  apply (Build_Transform transform' natural).
  intros x y f; symmetry; apply natural.
Defined.

#[export]
Program Instance Transform_Setoid : Setoid Transform :=
  {| equiv N0 N1 := ∀ x, (@transform N0 x) ≈ (@transform N1 x); |}.
Next Obligation.
  equivalence.
  transitivity (@transform y x0); auto.
Qed.

End Transform.

Arguments transform {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ _ _ _.
Arguments naturality_sym {_ _ _ _} _ _ _ _.

Declare Scope transform_scope.
Declare Scope transform_type_scope.
Bind Scope transform_scope with Transform.
Delimit Scope transform_type_scope with transform_type.
Delimit Scope transform_scope with transform.
Open Scope transform_type_scope.
Open Scope transform_scope.

Notation "F ⟹ G" := (@Transform _ _ F%functor G%functor)
  (at level 90, right associativity) : transform_type_scope.

Notation "transform[ F ]" := (@transform _ _ _ _ F%transform)
  (at level 9, only parsing) : morphism_scope.
Notation "naturality[ F ]" := (@naturality _ _ _ _ F%transform)
  (at level 9, only parsing) : morphism_scope.

Coercion transform : Transform >-> Funclass.

Ltac transform :=
  unshelve (refine {| transform := _ |}; simpl; intros).

Corollary fun_id_left {C D : Category} {F : C ⟶ D} : Id ◯ F ⟹ F.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_id_left_sym {C D : Category} {F : C ⟶ D} : F ⟹ Id ◯ F.
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_id_left_and_sym `(F : C ⟶ D) (x : C) :
  fun_id_left x ∘ fun_id_left_sym x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Lemma fun_id_left_sym_and `(F : C ⟶ D) (x : C) :
  fun_id_left_sym x ∘ fun_id_left x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Corollary fun_id_right {C D : Category} {F : C ⟶ D} : F ◯ Id ⟹ F.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_id_right_sym {C D : Category} {F : C ⟶ D} : F ⟹ F ◯ Id.
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_id_right_and_sym `(F : C ⟶ D) (x : C) :
  fun_id_right x ∘ fun_id_right_sym x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Lemma fun_id_right_sym_and `(F : C ⟶ D) (x : C) :
  fun_id_right_sym x ∘ fun_id_right x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Corollary fun_comp_assoc {C D E B : Category}
  {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : F ◯ (G ◯ H) ⟹ (F ◯ G) ◯ H.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_comp_assoc_sym {C D E B : Category}
  {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : (F ◯ G) ◯ H ⟹ F ◯ (G ◯ H).
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_comp_assoc_and_sym `(F : A ⟶ B) `(G : B ⟶ C) `(H : C ⟶ D) (x : A) :
  fun_comp_assoc x ∘ fun_comp_assoc_sym x ≈ fmap[H] (fmap[G] (fmap[F] id)).
Proof. simpl; cat. Qed.

Lemma fun_comp_assoc_sym_and `(F : A ⟶ B) `(G : B ⟶ C) `(H : C ⟶ D) (x : A) :
  fun_comp_assoc_sym x ∘ fun_comp_assoc x ≈ fmap[H] (fmap[G] (fmap[F] id)).
Proof. simpl; cat. Qed.

(*
The identity natural transformation `id_F : F ⟹ F`. Its component at `X` is
   `id_{F X}`, written here as `fmap[F] id` (equal to `id` by `fmap_id`).

--------
恒等自然变换 `id_F : F ⟹ F`。它在 `X` 处的分量是 `id_{F X}`，这里写作 `fmapXPROTECT0X id`（根据 `fmap_id` 等于 `id`）。
*)

Program Definition nat_id `{F : C ⟶ D} : F ⟹ F := {|
  transform := λ X, fmap (@id C X)
|}.

#[export] Hint Unfold nat_id : core.

(*
Vertical composition of natural transformations: for `g : F ⟹ G` and
   `f : G ⟹ K`, the composite `f ∙ g : F ⟹ K` has component
   `(f ∙ g)_X = f_X ∘ g_X`. This is the composition of the functor category
   `[C, D]`.

--------
自然变换的垂直合成：对于 `g : F ⟹ G` 和 `f : G ⟹ K`，复合 `f ∙ g : F ⟹ K` 的分量是 `(f ∙ g)_X = f_X ∘ g_X`。这是函子范畴 `XPROTECT0X` 的合成。
*)

Program Definition nat_compose `{F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := λ X, transform[f] X ∘ transform[g] X
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  now apply nat_compose_obligation_1.
Qed.

#[export] Hint Unfold nat_compose : core.

Notation "F ∙ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Program Definition nat_compose_respects
        `{F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@nat_compose C D F G K).
Proof. proper. Qed.

#[export]
Program Instance Transform_PreOrder {C E : Category} :
  PreOrder (@Transform C E).
Next Obligation.
  exact (λ _, nat_id).
Defined.
Next Obligation.
  exact (λ _ _ _ f g, nat_compose g f).
Defined.

#[export]
Program Instance Transform_respects {C D : Category} :
  Proper ((λ F G, G ⟹ F) ==> @Transform C D ==> arrow) (@Transform C D) :=
  λ _ _ F _ _ G H, nat_compose G (nat_compose H F).

(*
nLab: https://ncatlab.org/nlab/show/natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation

   Horizontal (Godement) composition. Given `η : F ⟹ G` between
   `F G : C ⟶ D` and `ε : J ⟹ K` between `J K : D ⟶ E`, functor composition
   yields `nat_hcompose ε η : J ◯ F ⟹ K ◯ G` whose component at `x` is
   `transform[ε] (G x) ∘ fmap[J] (transform[η] x)`, which by naturality of `ε`
   also equals `fmap[K] (transform[η] x) ∘ transform[ε] (F x)`. This operation
   is associative with identity, the identity coinciding with that for vertical
   composition, and the two compositions satisfy the interchange law.

--------
nLab：https://ncatlab.org/nlab/show/natural+transformation
维基百科：https://en.wikipedia.org/wiki/Natural_transformation

水平（Godement）组合。给定 `η : F ⟹ G` 在 `F G : C ⟶ D` 与 `ε : J ⟹ K` 之间，以及 `J K : D ⟶ E` 之间的情况，函子组合产生 `nat_hcompose ε η : J ◯ F ⟹ K ◯ G`，其在 `x` 处的分量为 `transformXPROTECT0X (G x) ∘ fmapXPROTECT1X (transformXPROTECT2X x)`，根据 `ε` 的自然性，也等于 `fmapXPROTECT3X (transformXPROTECT4X x) ∘ transformXPROTECT5X (F x)`。该操作具有结合性且有单位元，该单位元与垂直组合的单位元一致，并且两种组合满足交换律。
*)

Program Definition nat_hcompose {C D E} {F G : C ⟶ D} {J K : D ⟶ E}
  (ε : J ⟹ K) (η : F ⟹ G) : J ◯ F ⟹ K ◯ G := {|
  transform := fun x => transform[ε] (fobj[G] x) ∘ fmap[J] (transform[η] x)
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite comp_assoc.
  rewrite <- !fmap_comp.
  rewrite !naturality.
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  now apply nat_hcompose_obligation_1.
Qed.

#[export]
Program Instance Compose_respects_Transform {C D E : Category} :
  Proper (@Transform D E ==> @Transform C D ==> @Transform C E)
         (@Compose C D E) :=
  λ _ F M G _ N,
    {| transform := λ x, fmap[F] (transform[N] x) ∘ transform[M] (G x) |}.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite naturality.
  rewrite naturality.
  rewrite naturality.
  rewrite fmap_comp.
  cat.
Qed.
Next Obligation.
  symmetry.
  now apply Compose_respects_Transform_obligation_1.
Qed.

(*
nLab: https://ncatlab.org/nlab/show/whiskering

   Right whiskering `N ⊲ X`: precompose the natural transformation `N : F ⟹ G`
   with a functor `X : E ⟶ C`, yielding `F ◯ X ⟹ G ◯ X` with component
   `(N ⊲ X)_x = N (X x)`. This is the horizontal composite of `N` with the
   identity transformation on `X`; the naturality squares are inherited
   directly from `N`.

--------
nLab: https://ncatlab.org/nlab/show/whiskering

右鞭毛化 `N ⊲ X`：将自然变换 `N : F ⟹ G` 与函子 `X : E ⟶ C` 预组合，得到 `F ◯ X ⟹ G ◯ X`，其分量为 `(N ⊲ X)_x = N (X x)`。这是 `N` 与 `X` 上恒等变换的水平复合；自然性方形图直接继承自 `N`。
*)

Program Definition whisker_right {C D : Category} {F G : C ⟶ D} `(N : F ⟹ G)
        {E : Category} (X : E ⟶ C) : F ◯ X ⟹ G ◯ X := {|
  transform := λ x, N (X x);

  naturality     := λ _ _ _, naturality _ _ _ _;
  naturality_sym := λ _ _ _, naturality_sym _ _ _ _
|}.

Notation "N ⊲ F" := (whisker_right N F) (at level 10).

(*
nLab: https://ncatlab.org/nlab/show/whiskering

   Left whiskering `X ⊳ N`: postcompose the natural transformation `N : F ⟹ G`
   with a functor `X : D ⟶ E`, yielding `X ◯ F ⟹ X ◯ G` with component
   `(X ⊳ N)_x = fmap[X] (N x)`. This is the horizontal composite of the
   identity transformation on `X` with `N`; naturality follows from `fmap[X]`
   preserving composition (`fmap_comp`) and `N`'s naturality.

--------
nLab：https://ncatlab.org/nlab/show/whiskering

左鞭化 `X ⊳ N`：将自然变换 `N : F ⟹ G` 与函子 `X : D ⟶ E` 后组合，得到带有分量 `(X ⊳ N)_x = fmapXPROTECT0X (N x)` 的 `X ◯ F ⟹ X ◯ G`。这是同 `N` 在 `X` 上的恒等变换的水平复合；自然性来自 `fmapXPROTECT1X` 保持复合（`fmap_comp`）以及 `N` 的自然性。
*)

Program Definition whisker_left {C D : Category}
        {E : Category} (X : D ⟶ E)
        {F G : C ⟶ D} `(N : F ⟹ G) : X ◯ F ⟹ X ◯ G := {|
  transform := λ x, fmap[X] (N x)
|}.
Next Obligation.
  simpl; rewrite <- !fmap_comp;
  apply fmap_respects, naturality.
Qed.
Next Obligation.
  simpl; rewrite <- !fmap_comp;
  apply fmap_respects, naturality_sym.
Qed.

Notation "F ⊳ N" := (whisker_left F N) (at level 10).
