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

(* nLab: https://ncatlab.org/nlab/show/natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation

   函子 `F G : C ⟶ D` 之间的自然变换 `transform : F ⟹ G` 是一族态射
   `transform : F x ~> G x`，每个对象 `x : C` 一个（其分量），使得对每个态射
   `f : x ~> y`，自然性方块交换：`fmap[G] f ∘ transform ≈ transform ∘
   fmap[F] f`（即 `G f ∘ η_x ≈ η_y ∘ F f`）。直观上，在应用函子作用之前或之后
   变换被映射的对象，不会改变此类映射的效果。 *)

(* 自然变换从何而来，以及为何它们排在第一位

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
   积见同目录后续。 *)

(*
   本节说明 Transformation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Transform := {
  transform {x} : F x ~> G x;             (* the component at each object x *)

  (* naturality square: `G f ∘ η_x ≈ η_y ∘ F f` *)
  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  (* the symmetric orientation 自然性 square (built-in dual) （已译） *)
  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
  }.

(*
   本节说明 Transformation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(* The identity natural transformation `id_F : F ⟹ F`. Its component at `X` is
   `id_{F X}`, written here as `fmap[F] id` (equal to `id` by `fmap_id`). *)

Program Definition nat_id `{F : C ⟶ D} : F ⟹ F := {|
  transform := λ X, fmap (@id C X)
|}.

#[export] Hint Unfold nat_id : core.

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
