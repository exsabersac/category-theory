Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(* 函子从何而来，以及用途为何

   SEP:  https://plato.stanford.edu/entries/category-theory/
   nLab: https://ncatlab.org/nlab/show/General+Theory+of+Natural+Equivalences

   函子是范畴论的创始概念，而非派生概念。范畴、函子与自然变换一同进入数学，
   见于（Eilenberg, Mac Lane, "General theory of natural equivalences",
   Transactions of the American Mathematical Society 58, 1945）——nLab 上页
   称为范畴论奠基文献——提炼自他们 "Group Extensions and Homology"
   （Annals of Mathematics, 1942）在群层级的计算。作者对观念顺序很明确：
   「范畴的整个概念本质上是辅助性的」（SEP 条目引述），基本概念是函子与
   自然变换。范畴存在是为了让函子有定义域与陪域，函子存在是为了能陈述自然性。
   词本身借自 Rudolf Carnap，他在 The Logical Syntax of Language (1937) 中
   用于语言学概念，Mac Lane《Categories for the Working Mathematician》
   （Springer, 1971）第 30 页有记载。

   函子是范畴的同态概念——nLab 将其框为同态概念的水平范畴化——其目的是双面的。
   向外读，函子把整个局面从一数学世界运到另一世界，同调把空间带到群是创始例子；
   由 [fobj_iso] 记录的同构保持可知，封装为函子的不变量永远无法区分同构对象。
   向内读，进入某范畴的函子是图：C 中类型为 J 的图是从 J 到 C 的共变函子
   （Wikipedia, "Functor"），Structure/Limit.v 正取这样的 F : J ⟶ C 作为形成极限的形状。
   因 [Compose] 以 [Id] 为单位至多在 [Functor_Setoid] 的自然同构下结合
   （[fun_equiv_id_left]、[fun_equiv_id_right]、[fun_equiv_comp_assoc]），
   范畴自身组装成 Instance/Cat.v 的范畴 Cat，函子是其态射。本文件是该组装的定义层。

   应用跟踪两种读法。到 Sets 的反变函子是预层（nLab），其中 Functor/Hom.v 的
   hom 函子及由其建造的 Yoneda 嵌入是典范例子；从单对象范畴 BG 到向量空间的函子
   恰是群 G 的线性表示（nLab）；Lawvere 的函子语义通过把理论取为有限积范畴、
   把模型取为出之的保积函子来重铸泛代数（Lawvere, "Functorial Semantics of
   Algebraic Theories", PhD thesis, Columbia 1963; TAC Reprints No. 5, 2004），
   该视角在 Theory/Lawvere/Model.v 中基于本文件实现。文首所宣传的保结构「种」
   住在 Functor/Structure/ 下。

   计算读法是真实的。在带类型函数式编程中，类型构造子是对象映射、fmap 是态射映射，
   两条定律留给程序员的证明义务，由等词推理验证（Milewski, "Functors", 2015）；
   本文件因此附带仅解析用的 Haskell 拼写 <$>、<\$ 与 <&>，Theory/Coq/Functor.v
   承载该传统的仅 fmap 类，定律按实例消解。在 Haskell 中第二定律冗余，可由第一定律
   与 fmap 类型的 free theorem 导出（通常需对 bottom 与 seq 谨慎；Luposchainsky,
   "The second functor law is redundant"）。在带 setoid hom 集的任意范畴上无此参数性，
   故此处 [fmap_comp] 是类的真正义务，并出现 Haskell 使之不可见的第三定律 [fmap_respects]。
   同一 setoid 设计决定函子相等意味着什么：不是对象的逐点恒等，而是自然同构
   （[Functor_Setoid]）；更严格的基于 transport 的替代留到本文件末尾的
   [Functor_StrictEq_Setoid]。 *)

(*
   关于函子的来源与用途

   SEP:  https://plato.stanford.edu/entries/category-theory/
   nLab: https://ncatlab.org/nlab/show/General+Theory+of+Natural+Equivalences

   本节说明自然变换、函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;                                (* action on objects *)
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;  (* action on morphisms *)

  fmap_respects : ∀ x y,                       (* fmap respects ≈ (setoid law) *)
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;       (* functor law: preserves identities *)
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :  (* functor law: preserves composition *)
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
#[export] Existing Instance fmap_respects.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(* Functors used as functions map objects of categories, similar to the way
   type constructors behave in Haskell. We cannot, unfortunately, have a
   similar coercion for morphisms, because coercions cannot be bound to
   scopes. *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap
  {C%_category D%_category Functor%_functor x%_object y%_object} f%_morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 0, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 0, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

#[export]
Program Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D) := {
  (*
   本节说明 Functor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  equiv := fun F G =>
    (* Equality of objects in a category is taken to be a natural
       isomorphism *)
    { iso : ∀ x : C, F x ≅ G x
    & ∀ (x y : C) (f : x ~> y),
        fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x) }
}.
Next Obligation.
  equivalence.
  - isomorphism.
    + exact (from (x0 x1)).
    + exact (to (x0 x1)).
    + apply iso_from_to.
    + apply iso_to_from.
  - simpl.
    rewrite e.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - isomorphism.
    + apply (to (x0 x2) ∘ to (x1 x2)).
    + apply (from (x1 x2) ∘ from (x0 x2)).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x1 x2)).
      rewrite iso_to_from, id_left.
      apply iso_to_from.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x0 x2)⁻¹).
      rewrite iso_from_to, id_left.
      apply iso_from_to.
  - simpl.
    rewrite !comp_assoc.
    rewrite <- (comp_assoc _ (x0 y0)⁻¹).
    rewrite <- (comp_assoc _ ((x0 y0)⁻¹ ∘ _)).
    rewrite <- e.
    apply e0.
Qed.

Lemma fun_equiv_to_fmap {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    to (``eqv y) ∘ fmap[F] f ≈ fmap[G] f ∘ to (``eqv x).
Proof.
  intros.
  rewrite <- id_right.
  rewrite ((`2 eqv) _ _).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Lemma fun_equiv_fmap_from {C D : Category} {F G : C ⟶ D} (eqv : F ≈ G) :
  ∀ (x y : C) (f : x ~> y),
    fmap[F] f ∘ from (``eqv x) ≈ from (``eqv y) ∘ fmap[G] f.
Proof.
  intros.
  rewrite <- id_left.
  rewrite ((`2 eqv) _ _).
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now cat.
Qed.

Ltac constructive :=
  simpl;
  match goal with
    [ |- { iso : ?I & ?F } ] =>
    given (iso : I); [ intros; isomorphism; simpl; intros
                     | exists iso; intros ]
  end.

#[export]
Program Instance fobj_iso `(F : C ⟶ D) :
  Proper (Isomorphism ==> Isomorphism) (fobj[F]).
Next Obligation.
  proper.
  refine {| to   := fmap[F] (to X)
          ; from := fmap (from X) |}.
  - rewrite <- fmap_comp.
    rewrite iso_to_from; cat.
  - rewrite <- fmap_comp.
    rewrite iso_from_to; cat.
Defined.

#[export]
Instance fobj_respects `(F : C ⟶ D) :
  Proper (equiv ==> equiv) (@fobj C D F) := @fobj_iso C D F.

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

(*((()))通过关于抉择 I 没有将每个对象和 怎么形态很有可能
做出的承诺者构成为其纲的单位 没错,请参见 fun 的第一次报告。 你是不是在为弄清i units*)
Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 0, format "Id[ C ]") : functor_scope.

(* 函子复合 F ◯ G：先 G 后 F，作用于对象与态射；结合且以恒等为两侧单位。（已译） *)
Program Definition Compose {C D E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. intros; rewrite !fmap_comp; reflexivity. Qed.

#[export] Hint Unfold Compose : categories.

Notation "F ◯ G" := (Compose F%functor G%functor)
  (at level 40, left associativity) : category_scope.

#[export]
Program Instance Compose_respects {C D E : Category} :
  Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
Next Obligation.
  proper.
  - isomorphism; simpl; intros.
    + exact (fmap (to (x1 x3)) ∘ to (x2 (x0 x3))).
    + exact (from (x2 (x0 x3)) ∘ fmap (from (x1 x3))).
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (x2 (x0 x3))).
      rewrite iso_to_from, id_left.
      rewrite <- fmap_comp.
      rewrite iso_to_from; cat.
    + rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap _)).
      rewrite <- fmap_comp.
      rewrite iso_from_to, fmap_id, id_left.
      rewrite iso_from_to; cat.
  - simpl.
    rewrite e0, e.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite (comp_assoc (fmap _)).
    rewrite <- fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
Qed.

Corollary fobj_Compose `(F : D ⟶ E) `(G : C ⟶ D) {x} :
  fobj[F ◯ G] x = fobj[F] (fobj[G] x).
Proof. reflexivity. Defined.

Lemma fun_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_right {A B} F.

Lemma fun_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
Proof. construct; cat. Qed.

Arguments fun_equiv_id_left {A B} F.

Lemma fun_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
  F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
Proof. construct; cat. Qed.

Arguments fun_equiv_comp_assoc {A B C D} F G H.

(*
   nLab: https://ncatlab.org/nlab/show/full+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_functor

   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Full `(F : C ⟶ D) := {
  prefmap {x y} (g : F x ~> F y) : x ~> y;     (* chosen preimage of g under fmap *)

  fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g  (* prefmap is a section of fmap *)
}.

(* nLab: https://ncatlab.org/nlab/show/faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Faithful_functor

   F is faithful when each hom-map fmap[F] : (x ~> y) → (F x ~> F y) is
   injective. *)
Class Faithful `(F : C ⟶ D) := {
  fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g → f ≈ g  (* injectivity of fmap[F] *)
}.

(*
   nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_and_faithful_functors

   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma FullyFaithful `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y.
Proof.
  intros.
  construct.
  + apply prefmap, X.
  + apply prefmap, X.
  + abstract
      (apply fmap_inj;
       rewrite fmap_comp, !fmap_sur, fmap_id;
       apply iso_to_from).
  + abstract
      (apply fmap_inj;
       rewrite fmap_comp, !fmap_sur, fmap_id;
       apply iso_from_to).
Defined.

(*
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5, Remark 1.5.8,
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed., GTM 5,

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance Full_Compose {C D E : Category}
  (F : D ⟶ E) (G : C ⟶ D) `{@Full _ _ F} `{@Full _ _ G} : Full (F ◯ G) := {|
  prefmap := fun _ _ g => prefmap (F:=G) (prefmap (F:=F) g)  (* G's after F's *)
|}.
Next Obligation.
  (* 目标为 fmap[F] (fmap[G] (prefmap (prefmap g))) ≈ g；消去 G 在 fmap 下的截面对应。（已译） *)
  rewrite fmap_sur.
  apply fmap_sur.
Qed.

#[export] Instance Faithful_Compose {C D E : Category}
  (F : D ⟶ E) (G : C ⟶ D) `{@Faithful _ _ F} `{@Faithful _ _ G} :
  Faithful (F ◯ G).
Proof.
  constructor; intros x y f g Hfg.
  (* fmap[F ◯ G] h 定义上即 fmap[F] (fmap[G] h)，故假设已是 F 的单性形式。（已译） *)
  apply (fmap_inj (F:=G)).
  apply (fmap_inj (F:=F)).
  exact Hfg.
Qed.

(*
   nLab: https://ncatlab.org/nlab/show/faithful+functor
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed., GTM 5,
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.6,

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma faithful_reflects_monic `(F : C ⟶ D) `{@Faithful _ _ F}
      {x y : C} (f : x ~> y) : Morphisms.Monic (fmap[F] f) → Morphisms.Monic f.
Proof.
  intros [Hmonic].
  constructor; intros z g1 g2 Hg.
  apply (fmap_inj (F:=F)).
  apply (Hmonic (F z)).
  rewrite <- !fmap_comp.
  now rewrite Hg.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma faithful_reflects_epic `(F : C ⟶ D) `{@Faithful _ _ F}
      {x y : C} (f : x ~> y) : Morphisms.Epic (fmap[F] f) → Morphisms.Epic f.
Proof.
  intros [Hepic].
  constructor; intros z g1 g2 Hg.
  apply (fmap_inj (F:=F)).
  apply (Hepic (F z)).
  rewrite <- !fmap_comp.
  now rewrite Hg.
Qed.

(*
   nLab: https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/F-algebra

   本节说明 Functor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

Definition FCoalgebra `(F : C ⟶ C) (a : C) := a ~> F a.

Definition FGDialgebra `(F : C ⟶ C) `(G : C ⟶ C) (a : C) := F a ~> G a.

Section AFunctor.

Context {C D : Category}.

(* [AFunctor] allows the object mapping to be stated explicitly. *)
Class AFunctor (F : C → D) : Type := {
  a_fmap {x y : C} (f : x ~> y) : F x ~> F y;

  a_fmap_respects {x y : C} : Proper (equiv ==> equiv) (@a_fmap x y);

  a_fmap_id {x : C} : a_fmap (@id C x) ≈ id;
  a_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    a_fmap (f ∘ g) ≈ a_fmap f ∘ a_fmap g;
}.
#[export] Existing Instance a_fmap_respects.

Definition FromAFunctor `(AFunctor F) : C ⟶ D := {|
  fobj          := λ x, F x;
  fmap          := @a_fmap F _;
  fmap_respects := @a_fmap_respects F _;
  fmap_id       := @a_fmap_id F _;
  fmap_comp     := @a_fmap_comp F _;
|}.

Coercion FromAFunctor : AFunctor >-> Functor.

Definition ToAFunctor (F : C ⟶ D) : AFunctor F := {|
  a_fmap          := @fmap _ _ F;
  a_fmap_respects := @fmap_respects _ _ F;
  a_fmap_id       := @fmap_id _ _ F;
  a_fmap_comp     := @fmap_comp _ _ F;
|}.

Corollary FromAFunctor_ToAFunctor {F} :
  FromAFunctor (ToAFunctor F) = F.
Proof. reflexivity. Qed.

Corollary ToAFunctor_FromAFunctor `{H : AFunctor F} :
  ToAFunctor (FromAFunctor H) = H.
Proof. reflexivity. Qed.

End AFunctor.

(*
   本节说明函子、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section StrictEq.
 Lemma transport_adjunction (A : Type) (B : A -> Type) (R: forall a :A, crelation (B a)) :
   forall (a a' : A) (p : a = a') (x : B a) (y : B a'),
    ((R _ x (transport_r B p y) -> R _ (transport B p x) y)) *
      (R _ (transport B p x) y -> (R _ x (transport_r B p y))).
  intros a a' p x y. split.
  - destruct p. now unfold transport_r.
  - destruct p. now unfold transport_r.
Defined.

Lemma transport_relation_exchange (A : Type) (R : crelation A) :
  forall (a a' b b': A) (p : a = b) (q : a' = b') (t : R a a'),
    transport (fun z => R b z) q
      (transport (fun k => R k a') p t) =
      transport (fun k => R k b') p
        (transport (fun z => R a z) q t).
Proof.
  intros a a' b b' p q t; destruct p, q; reflexivity.
Defined.

Lemma transport_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a0) (p : a0 = a1) (q : a1 = a2),
    transport B q (transport B p x) = transport B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Lemma transport_r_trans (A : Type) (B : A -> Type) :
  forall (a0 a1 a2 : A) (x : B a2) (p : a0 = a1) (q : a1 = a2),
    transport_r B p (transport_r B q x) = transport_r B (eq_trans p q) x.
Proof.
  intros a0 a1 a2 x p q; destruct p, q; reflexivity.
Defined.

Global Instance proper_transport (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport B p).
Proof.
  intros a b p. destruct p. now unfold transport.
Defined.

Global Instance proper_transport_r (A : Type) (B : A -> Type) (S : forall a : A, Setoid (B a)) :
  forall (a a' : A) (p : a = a'), Proper (equiv ==> equiv) (transport_r B p).
Proof.
  intros a b p. destruct p. now (unfold transport_r).
Defined.

(* Global Instance proper_transport_hom_cod (C : Category) (c d d': C) (p : d = d')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom c z) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

(* Global Instance proper_transport_hom_dom (C : Category) (c c' d: C) (p : c = c')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom z d) p). *)
(* Proof. *)
(*   destruct p. now trivial. *)
(* Defined. *)

#[export] Instance proper_transport_dom (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c c' d : A) (p : c = c') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B z d) p).
Proof.
  destruct p. now trivial.
Defined.

#[export] Instance proper_transport_cod (A: Type) (B : A -> A -> Type)
  (S : forall i j, Setoid (B i j)) (c d d' : A) (p : d = d') :
  Proper (equiv ==> equiv) (Logic.transport (fun z => B c z) p).
Proof.
  destruct p. now trivial.
Defined.

Program Instance Functor_StrictEq_Setoid {C D : Category} : Setoid (C ⟶ D) := {
    equiv := fun F G =>
      { eq_on_obj : ∀ x : C, F x = G x
                  & ∀ (x y : C) (f : x ~> y),
            transport (fun z => hom (fobj[ F ] x) z) (eq_on_obj y) (fmap[F] f) ≈
                   (transport_r (fun z => hom z (fobj[G] y)) (eq_on_obj x) (fmap[G] f)) }
}.
Next Obligation.
  equivalence.
  - unfold transport_r. rewrite eq_sym_involutive.
    fold (transport_r (λ z : obj[D], fobj[y] x1 ~{ D }~> z) (x0 y0)).
    symmetry.
    rename x into F, y into G, x0 into eq_ob, x1 into x, y0 into y.
    refine ((snd
               (transport_adjunction D (hom (fobj[G] x))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    rewrite transport_relation_exchange.
    refine ((fst
               (transport_adjunction D (fun d' => hom d' (fobj[G] y))
                  (fun d t s => t ≈ s) _ _ _ _ _)) _).
    exact (e _ _ _).
  - exact(eq_trans (x1 x2) (x0 x2)).
  - rename x into F, y into G, z into H, x1 into F_eq_ob_G,
      e0 into F_eq_ob_G_resp_mor, x0 into G_eq_ob_H,
      e into G_eq_ob_H_resp_mor, x2 into domf, y0 into codf.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite F_eq_ob_G_resp_mor.
    unfold transport_r at 1 2. rewrite transport_relation_exchange.
    apply proper_transport_dom.
    apply G_eq_ob_H_resp_mor.
Defined.

Lemma transport_f_equal (A B : Type) (C : B -> Type) (f : A -> B)
  (x y : A) (p : x = y) (t : C (f x))
  : transport (fun a => C (f a)) p t = transport (fun b => C b) (f_equal f p) t.
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_dom (C D: Category) (F : @Functor C D) (c c' d : C)
  (p : c = c') (f : hom c d)
  : fmap[F] (transport (fun z => hom z d) p f) =
      transport (fun z => hom z (fobj[F] d)) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

Lemma transport_functorial_cod (C D: Category) (F : @Functor C D) (c d d': C)
  (p : d = d') (f : hom c d)
  : fmap[F] (transport (fun z => hom c z) p f) =
      transport (fun z => hom (fobj[F] c) z) (f_equal (fobj[F]) p) (fmap[F] f).
Proof.
  destruct p. reflexivity.
Defined.

#[export]
 Program Instance Compose_respects_stricteq {C D E : Category} :
   Proper (equiv ==> equiv ==> equiv) (@Compose C D E).
 Next Obligation.
  intros F G [FG_eq_on_obj FG_morphismcoherence] H K [HK_eq_on_obj HK_morphismcoherence].
  unshelve eapply (_ ; _).
  - intro c; simpl.
      exact(eq_trans (f_equal (fobj[F]) (HK_eq_on_obj c)) (FG_eq_on_obj (fobj[K] c))).
  - intros c c' f.
    simpl.
    rewrite <- transport_trans, <- transport_r_trans.
    rewrite <- transport_functorial_cod.
    rewrite HK_morphismcoherence.
    unfold transport_r at 1 2.
    rewrite transport_functorial_dom.
    rewrite transport_relation_exchange.
    rewrite <- eq_sym_map_distr.
    apply proper_transport_dom.
    now trivial.
 Defined.

 Lemma fun_strict_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_id_right {A B} F.

 Lemma fun_strict_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_id_left {A B} F.

 Lemma fun_strict_equiv_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B)  :
   F ◯ (G ◯ H) ≈ (F ◯ G) ◯ H.
 Proof. construct; cat. Qed.

 Arguments fun_strict_equiv_comp_assoc {A B C D} F G H.

End StrictEq.

