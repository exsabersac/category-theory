Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   A functor F : C ⟶ D assigns to each object x : C an object F x : D and to
   each morphism f : x ~> y a morphism fmap f : F x ~> F y, subject to the two
   functoriality laws fmap id ≈ id (fmap_id) and fmap (f ∘ g) ≈ fmap f ∘ fmap g
   (fmap_comp). Because hom-sets here are setoids, the morphism mapping must
   also respect ≈ (fmap_respects); the equational laws above use ≈ rather than
   = throughout. Functoriality forces functors to preserve isomorphisms (see
   [fobj_iso] below).

   Note that there are many species of functor, one each for the various
   categorical structures (included below), for example, the `CartesianFunctor`
   that maps products to products and preserves all its structural properties
   and laws.

--------
nLab: https://ncatlab.org/nlab/show/functor
   维基百科: https://en.wikipedia.org/wiki/Functor

   函子 F : C ⟶ D 将每个对象 x : C 映射到对象 F x : D，并将每个态射 f : x ~> y 映射到态射 fmap f : F x ~> F y，同时满足两个函子律 fmap id ≈ id (fmap_id) 和 fmap (f ∘ g) ≈ fmap f ∘ fmap g (fmap_comp)。因为这里的同态集合是集合同构（setoids），态射映射也必须尊重 ≈ (fmap_respects)；上述等式律全部使用 ≈ 而非 =。函子律迫使函子保持同构（参见下文 [fobj_iso]）。

   注意，函子有许多种类，每种对应不同的范畴结构（如下所示），例如将积映射到积并保持所有结构性质和律的 `CartesianFunctor`。
*)

(*
Where functors come from, and what they are for

   SEP:  https://plato.stanford.edu/entries/category-theory/
   nLab: https://ncatlab.org/nlab/show/General+Theory+of+Natural+Equivalences

   Functors are the founding notion of category theory, not a derived one.
   Categories, functors, and natural transformations entered mathematics
   together in (Eilenberg, Mac Lane, "General theory of natural
   equivalences", Transactions of the American Mathematical Society 58,
   1945) — the paper the nLab page above calls the foundational document of
   category theory — distilled from the group-level computations of their
   "Group Extensions and Homology" (Annals of Mathematics, 1942).  The
   authors were explicit about the order of ideas: "the whole concept of a
   category is essentially an auxiliary one" (quoted in the SEP entry
   above), the basic concepts being those of functor and natural
   transformation.  Categories exist so that functors have domains and
   codomains, and functors exist so that naturality can be stated.  The
   word itself was borrowed from Rudolf Carnap, who had used it for a
   linguistic notion in The Logical Syntax of Language (1937), as recorded
   in Mac Lane, Categories for the Working Mathematician (Springer, 1971),
   p. 30.

   A functor is the homomorphism notion for categories — the nLab frames it
   as a horizontal categorification of the homomorphism concept — and its
   purpose is double-sided.  Read outward, a functor transports whole
   situations from one mathematical world to another, homology carrying
   spaces to groups being the founding example; it follows from the iso
   preservation recorded in [fobj_iso] that an invariant packaged as a
   functor can never distinguish isomorphic objects.  Read inward, a
   functor INTO a category is a diagram: a diagram of type J in C is a
   covariant functor from J to C (Wikipedia, "Functor"), and
   Structure/Limit.v takes exactly such an F : J ⟶ C as the shape over
   which limits are formed.  Because [Compose] is associative with [Id] as
   unit up to the natural isomorphisms of [Functor_Setoid]
   ([fun_equiv_id_left], [fun_equiv_id_right], [fun_equiv_comp_assoc]),
   categories themselves assemble into the category Cat of Instance/Cat.v,
   whose morphisms are this file's functors; the same functors are the
   objects of the functor categories of Instance/Fun.v, whose morphisms —
   natural transformations, Theory/Natural/Transformation.v — form the next
   rung of the ladder.

   The applications track both readings.  Contravariant functors to Sets
   are presheaves (nLab), of which the hom-functors of Functor/Hom.v and
   the Yoneda embedding built from them are the canonical examples; a
   functor from a one-object category BG to vector spaces is precisely a
   linear representation of the group G (nLab); and Lawvere's functorial
   semantics recast universal algebra by taking a theory to be a category
   with finite products and a model to be a product-preserving functor out
   of it (Lawvere, "Functorial Semantics of Algebraic Theories", PhD
   thesis, Columbia University 1963; reprinted as TAC Reprints No. 5,
   2004), the perspective implemented over this file in
   Theory/Lawvere/Model.v.  The structure-preserving species the header
   advertises live under Functor/Structure/.

   The computational reading is genuine.  In typed functional programming
   the type constructor is the object map and fmap the morphism map, with
   the two laws left as the programmer's proof obligation, verified by
   equational reasoning (Milewski, "Functors", 2015); this file
   accordingly ships the Haskell spellings <$>, <$ and <&> as parsing-only
   notations, and Theory/Coq/Functor.v carries the fmap-only class of that
   tradition, its laws discharged per instance.  In Haskell the second law
   is redundant, derivable from the first together with the free theorem of
   the type of fmap, up to the usual caveat about bottom and seq
   (Luposchainsky, "The second functor law is redundant").  No such
   parametricity is available over arbitrary categories with setoid
   hom-sets, so here [fmap_comp] is a genuine obligation of the class, and
   a third law, [fmap_respects], appears that Haskell renders invisible.
   The same setoid design decides what functor equality means: not
   pointwise identity of objects but a natural isomorphism
   ([Functor_Setoid]), with a stricter transport-based alternative deferred
   to [Functor_StrictEq_Setoid] at the end of this file.

--------
函子从何而来，以及用途为何

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
   [Functor_StrictEq_Setoid]。
*)

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;                                (* action on objects / 对物体的动作 *)
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;  (* action on morphisms / 态射上的作用 *)

  fmap_respects : ∀ x y,                       (* fmap respects ≈ (setoid law) / fmap 遵守 ≈（等值律） *)
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;       (* functor law: preserves identities / 函子定律：保持恒等式 *)
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :  (* functor law: preserves composition / 函子定律：保持组合 *)
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

(*
Functors used as functions map objects of categories, similar to the way
   type constructors behave in Haskell. We cannot, unfortunately, have a
   similar coercion for morphisms, because coercions cannot be bound to
   scopes.

--------
用作函数的函子将范畴的对象映射，就像 Haskell 中的类型构造器的行为类似。不幸的是，我们无法对态射进行类似的强制转换，因为强制转换不能绑定到作用域。
*)
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
Note that it doesn't make much sense (with our definition of [Category])
     to ask that [∀ x : C, F x = G x] and
     [∀ (x y :C) (f : x ~> y), fmap[F] f ≈ fmap[G] f] because the second
     condition is hard to work with in the type-system since it needs lots of
     equality proofs.

--------
请注意，根据我们对 [Category] 的定义，要求 [∀ x : C, F x = G x] 和 [∀ (x y :C) (f : x ~> y), fmap[F] f ≈ fmap[G] f 并没有太大意义，因为第二个条件在类型系统中很难处理，因为它需要大量的等式证明。
*)
  equiv := fun F G =>
    (*
Equality of objects in a category is taken to be a natural
       isomorphism

--------
范畴中对象的等价被认为是自然同构
*)
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

(*
The identity functor Id[C] maps every object and morphism to itself; it is
   the unit for functor composition (see fun_equiv_id_left/right below).

--------
((()))通过关于抉择 I 没有将每个对象和 怎么形态很有可能
做出的承诺者构成为其纲的单位 没错,请参见 fun 的第一次报告。 你是不是在为弄清i units
*)
Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Arguments Id {C} /.

Notation "Id[ C ]" := (@Id C) (at level 0, format "Id[ C ]") : functor_scope.

(*
Composition of functors F ◯ G applies G then F on both objects and
   morphisms. It is associative with Id as unit, making Cat a category.

--------
函子 F ◯ G 的复合在对象和态射上先应用 G 再应用 F。它是结合的，以 Id 作为单位，使 Cat 成为一个范畴。
*)
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

   F is full when each hom-map fmap[F] : (x ~> y) → (F x ~> F y) is surjective.
   Constructively this is witnessed by a section [prefmap] of [fmap[F]]: a
   choice of preimage with fmap[F] (prefmap g) ≈ g ([fmap_sur]), rather than by
   a bare surjectivity proposition. No functoriality is demanded of [prefmap]
   itself — it need not respect ≈ nor preserve identities/composition; only that
   it lands in a genuine preimage. This matches the standard meaning of fullness
   (cf. issue #118); the previous definition's [prefmap_respects], [prefmap_id]
   and [prefmap_comp] fields were extraneous.

--------
nLab: https://ncatlab.org/nlab/show/full+functor
   维基百科: https://en.wikipedia.org/wiki/Full_functor

   当每个同态映射 fmap[F] : (x ~> y) → (F x ~> F y) 是满射时，F 是满的。
   在构造上，这由 [fmap[F] 的一个截面 [prefmap] 体现：
   选择一个原像，使得 fmap[F](prefmap g) ≈ g ([fmap_sur])，而不是仅仅通过一个裸的满射命题来证明。[prefmap] 本身不要求具有函子性 — 它不必尊重 ≈ 也不必保持恒等映射/复合；只要求它落在一个真正的原像上。这与满性的标准含义一致（参见 issue #118）；之前定义中的 [prefmap_respects]、[prefmap_id] 和 [prefmap_comp] 字段是多余的。
*)
Class Full `(F : C ⟶ D) := {
  prefmap {x y} (g : F x ~> F y) : x ~> y;     (* chosen preimage of g under fmap / 在 fmap 下 g 的选定原像 *)

  fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g  (* prefmap is a section of fmap / prefmap 是 fmap 的一个部分 *)
}.

(*
nLab: https://ncatlab.org/nlab/show/faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Faithful_functor

   F is faithful when each hom-map fmap[F] : (x ~> y) → (F x ~> F y) is
   injective.

--------
nLab：https://ncatlab.org/nlab/show/faithful+functor
   维基百科：https://en.wikipedia.org/wiki/Faithful_functor

   当每个同态映射 fmap[F] : (x ~> y) → (F x ~> F y) 是单射时，F 是忠实的。
*)
Class Faithful `(F : C ⟶ D) := {
  fmap_inj {x y} (f g : x ~> y) : fmap[F] f ≈ fmap[F] g → f ≈ g  (* injectivity of fmap[F] / fmap[F] 的单射性 *)
}.

(*
nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_and_faithful_functors

   A fully faithful functor (both Full and Faithful) reflects isomorphisms: if
   F x ≅ F y then x ≅ y. The witnesses are [prefmap] applied to the given iso;
   the inverse laws are discharged by faithfulness ([fmap_inj]), which reduces
   each to the corresponding law of the image iso after pushing [fmap] through
   composition ([fmap_comp]) and cancelling the sections ([fmap_sur]). Fullness
   alone no longer needs to be functorial.

--------
nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
   Wikipedia: https://en.wikipedia.org/wiki/Full_and_faithful_functors

   一个完全忠实的函子（既全又忠实）会反映同构：如果
   F x ≅ F y，那么 x ≅ y。见证由对给定同构应用 [prefmap] 得出；
   逆律由忠实性（[fmap_inj]）处理，这将每个逆律化简为通过组合推送 [fmap] 后对应像同构的律（[fmap_comp]）并消去截面（[fmap_sur]）。仅全性不再需要函子性质。
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
Fullness and faithfulness are LOCAL conditions, and both are closed under
   composition of functors.

   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5, Remark 1.5.8,
         printed p. 33, and Exercise 1.5.vi(i), printed p. 38
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed., GTM 5,
         Springer 1998, §I.3, printed pp. 14-15

   Riehl's Remark 1.5.8 stresses that neither condition is a global statement
   about the whole collection of morphisms: a faithful functor need not be
   injective on morphisms overall, and a full functor need not be surjective
   on morphisms overall.  That locality is definitional in the two classes
   just above — [fmap_inj] quantifies its two morphisms over a COMMON pair
   (x, y), and [prefmap] is only ever handed an arrow whose endpoints are
   already of the form (F x, F y).

   Exercise 1.5.vi(i) asks for the two closure properties below.  Note that
   [Full] here is the split, choice-carrying form, so [Full_Compose] must
   actually compose the two chosen sections; under a bare surjectivity
   proposition it would instead be a chain of two existential eliminations.
   The exercise's third clause, closure of essential surjectivity, is
   [EssentiallySurjective_Compose] in Theory/Equivalence.v, where that class
   is defined; its part (ii), transitivity of equivalence of categories, was
   already in the library as [Equivalence_trans]
   (Theory/Equivalence/Bundled.v).

--------
充实性和忠实性是局部条件，并且在函子复合下都是封闭的。

书籍：Riehl，《情境中的范畴论》，Dover 2016，第1.5节，注释1.5.8，第33页印刷，以及练习1.5.vi(i)，第38页印刷。
书籍：Mac Lane，《工作数学家的范畴》，第2版，GTM 5，Springer 1998，第I.3节，第14-15页印刷。

Riehl 的备注 1.5.8 强调，这两个条件都不是关于整个态射集合的全局陈述：一个忠实函子总体上不必在态射上是单射的，而一个满函子总体上不必在态射上是满射的。这种局部性在上面的两个类中是定义性的——[fmap_inj] 在共同的 (x, y) 对上量化它的两个态射，而 [prefmap] 仅仅被赋予一个其端点已经是 (F x, F y) 形式的箭头。

练习 1.5.vi(i) 要求下面的两个闭包性质。注意，这里的 [Full] 是拆分的、带选择的形式，因此 [Full_Compose] 必须实际组合两个选定的部分；在一个单纯的满射命题下，它将会是两个存在消去的链。练习的第三条款，即本质满射的闭包性，是在 Theory/Equivalence.v 中定义该类的 [EssentiallySurjective_Compose]；其第 (ii) 部分，即范畴等价的传递性，已经在库中作为 [Equivalence_trans]（Theory/Equivalence/Bundled.v）。
*)

#[export] Program Instance Full_Compose {C D E : Category}
  (F : D ⟶ E) (G : C ⟶ D) `{@Full _ _ F} `{@Full _ _ G} : Full (F ◯ G) := {|
  prefmap := fun _ _ g => prefmap (F:=G) (prefmap (F:=F) g)  (* G's after F's / F 之后的 G *)
|}.
Next Obligation.
  (*
The goal is fmap[F] (fmap[G] (prefmap (prefmap g))) ≈ g.  Cancel G's
     section underneath fmap[F] — legitimate because [fmap_respects] makes
     fmap[F] a setoid morphism — and then F's.

--------
目标是 fmap[F] (fmap[G] (prefmap (prefmap g))) ≈ g。取消 G 在 fmap[F] 下的部分——这是合法的，因为 [fmap_respects] 使 fmap[F] 成为集合同态——然后取消 F 的部分。
*)
  rewrite fmap_sur.
  apply fmap_sur.
Qed.

#[export] Instance Faithful_Compose {C D E : Category}
  (F : D ⟶ E) (G : C ⟶ D) `{@Faithful _ _ F} `{@Faithful _ _ G} :
  Faithful (F ◯ G).
Proof.
  constructor; intros x y f g Hfg.
  (*
fmap[F ◯ G] h is fmap[F] (fmap[G] h) definitionally, so the hypothesis
     is already F's injectivity premise at the pair (G x, G y).

--------
fmap[F ◯ G] h 在定义上等于 fmap[F] (fmap[G] h)，所以该假设已经是 F 在对 (G x, G y) 上的单射前提。
*)
  apply (fmap_inj (F:=G)).
  apply (fmap_inj (F:=F)).
  exact Hfg.
Qed.

(*
nLab: https://ncatlab.org/nlab/show/faithful+functor
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed., GTM 5,
         Springer 1998, §I.5, Exercise 9, printed p. 21
   Book: Riehl, "Category Theory in Context", Dover 2016, §1.6,
         Exercise 1.6.iv, printed p. 47

   A faithful functor REFLECTS monomorphisms: if the image fmap[F] f is left-
   cancellable in D, then f was already left-cancellable in C.  Given a pair
   g1, g2 with f ∘ g1 ≈ f ∘ g2, push it through F ([fmap_comp]) to cancel
   fmap[F] f, then pull the resulting fmap[F] g1 ≈ fmap[F] g2 back through
   injectivity ([fmap_inj]).  Each hypothesis is used at exactly one step of
   that proof: monicity of the image performs the cancellation, faithfulness
   transports the cancelled equation from D back to C.

   [Monic] and [Epic] are the left- and right-cancellation classes of
   Theory/Morphisms.v (imported at the head of this file for these two
   lemmas).  Neither of the two nearest in-tree results says this:
   Theory/Adjunction.v's [adj_monic] concerns the ADJUNCT of a monic under a
   faithfulness hypothesis, and Theory/Equivalence/FullFaithful.v cancels
   isomorphism-induced monos and epis.

--------
nLab: https://ncatlab.org/nlab/show/faithful+functor
书籍: Mac Lane，《为工作数学家准备的范畴论》，第2版，GTM 5，
      Springer 1998，第I.5节，练习9，印刷页21
书籍: Riehl，《上下文中的范畴论》，Dover 2016，第1.6节，
      练习1.6.iv，印刷页47

一个忠实函子会反映单态：如果像 fmap[F] f 在 D 中是左可消的，那么 f 在 C 中已经是左可消的。给定一对 g1, g2 满足 f ∘ g1 ≈ f ∘ g2，通过 F ([fmap_comp]) 推送它以消去 fmap[F] f，然后将结果 fmap[F] g1 ≈ fmap[F] g2 通过单射性 ([fmap_inj]) 拉回。每个假设在该证明的恰好一个步骤中被使用：像的单态性执行了消去操作，忠实性将消去后的方程从 D 传回 C。

[Monic] 和 [Epic] 是 Theory/Morphisms.v 的左消去和右消去类（在本文件开头导入了该文件以使用这两个引理）。在树中最近的两个结果都没有说明这一点：Theory/Adjunction.v 的 [adj_monic] 涉及在忠实性假设下单射的伴随，Theory/Equivalence/FullFaithful.v 则消去了由同构引起的单射和满射。
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
The dual, right-cancellation reading of the same argument.  It is proved
   directly, by mirroring the proof above, rather than transported across
   C^op: the opposite-category apparatus lives in Construction/Opposite.v and
   the opposite of a functor in Functor/Opposite.v's [Opposite_Functor], both
   later layers than this core file, and the direct proof is short.

--------
同一论证的双重右消去读法。它是直接证明的，通过反映上述证明，而不是通过跨越 C^op 进行传递：对偶范畴装置位于 Construction/Opposite.v 中，而函子对偶位于 Functor/Opposite.v 的 [Opposite_Functor] 中，这两个都比这个核心文件的层级更高，而且直接证明很简短。
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

   For an endofunctor F : C ⟶ C, an F-algebra on a carrier object a is a
   structure morphism F a ~> a; the dual F-coalgebra is a ~> F a. The
   (F, G)-dialgebra generalizes both to a morphism F a ~> G a between the
   images of two endofunctors. Here these definitions name only the carrying
   morphism type, not the full category of algebras.

--------
nLab: https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
   维基百科: https://en.wikipedia.org/wiki/F-algebra

   对于一个端函子 F : C ⟶ C，一个载体对象 a 上的 F-代数是一个结构态射 F a ~> a；对偶 F-余代数是 a ~> F a。
(F, G)-双代数将两者推广为一个在两个端函子映射之间的态射 F a ~> G a。
这里这些定义仅命名了载体态射的类型，而不是代数的完整范畴。
*)
Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

Definition FCoalgebra `(F : C ⟶ C) (a : C) := a ~> F a.

Definition FGDialgebra `(F : C ⟶ C) `(G : C ⟶ C) (a : C) := F a ~> G a.

Section AFunctor.

Context {C D : Category}.

(* [AFunctor] allows the object mapping to be stated explicitly. / [AFunctor] 允许显式地声明对象映射。 *)
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
An alternative setoid of functors that uses strict (propositional) equality
   of objects, F x = G x, rather than the natural isomorphism F x ≅ G x of
   [Functor_Setoid]. Because objects equal only up to = require transporting
   morphisms along those equalities, this section first develops the transport
   lemmas needed to state and prove the morphism-coherence condition
   ([Functor_StrictEq_Setoid]). This notion is stricter than [Functor_Setoid]
   and is provided for settings where object equality is available.

--------
另一种函子集的选择，它使用对象的严格（命题性）相等 F x = G x，而不是 [Functor_Setoid] 中的自然同构 F x ≅ G x。由于对象仅在 = 下相等，因此需要沿这些相等性传递态射，本节首先发展了陈述和证明态射相干条件（[Functor_StrictEq_Setoid]）所需的传递引理。这个概念比 [Functor_Setoid] 更严格，并且提供给可以使用对象相等的场景。
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

(* Global Instance proper_transport_hom_cod (C : Category) (c d d': C) (p : d = d') / 全局实例 proper_transport_hom_cod (C : 范畴) (c d d': C) (p : d = d')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom c z) p). / : 合适的 (equiv ==> equiv) (传输 (函数 z => hom c z) p)。 *)
(* Proof. / 证据。 *)
(*   destruct p. now trivial. / 现在拆解 p，就很显然。 *)
(* Defined. / 已定义。 *)

(* Global Instance proper_transport_hom_dom (C : Category) (c c' d: C) (p : c = c') / 全局实例 proper_transport_hom_dom (C : 范畴) (c c' d: C) (p : c = c')  *)
(*   : Proper (equiv ==> equiv) (transport (fun z => hom z d) p). / : 合适的 (equiv ==> equiv) (传输 (函数 z => 同态 z d) p)。 *)
(* Proof. / 证据。 *)
(*   destruct p. now trivial. / 现在拆解 p，就很显然。 *)
(* Defined. / 已定义。 *)

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

