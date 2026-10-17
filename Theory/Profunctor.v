Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Profunctors and representable profunctors. *)

(* nLab: https://ncatlab.org/nlab/show/profunctor
   Wikipedia: https://en.wikipedia.org/wiki/Profunctor

   从 C 到 D 的双函子 (profunctor)（也称 distributor 或 bimodule，写作 C ⇸ D）是函子

     C^op ∏ D ⟶ Sets,

   在第一变元反变、第二变元共变。它把对 (c, d) 送到「异态射」的 setoid P(c, d)，
   携带 C 的左作用与 D 的右作用（经复合）。因此处 hom 集是 setoid，双函子落在 setoid
   范畴 Sets。

   依本开发的绑定宇宙纪律，双函子保持为按对对象：C ⇸ D 的双函子是函子范畴
   [C^op ∏ D, Sets]（Instance/Fun.v）的对象，其态射是自然变换，对象等价 Prof_Setoid
   是自然同构（Functor_Setoid，Theory/Functor.v）。我们从不组装「所有范畴之间所有双函子」
   的单一范畴——那会抬高宇宙层级——故轻量双范畴式复合与连贯作为这些按对函子范畴中的
   引理存在（Construction/Profunctor 模块）。 *)

(* Where profunctors come from, and what they are for

   nLab: https://ncatlab.org/nlab/show/profunctor
   Paper: Bénabou, "Les distributeurs", Institut de Mathématique Pure
          et Appliquée, Rapport 33, Univ. Cath. de Louvain (1973)
   Paper: Lawvere, "Metric Spaces, Generalized Logic, and Closed
          Categories", Rend. Sem. Mat. Fis. Milano 43 (1973)

   The notion, and the several names it travels under, accumulated over
   roughly a decade.  Lawvere presented some of these ideas at
   Oberwolfach in 1966; the surviving record is a set of notes taken by
   Anders Kock of a talk by Lawvere, with a passing mention of
   "generalised functors" (now called profunctors) and their
   "generalised matrix multiplication" (nLab).  Jean Bénabou coined the
   word "profunctor" and later preferred "distributor" (distributeur),
   on the ground that a lax functor into the bicategory of distributors
   is a "distribution on a category", formally resembling a distribution
   as a generalized function (nLab).  The "bimodule" the header records,
   and the related name "module", come from the Australian school: for
   one-object V-categories, that is, monoids in V, a profunctor is
   literally a bimodule in the classical algebraic sense (nLab;
   Wikipedia).

   A profunctor is, in one image, a matrix of sets.  Where the header
   presents [Profunctor] C D as the functor type C^op ∏ D ⟶ Sets, the
   reading that motivates it is relational: P(c, d) is a proof-relevant
   relation between the objects of C and those of D, generalizing a
   functor as a relation generalizes a function.  Two such matrices
   compose by generalized matrix multiplication, a coend that traces out
   the shared middle index: (Q ∘ P)(c, e) = ∫^d P(c, d) × Q(d, e).  The
   unit of this composition is the hom-bifunctor, exactly [Id_Profunctor]
   C, that is Hom C.  Categories, profunctors, and natural
   transformations thereby form a bicategory, written Prof (also Mod or
   Dist), the setting in which much of formal and enriched category
   theory is carried out (nLab; Wikipedia).

   The library builds this bicategory not as one category but, keeping
   the binding discipline the header describes, as coherence lemmas over
   the per-pair functor categories.  Composition is [prof_compose] of
   Construction/Profunctor/Compose.v, assembled from the coend integrand
   [prof_integrand] via the coend calculus of Structure/Coend.v and
   Instance/Sets/Coend.v, with unit [prof_id] taken to be Hom C; the
   unitors and associator [prof_unit_left_iso], [prof_unit_right_iso],
   and [prof_assoc_iso] of Construction/Profunctor/Laws.v are the
   co-Yoneda unit laws and the associativity coherence, the last a
   Fubini-style rebracketing of the triple coend; Day convolution
   (Construction/Day.v) reuses the same integrand pattern.

   The header's [Repr_left] and [Repr_right] place ordinary functors
   inside this bicategory.  A functor gives a pair of representable
   profunctors that are adjoint in Prof, so the inclusion Cat ⟶ Prof is
   a proarrow equipment in Wood's sense, and the right-adjoint
   profunctors are exactly the functors into the Cauchy completion of
   the codomain (nLab).  In this file the corresponding statement is
   [representable_adjunction] of Theory/Profunctor/Adjunction.v: F ⊣ U
   holds precisely when [Repr_left] F ≅ [Repr_right] U as profunctors,
   the natural isomorphism recorded by [Prof_Setoid].

   The enriched case is where the notion earns much of its use.  A
   metric space is a category enriched over ([0, ∞], ≥, +), on Lawvere's
   reading (Lawvere 1973); profunctors between such enriched categories
   are the enriched distributors, and weighted colimits over them
   recover Cauchy-sequence completion.  At the discrete extreme a
   profunctor between sets is a span, and dg-bimodules between
   dg-categories are the profunctors appearing in the definition of
   noncommutative motives (nLab).

   Computationally, the profunctor is a familiar type class.  Haskell's
   Profunctor p, with dimap :: (c -> a) -> (b -> d) -> p a b -> p c d, is
   the functorial action of a profunctor Hask^op × Hask ⟶ Set; Milewski
   reads p a b as a proof-relevant relation, a container of values of
   type b keyed by a, and realizes coend composition by an existentially
   quantified datatype that collapses the shared middle variable, with
   the hom-functor as the identity by the ninja-Yoneda lemma (Milewski,
   "Ends and Coends", 2017; see Theory/Coend/Yoneda.v).  On this footing
   the optics — lenses, prisms, traversals — are polymorphic profunctor
   transformers, composed by function composition and proved equivalent
   to the concrete getter/setter representations (Pickering, Gibbons,
   Wu, "Profunctor Optics: Modular Data Accessors", Art, Science, and
   Engineering of Programming 1(2):7, 2017). *)

Definition Profunctor (C D : Category) := (C^op ∏ D) ⟶ Sets.

Notation "C ⇸ D" := (Profunctor C D)
  (at level 90, right associativity) : category_scope.

(* The identity profunctor on C is the hom-bifunctor Hom C : C^op ∏ C ⟶ Sets of
   Functor/Hom.v, viewed at the profunctor type C ⇸ C. On (c, c') it is the
   hom-set C(c, c'), with C acting on both sides by composition; it is the unit
   for profunctor composition (Construction/Profunctor/Compose.v reuses Hom C as
   its prof_id). *)
Definition Id_Profunctor (C : Category) : C ⇸ C := Hom C.

(* Representable profunctors. A functor F : C ⟶ D presents the profunctor

     Repr_left F : C ⇸ D,     (c, d) ↦ D(F c, d),

   covariantly representable on the left, while a functor U : D ⟶ C presents

     Repr_right U : C ⇸ D,    (c, d) ↦ C(c, U d),

   representable on the right. Both are built from the hom-bifunctor of the
   target (resp. source) precomposed with F (resp. U) in one slot and the
   identity in the other, exactly the two composites appearing in the hom-set
   adjunction hom_adj of Adjunction/Hom.v:

     Repr_left F  = Hom D ◯ (F^op ∏⟶ Id),
     Repr_right U = Hom C ◯ (Id^op ∏⟶ U).

   When F ⊣ U (the library orients F : D ⟶ C and U : C ⟶ D), these specialise
   to the two sides Hom C ◯ (F^op ∏⟶ Id) and Hom D ◯ (Id^op ∏⟶ U) of hom_adj,
   so the adjunction is precisely a natural isomorphism Repr_left F ≅ Repr_right
   U in the profunctor category (developed in Theory/Profunctor/Adjunction.v). *)

Definition Repr_left {C D : Category} (F : C ⟶ D) : C ⇸ D :=
  Hom D ◯ (F^op ∏⟶ (@Id D)).

Definition Repr_right {C D : Category} (U : D ⟶ C) : C ⇸ D :=
  Hom C ◯ ((@Id C)^op ∏⟶ U).

(* The equivalence of profunctors C ⇸ D is inherited from the functor category
   [C^op ∏ D, Sets]: two profunctors are equivalent exactly when they are
   naturally isomorphic (Functor_Setoid). This is a plain setoid handle, not a
   registered category instance, keeping the development fully polymorphic. *)
Definition Prof_Setoid (C D : Category) : Setoid (C ⇸ D) :=
  @Functor_Setoid (C^op ∏ D) Sets.
