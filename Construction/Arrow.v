Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

(** The arrow category C^→ (also written Arr(C), C², or [2, C]). *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出箭头范畴：对象为底范畴的态射，态射为交换方块。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Morphisms as objects: lifting, factorization, and the self-indexing

   nLab: https://ncatlab.org/nlab/show/weak+factorization+system
   nLab: https://ncatlab.org/nlab/show/orthogonal+factorization+system
   nLab: https://ncatlab.org/nlab/show/codomain+fibration
   nLab: https://ncatlab.org/nlab/show/display+map
   nLab: https://ncatlab.org/nlab/show/adjoint+string

   The arrow category is the device that makes the morphisms of C
   first-class: statements about maps become ordinary category theory
   inside C ⃗.  A commuting square is no longer a diagram condition but a
   single morphism; a class of maps — monomorphisms, fibrations, display
   maps — is a full subcategory; and closure of such a class under
   retracts or under limits means retracts or limits computed in the
   arrow category.  Because Cat is cartesian closed, the [2, C] reading
   of the header exhibits the arrow category as an exponential, the
   directed path object of C: functors X ⟶ Arr(Y) correspond exactly to
   natural transformations between functors X ⟶ Y (nLab, arrow
   category), just as a natural transformation F ⟹ G is a functor out
   of C × 2 restricting to F and G at the two endpoints of the walking
   arrow (Riehl, "Category Theory in Context", Dover 2016) — a homotopy
   at the level of categories.  Defining [Arrow] as the comma
   (Id[C] ↓ Id[C]) obtains all of this from the already-proven comma
   machinery: the category laws arrive as instances, and
   [comma_proj_nat] of Construction/Comma.v specializes to the generic
   arrow, the natural transformation dom ⟹ cod whose component at an
   object f of the arrow category is f itself.  The projections moreover
   flank the identity-arrow functor x ↦ id[x] in an adjoint triple
   cod ⊣ ids ⊣ dom (nLab, adjoint string).

   The classical applications run through homotopy theory.  The lifting
   problems of Quillen's model categories (Quillen, "Homotopical
   Algebra", Springer Lecture Notes in Mathematics 43, 1967) are
   commuting squares — that is, morphisms e → m of the arrow category —
   and both classes of a weak factorization system are closed under
   retracts formed there, a model structure being precisely two
   interlocking such systems (nLab, weak factorization system; model
   category).  In this library, Theory/Orthogonality.v states unique
   lifting in exactly this square form and proves the retract closure
   [ortho_left_retract].  Orthogonal factorization systems — first
   studied by Mac Lane ("Duality for groups", Bull. AMS 56, 1950),
   essentially present in Freyd and Kelly ("Categories of continuous
   functors, I", J. Pure Appl. Algebra 2, 1972), and named by Bousfield
   ("Constructions of factorization systems in categories", J. Pure
   Appl. Algebra 9, 1977) — likewise live here: the two classes are
   replete subcategories of the arrow category (nLab, orthogonal
   factorization system), and the construction itself carries the
   classifying monad, an orthogonal factorization system on K being an
   Eilenberg–Moore algebra, appropriately defined, for the monad of the
   squaring endofunctor K ↦ K² on Cat (Korostenski and Tholen, "Factorization
   systems as Eilenberg-Moore algebras", J. Pure Appl. Algebra 85,
   1993).  In-tree the systems are the class [OFS] of
   Structure/Factorization.v.

   The codomain projection opens fibred category theory.  The codomain
   functor [comma_proj2] is always a Grothendieck opfibration, and is a
   fibration exactly when C has pullbacks — the cartesian lift of a map
   is its pullback square — with the slice categories C/c as fibres
   (Construction/Slice.v), whence its names "self-indexing" and
   "fundamental fibration" (nLab, codomain fibration).  This library
   proves the fibred presentation equivalent to the present one:
   Construction/Displayed/Codomain.v renders the arrow category
   displayed over C, establishes the isomorphism
   [Codomain_Total_Arrow_iso] in Cat, and builds the cartesian lifts
   from chosen pullbacks in [codomain_cleaving].  Pullback-closed full
   subcategories of the arrow category are Taylor's classes of display
   maps, the semantic counterpart of dependent types: a display map
   p : B → A models the judgement x:A ⊢ B(x), with substitution
   interpreted as pullback, and in homotopy type theory the display
   maps are the fibrations (Taylor, "Practical Foundations of
   Mathematics", CUP 1999; nLab, display map).  The [2, C] equivalence
   of the header is proven in Theory/Shapes.v as
   [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C], over the walking arrow [_2]
   of Instance/Two.v, for [C : Category@{o Set Set}] -- a restriction that
   side genuinely forces, since Instance/Fun.v's [Fun] identifies the hom
   universes of source and target while [_2]'s homs live in [Set].  Read its strength precisely: [≅[Cat]] here is an
   EQUIVALENCE of categories, since Instance/Cat.v identifies functors up
   to natural isomorphism.  One of the two round trips is strict --
   [Arrow_Fun_Arrow_strict] there says the composite
   Arrow C -> [_2, C] -> Arrow C is [Functor_StrictEq_Setoid]-equal to the
   identity -- while the other is witnessed by a family of natural
   isomorphisms whose components are identities, and no more; that file's
   header records exactly what would be needed for a [StrictCat]
   isomorphism, which is not claimed.  The codomain isomorphism above is
   the separate comparison with the displayed presentation.

   Mac Lane's Exercise II.4.7 — functors INTO the arrow category are
   exactly natural transformations — is Construction/Arrow/Functor.v:
   extraction [Arrow_extract] (boundary functors plus the generic arrow
   assembled into a transformation), introduction [Arrow_intro] (a
   transformation materialized as a functor, naturality supplying the
   squares), and the bijection [Arrow_classification] as a setoid
   isomorphism in Sets; unlike the [_2] comparison it carries no
   Set-level universe pin (the library's ambient h = p constraint
   from [Functor] still applies), never leaving the comma
   presentation. *)

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.
