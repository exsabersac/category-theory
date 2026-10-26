Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * O-graphs, the composable-pairs product, and categories as monoids / * O-图，可组合对的积，及作为幺半群的范畴 *)

(*
nLab:      https://ncatlab.org/nlab/show/quiver
   nLab:      https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   nLab:      https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              §II.7 “The Category of All Categories”, printed pp. 48-49,
              display (3)

   Mac Lane fixes a collection O of objects once and for all and looks at the
   graphs that have O as their object set.  Those form a category O-Grph, and
   on it there is a product: two O-graphs A and B are multiplied by taking
   COMPOSABLE PAIRS, an arrow of A ×_O B being a pair <g, f> with the domain
   of g equal to the codomain of f.  This product has a unit, the trivial
   O-graph O itself, and it is associative up to isomorphism.  His remark is
   then that a category with object set O is EXACTLY a monoid for that
   product: an O-graph A with two O-graph morphisms c : A ×_O A ⟶ A and
   i : O ⟶ A making one associativity square and two unit triangles commute
   (his display (3)).  “Thus a category is like a monoid with Set replaced by
   O-Grph and cartesian product by ×_O.”

   The three catalog items formalised here are [maclane:II.7:def2] (O-graphs,
   O-graph morphisms, the trivial O-graph), [maclane:II.7:def3] (the product
   over O, its associativity and its unit), and [maclane:II.7:remark1] (a
   category is a monoid in O-Grph).  The sentences quoted in this header are
   the CATALOG's paraphrase of those items, from
   doc/plan/books/maclane/inventory/II.json, not Mac Lane's own wording; the
   book itself should be consulted for the latter.

   WHY THE SLOGAN MATTERS.  “A category is a monoid in O-Grph” is the
   graph-side member of a family of statements this library already carries
   on the functor side: a monad on C is a monoid in the monoidal category of
   endofunctors ([Theory/Monad.v], [Theory/Algebra/Monoid.v]), a monoidal
   category is a one-object bicategory ([Theory/Bicategory/OneObject.v]), a
   monoid is a one-object category ([Construction/Deloop.v]).  Each is the
   same move -- take a structure, find the monoidal category in which it is a
   monoid -- and the present one is the base case: it is composition itself
   that is being exhibited as a multiplication.  Fixing O is what makes it
   work.  Over varying object sets there is no product of graphs with this
   unit, because the composable-pairs construction has to know that the two
   graphs share their nodes; that is why the setting is O-Grph and not Grph,
   and why the statement is about categories WITH A GIVEN OBJECT SET rather
   than about categories at large.

   RELATION TO [Quiver] (Construction/Free/Quiver.v).  An [OGraph O] is a
   [Quiver] whose [nodes] field is fixed to O -- [QuiverOfOGraph] performs
   exactly that repackaging -- and an [OGraphHom] is the identity-on-nodes
   special case of a [QuiverHomomorphism], recorded by [OGrph_Quiver_nodes]
   ([fnodes] of the image is literally [fun x => x], by [eq_refl]).  The
   comparison functor [OGrph_Quiver : OGrph O ⟶ QuiverCategory] is built.
   This is a DIFFERENT setting, not a weaker one: [QuiverCategory] has more
   objects (quivers on every node type) and, at a fixed node type, more
   morphisms and a coarser hom-equivalence, since a quiver morphism may move
   nodes and [QuiverHomomorphismEquivalence] compares two of them up to an
   arbitrary family of node equalities.  That last point has a price:
   [OGrph_Quiver] is proved faithful only under [NodeUIP] -- along a node
   self-equality that is not [eq_refl] the transported edge maps need not be
   related -- and whether it is faithful without that hypothesis is left
   open.  This is the ONLY place in the file where UIP appears, and it is an
   explicit hypothesis, in the idiom of [Theory/Metacategory/General.v]'s
   [ObjUIP] and [Theory/Category/Monoid.v]'s [HomRigid], never an axiom.

   NOT THE METACATEGORY TABLE.  [Theory/Metacategory.v] and
   [Theory/Metacategory/ArrowsOnly.v] also speak of “composable pairs”, and
   the content is unrelated: there a composable pair is a key of a finite map
   [pairs : M.t arrow] recording the value of a PARTIAL COMPOSITION on a
   single sort of arrows (Mac Lane §I.1's arrows-only axiomatisation).  There
   is no product of graphs there, no unit, no monoid.  Nothing in this file
   uses those records and nothing in them is generalised here.

   RELATION TO [Theory/Category/Monoid.v].  That file formalises the germ of
   the same idea from §I.2 -- a category as a monoid for the composable-pairs
   product over its object set -- and the two developments differ in exactly
   one design decision, with a visible consequence.  There, a graph is TWO
   SORTED: one sort of arrows with [gdom] and [gcod] maps out of it.  Reading
   a category as such a graph must bundle all the homs into a single sort,
   which transports morphisms along object equalities, and that forces the
   explicit [HomRigid] hypothesis -- proved unavoidable there by a
   countermodel.  Here the edges stay INDEXED by their endpoints, as in
   [Quiver] and in [Category] itself, so nothing is ever bundled, no morphism
   is ever transported along an object equality, and no rigidity hypothesis
   is taken: [MonoidOfCat] applies to an arbitrary [Category] and
   [CategoryOfOMonoid] to an arbitrary monoid.  The second difference is
   packaging (below): that file states the monoid laws by hand in a bespoke
   [SpanMonoid] record; this one builds the monoidal category and uses the
   library's [Monoid] class.

   PACKAGING DECISION.  The full [Monoidal (OGrph O)] instance is built --
   the tensor as a genuine bifunctor [OGraph_Tensor : OGrph O ∏ OGrph O ⟶
   OGrph O], both unitors and the associator as isomorphisms IN [OGrph O],
   all six naturality fields, and BOTH coherence laws (triangle and
   pentagon).  Nothing is descoped and no coherence law is left unproved.
   The payoff is that [category_is_monoid_in_OGrph] is a statement about
   [Theory/Algebra/Monoid.v]'s actual [Monoid] class rather than about a
   record invented here: [OMonoid A] is by definition
   [@Monoid (OGrph O) (OGrph_Monoidal O) A], so [mu] IS Mac Lane's c, [eta]
   IS his i, and his display (3) IS the class's [mu_assoc], [mu_unit_left]
   and [mu_unit_right].  The cost was universe hygiene, not proof effort: the
   coherence obligations are all “destruct the composable pair and, where a
   node equality is in the way, destruct that too”, while [Monoidal] pins the
   shape of the category it applies to (see UNIVERSES below).

   THE PRODUCT'S SETOID, which is where the difficulty actually lives.  An
   arrow of A ×_O B from x to z is a [Composable] record: a middle node
   [cmid], an arrow [cleft] of A into z and an arrow [cright] of B out of x.
   Two of them are identified by [CompEquiv]: an equality q of the middle
   NODES together with [≈]-equality of the two legs after transporting along
   q.  Three things are worth stating precisely about this.

   (1) It is an equivalence relation with NO use of UIP, because q is only
   ever eliminated, never compared: every proof about [CompEquiv] destructs
   the sigma and then destructs q, after which the transports disappear.  Two
   proofs of one node equality are nowhere required to agree.

   (2) The one place where UIP WOULD have been needed is the left unitor.
   [oul_to] sends a pair (y; p : y = z, f : X x y) to [transport p f], and its
   respectfulness has to compare [transport p f] with [transport p' f'] for
   the two proofs p, p' carried by two equivalent pairs.  What discharges it
   is that the trivial O-graph's arrows -- which are precisely those proofs --
   are compared by LEIBNIZ equality, so the equivalence hands over p = p'
   directly.  Coarsen that setoid and the equation must be supplied instead,
   which is UIP on O.  The choice of setoid on [OGraph_unit] is therefore not
   cosmetic; it is what buys the whole file its freedom from UIP.

   (3) The node component is compared by Coq's [=] and not by any [≈].  That
   is not a lapse from the library's discipline: O is a bare [Type] with no
   setoid, exactly as [obj] is in [Theory/Category.v] and [nodes] is in
   [Quiver], and it is the graph's own notion of node equality.  Every
   ARROW-level comparison in the file, including both legs of a composable
   pair, is by [≈].

   ORIENTATION, chosen deliberately and pinned by computation.  Mac Lane
   writes the composable pair as <g, f> with dom g = cod f and sets
   dom<g, f> = dom f, cod<g, f> = cod g, so the left member is the arrow
   applied LAST.  [cleft]/[cright] follow him, which makes the monoid
   multiplication on a category's own O-graph agree with this library's
   [compose] on the nose: [ocat_mu_is_compose] and [ocat_eta_is_id] are
   [eq_refl].  Taking the other orientation would have produced the opposite
   category.

   ROUND TRIPS, measured rather than asserted.  From a monoid: the O-graph
   comes back by [eq_refl] ([OGraphOfCat_CategoryOfOMonoid]) and so does the
   multiplication's underlying map ([omul_roundtrip]) -- the latter because
   [Composable] is a primitive-projection record, so its eta rule is
   definitional ([composable_eta]).  The unit comes back only pointwise
   ([ounit_roundtrip], by [destruct] on the identity proof), because [eq] has
   no eta rule and [match p with eq_refl => _ end] is not the term it
   evaluates to.  From a category: all five data fields are [eq_refl]
   ([ocat_roundtrip_obj] through [ocat_roundtrip_compose]) and the comparison
   assembles into [ocat_roundtrip_iso : C ≅[Cat] CategoryOfOMonoid
   (MonoidOfCat C)], both functors identity on objects and on morphisms.
   Note the strength of that packaging: Cat's hom-setoid is [Functor_Setoid],
   so [≅[Cat]] IS an equivalence of categories (Instance/Cat.v); the extra
   content is in the construction, not the type.  Full Leibniz equality of
   the two [Category] records is NOT claimed and does not hold -- the law
   fields are rebuilt rather than projected -- which is the same boundary
   [Theory/Algebra/Rig.v]'s [EndRig_DeloopRig] and [Theory/Category/Monoid.v]
   report.

   WITNESS.  At O = [poly_unit] a monoid in O-Grph is a monoid, and the
   category it assembles is Mac Lane's B M: [Monoid_of_MonObject] turns any
   [MonObject] of [Construction/Deloop.v] into an [OMonoid], and
   [Deloop_of_MonObject_obj] through [Deloop_of_MonObject_compose] check by
   [eq_refl] that [CategoryOfOMonoid] of it agrees with [Deloop M] in every
   data field.  The converse leg is [MonObject_of_OMonoid], the endomorphism
   monoid at the single node, which returns the original monoid in all four
   data fields (again [eq_refl]); full record equality does not hold there,
   for the law fields alone, and the file says why beside the examples.  Everything
   computes: [ograph_nat_compose_2_3] evaluates 2 · 3 to 5 in (ℕ, +).

   NOT BUILT HERE, deliberately.  The free category on a graph
   ([maclane:II.7:construction2], [thm1]) and the adjunction with the
   forgetful functor ([construction3]) are Construction/Free/Quiver.v's
   [FreeOnQuiver] and [FreeForgetfulAdjunction]; nothing about them is
   restated.  ×_O is not symmetric and no braiding is claimed.  No
   [Grph]-level (varying-node) product is defined -- see WHY THE SLOGAN
   MATTERS above for why there is none of this shape.

   UNIVERSES (measured with [Set Printing Universes], not asserted; the
   printed signatures are quoted).

   - [OGraph@{o h p} : Type@{o} → Type@{max(o,h+1,p+1)}] with NO constraints:
     nodes at o, edges at h, the edge setoids' proofs at p, all independent.

   - [OGraph_prod@{o h p}] carries the single constraint [o <= h].  That is
     the honest content of the composable-pairs construction: an arrow of
     A ×_O B literally CONTAINS a node (its [cmid] field), so the node
     universe must sit at or below the edge universe for the product to be an
     O-graph again.  It propagates to everything monoidal.

   - [OGrph@{o h p hh oo} : Type@{o} → Category@{oo hh hh}].  The hom and
     proof universes of the category of O-graphs are IDENTIFIED, and the
     cause is [Structure/Monoidal.v]: its class is [Monoidal@{u u0} :
     Category@{u u0 u0} → Type], i.e. every monoidal category in this library
     has its hom and proof levels equal.  It is a statement about O-Grph
     itself and not about which categories can be read as O-graphs:
     [OGraphOfCat@{o h p} : ∀ C : Category@{o h p}, OGraph@{o h p} obj[C]]
     takes an ARBITRARY category, carrying only [Category]'s own [h <= p].

   - [MonoidOfCat@{o h p hh oo u} : ∀ C : Category@{o h p}, OMonoid
     (OGraphOfCat C)] and [CategoryOfOMonoid] carry further constraints (14
     in [MonoidOfCat]'s clause, most of them the [<=] bookkeeping of the
     records they mention), of which the one that RESTRICTS the input is
     [o <= h], inherited from the product: reading a
     category as a MONOID (as opposed to merely as a graph) puts its objects
     inside its arrows, so its object universe must sit at or below its hom
     universe.  [Category@{o h p}] does not itself demand this, so the
     statement is scoped to categories that satisfy it; every category
     constructed in this file does, [CategoryOfOMonoid] by construction.

   - [CategoryOfOMonoid@{o h p hh oo} : … → Category@{o h p}]: the category
     built from a monoid has its objects at the node universe, its homs at
     the edge universe and its proofs at the edge setoids' proof universe.
     No level is raised.

   - [OGraph_unit] and everything downstream carry [h <= equality.u0], a
     bound against the GLOBAL universe of the standard library's [eq], which
     is what the trivial O-graph's arrows are.  [Theory/Size.v] declines
     stdlib [=] in favour of its own level-polymorphic [ObjEq] for related
     reasons; nothing here needs that extra generality, and the library's own
     [Quiver] comparison likewise uses stdlib [=] on nodes.

   - [category_is_monoid_in_OGrph@{o h p hh oo co ch cp u}] keeps the two
     HALVES' universes apart -- the monoid half quantifies over
     [OGraph@{o h p}], the category half over [Category@{co ch cp}], and the
     o-family and co-family are genuinely distinct -- at the cost of an
     explicit universe binder on the theorem.  That separation is ALL the
     binder buys, and the constraint clause says so (audit-corrected; it is
     quoted here because it contradicts what one would guess):

         h = o    p = o    hh = o    ch = co    cp = co

     i.e. WITHIN each half minimisation still collapses everything to one
     level, because the round-trip Examples and [ORebuild_to]/[ORebuild_from]
     below do not carry the explicit binders the definitions above do.  The
     packaged theorem is therefore DEGENERATE in its universes; the general
     result is in the tree, but it lives in the components
     ([MonoidOfCat@{o h p hh oo u}], [CategoryOfOMonoid@{o h p hh oo}]),
     which carry only [o <= h] and [h <= p] and no equalities.  Applying the
     binder discipline to the round-trip Examples would repair the packaging;
     that is not done here and is recorded as a known gap rather than a
     claim.

   AXIOMS.  Every named constant of this file, and every constant the three
   records generate, reports “Closed under the global context” under [Print
   Assumptions]; the file contains no [Program], hence no obligations, no
   incomplete proof and no [Axiom].  UIP enters only as the explicit
   [NodeUIP] hypothesis of [OGrph_Quiver_Faithful], and no other hypothesis
   of any kind is taken anywhere.

--------
nLab:      https://ncatlab.org/nlab/show/quiver
   nLab:      https://ncatlab.org/nlab/show/monoidal+category

   O-图 (O-graph)：带有序节点对上箭头的图结构，支撑自由范畴/自由幺半等构造。本文件给出
   O-图范畴与保持节点恒等的态射。原英文文首极长；本波次译为定义性导言，细节后续可续译。
*)

(** ** O-graphs / ** O-图 *)

Record OGraph@{o h p} (O : Type@{o}) : Type@{max(o,h+1,p+1)} := {
  oedges : O → O → Type@{h};                 (* arrows, indexed by endpoints / 箭头，以端点索引 *)
  oedgeset : ∀ x y, Setoid@{h p} (oedges x y)  (* each arrow set is a setoid / 每个箭头集合都是一个集合型 *)
}.

Arguments oedges {_} _ _ _.
Arguments oedgeset {_} _ _ _.

#[export] Existing Instance oedgeset.

(*
A morphism of O-graphs: a map on arrows for each ordered pair of nodes,
   respecting the arrow setoids.  There is NO action on nodes -- that is
   exactly what “identity on objects” means, and it is the whole difference
   from [QuiverHomomorphism].

--------
O-图的态射：对每一对有序节点的箭头的映射，遵守箭头集合的规则。对节点没有任何作用——这正是“在对象上保持恒等”的含义，也是与 [QuiverHomomorphism] 的全部区别。
*)
Record OGraphHom@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : Type@{max(o,h,p)} := {
  oemap : ∀ x y, oedges A x y → oedges B x y;
  oemap_respects : ∀ x y,
    Proper@{h p} (respectful@{h p h p h p}
                    (@equiv@{h p} _ (oedgeset A x y))
                    (@equiv@{h p} _ (oedgeset B x y)))
      (oemap x y)
}.

Arguments oemap {_ _ _} _ _ _ _.
Arguments oemap_respects {_ _ _} _ _ _.

#[export] Existing Instance oemap_respects.

Definition OGraphHomEquiv@{o h p hh} {O : Type@{o}} {A B : OGraph@{o h p} O}
  (F G : OGraphHom@{o h p} A B) : Type@{hh} :=
  ∀ x y (f : oedges A x y),
    @equiv@{h p} _ (oedgeset B x y) (oemap F x y f) (oemap G x y f).

Lemma OGraphHomEquiv_Equivalence@{o h p hh} {O : Type@{o}}
  (A B : OGraph@{o h p} O) :
  Equivalence@{hh hh} (@OGraphHomEquiv@{o h p hh} O A B).
Proof.
  constructor.
  - intros F x y f; reflexivity.
  - intros F G H x y f; symmetry; apply H.
  - intros F G K H1 H2 x y f.
    transitivity (oemap G x y f); [ apply H1 | apply H2 ].
Qed.

Definition OGraphHom_Setoid@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : Setoid@{hh hh} (OGraphHom@{o h p} A B) := {|
  equiv := @OGraphHomEquiv@{o h p hh} O A B;
  setoid_equiv := OGraphHomEquiv_Equivalence@{o h p hh} A B
|}.

Definition ograph_id@{o h p} {O : Type@{o}} (A : OGraph@{o h p} O)
  : OGraphHom@{o h p} A A := {|
  oemap := fun _ _ f => f;
  oemap_respects := fun x y f g (H : @equiv@{h p} _ (oedgeset A x y) f g) => H
|}.

Definition ograph_compose@{o h p} {O : Type@{o}} {A B C : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} B C) (G : OGraphHom@{o h p} A B)
  : OGraphHom@{o h p} A C := {|
  oemap := fun x y f => oemap F x y (oemap G x y f);
  oemap_respects := fun x y f g (H : @equiv@{h p} _ (oedgeset A x y) f g) =>
    oemap_respects F x y _ _ (oemap_respects G x y _ _ H)
|}.

Lemma ograph_compose_respects@{o h p hh} {O : Type@{o}}
  (A B C : OGraph@{o h p} O) :
  Proper@{hh hh}
    (respectful@{hh hh hh hh hh hh} (@OGraphHomEquiv@{o h p hh} O B C)
       (respectful@{hh hh hh hh hh hh} (@OGraphHomEquiv@{o h p hh} O A B)
          (@OGraphHomEquiv@{o h p hh} O A C)))
    (@ograph_compose@{o h p} O A B C).
Proof.
  intros F F' HF G G' HG x y f; simpl.
  rewrite (HG x y f).
  now apply HF.
Qed.

Lemma ograph_id_left@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A B (ograph_compose (ograph_id B) F) F.
Proof. now intros x y f. Qed.

Lemma ograph_id_right@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A B (ograph_compose F (ograph_id A)) F.
Proof. now intros x y f. Qed.

Lemma ograph_comp_assoc@{o h p hh} {O : Type@{o}} (A B C D : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} C D) (G : OGraphHom@{o h p} B C)
  (H : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A D
    (ograph_compose F (ograph_compose G H))
    (ograph_compose (ograph_compose F G) H).
Proof. now intros x y f. Qed.

Lemma ograph_comp_assoc_sym@{o h p hh} {O : Type@{o}}
  (A B C D : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} C D) (G : OGraphHom@{o h p} B C)
  (H : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A D
    (ograph_compose (ograph_compose F G) H)
    (ograph_compose F (ograph_compose G H)).
Proof. now intros x y f. Qed.

(*
The category of O-graphs and identity-on-nodes morphisms.  Its hom and
   proof universes are identified ([Category@{oo hh hh}]) because
   Structure/Monoidal.v's [Monoidal@{o h}] demands exactly that shape of
   category; see the header.

--------
O-图范畴以及节点上恒等的态射。它的同态和证明宇宙被识别（[Category@{oo hh hh}]），因为 Structure/Monoidal.v 的 [Monoidal@{o h}] 正好要求该形状的范畴；参见头部。
*)
Definition OGrph@{o h p hh oo} (O : Type@{o}) : Category@{oo hh hh} := {|
  obj     := OGraph@{o h p} O;
  hom     := fun A B => OGraphHom@{o h p} A B;
  homset  := @OGraphHom_Setoid@{o h p hh} O;
  id      := @ograph_id@{o h p} O;
  compose := @ograph_compose@{o h p} O;

  compose_respects := @ograph_compose_respects@{o h p hh} O;

  id_left  := @ograph_id_left@{o h p hh} O;
  id_right := @ograph_id_right@{o h p hh} O;

  comp_assoc     := @ograph_comp_assoc@{o h p hh} O;
  comp_assoc_sym := @ograph_comp_assoc_sym@{o h p hh} O
|}.

(** ** The trivial O-graph / ** 平凡的O图 *)

(*
Leibniz equality as a setoid, with the carrier universe and the relation
   universe kept apart (Lib/Setoid.v's [eq_Setoid] identifies them).

--------
作为集合体的莱布尼茨等式，载体宇宙和关系宇宙保持分离（Lib/Setoid.v 的 [eq_Setoid] 识别它们）。
*)
Definition eq_setoid_poly@{a b} (A : Type@{a}) : Setoid@{a b} A := {|
  equiv := @eq A;
  setoid_equiv := eq_equivalence@{a b}
|}.

(*
The trivial (unit) O-graph -- Mac Lane's “O itself, with arrow set O and
   both domain and codomain functions the identity”.  Its arrows x ~> y are
   the PROOFS of x = y, compared by Leibniz equality.

   Two things about that, both load-bearing and neither an idealisation.
   First, Leibniz comparison does NOT collapse distinct proofs: absent UIP on
   the node type this graph may carry more than one loop at a node, so the
   reading “exactly one arrow per node” is available only when O has UIP.
   That costs nothing -- [OGraph_unit] is still a unit for the composable-
   pairs product, because the product's own setoid quotients by the middle
   node's equality (see [CompEquiv]), which is exactly the freedom the extra
   loops occupy.  Second, the comparison must be Leibniz and not coarser:
   [oul_to]'s respectfulness proof consumes an equation between two proofs of
   one node equality, and under a coarser setoid that equation would have to
   be supplied instead -- which is UIP.  So this setoid choice is what keeps
   the file free of any UIP hypothesis; see the header.

--------
平凡（单位）O-图 —— Mac Lane 的“O 本身”，箭头集为 O，域和陪域函数都是恒等函数”。 它的箭头 x ~> y 是 x = y 的证明，通过莱布尼茨等式进行比较。

关于这件事有两点，都是有实际意义的，并且都不是理想化的。首先，莱布尼茨比较并不会合并不同的证明：在节点类型上缺少UIP的情况下，这个图的一个节点可能会有多个循环，所以“每个节点恰好一条箭头”的解读仅在O具有UIP时可用。这不会有任何代价——[OGraph_unit]仍然是可组合对积的单位，因为积本身的集合等价会对中间节点的等式进行商化（见[CompEquiv]），这正是额外循环所占据的自由度。其次，比较必须是莱布尼茨比较，而不是更粗的比较：[oul_to]的尊重性证明消耗了一个关于一个节点等式的两个证明之间的等式，而在更粗的集合等价下，该等式必须被提供——这就是UIP。因此，这个集合等价的选择是保持文件不依赖任何UIP假设的原因；详见文件头部。
*)
Definition OGraph_unit@{o h p} (O : Type@{o}) : OGraph@{o h p} O := {|
  oedges := fun x y => x = y;
  oedgeset := fun x y => eq_setoid_poly@{h p} (x = y)
|}.

(** ** The bridge to Quiver / ** 通往颤动之桥 *)

Definition QuiverOfOGraph@{o h p} {O : Type@{o}} (A : OGraph@{o h p} O)
  : Quiver@{o h p} := {|
  nodes := O;
  edges := oedges A;
  edgeset := oedgeset A
|}.

Definition QuiverHomOfOGraphHom@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} A B) :
  QuiverHomomorphism@{o h p o h p} (QuiverOfOGraph A) (QuiverOfOGraph B).
Proof.
  unshelve refine (@Build_QuiverHomomorphism
                     (QuiverOfOGraph A) (QuiverOfOGraph B)
                     (fun x => x) (fun x y f => oemap F x y f) _).
  intros x y f g Hfg.
  now apply oemap_respects.
Defined.

Definition OGrph_Quiver@{o h p hh oo +|+} (O : Type@{o}) :
  OGrph@{o h p hh oo} O ⟶ QuiverCategory.
Proof.
  unshelve refine (@Build_Functor (OGrph@{o h p hh oo} O) QuiverCategory
                     (@QuiverOfOGraph@{o h p} O)
                     (@QuiverHomOfOGraphHom@{o h p} O) _ _ _).
  - intros A B F G HFG.
    exists (fun _ => eq_refl).
    intros x y f.
    exact (HFG x y f).
  - intros A.
    exists (fun _ => eq_refl).
    now intros x y f.
  - intros A B C F G.
    exists (fun _ => eq_refl).
    now intros x y f.
Defined.

(*
The comparison is the identity on nodes, definitionally: that is the whole
   content of “identity on objects”.

--------
在定义上，比较就是节点上的恒等：这就是“对象上的恒等”的全部内容。
*)
Example OGrph_Quiver_nodes {O : Type} {A B : OGraph O} (F : OGraphHom A B) :
  @fnodes _ _ (QuiverHomOfOGraphHom F) = fun x : O => x := eq_refl.

(*
Uniqueness of identity proofs on the NODE type, taken as an explicit
   hypothesis in the house idiom (Theory/Metacategory/General.v's [ObjUIP],
   Theory/Category/Monoid.v's [HomRigid]) rather than as an axiom.  It is not
   needed anywhere else in this file; it is needed HERE because
   [QuiverHomomorphismEquivalence] compares two quiver morphisms up to an
   ARBITRARY family of node equalities, and along a self-equality that is not
   [eq_refl] the transported edge maps need not be related.  Whether the
   comparison functor is faithful without it is left open.

--------
在 NODE 类型上恒等证明的唯一性，被作为显式假设放在 house 习语中（Theory/Metacategory/General.v 的 [ObjUIP]，Theory/Category/Monoid.v 的 [HomRigid]），而不是作为公理。在本文件的其他地方不需要；这里需要它是因为 [QuiverHomomorphismEquivalence] 比较两个 quiver 态射时会涉及任意节点相等的族，并且沿着一个不是 [eq_refl] 的自相等传递的边映射可能不相关。是否在没有它的情况下比较函子仍然忠实，则尚未确定。
*)
Definition NodeUIP (O : Type) : Type := ∀ (x : O) (p : x = x), p = eq_refl.

Lemma OGrph_Quiver_Faithful (O : Type) : NodeUIP O → Faithful (OGrph_Quiver O).
Proof.
  intros uip.
  constructor.
  intros A B F G HFG x y f.
  destruct HFG as [node_equiv coher].
  specialize (coher x y f); simpl in coher.
  rewrite (uip _ (node_equiv x)), (uip _ (node_equiv y)) in coher.
  exact coher.
Qed.

(** ** The composable-pairs product A ×_O B / ** 可组合对的积 A ×_O B *)

(*
An arrow of A ×_O B from x to z is Mac Lane's composable pair <g, f>: a
   middle node [cmid], an arrow [cleft] of A into z and an arrow [cright] of
   B out of x meeting at it.  Kept as a primitive-projection record, so that
   [composable_eta] below holds by [eq_refl].

--------
从 x 到 z 的 A ×_O B 的箭头是 Mac Lane 的可组合对 <g, f>：一个中间节点 [cmid]，一个从 A 到 z 的箭头 [cleft]，以及一个从 x 出发的 B 的箭头 [cright] 在此交汇。作为原始投影记录保存，因此下面的 [composable_eta] 由 [eq_refl] 成立。
*)
Record Composable@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O) (x z : O)
  : Type@{max(o,h)} := {
  cmid : O;
  cleft : oedges A cmid z;
  cright : oedges B x cmid
}.

Arguments cmid {_ _ _ _ _} _.
Arguments cleft {_ _ _ _ _} _.
Arguments cright {_ _ _ _ _} _.

Definition cpair@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (y : O) (g : oedges A y z) (f : oedges B x y)
  : Composable@{o h p} A B x z := {|
  cmid := y; cleft := g; cright := f
|}.

(* Record eta, definitionally, thanks to primitive projections. / 从定义上讲，记录是由于原始投影而产生的。 *)
Example composable_eta@{o h p +|+} {O : Type@{o}} {A B : OGraph@{o h p} O}
  {x z : O} (u : Composable@{o h p} A B x z)
  : cpair (cmid u) (cleft u) (cright u) = u := eq_refl.

(*
Two composable pairs are identified when their middle nodes are equal and
   the two legs agree after transporting along that equality.  The middle
   node is compared by Coq's [=] -- it is a NODE, and O carries no setoid --
   while the legs are compared by the edge setoids' own `≈`.

   No UIP is needed for this to be an equivalence relation, nor anywhere it
   is consumed: the node equality q is only ever ELIMINATED (every proof
   below destructs it, after which the two transports disappear) and never
   compared with a second proof of the same equation.  The header explains
   where a comparison of two such proofs WOULD have arisen, and what
   discharges it.

--------
当它们的中间节点相等并且在沿该等式传递后两条边一致时，会识别出两个可组合的对。中间节点由 Coq 的 [=] 进行比较——它是一个节点，而 O 不携带任何集合等价关系——而边则由边集合等价关系自身的 `≈` 进行比较。

不需要 UIP 来使其成为一个等价关系，也不需要在任何使用它的地方：节点等式 q 仅会被消解（下面的每个证明都会将其拆解，然后两个传递就消失了），且从不与同一等式的第二个证明进行比较。标题解释了两个此类证明的比较本可能出现的位置，以及如何处理它。
*)
Definition CompEquiv@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (u v : Composable@{o h p} A B x z) : Type@{p} :=
  { q : cmid u = cmid v &
      ((@equiv@{h p} _ (oedgeset A (cmid v) z)
          (match q in _ = m return oedges A m z with eq_refl => cleft u end)
          (cleft v)) *
       (@equiv@{h p} _ (oedgeset B x (cmid v))
          (match q in _ = m return oedges B x m with eq_refl => cright u end)
          (cright v)))%type }.

Lemma CompEquiv_Equivalence@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (x z : O) : Equivalence@{h p} (@CompEquiv@{o h p} O A B x z).
Proof.
  constructor.
  - intros u.
    exists eq_refl; simpl.
    now split.
  - intros [y g f] [y' g' f'] [q [Hg Hf]]; simpl in *.
    destruct q; simpl in *.
    exists eq_refl; simpl.
    now split; symmetry.
  - intros [y1 g1 f1] [y2 g2 f2] [y3 g3 f3] [q [Hg Hf]] [q' [Hg' Hf']];
      simpl in *.
    destruct q, q'; simpl in *.
    exists eq_refl; simpl.
    now split; [ transitivity g2 | transitivity f2 ].
Qed.

Definition Composable_Setoid@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (x z : O) : Setoid@{h p} (Composable@{o h p} A B x z) := {|
  equiv := @CompEquiv@{o h p} O A B x z;
  setoid_equiv := CompEquiv_Equivalence@{o h p} A B x z
|}.

Definition OGraph_prod@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : OGraph@{o h p} O := {|
  oedges := Composable@{o h p} A B;
  oedgeset := @Composable_Setoid@{o h p} O A B
|}.

(* The common special case of [CompEquiv]: same middle node, legs `≈`. / [CompEquiv] 的常见特殊情况：相同的中间节点，腿 `≈`。 *)
Lemma cpair_equiv@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (y : O) (g g' : oedges A y z) (f f' : oedges B x y) :
  @equiv@{h p} _ (oedgeset A y z) g g' →
  @equiv@{h p} _ (oedgeset B x y) f f' →
  @CompEquiv@{o h p} O A B x z (cpair y g f) (cpair y g' f').
Proof. intros Hg Hf; exists eq_refl; now split. Qed.

(** ** The tensor bifunctor / ** 张量双函子 *)

Definition ograph_prod_map@{o h p} {O : Type@{o}} {A A' B B' : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} A A') (G : OGraphHom@{o h p} B B') :
  OGraphHom@{o h p} (OGraph_prod A B) (OGraph_prod A' B').
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod A B) (OGraph_prod A' B')
                     (fun x z u =>
    cpair (cmid u) (oemap F _ _ (cleft u)) (oemap G _ _ (cright u))) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  apply cpair_equiv; now apply oemap_respects.
Defined.

Definition OGraph_Tensor@{o h p hh oo +|+} (O : Type@{o}) :
  OGrph@{o h p hh oo} O ∏ OGrph@{o h p hh oo} O ⟶ OGrph@{o h p hh oo} O.
Proof.
  unshelve refine (@Build_Functor (OGrph@{o h p hh oo} O ∏ OGrph@{o h p hh oo} O)
                     (OGrph@{o h p hh oo} O)
    (fun p => OGraph_prod (fst p) (snd p))
    (fun p q FG => ograph_prod_map (fst FG) (snd FG)) _ _ _).
  - intros [A B] [A' B'] [F G] [F' G'] [HF HG] x z u; simpl in *.
    destruct u as [y g f]; simpl.
    apply cpair_equiv; [ apply HF | apply HG ].
  - intros [A B] x z u; simpl.
    destruct u as [y g f]; simpl.
    now apply cpair_equiv.
  - intros [A B] [A' B'] [A'' B''] [F G] [F' G'] x z u; simpl.
    destruct u as [y g f]; simpl.
    now apply cpair_equiv.
Defined.

(** ** The unitors / ** 连接器 *)

Definition oul_to@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod (OGraph_unit@{o h p} O) X) X.
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod (OGraph_unit O) X) X (fun x z u =>
    match cleft u in _ = m return oedges X x m with eq_refl => cright u end) _).
  intros x z u v.
  destruct u as [y p f], v as [y' p' f']; simpl.
  intros [q [Hp Hf]]; simpl in *.
  destruct q; simpl in *.
  destruct Hp; simpl.
  now destruct p.
Defined.

Definition oul_from@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} X (OGraph_prod (OGraph_unit@{o h p} O) X).
Proof.
  unshelve refine (@Build_OGraphHom O X (OGraph_prod (OGraph_unit O) X)
                     (fun x z f => @cpair O (OGraph_unit O) X x z z eq_refl f) _).
  intros x z f f' Hf.
  now apply cpair_equiv.
Defined.

Definition OGraph_unit_left@{o h p hh oo +|+} {O : Type@{o}}
  (X : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod (OGraph_unit@{o h p} O) X) X.
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod (OGraph_unit@{o h p} O) X) X
                     (oul_to X) (oul_from X) _ _).
  - now intros x z f.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now apply cpair_equiv.
Defined.

Definition our_to@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod X (OGraph_unit@{o h p} O)) X.
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod X (OGraph_unit O)) X (fun x z u =>
    match cright u in _ = m return oedges X m z → oedges X x z with
    | eq_refl => fun g => g
    end (cleft u)) _).
  intros x z u v.
  destruct u as [y g p], v as [y' g' p']; simpl.
  intros [q [Hg Hp]]; simpl in *.
  destruct q; simpl in *.
  destruct Hp; simpl.
  now destruct p.
Defined.

Definition our_from@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} X (OGraph_prod X (OGraph_unit@{o h p} O)).
Proof.
  unshelve refine (@Build_OGraphHom O X (OGraph_prod X (OGraph_unit O))
                     (fun x z g => @cpair O X (OGraph_unit O) x z x g eq_refl) _).
  intros x z g g' Hg.
  now apply cpair_equiv.
Defined.

Definition OGraph_unit_right@{o h p hh oo +|+} {O : Type@{o}}
  (X : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod X (OGraph_unit@{o h p} O)) X.
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod X (OGraph_unit@{o h p} O)) X
                     (our_to X) (our_from X) _ _).
  - now intros x z g.
  - intros x z u; simpl.
    destruct u as [y g p]; simpl.
    destruct p; simpl.
    now apply cpair_equiv.
Defined.

(** ** The associator / ** 连接器 *)

Definition oassoc_to@{o h p} {O : Type@{o}} (A B C : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod (OGraph_prod A B) C)
                    (OGraph_prod A (OGraph_prod B C)).
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod (OGraph_prod A B) C)
                     (OGraph_prod A (OGraph_prod B C)) (fun x w u =>
    @cpair O A (OGraph_prod B C) x w (cmid (cleft u)) (cleft (cleft u))
      (@cpair O B C x (cmid (cleft u)) (cmid u) (cright (cleft u)) (cright u))) _).
  intros x w u v.
  destruct u as [y [z a b] c], v as [y' [z' a' b'] c']; simpl.
  intros [q [Hab Hc]]; simpl in *.
  destruct q; simpl in *.
  destruct Hab as [q' [Ha Hb]]; simpl in *.
  destruct q'; simpl in *.
  apply cpair_equiv; [ assumption | now apply cpair_equiv ].
Defined.

Definition oassoc_from@{o h p} {O : Type@{o}} (A B C : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod A (OGraph_prod B C))
                    (OGraph_prod (OGraph_prod A B) C).
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod A (OGraph_prod B C))
                     (OGraph_prod (OGraph_prod A B) C) (fun x w v =>
    @cpair O (OGraph_prod A B) C x w (cmid (cright v))
      (@cpair O A B (cmid (cright v)) w (cmid v) (cleft v) (cleft (cright v)))
      (cright (cright v))) _).
  intros x w u v.
  destruct u as [z a [y b c]], v as [z' a' [y' b' c']]; simpl.
  intros [q [Ha Hbc]]; simpl in *.
  destruct q; simpl in *.
  destruct Hbc as [q' [Hb Hc]]; simpl in *.
  destruct q'; simpl in *.
  apply cpair_equiv; [ now apply cpair_equiv | assumption ].
Defined.

Definition OGraph_assoc@{o h p hh oo +|+} {O : Type@{o}}
  (A B C : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod (OGraph_prod A B) C) (OGraph_prod A (OGraph_prod B C)).
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod (OGraph_prod A B) C)
                     (OGraph_prod A (OGraph_prod B C))
                     (oassoc_to A B C) (oassoc_from A B C) _ _).
  - intros x w v; simpl.
    exists eq_refl; simpl.
    now split; [ reflexivity | exists eq_refl; split ].
  - intros x w u; simpl.
    exists eq_refl; simpl.
    now split; [ exists eq_refl; split | reflexivity ].
Defined.

(** ** Coherence / ** 连贯性 *)

Lemma ograph_to_unit_left_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose g (oul_to X))
    (ograph_compose (oul_to Y) (ograph_prod_map (ograph_id _) g)).
Proof.
  intros x z u; simpl.
  destruct u as [y p f]; simpl.
  now destruct p.
Qed.

Lemma ograph_from_unit_left_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map (ograph_id _) g) (oul_from X))
    (ograph_compose (oul_from Y) g).
Proof. intros x z f; simpl; now apply cpair_equiv. Qed.

Lemma ograph_to_unit_right_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose g (our_to X))
    (ograph_compose (our_to Y) (ograph_prod_map g (ograph_id _))).
Proof.
  intros x z u; simpl.
  destruct u as [y h p]; simpl.
  now destruct p.
Qed.

Lemma ograph_from_unit_right_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map g (ograph_id _)) (our_from X))
    (ograph_compose (our_from Y) g).
Proof. intros x z f; simpl; now apply cpair_equiv. Qed.

Lemma ograph_to_assoc_natural@{o h p hh +|+} {O : Type@{o}}
  (A A' B B' C C' : OGraph@{o h p} O)
  (g : OGraphHom@{o h p} A A') (h : OGraphHom@{o h p} B B')
  (i : OGraphHom@{o h p} C C') :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map g (ograph_prod_map h i)) (oassoc_to A B C))
    (ograph_compose (oassoc_to A' B' C') (ograph_prod_map (ograph_prod_map g h) i)).
Proof.
  intros x w u; simpl.
  destruct u as [y [z a b] c]; simpl.
  apply cpair_equiv; [ reflexivity | now apply cpair_equiv ].
Qed.

Lemma ograph_from_assoc_natural@{o h p hh +|+} {O : Type@{o}}
  (A A' B B' C C' : OGraph@{o h p} O)
  (g : OGraphHom@{o h p} A A') (h : OGraphHom@{o h p} B B')
  (i : OGraphHom@{o h p} C C') :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map (ograph_prod_map g h) i) (oassoc_from A B C))
    (ograph_compose (oassoc_from A' B' C') (ograph_prod_map g (ograph_prod_map h i))).
Proof.
  intros x w u; simpl.
  destruct u as [z a [y b c]]; simpl.
  apply cpair_equiv; [ now apply cpair_equiv | reflexivity ].
Qed.

Lemma ograph_triangle@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_prod_map (our_to X) (ograph_id Y))
    (ograph_compose (ograph_prod_map (ograph_id X) (oul_to Y))
                    (oassoc_to X (OGraph_unit O) Y)).
Proof.
  intros x z u; simpl.
  destruct u as [m [n g e] q]; simpl.
  destruct e; simpl.
  now apply cpair_equiv.
Qed.

Lemma ograph_pentagon@{o h p hh +|+} {O : Type@{o}}
  (A B C D : OGraph@{o h p} O) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose
       (ograph_compose (ograph_prod_map (ograph_id A) (oassoc_to B C D))
                       (oassoc_to A (OGraph_prod B C) D))
       (ograph_prod_map (oassoc_to A B C) (ograph_id D)))
    (ograph_compose (oassoc_to A B (OGraph_prod C D))
                    (oassoc_to (OGraph_prod A B) C D)).
Proof.
  intros x w u; simpl.
  destruct u as [m [n [k a b] c] d]; simpl.
  apply cpair_equiv; [ reflexivity | ].
  apply cpair_equiv; [ reflexivity | ].
  now apply cpair_equiv.
Qed.

(** ** O-Grph is monoidal under ×_O / ** O-Grph 在 ×_O 下是幺半群的 *)

Definition OGrph_Monoidal@{o h p hh oo +|+} (O : Type@{o}) :
  @Monoidal (OGrph@{o h p hh oo} O).
Proof.
  unshelve refine (@Build_Monoidal (OGrph@{o h p hh oo} O)
                     (OGraph_unit@{o h p} O) (OGraph_Tensor@{o h p hh oo} O)
                     (@OGraph_unit_left@{o h p hh oo} O)
                     (@OGraph_unit_right@{o h p hh oo} O)
                     (@OGraph_assoc@{o h p hh oo} O) _ _ _ _ _ _ _ _).
  - exact (@ograph_to_unit_left_natural O).
  - exact (@ograph_from_unit_left_natural O).
  - exact (@ograph_to_unit_right_natural O).
  - exact (@ograph_from_unit_right_natural O).
  - exact (@ograph_to_assoc_natural O).
  - exact (@ograph_from_assoc_natural O).
  - exact (@ograph_triangle O).
  - exact (@ograph_pentagon O).
Defined.

#[export] Existing Instance OGrph_Monoidal.

(** ** Monoids in O-Grph / ** O-图中的幺半群 *)

Definition OMonoid@{o h p hh oo +|+} {O : Type@{o}} (A : OGraph@{o h p} O)
  : Type@{hh} :=
  @Monoid (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A.

Definition omul@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) : OGraphHom@{o h p} (OGraph_prod A A) A :=
  @mu (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M.

Definition ounit@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A)
  : OGraphHom@{o h p} (OGraph_unit@{o h p} O) A :=
  @eta (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M.

(*
The three monoid laws, restated in the pointwise form of [OGraphHomEquiv]
   so that they can be applied to a composable pair.  Each is the class field
   read through the definitional unfolding of `≈` in [OGrph O].

--------
三个幺半群定律，以 [OGraphHomEquiv] 的逐点形式重新表述，以便它们可以应用于可组合对。每一个都是通过 [OGrph O] 中 `≈` 的定义展开读取的类字段。
*)

Lemma omonoid_assoc@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod (OGraph_prod A A) A) A
    (ograph_compose (omul M) (ograph_prod_map (omul M) (ograph_id A)))
    (ograph_compose
       (ograph_compose (omul M) (ograph_prod_map (ograph_id A) (omul M)))
       (oassoc_to A A A)).
Proof.
  exact (@mu_assoc (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

Lemma omonoid_unit_left@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod (OGraph_unit@{o h p} O) A) A
    (ograph_compose (omul M) (ograph_prod_map (ounit M) (ograph_id A)))
    (oul_to A).
Proof.
  exact (@mu_unit_left (OGrph@{o h p hh oo} O)
           (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

Lemma omonoid_unit_right@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod A (OGraph_unit@{o h p} O)) A
    (ograph_compose (omul M) (ograph_prod_map (ograph_id A) (ounit M)))
    (our_to A).
Proof.
  exact (@mu_unit_right (OGrph@{o h p hh oo} O)
           (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

(** ** From a category to a monoid in O-Grph / ** 从范畴到 O-Grph 中的幺半群 *)

Definition OGraphOfCat@{o h p} (C : Category@{o h p}) : OGraph@{o h p} (obj[C])
  := {|
  oedges := @hom C;
  oedgeset := @homset C
|}.

Definition ocat_mu@{o h p +|+} (C : Category@{o h p}) :
  OGraphHom@{o h p} (OGraph_prod (OGraphOfCat C) (OGraphOfCat C))
                    (OGraphOfCat C).
Proof.
  unshelve refine (@Build_OGraphHom obj[C]
                     (OGraph_prod (OGraphOfCat C) (OGraphOfCat C)) (OGraphOfCat C)
                     (fun x z u => cleft u ∘ cright u) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  now rewrite Hg, Hf.
Defined.

Definition ocat_eta@{o h p +|+} (C : Category@{o h p}) :
  OGraphHom@{o h p} (OGraph_unit@{o h p} (obj[C])) (OGraphOfCat C).
Proof.
  unshelve refine (@Build_OGraphHom obj[C] (OGraph_unit obj[C]) (OGraphOfCat C)
                     (fun x z p =>
                        match p in _ = m return x ~{C}~> m with
                        | eq_refl => id
                        end)
                     (fun x z p p' (Hp : p = p') => _)).
  now destruct Hp.
Defined.

Definition MonoidOfCat@{o h p hh oo +|+} (C : Category@{o h p}) :
  OMonoid@{o h p hh oo} (OGraphOfCat@{o h p} C).
Proof.
  unshelve refine (@Build_Monoid (OGrph@{o h p hh oo} obj[C])
                     (OGrph_Monoidal@{o h p hh oo} obj[C])
                     (OGraphOfCat C) (ocat_mu C) (ocat_eta C) _ _ _).
  - intros x w u; simpl.
    destruct u as [y [z f g] h]; simpl.
    now rewrite comp_assoc.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now rewrite id_left.
  - intros x z u; simpl.
    destruct u as [y f p]; simpl.
    destruct p; simpl.
    now rewrite id_right.
Defined.

(*
ORIENTATION, pinned by computation rather than by prose.  Mac Lane writes
   the composable pair as <g, f> with dom g = cod f, and sets dom<g,f> = dom f,
   cod<g,f> = cod g; so the LEFT leg is the arrow applied last.  With that
   choice the monoid multiplication on a category's own O-graph is this
   library's [compose] on the nose, and the unit is [id].

--------
取向，由计算决定而非由散文决定。麦克·莱恩将可组合对写作<g, f>，其中 dom g = cod f，并设 dom<g,f> = dom f，cod<g,f> = cod g；因此左边的腿是最后应用的箭头。按照这个选择，一个范畴自身 O-图上的单子乘法正好是这个库的 [compose]，单位是 [id]。
*)
Example ocat_mu_is_compose (C : Category) (x y z : obj[C])
  (g : y ~{C}~> z) (f : x ~{C}~> y) :
  oemap (omul (MonoidOfCat C)) x z
    (@cpair obj[C] (OGraphOfCat C) (OGraphOfCat C) x z y g f) = g ∘ f := eq_refl.

Example ocat_eta_is_id (C : Category) (x : obj[C]) :
  oemap (ounit (MonoidOfCat C)) x x eq_refl = id[x] := eq_refl.

(** ** From a monoid in O-Grph to a category / ** 从O-图中的幺半群到一个范畴 *)

Definition omon_id@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x : O) : oedges A x x :=
  oemap (ounit M) x x eq_refl.

Definition omon_compose@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) {x y z : O}
  (g : oedges A y z) (f : oedges A x y) : oedges A x z :=
  oemap (omul M) x z (cpair y g f).

Lemma omon_compose_respects@{o h p hh oo +|+} {O : Type@{o}}
  {A : OGraph@{o h p} O} (M : OMonoid@{o h p hh oo} A) (x y z : O) :
  Proper@{h p} (respectful@{h p h p h p}
                  (@equiv@{h p} _ (oedgeset A y z))
                  (respectful@{h p h p h p}
                     (@equiv@{h p} _ (oedgeset A x y))
                     (@equiv@{h p} _ (oedgeset A x z))))
    (@omon_compose@{o h p hh oo} O A M x y z).
Proof.
  intros g g' Hg f f' Hf.
  unfold omon_compose.
  apply oemap_respects.
  now apply cpair_equiv.
Qed.

Lemma omon_id_left@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y : O) (f : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x y) (omon_compose M (omon_id M y) f) f.
Proof.
  exact (omonoid_unit_left M x y (@cpair O (OGraph_unit O) A x y y eq_refl f)).
Qed.

Lemma omon_id_right@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y : O) (f : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x y) (omon_compose M f (omon_id M x)) f.
Proof.
  exact (omonoid_unit_right M x y (@cpair O A (OGraph_unit O) x y x f eq_refl)).
Qed.

Lemma omon_comp_assoc@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y z w : O)
  (f : oedges A z w) (g : oedges A y z) (h : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x w)
    (omon_compose M f (omon_compose M g h))
    (omon_compose M (omon_compose M f g) h).
Proof.
  symmetry.
  exact (omonoid_assoc M x w
           (@cpair O (OGraph_prod A A) A x w y (@cpair O A A y w z f g) h)).
Qed.

Lemma omon_comp_assoc_sym@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y z w : O)
  (f : oedges A z w) (g : oedges A y z) (h : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x w)
    (omon_compose M (omon_compose M f g) h)
    (omon_compose M f (omon_compose M g h)).
Proof. symmetry; apply omon_comp_assoc. Qed.

Definition CategoryOfOMonoid@{o h p hh oo +|+} {O : Type@{o}}
  {A : OGraph@{o h p} O} (M : OMonoid@{o h p hh oo} A) : Category@{o h p} := {|
  obj     := O;
  hom     := oedges A;
  homset  := oedgeset A;
  id      := omon_id M;
  compose := @omon_compose@{o h p hh oo} O A M;

  compose_respects := omon_compose_respects M;

  id_left  := omon_id_left M;
  id_right := omon_id_right M;

  comp_assoc     := omon_comp_assoc M;
  comp_assoc_sym := omon_comp_assoc_sym M
|}.

(** ** The round trips / ** 往返 *)

(* Monoid side: the O-graph comes back on the nose, ... / 幺半群方面：O-图又回到了原点，... *)
Example OGraphOfCat_CategoryOfOMonoid {O : Type} {A : OGraph O} (M : OMonoid A) :
  OGraphOfCat (CategoryOfOMonoid M) = A := eq_refl.

(* ... and so does the multiplication, as a function. / ... 乘法也是如此，作为一个函数。 *)
Example omul_roundtrip {O : Type} {A : OGraph O} (M : OMonoid A) :
  oemap (omul (MonoidOfCat (CategoryOfOMonoid M)))
    = oemap (omul M) := eq_refl.

(*
The unit comes back only after eliminating the identity proof: there is no
   eta rule for [eq], so [match p with eq_refl => ... end] is not the term it
   evaluates to.

--------
该单元只有在消除恒等证明后才会返回：[eq] 没有 eta 规则，因此 [match p with eq_refl => ... end] 不是它评估得到的项。
*)
Lemma ounit_roundtrip {O : Type} {A : OGraph O} (M : OMonoid A) :
  ∀ x z (p : x = z),
    oemap (ounit (MonoidOfCat (CategoryOfOMonoid M))) x z p
      = oemap (ounit M) x z p.
Proof. intros x z p; now destruct p. Qed.

(* Category side: all five data fields are definitional. / 范畴方面：所有五个数据字段都是定义性的。 *)
Example ocat_roundtrip_obj (C : Category) :
  obj[CategoryOfOMonoid (MonoidOfCat C)] = obj[C] := eq_refl.

Example ocat_roundtrip_hom (C : Category) :
  @hom (CategoryOfOMonoid (MonoidOfCat C)) = @hom C := eq_refl.

Example ocat_roundtrip_homset (C : Category) :
  @homset (CategoryOfOMonoid (MonoidOfCat C)) = @homset C := eq_refl.

Example ocat_roundtrip_id (C : Category) :
  @id (CategoryOfOMonoid (MonoidOfCat C)) = @id C := eq_refl.

Example ocat_roundtrip_compose (C : Category) :
  @compose (CategoryOfOMonoid (MonoidOfCat C)) = @compose C := eq_refl.

(*
Conjugating by identity isomorphisms does nothing: this is the shape
   [Functor_Setoid]'s naturality condition takes when the two functors agree
   on objects definitionally, as both comparisons below do.  (The same lemma
   is proved for the same reason in Theory/Category/Monoid.v; it is restated
   here rather than imported, that file having nothing else this one needs.)

--------
通过恒等同构进行结合不起作用：当两个函子在对象上在定义上相同时，[Functor_Setoid] 的自然性条件就是这种形状，正如下方的两个比较所做的那样。（在 Theory/Category/Monoid.v 中由于相同的原因证明了同样的引理；这里重述它而不是导入，因为那个文件没有这个文件需要的其他内容。）
*)
Lemma ograph_iso_id_conj {D : Category} {x y : D} (h : x ~> y) :
  from (@iso_id D y) ∘ h ∘ to (@iso_id D x) ≈ h.
Proof. simpl; now rewrite id_right, id_left. Qed.

Definition ORebuild_to (C : Category) : C ⟶ CategoryOfOMonoid (MonoidOfCat C).
Proof.
  unshelve refine (@Build_Functor C (CategoryOfOMonoid (MonoidOfCat C))
                     (fun x => x) (fun x y f => f) _ _ _).
  - now intros x y f g Hfg.
  - reflexivity.
  - reflexivity.
Defined.

Definition ORebuild_from (C : Category) : CategoryOfOMonoid (MonoidOfCat C) ⟶ C.
Proof.
  unshelve refine (@Build_Functor (CategoryOfOMonoid (MonoidOfCat C)) C
                     (fun x => x) (fun x y f => f) _ _ _).
  - now intros x y f g Hfg.
  - reflexivity.
  - reflexivity.
Defined.

Definition ocat_roundtrip_iso (C : Category) :
  C ≅[Cat] CategoryOfOMonoid (MonoidOfCat C).
Proof.
  unshelve refine (@Build_Isomorphism Cat C (CategoryOfOMonoid (MonoidOfCat C))
                     (ORebuild_to C) (ORebuild_from C) _ _).
  - exists (fun x => iso_id).
    intros x y f.
    rewrite ograph_iso_id_conj.
    reflexivity.
  - exists (fun x => iso_id).
    intros x y f.
    rewrite ograph_iso_id_conj.
    reflexivity.
Defined.

(** ** Mac Lane's remark: a category IS a monoid in O-Grph / ** 麦克·莱恩的评论：一个范畴就是 O-Grph 中的一个幺半群 *)

Theorem category_is_monoid_in_OGrph@{o h p hh oo co ch cp +|+} :
  ((∀ (O : Type@{o}) (A : OGraph@{o h p} O) (M : OMonoid@{o h p hh oo} A),
      (*
every monoid in O-Grph is a category on O, and the monoid is
         recovered: its graph on the nose, its multiplication as a function
         on the nose, its unit pointwise

--------
O-Grph 中的每个幺半群都是 O 上的一个范畴，并且幺半群可以被恢复：它的图精确地对应，它的乘法精确地作为一个函数对应，它的单位点逐点对应
*)
      ((OGraphOfCat (CategoryOfOMonoid M) = A) *
       (oemap (omul (MonoidOfCat (CategoryOfOMonoid M))) = oemap (omul M)) *
       (∀ x z (p : x = z),
          oemap (ounit (MonoidOfCat (CategoryOfOMonoid M))) x z p
            = oemap (ounit M) x z p))%type)
   *
   (∀ C : Category@{co ch cp},
      (*
and every category is such a monoid, on its own underlying O-graph,
         recovered up to isomorphism in Cat

--------
并且每个范畴本身都是这样一个幺半群，在其自身的底层 O-图上，在 Cat 中可以恢复至同构
*)
      C ≅[Cat] CategoryOfOMonoid (MonoidOfCat C)))%type.
Proof.
  split.
  - intros O A M.
    split; [ split | ].
    + exact (OGraphOfCat_CategoryOfOMonoid M).
    + exact (omul_roundtrip M).
    + exact (ounit_roundtrip M).
  - exact ocat_roundtrip_iso.
Defined.

(** ** Witness: one node, and monoids / ** 见证：一个节点，以及幺半群 *)

Definition OGraph_of_MonObject (M : MonObject) : OGraph poly_unit := {|
  oedges := fun _ _ => carrier M;
  oedgeset := fun _ _ => is_setoid M
|}.

Definition ograph_mon_mu (M : MonObject) :
  OGraphHom (OGraph_prod (OGraph_of_MonObject M) (OGraph_of_MonObject M))
            (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_OGraphHom poly_unit
                     (OGraph_prod (OGraph_of_MonObject M)
                                  (OGraph_of_MonObject M))
                     (OGraph_of_MonObject M)
                     (fun x z u => mon_op (cleft u) (cright u)) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  now rewrite Hg, Hf.
Defined.

Definition ograph_mon_eta (M : MonObject) :
  OGraphHom (OGraph_unit poly_unit) (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_OGraphHom poly_unit (OGraph_unit poly_unit)
                     (OGraph_of_MonObject M)
                     (fun _ _ _ => mon_unit)
                     (fun x z p p' (Hp : p = p') => _)).
  reflexivity.
Defined.

Definition Monoid_of_MonObject (M : MonObject) : OMonoid (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_Monoid (OGrph poly_unit) (OGrph_Monoidal poly_unit)
                     (OGraph_of_MonObject M)
                     (ograph_mon_mu M) (ograph_mon_eta M) _ _ _).
  - intros x w u; simpl.
    destruct u as [y [z f g] h]; simpl.
    now rewrite mon_op_assoc.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now rewrite mon_op_unit_l.
  - intros x z u; simpl.
    destruct u as [y f p]; simpl.
    destruct p; simpl.
    now rewrite mon_op_unit_r.
Defined.

(*
The category assembled from that monoid is Mac Lane's B M, on the nose in
   every data field.

--------
由那个幺半群组装的范畴就是 Mac Lane 的 B M，在每一个数据字段上都恰好对应。
*)
Example Deloop_of_MonObject_obj (M : MonObject) :
  obj[CategoryOfOMonoid (Monoid_of_MonObject M)] = obj[Deloop M] := eq_refl.

Example Deloop_of_MonObject_hom (M : MonObject) :
  @hom (CategoryOfOMonoid (Monoid_of_MonObject M)) = @hom (Deloop M) := eq_refl.

Example Deloop_of_MonObject_homset (M : MonObject) :
  @homset (CategoryOfOMonoid (Monoid_of_MonObject M)) = @homset (Deloop M)
    := eq_refl.

Example Deloop_of_MonObject_id (M : MonObject) :
  @id (CategoryOfOMonoid (Monoid_of_MonObject M)) = @id (Deloop M) := eq_refl.

Example Deloop_of_MonObject_compose (M : MonObject) :
  @compose (CategoryOfOMonoid (Monoid_of_MonObject M)) = @compose (Deloop M)
    := eq_refl.

(* Conversely, a monoid in poly_unit-Grph is a monoid. / 相反，poly_unit-Grph 中的单子是一个单子。 *)
Definition MonObject_of_OMonoid {A : OGraph poly_unit} (M : OMonoid A) :
  MonObject := hom_monoid (CategoryOfOMonoid M) ttt.

(*
The monoid comes back in every data field.  Full record equality is
   blocked, as always in this library, by the proof-carrying law fields: the
   laws of [CategoryOfOMonoid] are derived from the monoid-object laws rather
   than projected from M, so they are not the same terms.  (Contrast
   Construction/Deloop.v's [hom_monoid_Deloop], which IS [eq_refl] on the
   whole record, because [Deloop] takes M's law fields verbatim.)

--------
在每个数据字段中都会出现单子。完整记录的相等性被阻止了，正如该库中一贯如此，这要归因于携带证明的法则字段：[CategoryOfOMonoid] 的法则是从单子对象法则派生的，而不是从 M 投影出来的，因此它们不是相同的项。（对比 Construction/Deloop.v 中的 [hom_monoid_Deloop]，它是整个记录上的 [eq_refl]，因为 [Deloop] 直接采用了 M 的法则字段。）
*)
Example MonObject_of_OMonoid_carrier (M : MonObject) :
  carrier (MonObject_of_OMonoid (Monoid_of_MonObject M)) = carrier M := eq_refl.

Example MonObject_of_OMonoid_setoid (M : MonObject) :
  is_setoid (MonObject_of_OMonoid (Monoid_of_MonObject M)) = is_setoid M
    := eq_refl.

Example MonObject_of_OMonoid_unit (M : MonObject) :
  @mon_unit (MonObject_of_OMonoid (Monoid_of_MonObject M)) = @mon_unit M
    := eq_refl.

Example MonObject_of_OMonoid_op (M : MonObject) :
  @mon_op (MonObject_of_OMonoid (Monoid_of_MonObject M)) = @mon_op M
    := eq_refl.

(*
And the whole passage computes.  [Nat_Plus] is Construction/Deloop.v's
   monoid (ℕ, +, 0).

--------
整个过程都是可以计算的。[Nat_Plus] 是 Construction/Deloop.v 的幺半群 (ℕ, +, 0)。
*)
Example ograph_nat_compose (a b : carrier Nat_Plus) :
  @omon_compose _ _ (Monoid_of_MonObject Nat_Plus) ttt ttt ttt a b
    = (a + b)%nat := eq_refl.

Example ograph_nat_id :
  omon_id (Monoid_of_MonObject Nat_Plus) ttt = 0%nat := eq_refl.

Example ograph_nat_compose_2_3 :
  @omon_compose _ _ (Monoid_of_MonObject Nat_Plus) ttt ttt ttt 2%nat 3%nat
    = 5%nat := eq_refl.

(** ** The unit setoid is load-bearing: coarsening it ENTAILS UIP / ** 单位集合是承重的：对它进行粗化意味着 UIP *)

(*
The header explains that no UIP is needed anywhere above, and localizes the
   reason to one choice: the trivial O-graph compares its edge-proofs by
   LEIBNIZ equality, which is what hands [oul_to]'s respectfulness obligation
   the equation [p = p'] it needs.  Coarsening that setoid -- identifying all
   proofs, which looks harmless, since morally there is one loop per node --
   is what would put UIP back.

   That is stated here as a THEOREM rather than left as a design argument.
   Build the trivial O-graph with the coarsest possible setoid, keep
   [oul_to]'s underlying map verbatim, and respectfulness of THAT map is not
   merely “UIP-shaped”: it entails UIP on O outright.  So the escape above is
   the setoid choice and nothing else.

   (Adapted from the adversarial audit's own probe, with thanks.)

--------
标题解释说，在上面任何地方都不需要 UIP，并将原因归结为一个选择：平凡的 O-图通过 LEIBNIZ 等式比较其边的证明，这正是满足 [oul_to] 尊重义务所需要的方程 [p = p']。 对该集合类型进行粗化——将所有证明视为相同，看起来无害，因为从本质上每个节点只有一个循环——才会把 UIP 引回。

这里将其表述为一个定理，而不是作为设计论证留待说明。使用最粗集合类型构建平凡的 O-图，按原样保留 [oul_to] 的底层映射，并且该映射的尊重性不仅仅是“UIP 形状的”：它完全推导出 O 上的 UIP。 因此，上述规避方法就是集合类型的选择，别无其他。

（改编自对抗性审计自身的探查，谨表感谢。）
*)

Program Definition coarse_unit (O : Type) : OGraph O := {|
  oedges := fun x y => x = y;
  oedgeset := fun x y => {| equiv := fun _ _ => True |}
|}.
Next Obligation. constructor; repeat intro; exact Logic.I. Qed.

(* [oul_to]'s underlying map, verbatim, over the coarsened unit. / [oul_to] 的底层地图，逐字地，超过粗化单元。 *)
Definition coarse_oul_map {O : Type} (X : OGraph O) (x z : O)
  (u : Composable (coarse_unit O) X x z) : oedges X x z :=
  match cleft u in _ = m return oedges X x m with eq_refl => cright u end.

Lemma coarse_map_on_unit {O : Type} (a : O) (p : a = a) :
  @coarse_oul_map O (OGraph_unit O) a a
    (@cpair O (coarse_unit O) (OGraph_unit O) a a a p eq_refl) = p.
Proof. unfold coarse_oul_map; simpl; now destruct p. Qed.

Theorem coarse_respectfulness_entails_UIP (O : Type)
  (H : ∀ (X : OGraph O) (x z : O),
         Proper (respectful
                   (@equiv _ (oedgeset (OGraph_prod (coarse_unit O) X) x z))
                   (@equiv _ (oedgeset X x z)))
           (@coarse_oul_map O X x z)) :
  NodeUIP O.
Proof.
  intros a p.
  assert (Hequiv : @equiv _ (oedgeset (OGraph_prod (coarse_unit O)
                                         (OGraph_unit O)) a a)
                     (@cpair O (coarse_unit O) (OGraph_unit O) a a a p eq_refl)
                     (@cpair O (coarse_unit O) (OGraph_unit O) a a a eq_refl eq_refl)).
  { exists eq_refl; simpl; split; [ exact Logic.I | reflexivity ]. }
  pose proof (H (OGraph_unit O) a a _ _ Hequiv) as Hr.
  simpl in Hr.
  rewrite <- (coarse_map_on_unit a p).
  exact Hr.
Qed.
