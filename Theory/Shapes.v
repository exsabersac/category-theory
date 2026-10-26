Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.

Generalizable All Variables.

(** * Functors out of the walking shapes 1, 2 and 3 / * 从行走的形状 1、2 和 3 出发的函子 *)

(*
nLab:      https://ncatlab.org/nlab/show/terminal+category
   nLab:      https://ncatlab.org/nlab/show/interval+category
   nLab:      https://ncatlab.org/nlab/show/walking+structure
   nLab:      https://ncatlab.org/nlab/show/arrow+category
   Book:      Mac Lane, Categories for the Working Mathematician, 2nd ed.
              (GTM 5), §I.3 “Functors”, printed p. 15 -- the exercise
              (catalogued as maclane:I.3:ex2) that functors out of the
              ordinal categories 1, 2 and 3 are, respectively, the objects,
              the arrows and the composable pairs of arrows of the target.
   Book:      Fong and Spivak, Seven Sketches in Compositionality (CUP,
              2019), §3.3.2 (Example 3.36 and Exercise 3.37, printed p. 91)
              and §3.3.3 (Exercise 3.45, printed p. 93).

   A diagram shape coCLASSIFIES a structure when functors OUT of it are
   exactly the instances of that structure in the target: the walking X is
   the category for which a functor to C is an X of C (nLab, “walking
   structure”).  The first three cases of the principle are the smallest
   ones, and they are what this file proves.  A functor out of the point
   [_1] is an object of C; a functor out of the walking arrow [_2] is a
   morphism of C; a functor out of [_3], the ordinal on three objects, is a
   composable pair.  Mac Lane sets exactly these three as an exercise in
   §I.3, printed p. 15, and the pattern continues: Instance/Ordinal.v's
   [Functor_of_Triple] already handles the next case, diagrams of shape 4
   as three composable arrows.

   NAME.  There is an unrelated Instance/Shapes.v in this tree; its
   [Shape] is a binary expression tree indexing tries, a different sense of
   the word entirely, and nothing here refers to it.  The present file is
   about DIAGRAM shapes -- the index categories of Instance/One.v,
   Instance/Two.v and Instance/Ordinal.v.

   THE FORM OF THE STATEMENTS.  The library has no carrier for a bijection
   between classes of objects, and objects of a category carry no setoid,
   so a “correspondence” here is an explicit pair of constructions together
   with both round-trip laws -- the two-map presentation.  For each shape:

     shape   forward           backward     round trips
     ------  ----------------  -----------  ---------------------------------
     [_1]    [Point]           [point_of]   [point_of_Point] (definitional),
                                            [Point_point_of_strict]
     [_2]    [Walk]            [arrow_of]   [arrow_of_Walk] (definitional),
                                            [Walk_arrow_of_strict]
     [_3]    [Functor_of_Pair] [pair_fst],  [Functor_of_Pair_fst],
                               [pair_snd]   [Functor_of_Pair_snd],
                                            [Functor_of_Pair_of_Functor]

   In the [_1] and [_2] rows one round trip holds definitionally (the
   extracted datum IS the datum that was fed in) and the other is the
   substantive one: it recovers a functor from what it does on the
   generators.  The [_3] row has NO definitional side -- the table above
   never marked one, and an audit caught the prose here claiming otherwise
   -- because [Functor_of_Pair]'s action on a step runs through
   Instance/Ordinal.v's [Functor_of_Steps_step], which consumes [id_right]
   and [le_t_irr].  For [_1] and
   [_2] the substantive direction is proven at [Functor_StrictEq_Setoid],
   the STRICT functor equality of Theory/Functor.v -- equal object maps on
   the nose, morphism maps agreeing after transport -- which is finer than
   the [Functor_Setoid] natural isomorphism that [Cat] uses, in the one
   direction Instance/StrictCat/ToCat.v proves; the [Cat]-level corollaries
   [Point_point_of] and [Walk_arrow_of] are exactly that implication,
   [strict_equiv_implies_fun_equiv], applied.
   For [_3] the substantive direction is at [Functor_Setoid]: the object
   part of a functor out of [_3] is defined on all of [Ord_obj 3] whereas
   the composable pair only names three objects, so the two functors are
   compared through the canonical isomorphisms that Instance/Ordinal.v's
   [ord_functor_iso] supplies, exactly as [Functor_of_Steps_of_Functor]
   does there.

   THE CATEGORY-LEVEL COMPARISONS, and their exact strength.  Both
   [One_Fun_iso : [_1, C] ≅[Cat] C] and
   [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C] are proven.  In this library
   [≅[Cat]] is an EQUIVALENCE of categories and not an isomorphism of
   categories: Instance/Cat.v's hom-setoid is [Functor_Setoid], which
   identifies functors up to natural isomorphism, so an isomorphism there
   is an equivalence -- that file's header says so, and the strict
   1-category is Instance/StrictCat.v.  One direction is nevertheless
   strict, and is recorded separately: [Arrow_Fun_Arrow_strict] says the
   composite Arrow C -> [_2, C] -> Arrow C is [Functor_StrictEq_Setoid]-
   equal to the identity functor, so the equivalence is a strict retraction
   on that side.  The other side is not given strictly, and the gap can be
   named exactly.  An isomorphism in [StrictCat] would
   need [Fun_of_Arrow ◯ Arrow_of_Fun] to be [Functor_StrictEq_Setoid]-equal
   to the identity of [[_2, C]], whose object component is a LEIBNIZ
   equality [Walk (arrow_of F) = F] between functor records.  What holds,
   and is proven as [Walk_arrow_of_strict], is one notch weaker: the two
   functors have the same object map on the nose, and their morphism maps
   agree up to [≈].  The records need not agree -- [Walk (arrow_of F)]
   sends [TwoIdX] to [id] by construction, while [F] sends it to whatever
   [F] supplies, and only [fmap_id] relates the two, which is a [≈] and not
   a [=].  Promoting that to Leibniz equality of records would need at
   least function extensionality and proof irrelevance, neither of which
   this library assumes.  So the [StrictCat] isomorphism is NOT delivered
   here and is not claimed; whether it is provable is left open.

   WHAT THIS CLOSES.  Construction/Arrow.v disclosed the [2, C] reading of
   the arrow category as documentation-level, with no in-tree comparison to
   a functor category over [_2]; [Two_Fun_Arrow] is that comparison.
   Instance/Two.v's header states the same correspondence as prose, as does
   Instance/One.v for [[1, C] ≃ C] and Instance/One/Diagonal.v where it is
   quoted in passing; [One_Fun_iso] and the [Point]/[point_of] pair are the
   theorems behind that prose.

   USE OF [=].  Statements of this file that use Coq's [=] rather than [≈]
   are of four kinds, each flagged where it occurs: equalities of OBJECTS
   of a category (the library puts no setoid on objects, so [=] is the only
   relation available and is the strongest possible claim); equalities in
   [nat], [nat * nat] and [list (nat * nat)]; the object component of
   [Functor_StrictEq_Setoid], which is what makes that setoid strict; and
   [two_three_mor_of_mor], whose subject [OrdMor 3] bundles a morphism of
   [Ordinal 3] -- there [≈] IS [=], since Instance/Ordinal.v installs
   [Morphism_equality] as the hom-setoid, so nothing is smuggled past the
   setoid discipline.  This remark is scoped to this file and says nothing
   about the rest of the tree.

   UNIVERSES.  This paragraph was headed “measured, not asserted” in the
   first commit and an audit then refuted two of its measurements, which is
   a fair reminder that a claim of rigour is not rigour.  What follows is
   the corrected account.

   THE CONSTRUCTIONS are free: [Point], [Walk], [One_Eval] and
   [Functor_of_Pair] all take [C : Category@{o h h}].  [Functor_of_Pair]
   produces a functor out of [_3@{u Set Set}] -- the same source profile
   Instance/Ordinal.v's own [Functor_of_Steps] and [Functor_of_Triple]
   already carry.

   THE THEOREMS ABOUT THEM ARE NOT.  Fifteen constants are stated for
   [C : Category@{o Set Set}], not the five the first commit named: besides
   [One_Const], [One_Fun_iso], [Arrow_of_Fun], [Fun_of_Arrow] and
   [Two_Fun_Arrow], the pinned set includes [point_of_Point],
   [Point_point_of_strict], [Point_point_of], [Point_equiv_iso],
   [Point_point_of_iso], [Walk_arrow_of_strict], [Walk_arrow_of],
   [Arrow_Fun_Arrow_strict], [Walk_arrow_of_iso] and
   [Functor_of_Pair_of_Functor].  Three of those are the substantive round
   trips, so it is wrong to say the correspondences are unpinned: you may
   BUILD the functors at any universe, but the round-trip theorems apply
   only at the restricted profile.

   FOR THE [_2] SIDE THE RESTRICTION IS FORCED, and that much was tested:
   Instance/Fun.v's [Fun] carries the constraint [u0 = u2], identifying the
   hom universes of source and target, and Instance/Two.v's [_2] is
   [Category@{u Set Set}] because [TwoHom] lands in [Set], so writing
   [[_2, C]] with [C : Category@{o h p}] is rejected with “Cannot enforce
   Set = h”.

   FOR THE [_1] SIDE IT IS NOT FORCED, contrary to what the first commit
   claimed.  That commit said an annotated variant had been tried and was
   rejected at [One_Const]; the audit built one that compiles end to end,
   including the strict round trip, over [Category@{u u u}] with
   [Set < u].  Note the trade rather than the strict improvement: that
   variant identifies the object and hom universes where this file's form
   identifies the hom universe with [Set], so neither statement subsumes
   the other.  The [Set] form is kept here because it is what the [_2]
   side forces and matching the two keeps the file uniform -- a deliberate
   choice, now stated as one instead of as an obstruction.

   The restriction does not empty the statements: [Two_Fun_Arrow_at_three]
   and [One_Fun_iso_at_three] instantiate both at the three-object
   ordinal.

   INSTANTIATIONS.  The three Seven Sketches items are the three concrete
   exercises of the correspondences.  Example 3.36 draws functors from the
   walking arrow into a free linear category: here the three non-identity
   morphisms [three_01], [three_12], [three_02] of [_3] give three functors
   [_2 ⟶ _3] that are proven PAIRWISE non-equivalent, and the example's
   observation that the object action already determines the functor is
   [two_three_objects_determine].  Exercise 3.37 asks for all functors
   [_2 ⟶ _3]; [two_three_enumeration] derives the count of six by
   transporting Instance/Ordinal.v's morphism count [ord_morphism_count]
   along the correspondence, rather than by writing six functors down.
   Exercise 3.45 asks for functors from the point into sets;
   [Sets_point_value] and [Sets_point_of] are the two directions at
   [Sets], and [Sets_point_separates] shows the identification is not
   degenerate by separating the empty setoid from the singleton.

--------
nLab:      https://ncatlab.org/nlab/show/terminal+category

   行走形状 (walking shapes)：终范畴、并行箭头、跨与共跨等小范畴，用作图的指标，
   使极限/余极限呈现为到这些形状的函子（Mac Lane §I.3）。本文件定义这些形状及其与
   C 中图的对应。长文首本波次压缩为导言；细节后续可续译。
*)

#[local] Obligation Tactic := idtac.

(* ---------------------------------------------------------------------- *)
(** ** Objects of C versus functors out of the point / ** 从点到函子与 C 的对象 *)
(* ---------------------------------------------------------------------- *)

(*
The functor picking out an object: everything goes to [x], the lone
   arrow of [_1] to [id].

--------
挑选对象的函子：所有东西都映射到 [x]，[_1] 到 [id] 的唯一箭头。
*)
Program Definition Point {C : Category} (x : C) : _1 ⟶ C := {|
  fobj := fun _ => x;
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

(* ... and the object it picks out. / ...以及它所指的对象。 *)
Definition point_of {C : Category} (F : _1 ⟶ C) : C := F ttt.

(*
First round trip.  This is [=] between OBJECTS, where the library offers
   no [≈]; it holds by [eq_refl], so it is near-trivial -- [Point x] was
   built to have [x] as its value.  The evidence that the pair is a
   correspondence is the other round trip, which is not.

--------
第一轮往返。这是对象之间的 [=]，库中没有提供 [≈]；它通过 [eq_refl] 成立，因此几乎是简单的——[Point x] 被构建为以 [x] 作为其值。证明这对是对应关系的证据是另一轮往返，而另一轮不是。
*)
Theorem point_of_Point {C : Category} (x : C) : point_of (Point x) = x.
Proof. reflexivity. Qed.

(*
Second round trip, at the strict functor equality: [Point (F ttt)] and
   [F] have the same object map on the nose, and their morphism maps agree.
   The lone hom of [_1] is the identity, so the content is [fmap_id].

--------
第二次来回，在严格函子相等下：[Point (F ttt)] 和 [F] 在对象映射上完全相同，并且它们的态射映射一致。[_1] 的唯一同态是恒等映射，因此内容是 [fmap_id]。
*)
Theorem Point_point_of_strict {C : Category} (F : _1 ⟶ C) :
  @equiv _ Functor_StrictEq_Setoid (Point (point_of F)) F.
Proof.
  unshelve refine (existT _ _ _).
  - intro x; destruct x; reflexivity.
  - intros x y f; destruct x, y, f; simpl.
    unfold transport, transport_r; simpl.
    symmetry; exact (@fmap_id _ _ F ttt).
Qed.

Corollary Point_point_of {C : Category} (F : _1 ⟶ C) : Point (point_of F) ≈ F.
Proof. apply strict_equiv_implies_fun_equiv, Point_point_of_strict. Qed.

(*
The correspondence is faithful in the strongest available sense: two
   objects give equivalent functors exactly when they are isomorphic.  This
   is what turns “objects of C” into “functors out of [_1]” as a statement
   about identifications, and it is the lemma the [Sets] instantiation
   below uses to separate two functors.

--------
这种对应在最强可用的意义上是忠实的：当且仅当两个对象同构时，它们才给出等价的函子。这就是将“C 的对象”转化为“从 [_1] 出发的函子”作为关于识别的陈述的原因，也是下面 [Sets] 实例化用来区分两个函子的引理。
*)
Theorem Point_equiv_iso {C : Category} (x y : C) : (Point x ≈ Point y) ↔ (x ≅ y).
Proof.
  split.
  - intros [i _]; exact (i ttt).
  - intro i; exists (fun _ => i); intros a b f; simpl.
    rewrite id_right, iso_from_to; reflexivity.
Qed.

(*
The same correspondence one level up, as functors between categories.
   [One_Eval] evaluates at the point, [One_Const] is [Point] made
   functorial.

--------
相同的对应关系在上一级，作为范畴之间的函子。[One_Eval] 在该点上求值，[One_Const] 是由 [Point] 变为函子的。
*)
Program Definition One_Eval {C : Category} : [_1, C] ⟶ C := {|
  fobj := fun F => F ttt;
  fmap := fun F G η => transform[η] ttt
|}.
Next Obligation. intros C F G η θ e; exact (e ttt). Qed.
Next Obligation. intros C F; exact (@fmap_id _ _ F ttt). Qed.
Next Obligation. intros C F G H η θ; reflexivity. Qed.

Program Definition One_Const {C : Category} : C ⟶ [_1, C] := {|
  fobj := Point;
  fmap := fun x y f => {| transform := fun _ => f |}
|}.
Next Obligation. intros C x y f a b g; now rewrite id_left, id_right. Qed.
Next Obligation. intros C x y f a b g; now rewrite id_left, id_right. Qed.
Next Obligation. intros C x y f g e a; exact e. Qed.
Next Obligation. intros C x a; reflexivity. Qed.
Next Obligation. intros C x y z f g a; reflexivity. Qed.

(*
[Point (F ttt) ≅ F] in the functor category, with identity components.
   [Point_point_of_strict] above is a different currency, an equality of
   functors; it does reach this isomorphism, but only via
   [strict_equiv_implies_fun_equiv] and then [Functor_Setoid_Nat_Iso], and
   that route hides the components.  Building the isomorphism directly
   keeps them visibly [id], which is what discharges the naturality
   obligation of [One_Fun_iso] below.

--------
在函子范畴中，[Point (F ttt) ≅ F] 具有恒等分量。上面的 [Point_point_of_strict] 是一种不同的“货币”，是函子的等式；它确实可以达到这个同构，但只能通过 [strict_equiv_implies_fun_equiv] 然后 [Functor_Setoid_Nat_Iso]，并且那条路径隐藏了分量。直接构建同构可以让它们明显地保持 [id]，这正是完成下面 [One_Fun_iso] 的自然性义务所需要的。
*)
Program Definition Point_point_of_iso {C : Category} (F : _1 ⟶ C) :
  @Isomorphism (@Fun _1 C) (Point (point_of F)) F := {|
  to   := {| transform := fun a =>
    match a as a' return Point (point_of F) a' ~> F a' with ttt => id end |};
  from := {| transform := fun a =>
    match a as a' return F a' ~> Point (point_of F) a' with ttt => id end |}
|}.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation. intros C F a; destruct a; simpl; cat. Qed.

(*
[[_1, C] ≃ C], the theorem behind Instance/One.v's header prose.  This
   is an EQUIVALENCE of categories: [≅[Cat]] in this library is [Cat]'s
   isomorphism, and [Cat]'s hom-setoid identifies functors up to natural
   isomorphism.  The [One_Eval ◯ One_Const] side is in fact strict (the
   witness below is a [Functor_StrictEq_Setoid] proof with [eq_refl]
   objects); the other side is not, for the reason the header records.

--------
[[_1, C] ≃ C]，Instance/One.v 标题部分的背后定理。这是范畴的一个等价：本库中的 [≅[Cat]] 是 [Cat] 的同构，而 [Cat] 的同态集合体将函子识别为自然同构。[One_Eval ◯ One_Const] 这一侧实际上是严格的（下面的见证是一个包含 [eq_refl] 对象的 [Functor_StrictEq_Setoid] 证明）；另一侧则不是，原因在标题中已经说明。
*)
Program Definition One_Fun_iso {C : Category} : [_1, C] ≅[Cat] C := {|
  to   := One_Eval;
  from := One_Const
|}.
Next Obligation.
  intro C.
  apply strict_equiv_implies_fun_equiv.
  unshelve refine (existT _ _ _).
  - intro x; reflexivity.
  - intros x y f; reflexivity.
Qed.
Next Obligation.
  intro C.
  exists (fun F => Point_point_of_iso F).
  intros F G η a; destruct a; simpl; now rewrite id_left, id_right.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Morphisms of C versus functors out of the walking arrow / ** C 的态射与来自行走箭头的函子 *)
(* ---------------------------------------------------------------------- *)

(*
The functor materializing a morphism: [TwoX] and [TwoY] go to its
   endpoints, [TwoXY] to the morphism itself, the two identities to [id].

--------
实现一个态射的函子：[TwoX] 和 [TwoY] 对应到它的端点，[TwoXY] 对应到态射本身，两个恒等映射对应到 [id]。
*)
Program Definition Walk {C : Category} {x y : C} (f : x ~> y) : _2 ⟶ C := {|
  fobj := fun a => match a with TwoX => x | TwoY => y end;
  fmap := fun a b (g : TwoHom a b) =>
    match g in TwoHom a' b'
      return (match a' with TwoX => x | TwoY => y end)
             ~> (match b' with TwoX => x | TwoY => y end) with
    | TwoIdX => id
    | TwoIdY => id
    | TwoXY  => f
    end
|}.
Next Obligation. intros C x y f a; destruct a; reflexivity. Qed.
Next Obligation.
  intros C x y f a b c g h.
  pose proof (TwoHom_inv _ _ g) as Hg.
  pose proof (TwoHom_inv _ _ h) as Hh.
  destruct a, b, c; simpl in *; try contradiction; subst; simpl; cat.
Qed.

(*
Instance/Two.v's [id] at [TwoX] reduces to [TwoIdX], so [fmap_id]
   applies to it up to conversion; but [TwoIdX] is not SYNTACTICALLY an
   [id], which is enough to stop [rewrite fmap_id] and [apply fmap_id].
   These two named lemmas restore the syntactic form for the rewrites
   below.

--------
Instance/Two.v 的 [id] 在 [TwoX] 下约化为 [TwoIdX]，因此 [fmap_id] 对它适用直到转换；但是 [TwoIdX] 在语法上不是 [id]，这足以阻止 [rewrite fmap_id] 和 [apply fmap_id]。这两个命名的引理恢复了下面重写的语法形式。
*)
Lemma fmap_TwoIdX {C : Category} (F : _2 ⟶ C) : fmap[F] TwoIdX ≈ id.
Proof. exact (@fmap_id _ _ F TwoX). Qed.

Lemma fmap_TwoIdY {C : Category} (F : _2 ⟶ C) : fmap[F] TwoIdY ≈ id.
Proof. exact (@fmap_id _ _ F TwoY). Qed.

(* ... and the morphism it materializes. / ... 以及它所体现的态射。 *)
Definition arrow_of {C : Category} (F : _2 ⟶ C) : F TwoX ~> F TwoY := fmap[F] TwoXY.

(*
First round trip, definitional and therefore near-trivial: [Walk f] was
   built so that [TwoXY] goes to [f], and its endpoints are already the
   endpoints of [f], so both sides even have the same type on the nose.

--------
第一轮来回，定义性的，因此几乎是简单的：[Walk f] 被构建为让 [TwoXY] 变为 [f]，并且它的端点已经是 [f] 的端点，所以双方甚至在类型上完全相同。
*)
Theorem arrow_of_Walk {C : Category} {x y : C} (f : x ~> y) : arrow_of (Walk f) ≈ f.
Proof. reflexivity. Qed.

(*
Second round trip, at the strict functor equality.  The two identity
   cases are where the content is: [Walk (arrow_of F)] sends them to [id]
   by construction, and only [fmap_id] identifies that with [fmap[F]] of
   them.  That gap -- a [≈] and not a [=] -- is where a Leibniz equality
   of the two functor records would have to be bridged, which is why the
   header does not claim one.

--------
第二次往返，在严格函子相等的情况下。两个恒等情况是内容为：[Walk (arrow_of F)] 通过构造将它们发送到 [id]，而只有 [fmap_id] 将它们与 [fmap[F] 识别为相同。那个差距——一个 [≈] 而不是 [=]——正是两个函子记录的莱布尼茨相等必须被弥合的地方，这就是为什么标题没有声明相等的原因。
*)
Theorem Walk_arrow_of_strict {C : Category} (F : _2 ⟶ C) :
  @equiv _ Functor_StrictEq_Setoid (Walk (arrow_of F)) F.
Proof.
  unshelve refine (existT _ _ _).
  - intro a; destruct a; reflexivity.
  - intros a b g; destruct g; simpl; unfold transport, transport_r; simpl.
    + symmetry; apply fmap_TwoIdX.
    + symmetry; apply fmap_TwoIdY.
    + reflexivity.
Qed.

Corollary Walk_arrow_of {C : Category} (F : _2 ⟶ C) : Walk (arrow_of F) ≈ F.
Proof. apply strict_equiv_implies_fun_equiv, Walk_arrow_of_strict. Qed.

(*
The object action of [Walk f] does not see [f] at all: parallel
   morphisms give functors with literally the same action on objects.
   This lemma is trivially true -- it is [eq_refl] in both cases -- and it
   is stated only as the negative half of a pair: [Walk_objects_insufficient]
   below exhibits a concrete target where two functors out of [_2] agree on
   objects and are separated by [arrow_of], so the determination theorem
   [two_three_objects_determine] proven for the target [_3] is a fact about
   that target and not about functors out of [_2] in general.

--------
[Walk f] 的对象作用完全不考虑 [f]：平行态射提供带有在对象上字面相同作用的函子。这个引理显然成立——在两种情况下都是 [eq_refl]——并且它只作为一对中的否定部分陈述：下面的 [Walk_objects_insufficient] 展示了一个具体的目标，在该目标中来自 [_2] 的两个函子在对象上相同，但被 [arrow_of] 分开，因此对目标 [_3] 证明的判定定理 [two_three_objects_determine] 是关于该目标的事实，而不是关于来自 [_2] 的函子的一般性事实。
*)
Theorem Walk_objects_agree {C : Category} {x y : C} (f g : x ~> y) :
  ∀ a, Walk f a = Walk g a.
Proof. intro a; destruct a; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** ** The comparison [_2, C] versus the arrow category / ** [_2, C] 与箭头范畴的比较 *)
(* ---------------------------------------------------------------------- *)

(*
A functor out of [_2] gives the object of [Arrow C] that its generating
   arrow names; a natural transformation gives the commuting square, which
   is precisely its naturality at [TwoXY].

--------
从 [_2] 出发的函子给出 [Arrow C] 的对象，该对象由其生成箭头命名；自然变换给出交换图，这正是其在 [TwoXY] 上的自然性。
*)
Program Definition Arrow_of_Fun {C : Category} : [_2, C] ⟶ @Arrow C := {|
  fobj := fun F => ((F TwoX, F TwoY); fmap[F] TwoXY);
  fmap := fun F G η => ((transform[η] TwoX, transform[η] TwoY); _)
|}.
Next Obligation. intros C F G η; simpl; apply naturality. Qed.
Next Obligation.
  intros C F G η θ e; split; simpl; [ exact (e TwoX) | exact (e TwoY) ].
Qed.
Next Obligation. intros C F; split; simpl; [ apply fmap_TwoIdX | apply fmap_TwoIdY ]. Qed.
Next Obligation. intros C F G H η θ; split; simpl; reflexivity. Qed.

(*
Conversely an object of [Arrow C] is a morphism, hence a [Walk], and a
   commuting square is a natural transformation between the two [Walk]s:
   naturality at the two identities is unit laws, and at [TwoXY] it is the
   square itself.

--------
相反，[Arrow C] 的一个对象是一个态射，因此是一个 [Walk]，而一个交换方格是在两个 [Walk] 之间的一个自然变换：在两个恒等上的自然性是单位律，在 [TwoXY] 上就是方格本身。
*)
Program Definition Fun_of_Arrow {C : Category} : @Arrow C ⟶ [_2, C] := {|
  fobj := fun x => Walk (`2 x);
  fmap := fun x y u =>
    {| transform := fun a =>
         match a as a' return Walk (`2 x) a' ~> Walk (`2 y) a' with
         | TwoX => fst (`1 u)
         | TwoY => snd (`1 u)
         end |}
|}.
Next Obligation.
  intros C x y u a b f; destruct f; simpl;
    try (now rewrite id_left, id_right).
  exact (`2 u).
Qed.
Next Obligation.
  intros C x y u a b f; destruct f; simpl;
    try (now rewrite id_left, id_right).
  symmetry; exact (`2 u).
Qed.
Next Obligation. intros C x y u v [H1 H2] a; destruct a; simpl; assumption. Qed.
Next Obligation. intros C x a; destruct a; reflexivity. Qed.
Next Obligation. intros C x y z f g a; destruct a; reflexivity. Qed.

(*
The strict half of the comparison: going Arrow C -> [_2, C] -> Arrow C
   returns the object one started from, on the nose.  The object equality
   needs the pair of the comma object destructured, which is why the proof
   opens with a pattern rather than [eq_refl]; the morphism component is
   then reflexivity in both legs of the commuting square.

--------
比较的严格一半：从 Arrow C -> [_2, C] -> Arrow C 返回最初的对象，准确无误。对象相等性需要对逗号对象进行解构，这就是为什么证明以一个模式而不是 [eq_refl] 开始；然后同态分量在换位方格的两个边上都是自反性。
*)
Theorem Arrow_Fun_Arrow_strict {C : Category} :
  @equiv _ Functor_StrictEq_Setoid (Arrow_of_Fun ◯ Fun_of_Arrow) (Id[@Arrow C]).
Proof.
  unshelve refine (existT _ _ _).
  - intros [[a b] h]; reflexivity.
  - intros [[a b] h] [[a' b'] h'] u; simpl.
    unfold transport, transport_r; simpl.
    split; reflexivity.
Qed.

(*
The other half, as a natural isomorphism in [[_2, C]].  Its components
   are identities, which is the sense in which the two functors differ only
   in how they present [fmap] at the two identity arrows of [_2]; the
   naturality obligations below consume exactly that.

--------
另一半，作为 [[_2, C] 中的自然同构。它的组成部分是恒等式，这就是两个函子仅在如何在 [_2] 的两个恒等箭头上呈现 [fmap] 上有所不同的意义；下面的自然性约束正好消耗了这一点。
*)
Program Definition Walk_arrow_of_iso {C : Category} (F : _2 ⟶ C) :
  @Isomorphism (@Fun _2 C) (Walk (arrow_of F)) F := {|
  to   := {| transform := fun a =>
    match a as a' return Walk (arrow_of F) a' ~> F a' with
    | TwoX => id
    | TwoY => id
    end |};
  from := {| transform := fun a =>
    match a as a' return F a' ~> Walk (arrow_of F) a' with
    | TwoX => id
    | TwoY => id
    end |}
|}.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.

(*
The comparison Construction/Arrow.v left open.  [≅[Cat]] is an
   EQUIVALENCE of categories, not an isomorphism of categories -- see the
   header for exactly which of the two round trips is strict and why the
   other one cannot be.

--------
比较 Construction/Arrow.v 保持打开。[≅[Cat]] 是范畴的等价，而不是范畴的同构——参见头部，了解哪一个往返是严格的，以及为什么另一个不能是严格的。
*)
Program Definition Two_Fun_Arrow {C : Category} : [_2, C] ≅[Cat] @Arrow C := {|
  to   := Arrow_of_Fun;
  from := Fun_of_Arrow
|}.
Next Obligation.
  intro C.
  apply strict_equiv_implies_fun_equiv, Arrow_Fun_Arrow_strict.
Qed.
Next Obligation.
  intro C.
  exists (fun F => Walk_arrow_of_iso F).
  intros F G η a; destruct a; simpl; now rewrite id_left, id_right.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Composable pairs versus functors out of the ordinal 3 / ** 从序数3的可组合对与函子 *)
(* ---------------------------------------------------------------------- *)

(*
The two generating steps of [_3] are [ord_step] at the two objects of
   [Ordinal 2]; their endpoints are Instance/Ordinal.v's [ord3_0],
   [ord3_1], [ord3_2] definitionally, which is what lets the types below be
   written without transports.

--------
[_3] 的两个生成步骤是 [ord_step]，在 [Ordinal 2] 的两个对象上；它们的端点在定义上是 Instance/Ordinal.v 的 [ord3_0]、[ord3_1]、[ord3_2]，这就是让下面的类型可以在不使用迁移的情况下书写的原因。
*)
Definition ord2_0 : Ord_obj 2 := ord_at 0%nat (le_t_S le_t_n).
Definition ord2_1 : Ord_obj 2 := ord_at 1%nat le_t_n.

Definition three_01 : ord3_0 ~{_3}~> ord3_1 := ord_step ord2_0.
Definition three_12 : ord3_1 ~{_3}~> ord3_2 := ord_step ord2_1.
Definition three_02 : ord3_0 ~{_3}~> ord3_2 := three_12 ∘ three_01.

(*
The object assignment of a composable pair, read off an index.  It is
   total on [nat] because Instance/Ordinal.v's [OrdSteps] is; the values
   past 2 are never consulted.

--------
可组合对的对象赋值，从索引读取。它在 [nat] 上是全局的，因为 Instance/Ordinal.v 的 [OrdSteps] 是全局的；超过 2 的值从未被使用。
*)
Definition pair_obj {C : Category} (x y z : C) : nat → C :=
  fun k => match k with O => x | S O => y | _ => z end.

Definition pair_steps {C : Category} (X : nat → C)
  (f : X 0%nat ~> X 1%nat) (g : X 1%nat ~> X 2%nat) : OrdSteps 2 X :=
  fun k =>
    match k as k0 return le_t (S k0) 2 → X k0 ~> X (S k0) with
    | O        => fun _ => f
    | S O      => fun _ => g
    | S (S k') => fun H =>
        False_rect _ (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H)))
    end.

(*
A composable pair gives a diagram of shape 3.  This is
   Instance/Ordinal.v's [Functor_of_Steps] at n = 2, the case one below its
   [Functor_of_Triple].

--------
一个可组合对给出了形状为3的图。这是Instance/Ordinal.v中的[Functor_of_Steps]，当n = 2时，即它的[Functor_of_Triple]下一种情况。
*)
Definition Functor_of_Pair {C : Category} {x y z : C}
  (f : x ~> y) (g : y ~> z) : _3 ⟶ C :=
  Functor_of_Steps (pair_steps (pair_obj x y z) f g).

Theorem Functor_of_Pair_fst {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_01 ≈ f.
Proof. exact (Functor_of_Steps_step (pair_steps (pair_obj x y z) f g) ord2_0). Qed.

Theorem Functor_of_Pair_snd {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_12 ≈ g.
Proof. exact (Functor_of_Steps_step (pair_steps (pair_obj x y z) f g) ord2_1). Qed.

(*
[_3] has six arrows: three identities, the two generating steps, and
   [three_02].  That last one goes to the composite -- which is the sense
   in which a functor out of [_3] is a COMPOSABLE pair and not two
   unrelated arrows.

--------
[_3] 有六个箭头：三个恒等箭头、两个生成步骤，以及 [three_02]。最后一个箭头指向复合体——这就是从 [_3] 出发的函子是一个可组合对，而不是两个不相关的箭头的意义所在。
*)
Theorem Functor_of_Pair_comp {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_02 ≈ g ∘ f.
Proof.
  unfold three_02.
  rewrite fmap_comp, Functor_of_Pair_fst, Functor_of_Pair_snd.
  reflexivity.
Qed.

(* ... and the composable pair a diagram of shape 3 carries. / ... 可组合对携带的形状为3的图表。 *)
Definition pair_fst {C : Category} (F : _3 ⟶ C) : F ord3_0 ~> F ord3_1 :=
  fmap[F] three_01.
Definition pair_snd {C : Category} (F : _3 ⟶ C) : F ord3_1 ~> F ord3_2 :=
  fmap[F] three_12.

(*
The comparison isomorphism at each object of [_3].  An object is one of
   the three, so the three named ones are hit; the fourth branch is the
   out-of-range index, ruled out by the bound.

--------
在 [_3] 的每个对象上的比较同构。一个对象是三个中的一个，所以三个命名的对象都被命中；第四个分支是超出范围的索引，已被边界排除。
*)
Definition pair_theta {C : Category} (F : _3 ⟶ C) (w : Ord_obj 3) :
  Functor_of_Pair (pair_fst F) (pair_snd F) w ≅ F w.
Proof.
  destruct w as [i H]; destruct i as [| [| [| i]]].
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_0 (ord_at 0%nat H) eq_refl)).
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_1 (ord_at 1%nat H) eq_refl)).
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_2 (ord_at 2%nat H) eq_refl)).
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Defined.

(*
The substantive round trip: every diagram of shape 3 is the one built
   from its own composable pair.  The comparison is at [Functor_Setoid],
   the same strength Instance/Ordinal.v's [Functor_of_Steps_of_Functor]
   delivers for the general shape, and unlike the [_1] and [_2] cases it is
   not also given at [Functor_StrictEq_Setoid].  The reason it is not
   ATTEMPTED here: the object part of the built functor is [pair_obj] read
   off an index, which agrees with [F] only after an object of [_3] has
   been identified with one of the three named ones, and the identification
   [ord_obj_eq] supplies is [Qed]-opaque rather than [eq_refl], so the
   transports in the strict setoid do not reduce away.  Whether the strict
   form nonetheless holds is left open, not settled.
   Naturality itself need only be checked on the two generating steps, by
   Instance/Ordinal.v's [ord_functor_equiv_from_steps].

--------
实质性往返：每个形状为3的图都是由其自身的可组合对构建的。比较在[Functor_Setoid]处进行，它具有Instance/Ordinal.v的[Functor_of_Steps_of_Functor]为一般形状提供的相同强度，并且与[_1]和[_2]的情况不同，它并未在[Functor_StrictEq_Setoid]处给出。未在此尝试的原因：构建函子（functor）的对象部分是从索引读取的[pair_obj]，仅在将[_3]的某个对象与三个命名对象之一进行识别后，才与[F]一致，而[ord_obj_eq]提供的识别是[Qed]不透明的，而非[eq_refl]，因此严格集合中传输不会消失。严格形式是否仍然成立尚未确定，保持开放状态。自然性本身只需在两个生成步骤上检查，由Instance/Ordinal.v的[ord_functor_equiv_from_steps]提供。
*)
Theorem Functor_of_Pair_of_Functor {C : Category} (F : _3 ⟶ C) :
  Functor_of_Pair (pair_fst F) (pair_snd F) ≈ F.
Proof.
  apply (ord_functor_equiv_from_steps _ F (pair_theta F)).
  intros [i H]; destruct i as [| [| i]]; simpl.
  - rewrite (Functor_of_Steps_step
               (pair_steps (pair_obj (F ord3_0) (F ord3_1) (F ord3_2))
                           (pair_fst F) (pair_snd F)) (ord_at 0%nat H)).
    simpl.
    unfold pair_fst, three_01.
    rewrite <- !fmap_comp.
    apply fmap_respects, le_t_irr.
  - rewrite (Functor_of_Steps_step
               (pair_steps (pair_obj (F ord3_0) (F ord3_1) (F ord3_2))
                           (pair_fst F) (pair_snd F)) (ord_at 1%nat H)).
    simpl.
    unfold pair_snd, three_12.
    rewrite <- !fmap_comp.
    apply fmap_respects, le_t_irr.
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H))).
Qed.

(*
The list vocabulary ([In], [NoDup], [length]) and [lia] are used from
   here on.  Instance/Ordinal.v requires the same two standard-library
   modules, under the same spelling, and for the same reason: the closed
   morphism count this section transports lives there.

--------
从这里开始使用列表词汇 ([In]、[NoDup]、[length]) 和 [lia]。Instance/Ordinal.v 需要相同的两个标准库模块，拼写相同，原因也相同：本节所传输的闭合态射计数在那里生效。
*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.2, Example 3.36: the correspondence at [_3] / ** 七个草图 §3.3.2，例子 3.36：在 [_3] 的对应 *)
(* ---------------------------------------------------------------------- *)

(*
[_3] has exactly three non-identity morphisms, and the [_2]-correspondence
   turns each into a functor [_2 ⟶ _3].  These are the three the example
   draws.

--------
[_3] 恰好有三个非同一态态射，[_2] 对应将每一个变为一个函子 [_2 ⟶ _3]。这就是例子中画出的三个。
*)
Definition Two_Three_01 : _2 ⟶ _3 := Walk three_01.
Definition Two_Three_12 : _2 ⟶ _3 := Walk three_12.
Definition Two_Three_02 : _2 ⟶ _3 := Walk three_02.

(*
Their object actions, computed.  These are [=] between objects, by
   [eq_refl]; they are near-trivial individually and are recorded because
   together they are what distinguishes the three functors.

--------
它们的对象动作，已计算。这些是在对象之间，由 [eq_refl] 执行的 [=]；它们单独来看近乎平凡，并且被记录下来，因为它们合在一起构成了区分这三个函子（functor）的特征。
*)
Example Two_Three_01_dom : Two_Three_01 TwoX = ord3_0 := eq_refl.
Example Two_Three_01_cod : Two_Three_01 TwoY = ord3_1 := eq_refl.
Example Two_Three_12_dom : Two_Three_12 TwoX = ord3_1 := eq_refl.
Example Two_Three_12_cod : Two_Three_12 TwoY = ord3_2 := eq_refl.
Example Two_Three_02_dom : Two_Three_02 TwoX = ord3_0 := eq_refl.
Example Two_Three_02_cod : Two_Three_02 TwoY = ord3_2 := eq_refl.

(*
The correspondence exercised on this concrete target: each functor gives
   back the morphism it came from.

--------
在这个具体目标上施加的对应关系：每个函子都会返回它所来源的态射。
*)
Corollary Two_Three_01_arrow : arrow_of Two_Three_01 ≈ three_01.
Proof. exact (arrow_of_Walk three_01). Qed.
Corollary Two_Three_12_arrow : arrow_of Two_Three_12 ≈ three_12.
Proof. exact (arrow_of_Walk three_12). Qed.
Corollary Two_Three_02_arrow : arrow_of Two_Three_02 ≈ three_02.
Proof. exact (arrow_of_Walk three_02). Qed.

(*
The two category-level comparisons instantiated at this same target,
   which is neither empty nor the point: [_3] has three objects and six
   morphisms, as the enumeration below records.  These also witness that
   the universe restriction disclosed in the header leaves both statements
   inhabited.

--------
在同一个目标上实例化的两个范畴级比较，该目标既非空也非点：[_3] 有三个对象和六个态射，如下列枚举所记录的。这些也证明了标题中披露的宇宙限制使得两个陈述都有实例。
*)
Example Two_Fun_Arrow_at_three : [_2, _3] ≅[Cat] @Arrow _3 := Two_Fun_Arrow.
Example One_Fun_iso_at_three : [_1, _3] ≅[Cat] _3 := One_Fun_iso.

(*
In an ordinal, isomorphic objects have equal indices: the two legs give
   inequalities in both directions.

--------
在序数中，同构对象具有相等的指标：这两条腿在两个方向上给出不等式。
*)
Lemma ord_iso_val {n} {x y : Ord_obj n} (i : @Isomorphism (Ordinal n) x y) :
  ord_val x = ord_val y.
Proof.
  pose proof (le_t_to_le (to i)) as H1.
  pose proof (le_t_to_le (from i)) as H2.
  simpl in *; lia.
Qed.

(*
Non-vacuity of Example 3.36: the three functors are pairwise
   non-equivalent -- not merely distinct as terms, but not naturally
   isomorphic, since a natural isomorphism would force equal indices at an
   object where they differ.  So the correspondence really does separate
   the three morphisms of [_3] it came from.

--------
示例 3.36 的非空性：这三个函子是两两非等价的——不仅仅是作为项不同，而是没有自然同构，因为自然同构会在它们不同的对象处强制相等的指标。因此，这种对应确实区分了它所来自的 [_3] 的三个态射。
*)
Theorem Two_Three_01_12 : (Two_Three_01 ≈ Two_Three_12) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoX)) as E; discriminate. Qed.

Theorem Two_Three_01_02 : (Two_Three_01 ≈ Two_Three_02) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoY)) as E; discriminate. Qed.

Theorem Two_Three_12_02 : (Two_Three_12 ≈ Two_Three_02) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoX)) as E; discriminate. Qed.

(*
The example's own observation: over this target the object action
   already determines the functor.  The proof consumes thinness of [_3] and
   nothing else -- the two transported morphism actions are parallel arrows
   of [Ordinal 3], and [le_t_irr] says there is at most one such.  The
   other way round has been checked rather than assumed:
   [Walk_objects_insufficient] below exhibits two functors [_2 ⟶ Sets] with
   literally the same object action that [arrow_of] separates, so agreement
   on objects carries no arrow information in general.  This theorem is
   therefore a fact about the thin target, not about functors out of
   [_2].

--------
该示例自身的观察：在这个目标上，宾语的动作已经决定了函子。证明只消耗了 [_3] 的单薄性，而没有其他——两个被传输的态射动作是 [Ordinal 3] 的平行箭头，且 [le_t_irr] 表明最多只有一个这样的。相反的情况已经被检查过，而不是假设的：下面的 [Walk_objects_insufficient] 展示了两个函子 [_2 ⟶ Sets]，它们具有完全相同的宾语动作，而 [arrow_of] 将它们区分开，因此在一般情况下，对宾语的一致性并不携带箭头信息。因此，这一定理是关于单薄目标的事实，而不是关于来自 [_2] 的函子。
*)
Theorem two_three_objects_determine (F G : _2 ⟶ _3) (H : ∀ a, F a = G a) :
  @equiv _ Functor_StrictEq_Setoid F G.
Proof. exists H; intros a b f; apply le_t_irr. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.2, Exercise 3.37: there are exactly six / ** 七个素描 §3.3.2，练习3.37：恰好有六个 *)
(* ---------------------------------------------------------------------- *)

(*
The correspondence, packaged at the total space of morphisms of [_3].
   [OrdMor 3] bundles a morphism with its endpoints, which is exactly the
   data a functor out of [_2] carries.

--------
该对应关系被打包在 [_3] 的态射总空间中。[OrdMor 3] 将一个态射与其端点捆绑在一起，这正是来自 [_2] 的函子所携带的数据。
*)
Definition two_three_mor (F : _2 ⟶ _3) : OrdMor 3 :=
  existT _ (F TwoX) (existT _ (F TwoY) (fmap[F] TwoXY)).

Definition mor_two_three (m : OrdMor 3) : _2 ⟶ _3 := Walk (projT2 (projT2 m)).

(*
Near-trivial by destructuring: [Walk] stores its argument verbatim.  The
   [=] here reaches a morphism, but of [Ordinal 3], whose hom-setoid IS
   [Morphism_equality]; [≈] and [=] coincide there.

--------
通过解构几乎是平凡的：[Walk] 原样存储其参数。这里的 [=] 达到了一个态射，但属于 [Ordinal 3]，其同态集是 [Morphism_equality]；[≈] 和 [=] 在此处相同。
*)
Theorem two_three_mor_of_mor (m : OrdMor 3) : two_three_mor (mor_two_three m) = m.
Proof. destruct m as [a [b h]]; reflexivity. Qed.

Theorem mor_of_two_three_mor (F : _2 ⟶ _3) :
  @equiv _ Functor_StrictEq_Setoid (mor_two_three (two_three_mor F)) F.
Proof. exact (Walk_arrow_of_strict F). Qed.

(*
A functor [_2 ⟶ _3] read as a pair of indices, THROUGH the
   correspondence: [ord_coords] is Instance/Ordinal.v's coordinate map on
   morphisms, and [two_three_mor] is the correspondence.

--------
函子 [_2 ⟶ _3] 被读取为一对索引，通过对应关系：[ord_coords] 是 Instance/Ordinal.v 上关于态射的坐标映射，[two_three_mor] 是该对应关系。
*)
Definition two_three_coords (F : _2 ⟶ _3) : (nat * nat)%type :=
  ord_coords (two_three_mor F).

Definition two_three_index : list (nat * nat) := ord_pairs 3.

(*
The count.  It is DERIVED, from Instance/Ordinal.v's closed formula
   [ord_morphism_count n : 2 * length (ord_pairs n) = n * (n + 1)] at
   n = 3, and not from writing six functors down or from computing a
   numeral: [lia] halves 3 * 4.

--------
计数。它是从 Instance/Ordinal.v 的闭式公式派生的 [ord_morphism_count n : 2 * length (ord_pairs n) = n * (n + 1)] 在 n = 3 时，而不是通过写下六个函子或计算一个数字：[lia] 将 3 * 4 对半分。
*)
Theorem two_three_count : (length two_three_index = 6)%nat.
Proof. pose proof (ord_morphism_count 3) as H; unfold two_three_index; lia. Qed.

Theorem two_three_nodup : NoDup two_three_index.
Proof. exact (ord_pairs_nodup 3). Qed.

Theorem two_three_coords_in (F : _2 ⟶ _3) : In (two_three_coords F) two_three_index.
Proof. exact (ord_coords_in_pairs (two_three_mor F)). Qed.

(*
Distinct indices are the only way two of these functors can differ:
   equal coordinates force strict equality of the functors, by transporting
   Instance/Ordinal.v's [ord_coords_inj] along the correspondence.

--------
不同的指标是这两个函子可能不同的唯一方式：相等的坐标通过沿着对应关系传输 Instance/Ordinal.v 的 [ord_coords_inj] 强制函子严格相等。
*)
Theorem two_three_coords_faithful (F G : _2 ⟶ _3) :
  two_three_coords F = two_three_coords G →
  @equiv _ Functor_StrictEq_Setoid F G.
Proof.
  intro E.
  pose proof (ord_coords_inj (two_three_mor F) (two_three_mor G) E) as Em.
  pose proof (mor_of_two_three_mor F) as H1.
  pose proof (mor_of_two_three_mor G) as H2.
  rewrite Em in H1.
  exact (Equivalence_Transitive _ _ _ (Equivalence_Symmetric _ _ H1) H2).
Qed.

(*
... and every admissible pair of indices is realized, one functor per
   pair i ≤ j < 3.

--------
... 并且每一个可接受的索引对都被实现，每一对 i ≤ j < 3 对应一个函子。
*)
Theorem two_three_coords_onto (i j : nat) (Hij : (i <= j)%nat) (Hj : (j < 3)%nat) :
  { F : _2 ⟶ _3 & two_three_coords F = (i, j) }.
Proof.
  destruct (ord_mor_of_pair i j Hij Hj) as [m Em].
  exists (mor_two_three m).
  unfold two_three_coords.
  now rewrite two_three_mor_of_mor.
Qed.

(* The index list is exactly the pairs i ≤ j < 3. / 索引列表正好是满足 i ≤ j < 3 的所有对。 *)
Theorem two_three_index_char (i j : nat) :
  In (i, j) two_three_index ↔ ((i <= j)%nat ∧ (j < 3)%nat).
Proof.
  split.
  - intro H; destruct (ord_pairs_sound 3 i j H) as [H1 H2]; exact (H1, H2).
  - intros [H1 H2]; exact (ord_pairs_complete 3 i j H1 H2).
Qed.

(*
Exercise 3.37, assembled: the functors [_2 ⟶ _3] are classified, up to
   strict functor equality, by a duplicate-free list of SIX index pairs,
   one per i ≤ j.

--------
练习 3.37，汇总：函子 [_2 ⟶ _3] 被归类为，直到严格的函子相等，由一个无重复的六个索引对列表组成，每个 i ≤ j 对应一个索引对。
*)
Theorem two_three_enumeration :
  ((length two_three_index = 6)%nat *
   NoDup two_three_index *
   (∀ F : _2 ⟶ _3, In (two_three_coords F) two_three_index) *
   (∀ i j, (i <= j)%nat → (j < 3)%nat →
      { F : _2 ⟶ _3 & two_three_coords F = (i, j) }) *
   (∀ F G : _2 ⟶ _3, two_three_coords F = two_three_coords G →
      @equiv _ Functor_StrictEq_Setoid F G))%type.
Proof.
  exact (two_three_count, two_three_nodup, two_three_coords_in,
         two_three_coords_onto, two_three_coords_faithful).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.3, Exercise 3.45: the point into [Sets] / ** 七个素描 §3.3.3，练习 3.45：点进入 [Sets] *)
(* ---------------------------------------------------------------------- *)

(* Two small setoids used only as witnesses below. / 两个小集合只在下面用作证据。 *)
Definition empty_setoid_object : SetoidObject :=
  {| carrier := False; is_setoid := eq_Setoid False |}.

Definition two_setoid_object : SetoidObject :=
  {| carrier := TwoObj; is_setoid := eq_Setoid TwoObj |}.

Program Definition const_TwoX : two_setoid_object ~{Sets}~> two_setoid_object := {|
  morphism := fun _ => TwoX
|}.

(*
The tested converse promised at [Walk_objects_agree] and at
   [two_three_objects_determine]: over [Sets] the identity and a constant
   map on a two-element setoid give two functors out of [_2] with the SAME
   object action, which [arrow_of] separates.  So the object action does
   not determine a functor out of [_2] in general, and the determination
   theorem above is a fact about the thin target [_3].

--------
在 [Walk_objects_agree] 和 [two_three_objects_determine] 上测试的逆命题：在 [Sets] 上，恒等映射和一个两元素集合的恒定映射给出了从 [_2] 出发的两个函子，它们具有相同的对象作用，但 [arrow_of] 可以将它们区分开。因此，一般来说，对象作用并不能确定一个从 [_2] 出发的函子，上述确定性定理是关于薄目标 [_3] 的事实。
*)
Theorem Walk_objects_insufficient :
  ((∀ a, Walk (@id Sets two_setoid_object) a = Walk const_TwoX a) *
   ((arrow_of (Walk (@id Sets two_setoid_object)) ≈ arrow_of (Walk const_TwoX))
      → False))%type.
Proof.
  split.
  - apply Walk_objects_agree.
  - intro H.
    pose proof (H TwoY) as E; simpl in E.
    discriminate.
Qed.

(*
Exercise 3.45, the constructive direction: for every setoid S there is a
   functor from the point whose value at the point is S.  [=] between
   objects again, and near-trivial -- [Point S] was built for it -- but it
   is precisely the statement the exercise asks for.

--------
练习 3.45，构造方向：对于每一个集合同构 S，存在一个从单点出发的函子，其在该点的值为 S。对象之间再次使用 [=]，几乎平凡——[Point S] 为此构建——但这正是练习要求的陈述。
*)
Theorem Sets_point_value (S : Sets) : Point S ttt = S.
Proof. reflexivity. Qed.

(* ... and the round trip back. / ...以及往返行程。 *)
Corollary Sets_point_of (F : _1 ⟶ Sets) : Point (point_of F) ≈ F.
Proof. exact (Point_point_of F). Qed.

(*
The identification is at the right granularity: two setoids give
   equivalent functors from the point exactly when they are isomorphic in
   [Sets].

--------
该识别具有正确的粒度：当且仅当两个集合型在 [Sets] 中同构时，它们从点出发给出的函子是等价的。
*)
Corollary Sets_point_iso (S T : Sets) :
  (Point S ≈ Point T) ↔ (S ≅[Sets] T).
Proof. exact (Point_equiv_iso S T). Qed.

(*
Non-vacuity of the [Sets] instantiation, with a witness that escapes the
   degenerate case: the empty setoid and the singleton give NON-equivalent
   functors from the point.  The inverse leg of a hypothetical isomorphism
   would send [ttt] to an inhabitant of [False].

--------
[Sets] 实例化的非空性，带有一个能逃避退化情况的证据：空集合化和单元素集合化给出从点出发的不等价函子。假设同构的逆边会将 [ttt] 发送到 [False] 的一个元素。
*)
Theorem Sets_point_separates :
  (Point (C:=Sets) empty_setoid_object ≈ Point (C:=Sets) unit_setoid_object)
    → False.
Proof.
  intro H.
  destruct (fst (Point_equiv_iso _ _) H) as [f g _ _].
  exact (g ttt).
Qed.
