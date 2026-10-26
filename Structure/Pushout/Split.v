Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.

Generalizable All Variables.

(* * * When a pushout injection splits / * * 当一个推出注入分裂时 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Pushout_(category_theory)

 Three lines of generic category theory, factored out of
 Instance/Grp/Pushout.v because nothing in them is about groups.

 THE OBSERVATION.  For a span [y <-f- x -g-> z] with pushout apex [P],
 the first injection [i1 : y ~> P] SPLITS as soon as [f] factors through
 [g] — that is, as soon as there is [r : z ~> y] with [r ∘ g ≈ f].
 Feed the competing cocone [(id[y], r)] to the universal property: its
 commutation obligation [id ∘ f ≈ r ∘ g] is exactly the factorization,
 and the mediator [u] it produces satisfies [u ∘ i1 ≈ id].  So [i1] is a
 section, hence monic by Theory/Morphisms.v's [sections_are_monic].

 WHY THIS IS WORTH NAMING.  It is the constructively cheap fragment of
 the classical refinement “if both legs of the span are monic then both
 pushout injections are monic”.  That refinement in full is, for groups,
 the Schreier normal-form theorem for amalgamated free products, whose
 usual proof (van der Waerden's trick) chooses coset transversals; the
 split fragment below needs no normal form, no transversal and no choice
 principle, and it is available in EVERY category with the relevant
 pushout.  Instance/Grp/Pushout.v discusses the gap in detail.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  [pushout_in1_Section] and
 [pushout_in2_Section] produce a [Theory/Morphisms.v] [Section]
 instance — a genuine retraction, exhibited, not merely the existence of
 one — and [pushout_in1_Monic] / [pushout_in2_Monic] read off monicity.
 [pushout_in1_Section_of_Retraction] is the corollary a reader of the
 classical statement wants: if [g] is a SPLIT monomorphism then [i1]
 splits, because [f] then factors through [g] via [f ∘ retraction].
 The retraction produced is [pushout_med] applied to the cocone
 [(id, r)], so it is the mediator of the universal property and not a
 second construction.

 WHAT IS NOT DELIVERED.  Nothing about pushouts along merely monic
 legs; no van Kampen / effective-descent property; no claim that the
 splitting hypothesis is NECESSARY for the injection to be monic (it is
 not — in Grp the injections are monic whenever the legs are, by
 Schreier, and that is exactly the theorem this file does not reach).
 No dual file for pullbacks: the [C^op] instance of these statements is
 available by instantiation but is not spelled out. 

 --------
 nLab:       https://ncatlab.org/nlab/show/pushout 
 维基百科:  https://en.wikipedia.org/wiki/Pushout_(category_theory) 

 三行通用范畴论内容，从 Instance/Grp/Pushout.v 中拆分出来，因为里面没有关于群的内容。

 观察。对于一个跨度 [y <-f- x -g-> z]，其推挤顶点为 [P] ，只要 [f] 通过 [g] 分解，第一注入 [i1 : y ~> P] 就会分裂——也就是说，只要存在 [r : z ~> y] 且 [r ∘ g ≈ f] 。将竞争余锥 [(id[y] , r)] 输入到泛性质：它的交换义务 [id ∘ f ≈ r ∘ g] 正是该分解，而它产生的中介 [u] 满足 [u ∘ i1 ≈ id] 。因此 [i1] 是一个截面，从而根据 Theory/Morphisms.v 的 [sections_are_monic] 是单射。为什么这值得命名。它是经典细化的一个构造上廉价的片段——“如果跨距的两条腿都是单射，那么两个推出注入都是单射”。完整的细化在群的情况下是用于合并自由积的施赖尔正规形式定理，其通常证明（范德瓦尔登的技巧）选择陪集横截面；下面的分裂片段不需要正规形式、不需要横截面，也不需要选择公理，并且在具有相关推出的每个范畴中都可用。Instance/Grp/Pushout.v 详细讨论了这个间隙。已证明的内容及其强度。[pushout_in1_Section] 和 [pushout_in2_Section] 产生了一个 [Theory/Morphisms.v] [Section] 实例——一个真正的收缩映射，被展示出来，而不仅仅是其存在——且 [pushout_in1_Monic] / [pushout_in2_Monic] 显示单射性。[pushout_in1_Section_of_Retraction] 是读者想要的经典陈述的推论：如果 [g] 是一个可分单态映射，则 [i1] 可分，因为 [f] 然后通过 [g] 经过 [f ∘ retraction] 因子化。所产生的收缩映射是 [pushout_med] 作用于余锥 [(id, r)]，因此它是泛性质的中介，而不是第二次构造。未提供的内容。没有关于仅沿单射腿的推挤；没有van Kampen / 有效下降性质；没有声称分裂假设对于单射为单射是必要的（它不是 — 在Grp中，只要腿是单射，注入就是单射，由Schreier定理，这是该文件未达到的确切定理）。没有关于拉回的对偶文件：这些陈述的[C^op]实例可以通过实例化获得，但未明确说明。
*)

Section PushoutSplit.

Context {C : Category}.
Context {x y z : C}.
Context {f : x ~> y} {g : x ~> z}.
Context (P : IsPushout f g).

(** ** The first injection / ** 第一次注射 *)

(* If [f] factors through [g], the cocone [(id[y], r)] commutes, so the pushout hands back a retraction of [pushout_in1]. / 如果 [f] 通过 [g] 分解，余锥 [(id[y], r) 就会交换，因此推出图会返回 [pushout_in1] 的一个回撤。 *)
Lemma pushout_in1_factor_commutes (r : z ~> y) (Hr : r ∘ g ≈ f) :
  id[y] ∘ f ≈ r ∘ g.
Proof.
  rewrite id_left.
  symmetry.
  exact Hr.
Qed.

Definition pushout_in1_retract (r : z ~> y) (Hr : r ∘ g ≈ f)
  : pushout_apex P ~> y :=
  pushout_med P (pushout_in1_factor_commutes r Hr).

Lemma pushout_in1_retract_comp (r : z ~> y) (Hr : r ∘ g ≈ f) :
  pushout_in1_retract r Hr ∘ pushout_in1 P ≈ id.
Proof.
  unfold pushout_in1_retract.
  exact (pushout_med_in1 P (pushout_in1_factor_commutes r Hr)).
Qed.

Definition pushout_in1_Section (r : z ~> y) (Hr : r ∘ g ≈ f)
  : Section (pushout_in1 P) :=
  {| section      := pushout_in1_retract r Hr
   ; section_comp := pushout_in1_retract_comp r Hr |}.

Lemma pushout_in1_Monic (r : z ~> y) (Hr : r ∘ g ≈ f) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section r Hr).
Qed.

(** ** The second injection / ** 第二次注射 *)

Lemma pushout_in2_factor_commutes (s : y ~> z) (Hs : s ∘ f ≈ g) :
  s ∘ f ≈ id[z] ∘ g.
Proof.
  rewrite id_left.
  exact Hs.
Qed.

Definition pushout_in2_retract (s : y ~> z) (Hs : s ∘ f ≈ g)
  : pushout_apex P ~> z :=
  pushout_med P (pushout_in2_factor_commutes s Hs).

Lemma pushout_in2_retract_comp (s : y ~> z) (Hs : s ∘ f ≈ g) :
  pushout_in2_retract s Hs ∘ pushout_in2 P ≈ id.
Proof.
  unfold pushout_in2_retract.
  exact (pushout_med_in2 P (pushout_in2_factor_commutes s Hs)).
Qed.

Definition pushout_in2_Section (s : y ~> z) (Hs : s ∘ f ≈ g)
  : Section (pushout_in2 P) :=
  {| section      := pushout_in2_retract s Hs
   ; section_comp := pushout_in2_retract_comp s Hs |}.

Lemma pushout_in2_Monic (s : y ~> z) (Hs : s ∘ f ≈ g) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section s Hs).
Qed.

End PushoutSplit.

(*
   * ** The classical special case: a split leg

   If [g] is a split monomorphism, with retraction [t : z ~> x], then [f]
   factors through [g] as [f ∘ t], because [(f ∘ t) ∘ g ≈ f ∘ (t ∘ g) ≈ f].
   So the OPPOSITE injection splits.  This is the constructively available
   fragment of “monic legs give monic injections”. 

   --------
   * ** 经典的特例：分裂的箭腿

   如果 [g] 是一个分裂单射，并且有重traction [t : z ~> x]，那么 [f]
   可以作为 [f ∘ t] 经过 [g] 因式分解，因为 [(f ∘ t) ∘ g ≈ f ∘ (t ∘ g) ≈ f]。
   因此，相反的注入是可分裂的。这是“单射箭腿给出单射注入”中可构造获得的部分片段。
*)

Definition pushout_in1_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sg : Section g)
  : Section (pushout_in1 P).
Proof.
  unshelve refine (pushout_in1_Section P (f ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Definition pushout_in2_Section_of_Retraction
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f)
  : Section (pushout_in2 P).
Proof.
  unshelve refine (pushout_in2_Section P (g ∘ section) _).
  rewrite <- comp_assoc.
  rewrite section_comp.
  apply id_right.
Defined.

Lemma pushout_in1_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sg : Section g) :
  Monic (pushout_in1 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in1_Section_of_Retraction P Sg).
Qed.

Lemma pushout_in2_Monic_of_Retraction
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) :
  Monic (pushout_in2 P).
Proof.
  apply sections_are_monic.
  exact (pushout_in2_Section_of_Retraction P Sf).
Qed.

(*
   * ** Both injections at once

   “Split-monic legs give split-monic injections” — the strength at which
   Mac Lane's monic-legs refinement is available with no normal-form
   theorem.  Note the CROSSING: a splitting of [g] is what splits the
   injection out of [y], and vice versa. 

   --------
   * ** 同时进行两次注射

   “分单态腿提供分单态注射”——在没有正规形式定理时，Mac Lane 的单态腿细化可用的强度。注意交叉：[g] 的分裂就是从 [y] 中分裂出注射，反之亦然。
*)

Definition pushout_both_Section
           {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) (Sf : Section f) (Sg : Section g)
  : Section (pushout_in1 P) * Section (pushout_in2 P) :=
  (pushout_in1_Section_of_Retraction P Sg,
   pushout_in2_Section_of_Retraction P Sf).

Lemma pushout_both_Monic
      {C : Category} {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) (Sf : Section f) (Sg : Section g) :
  Monic (pushout_in1 P) * Monic (pushout_in2 P).
Proof.
  exact (pushout_in1_Monic_of_Retraction P Sg,
         pushout_in2_Monic_of_Retraction P Sf).
Qed.
