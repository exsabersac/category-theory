Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Additive.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

Open Scope addition_scope.

(*
   * * Ab-categories and additive functors

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.8
   (printed pp. 28–29) [maclane:I.8:def4, maclane:I.8:def6,
   maclane:I.8:construction1], restated verbatim in §VIII.2 (printed
   pp. 194, 197) [maclane:VIII.2:def1, maclane:VIII.2:def4]: an
   Ab-CATEGORY has abelian-group hom-sets with bilinear composition; a
   functor between Ab-categories is ADDITIVE when its hom-actions are
   group homomorphisms; additive functors compose, identities are
   additive, and small Ab-categories with additive functors form the
   category Ab-cat.
   nLab: https://ncatlab.org/nlab/show/Ab-enriched+category
   https://ncatlab.org/nlab/show/additive+functor

   THE EXACT CLASS.  Neither in-tree neighbour is Mac Lane's notion:
   [Preadditive] (Structure/Preadditive.v) is deliberately
   commutative-MONOID enrichment — additive inverses are not demanded
   — while [Additive] (Structure/Additive.v) has the group homs but
   bundles a zero object and chosen biproducts, which an Ab-category
   need not carry.  [AbEnriched] below is the exact intermediate:
   [Preadditive] plus negation and the inverse law, NOTHING MORE — no
   zero object, no biproducts — with negation's bilinearity DERIVED
   from uniqueness of additive inverses ([compose_abneg_left]/
   [_right]), not demanded.  Every [Additive] category is an instance
   ([Additive_AbEnriched]); the standalone concrete witness is [Ab]
   itself ([Ab_Preadditive], [Ab_AbEnriched] — pointwise addition and
   negation of homomorphisms, closing the gap Instance/Ab.v's header
   records as "available and ... not attempted").

   ADDITIVE FUNCTORS ([AdditiveFunctor]): preservation of [padd] is
   the only field; preservation of [pzero] and [abneg] are THEOREMS
   ([fmap_pzero], [fmap_abneg] — cancel by the inverse, respectively
   uniqueness of inverses), exactly Mac Lane's "whence T0 = 0".
   Identity and composition closure are instances
   ([Id_AdditiveFunctor], [Compose_AdditiveFunctor]).

   AB-CAT ([AbCat]): objects are categories bundled with an
   [AbEnriched] structure, morphisms are functors bundled with an
   [AdditiveFunctor] witness — the class is what the category is
   built from, its identity and composition instances supplying
   [AbCat]'s — compared by [Functor_Setoid] on the underlying
   functors.  That is the same natural-isomorphism hom-equivalence
   as [Cat], and the same deliberate deviation: Mac Lane's Ab-cat,
   like his Cat, is strict, and this is its
   natural-isomorphism-quotiented reading (a strict variant would
   mirror [StrictCat]).  Universe-polymorphic like [Cat]: "small" is
   whatever the instantiated universe says.

   NAMING.  The negation field is [abneg]/[padd_abneg] rather than
   the issue's suggested [pneg]/[padd_pneg] because
   Structure/Additive.v — imported here for [Additive_AbEnriched] —
   already owns those names as fields of [Additive].

   The biproduct-preservation characterization of additive functors
   (Mac Lane Proposition VIII.2.4) demands strictly more than the
   definition and is a separate catalog item depending on this one. 

   --------
   * * 阿贝尔类别与加法函子

   Mac Lane，《为工作数学家准备的范畴论》，第二版，§I.8
   （印刷页 28–29）[maclane:I.8:def4, maclane:I.8:def6, maclane:I.8:construction1]，在 §VIII.2 中逐字重述（印刷页 194, 197）  [maclane:VIII.2:def1, maclane:VIII.2:def4] ：一个阿贝尔类别具有阿贝尔群的 Hom 集合，并且复合运算双线性；一个阿贝尔类别之间的函子当其 Hom 作用是群同态时被称为加法函子；加法函子可以组合，恒等函子是加法函子，并且小的阿贝尔类别与加法函子构成类别 Ab-cat。
   nLab:  https://ncatlab.org/nlab/show/Ab-enriched+category 
   https://ncatlab.org/nlab/show/additive+functor精确的类别。树中的邻居都不是 Mac Lane 的概念：[Preadditive]（Structure/Preadditive.v）是有意的交换单元增强——不要求有加法逆元——而 [Additive]（Structure/Additive.v）具有群态射（group homs），但捆绑了一个零对象和选定的双积，而 Ab-范畴并不一定包含这些。下面的 [AbEnriched] 是精确的中间物：[Preadditive] 加上取负和逆律，仅此而已——没有零对象，没有双积——并且取负的双线性是从加法逆元的唯一性（[compose_abneg_left] / [_right]）推导出来的，而不是要求的。每个 [Additive] 范畴都是一个实例 ([Additive_AbEnriched])；独立的具体见证是 [Ab] 本身 ([Ab_Preadditive], [Ab_AbEnriched] — 同态的逐点加法和取反，闭合 Instance/Ab.v 的头记录为“可用且...未尝试”)。

   加性函子 ([AdditiveFunctor])：保持 [padd] 是唯一的字段；保持 [pzero] 和 [abneg] 是定理 ([fmap_pzero], [fmap_abneg] — 分别通过逆元抵消，逆元的唯一性)，完全符合 Mac Lane 的“由此 T0 = 0”。
   身份与复合封闭是实例 ([Id_AdditiveFunctor], [Compose_AdditiveFunctor])。AB-CAT（[AbCat]）：对象是绑定了[AbEnriched]结构的范畴，态射是绑定了[AdditiveFunctor]证据的函子——这个类是构建范畴的基础，它的恒等和复合实例提供[AbCat]——通过底层函子上的[Functor_Setoid]进行比较。这与[Cat]的自然同构Hom-等价相同，并且具有同样的刻意偏差：Mac Lane的Ab-cat，就像他的Cat一样，是严格的，而这是它的自然同构等价化的解读（严格变体会镜像[StrictCat]）。像[Cat]一样是宇宙多态的：“小”是由实例化宇宙决定的。命名。否定字段是 [abneg] / [padd_abneg]，而不是该问题建议的 [pneg] / [padd_pneg]，因为 Structure/Additive.v——在这里为 [Additive_AbEnriched] 导入——已经将这些名称作为 [Additive] 的字段所有。

   加性函子的积物保持特性（Mac Lane 命题 VIII.2.4）严格要求比定义更多的内容，并且是一个独立的目录项，依赖于此项。
*)

(** ** The Ab-enriched class / ** 富含Ab的等级 *)

Class AbEnriched (C : Category) := {
  abenriched_preadditive : @Preadditive C;

  abneg {x y : C} : (x ~> y) -> (x ~> y);

  abneg_respects {x y : C} :
    Proper (equiv ==> equiv) (@abneg x y);

  padd_abneg {x y : C} (f : x ~> y) :
    padd f (abneg f) ≈ pzero
}.

#[export] Existing Instance abenriched_preadditive.
#[export] Existing Instance abneg_respects.

Section AbEnrichedFacts.

Context {C : Category}.
Context {A : AbEnriched C}.

(* Additive inverses are unique in each hom-monoid. / 在每个同态幺半群中，加法逆元是唯一的。 *)
Lemma abneg_unique {x y : C} (f g : x ~> y) :
  padd f g ≈ pzero → g ≈ abneg f.
Proof.
  intro H.
  rewrite <- (padd_zero_left g).
  rewrite <- (padd_abneg f).
  rewrite (padd_comm f (abneg f)).
  rewrite padd_assoc.
  rewrite H.
  now rewrite padd_zero_right.
Qed.

(*
 Bilinearity of negation is derived, not demanded: h ∘ (−f) is an
 additive inverse of h ∘ f, hence THE inverse. 

 --------
 否定的双线性是推导出来的，而不是要求的：h ∘ (−f) 是 h ∘ f 的加法逆元，因此是唯一的逆元。
*)
Lemma compose_abneg_left {x y z : C} (h : y ~> z) (f : x ~> y) :
  h ∘ abneg f ≈ abneg (h ∘ f).
Proof.
  apply abneg_unique.
  rewrite <- compose_padd_left.
  rewrite (padd_abneg f).
  apply compose_pzero_right.
Qed.

Lemma compose_abneg_right {x y z : C} (f : y ~> z) (h : x ~> y) :
  abneg f ∘ h ≈ abneg (f ∘ h).
Proof.
  apply abneg_unique.
  rewrite <- compose_padd_right.
  rewrite (padd_abneg f).
  apply compose_pzero_left.
Qed.

Lemma abneg_pzero {x y : C} : abneg (@pzero C _ x y) ≈ pzero.
Proof.
  symmetry; apply abneg_unique.
  apply padd_zero_left.
Qed.

(* An idempotent element of a hom-group is the zero. / 同群的幂等元素是零。 *)
Lemma padd_idem_zero {x y : C} (f : x ~> y) : padd f f ≈ f → f ≈ pzero.
Proof.
  intro H.
  rewrite <- (padd_zero_right f).
  rewrite <- (padd_abneg f).
  rewrite <- padd_assoc.
  rewrite H.
  reflexivity.
Qed.

Lemma abneg_invol {x y : C} (f : x ~> y) : abneg (abneg f) ≈ f.
Proof.
  symmetry; apply abneg_unique.
  rewrite padd_comm.
  apply padd_abneg.
Qed.

End AbEnrichedFacts.

(*
 Every Additive category — group homs plus a zero object and
 biproducts — is in particular Ab-enriched. 

 --------
 每一个加法范畴——具有群同态、零对象和双积——特别是Ab-增强的。
*)
#[export] Instance Additive_AbEnriched {C : Category} (A : @Additive C) :
  AbEnriched C := {|
  abenriched_preadditive := @additive_preadditive C A;
  abneg := fun x y => @pneg C A x y;
  abneg_respects := fun x y => @pneg_respects C A x y;
  padd_abneg := fun x y => @padd_pneg C A x y
|}.

(** ** Additive functors / ** 加性函子 *)

Class AdditiveFunctor {C D : Category}
  {AC : AbEnriched C} {AD : AbEnriched D} (F : C ⟶ D) := {
  fmap_padd {x y : C} (f g : x ~> y) :
    fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g)
}.

Section AdditiveFunctorFacts.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context (F : C ⟶ D).
Context `{AF : @AdditiveFunctor C D AC AD F}.

(*
 "Whence T0 = 0": cancel by the inverse of the image of zero. 

 --------
 “由此 T0 = 0”：通过零的像的逆来取消。
*)
Lemma fmap_pzero {x y : C} :
  fmap[F] (@pzero C _ x y) ≈ pzero.
Proof using AC AD AF C D F.
  apply padd_idem_zero.
  rewrite <- fmap_padd.
  now rewrite (padd_zero_left (@pzero C _ x y)).
Qed.

Lemma fmap_abneg {x y : C} (f : x ~> y) :
  fmap[F] (abneg f) ≈ abneg (fmap[F] f).
Proof using AC AD AF C D F.
  apply abneg_unique.
  rewrite <- fmap_padd.
  rewrite (padd_abneg f).
  apply fmap_pzero.
Qed.

End AdditiveFunctorFacts.

#[export] Program Instance Id_AdditiveFunctor
  {C : Category} {AC : AbEnriched C} : AdditiveFunctor (@Id C).
Next Obligation.
  intros C AC x y f g; simpl; reflexivity.
Qed.

#[export] Program Instance Compose_AdditiveFunctor
  {C D E : Category} {AC : AbEnriched C} {AD : AbEnriched D} {AE : AbEnriched E}
  (F : D ⟶ E) (G : C ⟶ D)
  `{@AdditiveFunctor D E _ _ F} `{@AdditiveFunctor C D _ _ G} :
  AdditiveFunctor (F ◯ G).
Next Obligation.
  intros C D E AC AD AE F G AF AG x y f g; simpl.
  transitivity (fmap[F] (padd (fmap[G] f) (fmap[G] g))).
  - exact (@fmap_respects _ _ F _ _ _ _
             (@fmap_padd C D AC AD G AG x y f g)).
  - exact (@fmap_padd D E AD AE F AF _ _ (fmap[G] f) (fmap[G] g)).
Qed.

(** ** The category of Ab-categories / ** Ab-范畴的类别 *)

Definition AbCatObj : Type := { C : Category & AbEnriched C }.

Definition AbCatHom (C D : AbCatObj) : Type :=
  { F : `1 C ⟶ `1 D
  & @AdditiveFunctor (`1 C) (`1 D) (`2 C) (`2 D) F }.

(*
 Morphisms are compared by the underlying functors' natural-iso
 setoid — the same hom-equivalence as Cat, the documented choice. 

 --------
 态射通过底层函子上的自然同构集合来比较——与 Cat 相同的同态等价，这是文档中选择的方式。
*)
Program Definition AbCat : Category := {|
  obj := AbCatObj;
  hom := AbCatHom;
  homset := fun C D =>
    {| Setoid.equiv := fun F G => `1 F ≈ `1 G |};
  id := fun C =>
    (Id[`1 C]; @Id_AdditiveFunctor (`1 C) (`2 C));
  compose := fun C D E F G =>
    ((`1 F) ◯ (`1 G);
     @Compose_AdditiveFunctor (`1 C) (`1 D) (`1 E)
       (`2 C) (`2 D) (`2 E) (`1 F) (`1 G) (`2 F) (`2 G))
|}.
Next Obligation.
  intros C D; constructor.
  - intros F; reflexivity.
  - intros F G H1; symmetry; exact H1.
  - intros F G H H1 H2; transitivity (`1 G); [ exact H1 | exact H2 ].
Qed.
Next Obligation.
  intros C D E F F' HF G G' HG; simpl in *.
  exact (@compose_respects Cat (`1 C) (`1 D) (`1 E)
           (`1 F) (`1 F') HF (`1 G) (`1 G') HG).
Qed.
Next Obligation.
  intros C D F; simpl.
  exists (fun x => iso_id).
  intros x y f; simpl; cat.
Qed.
Next Obligation.
  intros C D F; simpl.
  exists (fun x => iso_id).
  intros x y f; simpl; cat.
Qed.
Next Obligation.
  intros B C D E F G H; simpl.
  exists (fun x => iso_id).
  intros x y f; simpl; cat.
Qed.
Next Obligation.
  intros B C D E F G H; simpl.
  exists (fun x => iso_id).
  intros x y f; simpl; cat.
Qed.

(** ** Ab itself is Ab-enriched / ** Ab 本身含有丰富的 Ab *)

(*
 Pointwise addition and negation of homomorphisms into an abelian
 group are homomorphisms again; this closes the instance
 Instance/Ab.v's header records as available but not attempted. 

 --------
 将同态映射到阿贝尔群的逐点加法和取反仍然是同态；这使得 Instance/Ab.v 的实例头部记录为可用，但未尝试。
*)
Program Definition ab_hom_add {A B : AbObject} (f g : AbHom A B) :
  AbHom A B := {|
  cmon_map := {| morphism := fun a =>
    cmon_plus B (cmon_map f a) (cmon_map g a) |}
|}.
Next Obligation.
  intros A B f g a b Hab.
  now rewrite Hab.
Qed.
Next Obligation.
  intros A B f g; simpl.
  rewrite (cmon_map_zero f), (cmon_map_zero g).
  apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros A B f g a b; simpl.
  rewrite (cmon_map_plus f a b), (cmon_map_plus g a b).
  rewrite !cmon_plus_assoc.
  apply cmon_plus_respects; [ reflexivity |].
  rewrite <- !cmon_plus_assoc.
  apply cmon_plus_respects; [| reflexivity ].
  apply cmon_plus_comm.
Qed.

Program Definition ab_hom_zero {A B : AbObject} : AbHom A B := {|
  cmon_map := {| morphism := fun _ => cmon_zero B |}
|}.
Next Obligation. intros A B a b Hab; reflexivity. Qed.
Next Obligation. intros A B; simpl; reflexivity. Qed.
Next Obligation.
  intros A B a b; simpl.
  symmetry; apply cmon_plus_zero_l.
Qed.

Program Definition ab_hom_neg {A B : AbObject} (f : AbHom A B) :
  AbHom A B := {|
  cmon_map := {| morphism := fun a => ab_neg B (cmon_map f a) |}
|}.
Next Obligation.
  intros A B f a b Hab.
  now rewrite Hab.
Qed.
Next Obligation.
  intros A B f; simpl.
  rewrite (cmon_map_zero f).
  apply ab_neg_zero.
Qed.
Next Obligation.
  intros A B f a b; simpl.
  rewrite (cmon_map_plus f a b).
  apply ab_neg_plus.
Qed.

#[export] Program Instance Ab_Preadditive : @Preadditive Ab := {
  padd := fun x y => ab_hom_add;
  pzero := fun x y => ab_hom_zero
}.
Next Obligation.
  intros x y f f' Hf g g' Hg a; simpl.
  now rewrite (Hf a), (Hg a).
Qed.
Next Obligation.
  intros x y f g h a; simpl; apply cmon_plus_assoc.
Qed.
Next Obligation.
  intros x y f g a; simpl; apply cmon_plus_comm.
Qed.
Next Obligation.
  intros x y f a; simpl; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros x y z h f g a; simpl.
  apply cmon_map_plus.
Qed.
Next Obligation.
  intros x y z f g h a; simpl; reflexivity.
Qed.
Next Obligation.
  intros x y z f a; simpl; reflexivity.
Qed.
Next Obligation.
  intros x y z f a; simpl.
  apply cmon_map_zero.
Qed.

#[export] Program Instance Ab_AbEnriched : AbEnriched Ab := {
  abenriched_preadditive := Ab_Preadditive;
  abneg := fun x y => ab_hom_neg
}.
Next Obligation.
  intros x y f g Hfg a; simpl.
  now rewrite (Hfg a).
Qed.
Next Obligation.
  intros x y f a; simpl.
  rewrite cmon_plus_comm.
  apply ab_neg_left.
Qed.
