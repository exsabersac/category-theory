Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.

Generalizable All Variables.

(** * Naturality of the Yoneda isomorphism in both variables

    Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.2,
    Lemma 2 (printed p. 61) [maclane:III.2:lem2]; Awodey, “Category Theory”,
    §8.3 Lemma 8.2 [awodey:8.3:lem2]; Riehl, “Category Theory in Context”,
    2nd ed., §2.2 Theorem 2.2.4 [riehl:2.2:thm4], the unnumbered two-variable
    construction on printed p. 63 [riehl:2.2:construction-yoneda-bifunctor],
    Remark 2.2.7 [riehl:2.2:remark7], Exercise 2.2.i [riehl:2.2:exi], and the
    Epilogue §E.1 restatement [riehl:E.1:thm-yoneda].
    nLab: https://ncatlab.org/nlab/show/Yoneda+lemma

    Functor/Hom/Yoneda.v proves the Yoneda bijection one pair at a time:
    for each copresheaf F and each object A it exhibits an isomorphism of
    setoids Nat([Hom A,─], F) ≅ F A.  Mac Lane's addendum to the lemma —
    his Lemma 2, and the clause “natural in both c and F” that Riehl builds
    into the statement of the theorem itself — says that the family is a
    natural isomorphism between two functors of two variables:

        E : [C, Sets] ∏ C ⟶ Sets,   E ⟨F, A⟩ = F A
        N : [C, Sets] ∏ C ⟶ Sets,   N ⟨F, A⟩ = Nat([Hom A,─], F)

    and the forward map, evaluation at the identity, is a natural
    isomorphism N ≅ E.  That is what this file adds.

    Why the upgrade is not bookkeeping.  A family of isomorphisms indexed
    by the objects of a category is strictly weaker than an isomorphism of
    functors, and this library already carries the separation: for
    finite-dimensional vector spaces the pointwise isomorphism V ≅ V* is
    built at EVERY object (Instance/FdVect/DoubleDual.v's
    [fd_dual_pointwise_iso]) and Instance/FdVect/NonNatural.v then refutes
    naturality of any such family, at a single square; the character-group
    analogue for finite abelian groups is Instance/Ab/Character/NonNatural.v.
    So “the Yoneda bijection is natural” is a theorem about the family and
    not a restatement of the bijection.

    The tree's own downstream consumers do not need it, which is why the
    clause could go unformalized — but the two cases differ and an audit
    corrected an earlier draft that ran them together.
    Structure/UniversalProperty.v does consume [Yoneda_Lemma], and proves
    its representability results from the pointwise bijection alone.
    [Yoneda_Full] and [Yoneda_Faithful] consume nothing from this file and
    could not: they live in Functor/Hom.v, which is UPSTREAM — Yoneda.v
    requires it, not the other way round — and each inlines evaluation at
    the identity directly.  What is true of all of them, and is the point,
    is that none needs NATURALITY.  Nothing below is required by any of
    them, and nothing below changes them.

    Riehl's Remark 2.2.7 packages naturality in the FIRST variable alone.
    For a fixed object c the evaluation functor ev_c : [C, Sets] ⟶ Sets,
    F ↦ F c, is REPRESENTED by the copresheaf [Hom c,─] — in her reading,
    with the identity of c as universal element.  The representability half
    is delivered here as an [#[export] Instance] of
    Functor/Representable.v's [Representable] class, so it is an in-tree
    statement and not only a corollary one might read off the two-variable
    isomorphism; the universal-element packaging (Theory/Universal/Element.v)
    is NOT built, see below.

    Riehl also records a size caveat: when C is merely locally small the
    functor category [C, Sets] need not be, yet the Yoneda bijection shows
    N lands in genuine small sets.  In this library that observation is
    discharged by universe polymorphism rather than proved — nothing below
    is a smallness theorem, and none is claimed.

    ** What is delivered

    - [YoEval C] : the evaluation bifunctor E, built directly, as a plain
      [Definition] whose [fobj] and [fmap] fields are transparent (its three
      law fields are separate lemmas, so no [Program] obligation stands
      between a consumer and the arrow action).  [yo_eval_map_alt] records
      that the other factorization of the arrow action — post-compose with
      the transformation after transporting, rather than before — agrees
      with it up to ≈, that agreement being exactly the naturality square.

    - [YoNat C] : the Nat-bifunctor N, built as Riehl builds it, by
      COMPOSING parts already in tree: the hom-bifunctor [Hom] of
      Functor/Hom.v applied to the functor category, precomposed with the
      Yoneda functor [Curried_Hom] in its first slot and a factor swap.  No
      functor law is proved for it: all three are inherited.  Its object
      action agrees with the hand-written record on the nose
      ([yo_nat_obj_agrees], Leibniz [eq_refl] — the convertibility
      exception), and its arrow action agrees pointwise on the nose
      ([yo_nat_map_agrees]); the two arrow actions are NOT equal as
      [SetoidMorphism] records, and that is not claimed — the [morphism]
      fields are convertible (pointwise agreement plus record eta), so what
      separates them is the [proper_morphism] field, which is a different
      proof term on each side.

    - [yoneda_natural C] : Mac Lane's Lemma 2, an [Isomorphism] in the
      functor category [[[C, Sets] ∏ C], Sets].  Its components ARE the
      in-tree [Covariant_Yoneda_Lemma], in both legs, at Leibniz [eq_refl]
      ([yoneda_natural_to_component], [yoneda_natural_from_component]) — it
      is the existing isomorphism assembled, not a parallel construction.
      [yoneda_natural_square] and [yoneda_eval_at_identity] state the
      naturality square in elementary terms.

    - [YoEvalAt C c] : Riehl's ev_c, with [YoEvalAt_Representable] the
      registered [Representable] instance whose [repr_obj] is [Hom c,─] on
      the nose.  Naturality in the functor variable is DEFINITIONAL here,
      and [yo_repr_naturality_strict] records that at [eq_refl]: composing
      transformations and then evaluating at the identity is the same term
      as evaluating and then applying the component.

    - The contravariant orientation, obtained by INSTANTIATION and not by a
      second proof: [YoEvalPre], [YoNatPre] and [yoneda_natural_pre] are
      literally the covariant constants at C^op.  This needs no appeal to
      [op_invol], because [Curried_CoHom C] IS [Curried_Hom C^op] by
      definition and [@Presheaves C Sets] IS [@Copresheaves C^op Sets] by
      definition, so the presheaf statement is the copresheaf statement at
      the opposite category up to conversion alone.  Nor would the REVERSE
      derivation need it, contrary to an earlier draft of this paragraph
      that an audit corrected: [(C^op)^op = C] holds by [eq_refl] in this
      library — Construction/Opposite.v says so in terms — so reading
      the covariant statement at C off the contravariant one is conversion
      as well.  [op_invol] is simply not on either path.
      [Yoneda_Lemma_derived] is the same move one level down: the pointwise
      contravariant lemma derived from the covariant one, closing the gap
      Riehl's Exercise 2.2.i names.

    - Non-vacuity over [Deloop Nat_Plus]: the naturality square instantiated
      at a non-identity transformation and a non-identity morphism, both
      sides computing to 10 by [eq_refl] through visibly different
      intermediate values, together with witnesses that neither bifunctor is
      degenerate there.

    ** What is NOT delivered

    - The tree's [Yoneda_Lemma] (Functor/Hom/Yoneda.v) is NOT replaced,
      removed, or shown redundant.  [Yoneda_Lemma_derived] exhibits the
      derivation and [yoneda_lemma_derived_agrees] records that the two
      agree, but they remain two constants and the file leaves the existing
      one in force.

    - No representability statement in the SECOND variable.  Riehl's Remark
      2.2.7 is about ev_c for fixed c, and nothing here asserts that the
      partial application of E in the other slot is representable.

    - No comparison with the end form of the lemma
      (Theory/Coend/Yoneda.v's [yoneda_reduction]), and no smallness
      theorem.

    - No universal element.  Riehl's phrasing of Remark 2.2.7 names id_c as
      the universal element of ev_c, but no [AUniversalElement] or
      [UniversalElement] (Theory/Universal/Element.v) is constructed here,
      and no comparison with that class is made.

    - A UNIVERSE RESTRICTION, inherited and measured.  [Covariant_Yoneda_
      Lemma] is stated over [C : Category@{u u u}] — object, hom and proof
      universes identified — so it cannot be applied to a category whose
      objects live strictly below its homs, and neither can anything built
      over it.  The boundary runs exactly where that constant is consumed,
      and the constraint sets say so: [YoEval], [YoNat] and [YoEvalAt] are
      over [Category@{u u0 u0}] carrying [u <= u0] and no [u = u0], so their
      object universe is FREE below the hom universe; [yoneda_natural],
      [yoneda_natural_pre], [Yoneda_Lemma_derived] and
      [YoEvalAt_Representable] all carry the identification (the first three
      display [Category@{u0 u0 u0}]; the instance displays
      [Category@{u u0 u0}] but its constraint set contains [u = u0]).
      Test/ProbeYonedaNatural.v pins the four rejections against four
      positive controls, one of them an identity isomorphism in the very
      functor category the theorem lives in, so the rejection is
      attributable to the donor and not to the packaging.  The restriction
      is the donor's; no claim is made that it is unavoidable. *)

(** ** The two bifunctors  / ** 两个双函子*)

Section YonedaBifunctors.

Context (C : Category).

(**
*** Evaluation: E ⟨F, A⟩ = F A

    On a morphism ⟨τ, f⟩ : ⟨F, A⟩ ~> ⟨G, B⟩ — a natural transformation
    τ : F ⟹ G together with f : A ~> B — the action transports along f
    inside F and then applies the component of τ at B. 

--------
*** 评估：E ⟨F, A⟩ = F A

 关于态射 ⟨τ, f⟩ : ⟨F, A⟩ ~> ⟨G, B⟩ — 自然变换
 τ : F ⟹ G 与 f : A ~> B — 动作沿着 f 传输
 在 F 内，然后在 B 处应用 τ 的分量。 
*)

Definition yo_eval_obj (p : [C, Sets] ∏ C) : Sets := fst p (snd p).

Definition yo_eval_map {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_eval_obj x ~{Sets}~> yo_eval_obj y :=
  transform[fst tf] (snd y) ∘ fmap[fst x] (snd tf).

Lemma yo_eval_map_respects (x y : [C, Sets] ∏ C) :
  Proper (equiv ==> equiv) (@yo_eval_map x y).
Proof.
  destruct x as [F a], y as [G b].
  intros [tau f] [tau' f'] [Ht Hf] z; simpl in *.
  rewrite (@fmap_respects _ _ F _ _ _ _ Hf z).
  apply Ht.
Qed.

Lemma yo_eval_map_id (x : [C, Sets] ∏ C) : @yo_eval_map x x id ≈ id.
Proof.
  destruct x as [F a]; intro z; simpl.
  srewrite (@fmap_id _ _ F a).
  now srewrite (@fmap_id _ _ F a).
Qed.

Lemma yo_eval_map_comp (x y z : [C, Sets] ∏ C) (g : y ~> z) (f : x ~> y) :
  yo_eval_map (g ∘ f) ≈ yo_eval_map g ∘ yo_eval_map f.
Proof.
  destruct x as [F a], y as [G b], z as [H c].
  destruct g as [sigma g], f as [tau f]; intro w; simpl in *.
  srewrite (@naturality _ _ _ _ tau b c g).
  now srewrite (@fmap_comp _ _ F a b c g f).
Qed.

Definition YoEval : ([C, Sets] ∏ C) ⟶ Sets := {|
  fobj          := yo_eval_obj;
  fmap          := @yo_eval_map;
  fmap_respects := yo_eval_map_respects;
  fmap_id       := fun x => yo_eval_map_id x;
  fmap_comp     := fun x y z g f => yo_eval_map_comp x y z g f
|}.

(* The evaluation bifunctor has two evident arrow actions, differing in the
   order of the two moves, and they agree — the agreement being exactly the
   naturality square of τ.  The library's own implicit evaluation, the
   uncurried identity inside [Cat_Closed]'s [exp_iso] (see
   Instance/Cat/Cartesian/Closed.v, whose header describes it at lines
   34-36 but which names no constant for it), takes the other order.  This
   lemma is the bridge, and states plainly that neither order is canonical. *)
Lemma yo_eval_map_alt {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_eval_map tf ≈ fmap[fst y] (snd tf) ∘ transform[fst tf] (snd x).
Proof.
  destruct x as [F a], y as [G b], tf as [tau f]; intro z; simpl in *.
  now srewrite (@naturality _ _ _ _ tau a b f).
Qed.

(**
*** The Nat-bifunctor: N ⟨F, A⟩ = Nat([Hom A,─], F)

    Riehl builds N as the composite of the Yoneda functor with the
    hom-bifunctor of the functor category, and so does this: [Curried_Hom C]
    is the Yoneda functor C^op ⟶ [C, Sets], its opposite is a functor
    C ⟶ [C, Sets]^op (the double opposite of a category being the category
    itself, by [reflexivity], in this library), and feeding it into the
    contravariant slot of [Hom ([C, Sets])] after a factor swap gives
    ⟨F, A⟩ ↦ hom([Hom A,─], F).  Every functor law is inherited; none is
    proved here. 

--------
*** Nat 双函子：N ⟨F, A⟩ = Nat([Hom A,─], F)

 Riehl 将 N 构建为 Yoneda 函子与
 函子类别的 hom-bifunctor 也是如此：[Curried_Hom C]
 是米田函子 C^op ⟶ [C, Sets]，它的对立面是函子
 C ⟶ [C, Sets]^op （类别的双重对立面是类别
 本身，由 [reflexivity]，在这个库中），并将其输入到
 [Hom ([C, Sets])] 因子交换后的逆变槽给出
 ⟨F，A⟩↦ hom([Hom A,─]，F)。 每个函子法则都是继承的； 没有一个是
 在这里证明了。 
*)

Definition Yoneda_op : C ⟶ ([C, Sets])^op := Opposite_Functor (Curried_Hom C).

Definition YoNat : ([C, Sets] ∏ C) ⟶ Sets :=
  Hom ([C, Sets]) ◯ (Yoneda_op ∏⟶ Id) ◯ Swap.

(*
The hand-written object action, and the record that the composite hits it
   on the nose.  [eq_refl] here is Leibniz equality — the convertibility
   exception to the ≈-discipline: both sides are the same term. 

--------
手写的物体动作，以及合成击中它的记录
 在鼻子上。 [eq_refl] 这里是莱布尼茨等式——可转换性
 ≈-规则的例外：两边都是同一个术语。 
*)
Definition yo_nat_obj (p : [C, Sets] ∏ C) : Sets :=
  {| carrier   := @hom ([C, Sets]) [Hom (snd p),─] (fst p)
   ; is_setoid := @homset ([C, Sets]) [Hom (snd p),─] (fst p) |}.

Definition yo_nat_obj_agrees (p : [C, Sets] ∏ C) :
  fobj[YoNat] p = yo_nat_obj p := eq_refl.

(*
The hand-written arrow action: whisker on the left by τ, precompose on
   the right with the representable's action on f. 

--------
手写箭头动作：τ左边的胡须，预合成
 右边代表代表对 f 采取的行动。 
*)
Program Definition yo_nat_map {x y : [C, Sets] ∏ C} (tf : x ~> y) :
  yo_nat_obj x ~{Sets}~> yo_nat_obj y :=
  {| morphism := fun a =>
       fst tf ∘[[C, Sets]] a ∘[[C, Sets]]
         (@fmap _ _ (Curried_Hom C) (snd y) (snd x) (snd tf)) |}.
Next Obligation.
  repeat intro; simpl.
  now rewrite X.
Qed.

(*
The composite's arrow action is the hand-written one pointwise, at
   Leibniz [eq_refl].  Equality of the two [SetoidMorphism] RECORDS does not
   hold and is not claimed: their [proper_morphism] fields are different
   proof terms (one a fresh obligation of this file, the other assembled
   from [Hom]'s and [Swap]'s).  That negative is pinned in
   Test/ProbeYonedaNatural.v. 

--------
复合材料的箭头动作是逐点手写的，位于
 莱布尼茨 [eq_refl]。 两个 [SetoidMorphism] RECORDS 不相等
 持有且未被认领：它们的 [proper_morphism] 字段不同
 证明条款（一个是该文件的新义务，另一个是组装的
 来自 [Hom] 和 [Swap]）。 那个负数被固定在
 测试/探针YonedaNatural.v。 
*)
Definition yo_nat_map_agrees {x y : [C, Sets] ∏ C} (tf : x ~> y)
  (a : fobj[YoNat] x) : fmap[YoNat] tf a = yo_nat_map tf a := eq_refl.

End YonedaBifunctors.

Arguments yo_eval_obj {C} p.
Arguments yo_eval_map {C x y} tf.
Arguments yo_nat_obj {C} p.
Arguments yo_nat_map {C x y} tf.

(** ** Mac Lane's Lemma 2: N ≅ E, naturally in both variables  / ** Mac Lane 引理 2：N ≅ E，自然在两个变量中*)

(*
The components are the in-tree [Covariant_Yoneda_Lemma] verbatim; the six
   obligations are the two naturality squares of each leg and the two round
   trips.  Naturality of the forward leg is the naturality of the
   transformation being evaluated; naturality of the backward leg is the
   naturality of τ together with functoriality of F. 

--------
这些组件是树内 [Covariant_Yoneda_Lemma] 逐字记录； 六个
 义务是每条腿的两个自然正方形和两个圆形
 旅行。 前腿的自然性就是后腿的自然性
 正在评估转型； 后腿的自然性是
 τ 的自然性和 F 的函数性。 
*)
Program Definition yoneda_natural (C : Category) :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoNat C) (YoEval C) := {|
  to   := {| transform :=
               fun p => to   (Covariant_Yoneda_Lemma C (fst p) (snd p)) |};
  from := {| transform :=
               fun p => from (Covariant_Yoneda_Lemma C (fst p) (snd p)) |}
|}.
Next Obligation.
  srewrite (@naturality _ _ _ _ x0 o0 o h).
  apply proper_morphism, proper_morphism.
  unfold op; cat.
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ x0 o0 o h).
  apply proper_morphism, proper_morphism.
  unfold op; cat.
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ t o x1 x2).
  apply proper_morphism.
  unfold op; now srewrite (@fmap_comp _ _ f0 o0 o x1 x2 h).
Qed.
Next Obligation.
  srewrite (@naturality _ _ _ _ t o x1 x2).
  apply proper_morphism.
  unfold op; now srewrite (@fmap_comp _ _ f0 o0 o x1 x2 h).
Qed.
Next Obligation.
  srewrite (@fmap_id _ _ f o).
  now srewrite (@fmap_id _ _ f o).
Qed.
Next Obligation.
  srewrite (@fmap_id _ _ f x1).
  srewrite (@naturality _ _ _ _ x0 o x1 x2).
  apply proper_morphism.
  unfold op; cat.
Qed.

(*
The components ARE the existing pointwise Yoneda isomorphism, in both
   legs.  Leibniz [eq_refl] — the convertibility exception. 

--------
这些组件是现有的点式米田同构，在两个方面
 腿。 Leibniz [eq_refl] — 可转换性例外。 
*)
Definition yoneda_natural_to_component
  (C : Category) (F : C ⟶ Sets) (A : C) :
  transform[to (yoneda_natural C)] (F, A) = to (Covariant_Yoneda_Lemma C F A)
  := eq_refl.

Definition yoneda_natural_from_component
  (C : Category) (F : C ⟶ Sets) (A : C) :
  transform[from (yoneda_natural C)] (F, A)
    = from (Covariant_Yoneda_Lemma C F A)
  := eq_refl.

(* The naturality square, written out at a pair of arrows.  / 自然性正方形，写在一对箭头处。*)
Lemma yoneda_natural_square (C : Category) (F G : C ⟶ Sets) (A B : C)
      (tau : F ⟹ G) (f : A ~{C}~> B) (al : fobj[YoNat C] (F, A)) :
  transform[to (yoneda_natural C)] (G, B)
      (@fmap _ _ (YoNat C) (F, A) (G, B) (tau, f) al)
    ≈ @fmap _ _ (YoEval C) (F, A) (G, B) (tau, f)
        (transform[to (yoneda_natural C)] (F, A) al).
Proof.
  exact (@naturality_sym _ _ _ _ (to (yoneda_natural C))
           (F, A) (G, B) (tau, f) al).
Qed.

(*
...and the same square in elementary terms: Mac Lane's two readings of
   the composite, one going through the representable and one through F. 

--------
...以及基本术语中的同一个正方形：Mac Lane 的两个读物
 复合体，一个通过可表示物，一个通过 F。 
*)
Corollary yoneda_eval_at_identity (C : Category) (F G : C ⟶ Sets) (A B : C)
      (tau : F ⟹ G) (f : A ~{C}~> B) (al : [Hom A,─] ⟹ F) :
  transform[tau] B (transform[al] B (id ∘ f))
    ≈ transform[tau] B (fmap[F] f (transform[al] A id)).
Proof. exact (yoneda_natural_square C F G A B tau f al). Qed.

(** ** Riehl's Remark 2.2.7: evaluation at c is representable  / ** Riehl 的评论 2.2.7：c 处的评估是可表示的*)

Section EvaluationAt.

Context (C : Category).
Context (c : C).

(* ev_c : [C, Sets] ⟶ Sets, F ↦ F c.  / ev_c ：[C, Sets] ⟶ 集，F ↦ F c。*)
Program Definition YoEvalAt : [C, Sets] ⟶ Sets := {|
  fobj := fun F => F c;
  fmap := fun F G tau => transform[tau] c
|}.
Next Obligation. srewrite (@fmap_id _ _ x c). reflexivity. Qed.

(*
It is the partial application of the evaluation bifunctor: on objects
   definitionally (Leibniz [eq_refl]), on arrows only up to ≈, because the
   bifunctor's action at ⟨τ, id⟩ still transports along [fmap[F] id]. 

--------
这是评估双函子的部分应用：在对象上
 定义上（Leibniz [eq_refl]），箭头仅达到 ≈，因为
 bifunctor 在 ⟨τ, id⟩ 处的作用仍然沿着 [fmap[F] id] 传输。 
*)
Definition yo_eval_at_obj (F : C ⟶ Sets) :
  fobj[YoEvalAt] F = fobj[YoEval C] (F, c) := eq_refl.

Lemma yo_eval_at_map (F G : C ⟶ Sets) (tau : F ⟹ G) :
  fmap[YoEvalAt] tau ≈ @fmap _ _ (YoEval C) (F, c) (G, c) (tau, id[c]).
Proof. intro z; simpl; symmetry; now srewrite (@fmap_id _ _ F c). Qed.

(*
Naturality in the FUNCTOR variable is definitional: composing
   transformations and then evaluating at the identity is the same term as
   evaluating and then applying the component.  Leibniz [eq_refl]. 

--------
FUNCTOR 变量的自然性是定义性的：组合
 转换然后评估同一性是同一个术语
 评估然后应用该组件。 莱布尼茨 [eq_refl]。 
*)
Definition yo_repr_naturality_strict (F G : C ⟶ Sets) (tau : F ⟹ G)
  (al : [Hom c,─] ⟹ F) :
  transform[tau] c (transform[al] c id)
    = transform[nat_compose tau al] c id
  := eq_refl.

#[export] Program Instance YoEvalAt_Representable : Representable YoEvalAt := {|
  repr_obj := [Hom c,─];
  represented :=
    {| to   := {| transform := fun F => to   (Covariant_Yoneda_Lemma C F c) |}
     ; from := {| transform := fun F => from (Covariant_Yoneda_Lemma C F c) |} |}
|}.
Next Obligation. now srewrite (@naturality _ _ _ _ f c x1 x2). Qed.
Next Obligation. now srewrite (@naturality _ _ _ _ f c x1 x2). Qed.
Next Obligation.
  srewrite (@fmap_id _ _ x x1).
  srewrite (@naturality _ _ _ _ x0 c x1 x2).
  apply proper_morphism; cat.
Qed.

(* The representing object is the representable copresheaf on the nose.  / 代表对象是鼻子上的可代表的干草。*)
Definition yo_repr_obj : @repr_obj _ _ YoEvalAt_Representable = [Hom c,─]
  := eq_refl.

End EvaluationAt.

Arguments YoEvalAt {C} c.

(**
** The contravariant orientation, by instantiation at C^op

    Riehl's Exercise 2.2.i asks for the contravariant Yoneda lemma with its
    naturality, and makes the point that the DERIVATION is what matters.
    Everything below is the covariant development read at C^op; nothing is
    reproved.  [Curried_CoHom C] is [Curried_Hom C^op] by definition
    (Functor/Hom.v) and [@Presheaves C Sets] is [@Copresheaves C^op Sets]
    by definition (Theory/Sheaf.v), so the presheaf-side types are the
    copresheaf-side types at the opposite category up to conversion, and
    [op_invol] is not consumed. 

--------
** 逆变方向，通过在 C^op 处实例化

 Riehl 的练习 2.2.i 要求逆变米田引理及其
 自然性，并指出推导才是最重要的。 
下面的所有内容都是在 C^op 上阅读的协变开发； 没有什么是
 责备。 根据定义，[Curried_CoHom C] 是 [Curried_Hom C^op]
 (Functor/Hom.v) 并且 [@Presheaves C Sets] 是 [@Copresheaves C^op Sets]
 根据定义（Theory/Sheaf.v），因此 presheaf 侧类型是
 直到转换为止，相反类别的 copresheaf 侧类型，以及
 [op_invol] 不被消耗。 
*)

(*
The universe binders are EXPLICIT here, and that is load-bearing rather
   than decorative.  Written as a bare [Definition (C : Category)] these four
   constants come out pinned at [Category@{u0 u0 u0}] — not because of the
   donor, whose restriction they do not inherit (their bodies are [YoEval]
   and [YoNat], neither of which consumes [Covariant_Yoneda_Lemma]), but
   because universe minimization at an unannotated top-level binder
   identifies the three levels.  An audit caught exactly that: the covariant
   originals were free while their opposite-category readings silently were
   not.  Annotating restores the parity. 

--------
宇宙粘合剂在这里是明确的，这是承重的而不是
 比装饰性的。 这四个写成裸[Definition (C : Category)]
 常量固定在 [Category@{u0 u0 u0}] 上 — 不是因为
 捐赠者，他们没有继承其限制（他们的身体是 [YoEval]
 和 [YoNat]，两者都不消耗 [Covariant_Yoneda_Lemma]），但是
 因为在未注释的顶级活页夹中进行宇宙最小化
 确定了三个级别。 一项审计准确地发现了这一点：协变
 原著是免费的，而相反类别的阅读则默默地被收取
 不。 注释可以恢复奇偶性。 
*)

Definition YoEvalPre@{u u0 u1} (C : Category@{u u0 u0}) :
  ((@Presheaves C Sets@{u0 u1}) ∏ (C^op)) ⟶ Sets@{u0 u1} := YoEval (C^op).

Definition YoNatPre@{u u0 u1} (C : Category@{u u0 u0}) :
  ((@Presheaves C Sets@{u0 u1}) ∏ (C^op)) ⟶ Sets@{u0 u1} := YoNat (C^op).

Definition yoneda_natural_pre (C : Category) :
  @Isomorphism ([((@Presheaves C Sets) ∏ (C^op)), Sets])
               (YoNatPre C) (YoEvalPre C)
  := yoneda_natural (C^op).

(* The presheaf-side object actions, read in C's own vocabulary.  / presheaf 端对象动作，用 C 自己的词汇来读。*)
Definition yo_nat_pre_obj@{u u0 u1} (C : Category@{u u0 u0})
  (F : C^op ⟶ Sets@{u0 u1}) (A : C) :
  fobj[YoNatPre C] (F, A) = Presheaves [Hom ─,A] F := eq_refl.

Definition yo_eval_pre_obj@{u u0 u1} (C : Category@{u u0 u0})
  (F : C^op ⟶ Sets@{u0 u1}) (A : C) :
  fobj[YoEvalPre C] (F, A) = F A := eq_refl.

(**
*** The pointwise lemma, derived rather than reproved

    Functor/Hom/Yoneda.v declares [Yoneda_Lemma] and
    [Covariant_Yoneda_Lemma] as two separate [Program Instance]s with
    separately discharged obligations, neither derived from the other.  The
    derivation is available and costs nothing: the two statements are
    convertible. 

--------
*** 逐点引理，是派生的，而不是反驳的

 Functor/Hom/Yoneda.v 声明 [Yoneda_Lemma] 和
 [Covariant_Yoneda_Lemma] 作为两个独立的 [Program Instance]
 单独履行的义务，两者均不源自另一方。 的
 推导是可用的并且不需要任何成本：这两个语句是
 敞篷车。 
*)

Definition Yoneda_Lemma_derived (C : Category) (F : C^op ⟶ Sets) (A : C) :
  Presheaves [Hom ─,A] F ≅ F A := Covariant_Yoneda_Lemma (C^op) F A.

(*
The forward legs agree once applied: the value is an element of F A, and
   it is the same term.  Leibniz [eq_refl] — the convertibility exception.
   The two [to] MORPHISMS are not equal as records, their [proper_morphism]
   fields being different opaque obligation constants of the two donor
   instances; that negative is pinned in Test/ProbeYonedaNatural.v. 

--------
应用后，前腿一致：该值是 F A 的一个元素，并且
 这是同一个术语。 Leibniz [eq_refl] — 可转换性例外。 
两个 [to] MORPHISMS 作为记录并不相等，它们的 [proper_morphism]
 两个捐助者的不同不透明义务常数的字段
 实例； 该阴性结果固定在 Test/ProbeYonedaNatural.v 中。 
*)
Definition yoneda_lemma_derived_to (C : Category) (F : C^op ⟶ Sets) (A : C)
  (x : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) x = to (Yoneda_Lemma C F A) x := eq_refl.

(*
The backward legs agree only one level further in: their VALUES are
   whole [Transform] records, whose [naturality] and [naturality_sym] fields
   are different opaque obligation constants, so [eq_refl] on the value is
   rejected (pinned in Test/ProbeYonedaNatural.v).  What does hold on the
   nose is the agreement of the COMPONENTS. 

--------
后面的腿仅进一步同意一级：它们的值是
 整个 [Transform] 记录，其 [naturality] 和 [naturality_sym] 字段
 是不同的不透明义务常量，因此 [eq_refl] 的值为
 被拒绝（固定在 Test/ProbeYonedaNatural.v 中）。 持有什么
 鼻子是组件的协议。 
*)
Definition yoneda_lemma_derived_from_at
  (C : Category) (F : C^op ⟶ Sets) (A : C) (y : F A) (x : C)
  (phi : x ~{C}~> A) :
  transform[from (Yoneda_Lemma_derived C F A) y] x phi
    = transform[from (Yoneda_Lemma C F A) y] x phi := eq_refl.

(*
Equality of the whole [Isomorphism] records does NOT hold — its four
   fields differ as terms, the [to] and [from] morphisms by their
   [proper_morphism] obligations and [iso_to_from]/[iso_from_to] by being
   different opaque constants — so the agreement is stated at ≈, which is
   what a setoid consumer needs.  The [eq_refl] negative is pinned in
   Test/ProbeYonedaNatural.v. 

--------
整个 [Isomorphism] 记录的相等性不成立 — 它的四个
 字段作为术语不同，[to] 和 [from] 态射的不同
 [proper_morphism] 义务和 [iso_to_from]/[iso_from_to] 的义务
 不同的不透明常数 - 因此协议在 ≈ 处表示，即
 类固醇消费者需要什么。 [eq_refl] 负片固定在
 测试/探针YonedaNatural.v。 
*)
Lemma yoneda_lemma_derived_agrees (C : Category) (F : C^op ⟶ Sets) (A : C) :
  to (Yoneda_Lemma_derived C F A) ≈ to (Yoneda_Lemma C F A)
    ∧ from (Yoneda_Lemma_derived C F A) ≈ from (Yoneda_Lemma C F A).
Proof. split; simpl; intros; reflexivity. Qed.

(*
The components of the presheaf-side natural isomorphism are the in-tree
   [Yoneda_Lemma]'s maps, pointwise on the nose. 

--------
presheaf侧自然同构的组成部分是树内
 [Yoneda_Lemma] 的贴图，在鼻子上逐点进行。 
*)
Definition yoneda_natural_pre_to_component
  (C : Category) (F : C^op ⟶ Sets) (A : C) (x : Presheaves [Hom ─,A] F) :
  transform[to (yoneda_natural_pre C)] (F, A) x = to (Yoneda_Lemma C F A) x
  := eq_refl.

Definition yoneda_natural_pre_from_component
  (C : Category) (F : C^op ⟶ Sets) (A : C) (y : F A) (x : C)
  (phi : x ~{C}~> A) :
  transform[transform[from (yoneda_natural_pre C)] (F, A) y] x phi
    = transform[from (Yoneda_Lemma C F A) y] x phi
  := eq_refl.

(**
** Non-vacuity

    The two bifunctors and the naturality square, exercised over the
    delooping of (ℕ, +): one object, the naturals as arrows, composition
    addition, identity 0 (Construction/Deloop.v).  [Nat_Plus] has a
    [Set]-sized carrier, so the theorem is instantiated here at
    [Category@{Set Set Set}] — measured, not assumed: the witnesses elaborate
    [yoneda_natural@{u Set}], the category's single identified universe being
    [Set] and [u] the ambient [Sets]' object universe one level above.  Every
    general result above is polymorphic; the pin is the concrete witness's
    alone.

    The copresheaf probed is the representable [Hom ttt,─], whose value at
    the single object is ℕ itself, so [YoEval] there has a carrier with more
    than one element and the arrow actions can be told apart. 

--------
** 非空性

 两个双函子和自然性平方，在
 (ℕ, +) 的去循环：一个对象，自然数为箭头，组合
 另外，恒等式 0 (Construction/Deloop.v)。 [Nat_Plus] 有一个
 [Set] 大小的载体，因此该定理在此实例化
 [Category@{Set Set Set}] — 测量，而非假设：目击者详细阐述
 [yoneda_natural@{u Set}]，该类别的单一识别宇宙是
 [Set] 和 [u] 比环境 [Sets] 的对象宇宙高一级。 每个
 上面的一般结果是多态的； 针是具体证人的
 独自一人。 

探测的 copresheaf 是可表示的 [Hom ttt,─]，其值为
 单个对象是 ℕ 本身，因此 [YoEval] 有一个载体，其中包含更多
 可以区分一个元素和箭头动作。 
*)

Section Witness.

Notation NatCat := (Deloop Nat_Plus).
Notation NatRep := (fobj[Curried_Hom NatCat] ttt).

(*
Two endomorphisms of the representable: precomposition with 5 and with
   2.  Each is [fmap] of the Yoneda functor at that arrow. 

--------
可表征的两种自同态：与 5 的预组合和与
 2. 每个都是该箭头处的米田函子的 [fmap]。 
*)
Definition yo_wit_alpha (n : nat) : NatRep ⟹ NatRep :=
  @fmap _ _ (Curried_Hom NatCat) ttt ttt n.

(*
Evaluation at the identity reads the arrow back off the transformation:
   the forward leg of the Yoneda isomorphism sends [yo_wit_alpha n] to n. 

--------
对恒等式的求值读取了变换后的箭头：
 米田同构的前向支路将 [yo_wit_alpha n] 发送至 n。 
*)
Example yo_wit_to_alpha_5 :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt) (yo_wit_alpha 5%nat) = 5%nat
  := eq_refl.

Example yo_wit_to_alpha_2 :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt) (yo_wit_alpha 2%nat) = 2%nat
  := eq_refl.

(*
...so the forward leg is not constant, and the transformations are
   distinct: the isomorphism separates them. 

--------
...所以前腿不是恒定的，并且变换是
 不同：同构将它们分开。 
*)
Lemma yo_wit_alpha_distinct :
  yo_wit_alpha 5%nat ≈ yo_wit_alpha 2%nat → False.
Proof.
  intro H.
  pose proof (H ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

(*
Both components of the pair the square is probed at are non-identity, so
   the instance below is not a disguised unit law. 

--------
探测正方形的对的两个分量都是非同一的，所以
 下面的例子并不是变相的单位法。 
*)
Lemma yo_wit_alpha_not_id :
  yo_wit_alpha 2%nat ≈ @id ([NatCat, Sets]) NatRep → False.
Proof.
  intro H.
  pose proof (H ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma yo_wit_arrow_not_id :
  (3%nat : ttt ~{NatCat}~> ttt) ≈ @id NatCat ttt → False.
Proof. intro H; simpl in H; discriminate. Qed.

(*
The naturality square at the NON-identity pair ⟨alpha 2, 3⟩, applied to
   [alpha 5].  Left-hand side: whisker and precompose inside N, then
   evaluate at the identity — the intermediate values are 0, 3, 8, 10.
   Right-hand side: evaluate at the identity first, then act in E — the
   intermediate values are 0, 5, 8, 10.  Both reduce to 10 by
   computation. 

--------
非恒等对 ⟨alpha 2, 3⟩ 处的自然性平方，应用于
 [alpha 5]。 左侧：在N内进行胡须和预合成，然后
 评估同一性 - 中间值为 0、3、8、10。 
右侧：首先评估恒等式，然后执行 E —
 中间值为 0、5、8、10。两者都减少到 10
 计算。 
*)
Example yo_wit_square_left :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt)
    (@fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
       (yo_wit_alpha 2%nat, 3%nat) (yo_wit_alpha 5%nat)) = 10%nat
  := eq_refl.

Example yo_wit_square_right :
  @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat)
    (transform[to (yoneda_natural NatCat)] (NatRep, ttt)
       (yo_wit_alpha 5%nat))
    = 10%nat
  := eq_refl.

(*
The square itself, at that pair — an instance of the theorem, not of
   [eq_refl]. 

--------
正方形本身，在该对处 - 定理的一个实例，而不是
 [eq_refl]。 
*)
Lemma yo_wit_square :
  transform[to (yoneda_natural NatCat)] (NatRep, ttt)
    (@fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
       (yo_wit_alpha 2%nat, 3%nat) (yo_wit_alpha 5%nat))
    ≈ @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
        (yo_wit_alpha 2%nat, 3%nat)
        (transform[to (yoneda_natural NatCat)] (NatRep, ttt)
           (yo_wit_alpha 5%nat)).
Proof.
  exact (yoneda_natural_square NatCat NatRep NatRep ttt ttt
           (yo_wit_alpha 2%nat) 3%nat (yo_wit_alpha 5%nat)).
Qed.

(*
Neither bifunctor is degenerate at this pair: E's arrow action moves the
   element 5 to 10, so it is not the identity map, and N's arrow action
   moves [alpha 5] to a transformation the isomorphism reads back as 10 and
   not 5. 

--------
这对双函子都不是退化的：E 的箭头动作移动了
 元素5到10，所以它不是恒等映射，以及N的箭头动作
 将 [alpha 5] 移动到同构读回为 10 的转换，并且
 不是 5。 
*)
Lemma yo_wit_eval_map_not_id :
  @fmap _ _ (YoEval NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat) ≈ id → False.
Proof.
  intro H.
  pose proof (H 5%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma yo_wit_nat_map_not_id :
  @fmap _ _ (YoNat NatCat) (NatRep, ttt) (NatRep, ttt)
    (yo_wit_alpha 2%nat, 3%nat) ≈ id → False.
Proof.
  intro H.
  pose proof (H (yo_wit_alpha 5%nat) ttt 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

(*
...and the object of E at this pair genuinely has more than one element,
   so the isomorphism is not between singletons. 

--------
...并且 E 在这一对中的宾语确实具有多个元素，
 所以同构不在单例之间。 
*)
Lemma yo_wit_eval_obj_nontrivial :
  ∃ u v : fobj[YoEval NatCat] (NatRep, ttt), u ≈ v → False.
Proof. exists 0%nat, 1%nat; intro H; discriminate. Qed.

(*
Riehl's Remark 2.2.7 at this witness: evaluation at the single object is
   represented by the representable copresheaf. 

--------
Riehl 对此证人的评论 2.2.7：对单个对象的评估是
 由可代表的copresheaf 代表。 
*)
Example yo_wit_repr_obj :
  @repr_obj _ _ (YoEvalAt_Representable NatCat ttt)
    = fobj[Curried_Hom NatCat] ttt := eq_refl.

Example yo_wit_repr_to :
  transform[to (@represented _ _ (YoEvalAt_Representable NatCat ttt))]
    NatRep (yo_wit_alpha 5%nat) = 5%nat := eq_refl.

End Witness.
