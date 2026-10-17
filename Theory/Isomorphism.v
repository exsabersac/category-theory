Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

Section Isomorphism.

Universes o h p.
Context {C : Category@{o h p}}.

(* nLab: https://ncatlab.org/nlab/show/isomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Isomorphism

   同构 `x ≅ y` 是配备双侧逆 `from : y ~> x` 的态射 `to : x ~> y`，由
   `to ∘ from ≈ id`（iso_to_from）与 `from ∘ to ≈ id`（iso_from_to）见证。
   因恒等是同构（iso_id）、同构的逆是同构（iso_sym）、同构的复合是同构
   （iso_compose），关系 `≅` 是对象上的等价关系（iso_equivalence）。与库中别处一样，
   逆定律使用 hom-setoid 等价 `≈` 而非 Coq 的 `=`。 *)

(* 这定义范畴中两对象「同构」意味着什么。需要同构的双方见证，以及它们的复合
   在两方向都等价于恒等的证明。因这是计算相关定义，拥有同构允许在定义内转换对象。

   Cat 中的同构与范畴等价相同。要得到范畴之间真正的同构，复合 F ○ G 与 G ○ F
   需相等（而非等价）于恒等。这通常过强，故此处没有单独抽象。 *)

(* 同构意义下的相同：历史、原则与范围

   nLab:  https://ncatlab.org/nlab/show/principle+of+equivalence
   nLab:  https://ncatlab.org/nlab/show/core
   Words: https://mathshistory.st-andrews.ac.uk/Miller/mathword/i/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural Equivalences",
          Trans. Amer. Math. Soc. 58, 1945
   Essay: Mazur, "When is one thing equal to some other thing?", 2007

   该词早于理论。由希腊语 isos（相等）与 morphe（形式）构成，从晶体学进入数学：
   据 Jeff Miller 的 Earliest Known Uses 调查，1864 年前地质文本已谈晶体的几何同构，
   Camille Jordan 的 Traité des substitutions (1870) 称一群「isomorphe」于另一群，
   Walther von Dyck 在 Gruppentheoretische Studien (1882) 中使用。范畴论奠基论文随后
   重命名该概念：Eilenberg 与 Mac Lane (1945) 对可逆态射说「等价」，作为 Lemma 1.4
   证明其左右逆重合且唯一，并注记所得对象关系自反、对称、传递。本文件以 setoid 形式
   重述那些开篇引理：[comp_inverse_unique] 是 Lemma 1.4，[iso_equivalence] 是等价关系
   注记，在对象上记为 [ob_setoid]。

   该概念决定两对象在范畴目的下何时相同。「在范畴语境中取代相等的主要概念是同构」
   （nLab, principle of equivalence）：可对同构陈述的性质对同构对象同样成立，而不依赖
   「严格相等」的选择。本文件的 [iso_to] / [iso_from] 见证与 [ob_setoid] 使库其余部分
   可按该原则运作；Cat 中的同构是范畴等价（见上文短注），真正的范畴同构需更强
   （StrictCat）。[iso_compose]、[iso_sym]、[iso_id] 使 ≅ 成为对象上的等价；转换
   （transport）因定义计算相关而可在构造中使用。 *)

Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;            (* the forward morphism x ~> y *)
  from : y ~> x;            (* its two-sided inverse y ~> x *)

  iso_to_from : to ∘ from ≈ id;   (* right inverse law: to ∘ from ≈ id *)
  iso_from_to : from ∘ to ≈ id    (* left  inverse law: from ∘ to ≈ id *)
}.

Arguments to {x y} _.
Arguments from {x y} _.
Arguments iso_to_from {x y} _.
Arguments iso_from_to {x y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

(*
   The predicate form: `f` is an 同构 iff it has a two-sided inverse.

   本节：This is nLab 定义 "an invertible 态射", phrased about single 态射 `f` rather than about pair 对象;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class IsIsomorphism {x y : C} (f : x ~> y) := {
    two_sided_inverse : y ~> x;                  (* the inverse g : y ~> x *)
    is_right_inverse : f ∘ two_sided_inverse ≈ id;  (* right inverse: f ∘ g ≈ id *)
    is_left_inverse : two_sided_inverse ∘ f ≈ id    (* left  inverse: g ∘ f ≈ id *)
  }.

#[export]
Instance IsIsoToIso {x y : C} (f : x ~> y) ( _ : IsIsomorphism f) : Isomorphism x y :=
  {|
    to := f;
    from := two_sided_inverse;
    iso_to_from := is_right_inverse;
    iso_from_to := is_left_inverse
  |}.

(* Reflexivity of ≅: the identity is an isomorphism. *)
#[export] Program Instance iso_id {x : C} : x ≅ x := {
  to   := id;
  from := id
}.

(* Symmetry of ≅: the inverse of an isomorphism is an isomorphism,
   obtained by swapping `to` and `from` and the two inverse laws. *)
Program Definition iso_sym {x y : C} `(f : x ≅ y) : y ≅ x := {|
  to   := from f;
  from := to f;

  iso_to_from := iso_from_to f;
  iso_from_to := iso_to_from f
|}.

(* Transitivity of ≅: a composite of isomorphisms is an isomorphism, with
   inverse `from g ∘ from f` (the inverses compose in the opposite order). *)
Program Definition iso_compose {x y z : C} `(f : y ≅ z) `(g : x ≅ y) :
  x ≅ z := {|
  to   := to f ∘ to g;
  from := from g ∘ from f
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Defined.

(*
   Bundling the three constructions above: `≅` is an 等价 relation on

   本节说明相关定义、性质与动机。 the 对象 C. (Per nLab, isomorphisms C are 态射 its core groupoid;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance iso_equivalence : Equivalence Isomorphism := {
  Equivalence_Reflexive  := @iso_id;
  Equivalence_Symmetric  := @iso_sym;
  Equivalence_Transitive := fun _ _ _ g f => iso_compose f g
}.

Definition ob_equiv : crelation C := Isomorphism.

#[export] Instance ob_setoid : Setoid C :=
  {| equiv := Isomorphism
   ; setoid_equiv := iso_equivalence |}.

(*
   等价 of two isomorphisms between the *same* pair of 对象 (as

   本节说明相关定义、性质与动机。 opposed `≅`, which relates 对象): two isos are equal when their `to` `from` components are equal 态射 under `≈`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition iso_equiv {x y : C} : crelation (x ≅ y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

#[export] Program Instance iso_equiv_equivalence {x y : C} :
  Equivalence (@iso_equiv x y).
Next Obligation. now firstorder. Qed.
Next Obligation. now firstorder. Qed.
Next Obligation.
  firstorder;
  try solve [ now transitivity (to y0)
            | now transitivity (from y0) ].
Qed.

#[export] Instance iso_setoid {x y : C} : Setoid (x ≅ y) := {
  equiv := iso_equiv;
  setoid_equiv := iso_equiv_equivalence
  }.

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Iso_Proper :
  Proper (Isomorphism ==> Isomorphism ==> iffT) Isomorphism.
Next Obligation.
  proper.
  - refine (iso_compose _ (iso_sym X)).
    exact (iso_compose _ X1).
  - refine (iso_compose _ X).
    refine (iso_compose _ X1).
    exact (iso_sym X0).
Defined.

End Isomorphism.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 91, only parsing) : isomorphism_scope.

Arguments to {_%_category x%_object y%_object} _%_morphism.
Arguments from {_%_category x%_object y%_object} _%_morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

#[export] Hint Unfold iso_equiv : core.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).

(*
   Every 同构 is both monic and epic, in each direction: `to` and

   本节说明相关定义、性质与动机。 `from` are cancellable both sides because each has two-sided inverse. (The converse fails 一般地;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance iso_to_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic iso.
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_from_to iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

#[export]
Program Instance iso_from_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic (iso⁻¹).
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_to_from iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

#[export]
Program Instance iso_to_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic iso.
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_to_from iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

(*
   本节说明相关定义、性质与动机。 Two-sided inverses are unique up ≈: if `g` is right inverse `g'`. left inverse same `f`, they agree. Stated plain 态射 (no 同构 packaging), which is form inverted coherence laws downstream consume (e.g.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma comp_inverse_unique
      {C : Category} {x y : C} (f : x ~> y) (g g' : y ~> x) :
  f ∘ g ≈ id[y] -> g' ∘ f ≈ id[x] -> g ≈ g'.
Proof.
  intros H1 H2.
  rewrite <- (id_left g).
  rewrite <- H2.
  rewrite <- comp_assoc.
  rewrite H1.
  apply id_right.
Qed.

(*
   Two-sided inverses are unique, so an 同构 is determined by its `to`

   本节说明相关定义、性质与动机。 component: if `to f ≈ g` then `from` components agree well, hence `f ≈ g`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Proposition to_equiv_implies_iso_equiv {C : Category} {x y} (f g : x ≅ y) :
  to f ≈ to g -> f ≈ g.
Proof.
  intro eq. split; [ assumption | ].
  assert (m := iso_to_epic f).
  destruct f as [tof fromf tofrom_eqf fromto_eqf],
      g as [tog fromg tofrom_eqg fromto_eqg].
  simpl in *.
  destruct m as [epic]. apply epic.
  rewrite fromto_eqf, eq, fromto_eqg; reflexivity.
Qed.

#[export]
Instance iso_sym_proper {C: Category} {x y : C} : Proper (equiv ==> equiv) (@iso_sym C x y).
Proof.
  intros f g [fg_toeq fg_fromeq]; destruct f as [ffrom fto ? ?], g as [gfrom gto ? ?];
    simpl in *.
  unfold iso_equiv; split; assumption.
Qed.

#[export]
Instance iso_compose_proper {C : Category} {x y z : C} :
  Proper ((@iso_equiv C y z) ==> @iso_equiv C x y ==> (@iso_equiv C x z)) iso_compose.
Proof.
  intros f1 f2 eqf g1 g2 eqg.
  apply to_equiv_implies_iso_equiv.
  destruct f1 as [f1to ? ? ?], f2 as [f2to ? ? ?], eqf as [eqfto _], eqg as [eqgto _].
  simpl in *.
  rewrite eqfto, eqgto.
  reflexivity.
Qed.

Proposition iso_sym_left_inverse {C : Category} {x y : C} (f : x ≅ y) :
  iso_compose (iso_sym f) f ≈ iso_id.
Proof.
  apply to_equiv_implies_iso_equiv, iso_from_to.
Qed.

Proposition iso_sym_right_inverse {C : Category} {x y : C} (f : x ≅ y) :
  iso_compose f (iso_sym f) ≈ iso_id.
Proof.
  apply to_equiv_implies_iso_equiv, iso_to_from.
Qed.

Proposition from_equiv_implies_iso_equiv {C : Category} {x y} (f g : x ≅ y) :
  from f ≈ from g -> f ≈ g.
Proof.
  set (f1 := iso_sym f).
  set (g1 := iso_sym g).
  change f with (iso_sym (iso_sym f)).
  change g with (iso_sym (iso_sym g)).
  change (iso_sym f) with f1.
  change (iso_sym g) with g1.
  clearbody f1 g1. clear f g.
  simpl. intro eq; apply to_equiv_implies_iso_equiv in eq.
  now apply iso_sym_proper.
Qed.

#[export]
Program Instance iso_from_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic (iso⁻¹).
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_from_to iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

(*
   Partial converses to "isos are monic and epic": a 态射 即 both

   本节说明相关定义、性质与动机。 monic retraction (split epi) is 同构, dually 态射 即 both epic section (split mono) is 同构.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Monic_Retraction_Iso
        {C : Category} {x y : C} `(r : @Retraction _ _ _ f) `(m : @Monic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := retract
}.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite <- retract_comp; cat.
Qed.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite retract_comp; cat.
Qed.

#[export]
Program Instance Epic_Section_Iso
        {C : Category} {x y : C} `(s : @Section _ _ _ f) `(e : @Epic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := section
}.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite section_comp; cat.
Qed.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite <- section_comp; cat.
Qed.

Notation "f ⊙ g" := (@iso_compose _ _ _ _ f g) (at level 40, left associativity).
