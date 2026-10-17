Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/quotient+category
    Wikipedia: https://en.wikipedia.org/wiki/Quotient_category

   本文件给出商/商对象相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomCast.

Context {C : Category}.

(** The identity morphism, transported along an object equality. *)
Definition id_cast {x y : C} (e : x = y) : x ~> y :=
  match e in _ = T return x ~> T with eq_refl => id end.

(** At [eq_refl], cast literal 恒等. （已译） *)
Lemma id_cast_refl {x : C} : id_cast (@eq_refl _ x) = id.
Proof. reflexivity. Qed.

(** Composing two casts gives cast along 复合 equality. （已译） *)
Lemma id_cast_trans {x y z : C} (e1 : x = y) (e2 : y = z) :
  id_cast e2 ∘ id_cast e1 ≈ id_cast (eq_trans e1 e2).
Proof. destruct e2, e1; cat. Qed.

(** Casting along [e] back along [eq_sym e] 恒等. （已译） *)
Lemma id_cast_inv_l {x y : C} (e : x = y) :
  id_cast (eq_sym e) ∘ id_cast e ≈ id.
Proof. destruct e; cat. Qed.

Lemma id_cast_inv_r {x y : C} (e : x = y) :
  id_cast e ∘ id_cast (eq_sym e) ≈ id.
Proof. destruct e; cat. Qed.

(** Solve [f ≈ g ∘ cast⁻¹] from [f ∘ cast ≈ g]. *)
Lemma comp_cast_shift {x y z : C} (e : x = y) (f : y ~> z) (g : x ~> z) :
  f ∘ id_cast e ≈ g → f ≈ g ∘ id_cast (eq_sym e).
Proof.
  intros Hf.
  rewrite <- Hf.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  now rewrite id_right.
Qed.

(** Nested cast conjugations fuse along [eq_trans]. *)
Lemma id_cast_conj_fuse {x y x' y' x'' y'' : C}
  (e1 : x = x') (e2 : y = y') (d1 : x' = x'') (d2 : y' = y'')
  (f : x ~> y) :
  id_cast d2 ∘ (id_cast e2 ∘ f ∘ id_cast (eq_sym e1)) ∘ id_cast (eq_sym d1)
    ≈ id_cast (eq_trans e2 d2) ∘ f ∘ id_cast (eq_sym (eq_trans e1 d1)).
Proof. destruct e1, e2, d1, d2; cat. Qed.

(** Leibniz-equal 对象 particular isomorphic, via casts. （已译） *)
Definition id_cast_iso {x y : C} (e : x = y) : x ≅ y := {|
  to := id_cast e;
  from := id_cast (eq_sym e);
  iso_to_from := id_cast_inv_r e;
  iso_from_to := id_cast_inv_l e
|}.

(** A whole morphism transported along equalities on both endpoints. *)
Definition hom_cast {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x ~> y) : x' ~> y' :=
  match ey in _ = b return x' ~> b with eq_refl =>
    match ex in _ = a return a ~> y with eq_refl => f end end.

(** At [eq_refl] both ends, cast 态射 itself. （已译） *)
Lemma hom_cast_refl {x y : C} (f : x ~> y) :
  hom_cast eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

(** A [hom_cast] is conjugation by the endpoint [id_cast]s. *)
Lemma hom_cast_decompose {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x ~> y) :
  hom_cast ex ey f ≈ id_cast ey ∘ f ∘ id_cast (eq_sym ex).
Proof. destruct ex, ey; cat. Qed.

(** Casting 恒等 along same equality twice 恒等. （已译） *)
Lemma hom_cast_id {x x' : C} (e : x = x') : hom_cast e e id ≈ id.
Proof. destruct e; cat. Qed.

(** Casts fuse across composition when the middle equalities agree. *)
Lemma hom_cast_comp {x y z x' y' z' : C}
  (ex : x = x') (ey : y = y') (ez : z = z')
  (g : y ~> z) (f : x ~> y) :
  hom_cast ey ez g ∘ hom_cast ex ey f ≈ hom_cast ex ez (g ∘ f).
Proof. destruct ex, ey, ez; cat. Qed.

(** Casting there back 恒等 operation. （已译） *)
Lemma hom_cast_roundtrip {x y x' y' : C} (ex : x = x') (ey : y = y')
  (f : x' ~> y') :
  hom_cast ex ey (hom_cast (eq_sym ex) (eq_sym ey) f) = f.
Proof. destruct ex, ey; reflexivity. Qed.

(** [hom_cast] respects the hom-setoid equivalence. *)
#[export] Instance hom_cast_respects {x y x' y' : C}
  (ex : x = x') (ey : y = y') :
  Proper (equiv ==> equiv) (@hom_cast x y x' y' ex ey).
Proof. destruct ex, ey; repeat intro; assumption. Qed.

End HomCast.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fmap_id_cast {C D : Category} (F : C ⟶ D) {x y : C} (e : x = y) :
  fmap[F] (id_cast e) ≈ id_cast (f_equal F e).
Proof. destruct e; apply fmap_id. Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class ObjDecEq (C : Category) : Type :=
  obj_eq_dec : ∀ x y : obj[C], {x = y} + {x ≠ y}.

(** Uniqueness of identity proofs on objects, with no axioms. *)
Lemma obj_uip {C : Category} `{@ObjDecEq C} {x y : C} (e1 e2 : x = y) :
  e1 = e2.
Proof. exact (UIP_dec obj_eq_dec e1 e2). Qed.

(** [id_cast] does not depend choice equality 证明. （已译） *)
Lemma id_cast_irr {C : Category} `{@ObjDecEq C} {x y : C} (e1 e2 : x = y) :
  id_cast e1 = id_cast e2.
Proof. rewrite (obj_uip e1 e2); reflexivity. Qed.

(** Any cast along a loop equality [e : x = x] is the identity. *)
Lemma id_cast_loop {C : Category} `{@ObjDecEq C} {x : C} (e : x = x) :
  id_cast e = id.
Proof. rewrite (obj_uip e eq_refl); reflexivity. Qed.

(** Conjugation along different proofs of the same equalities agrees. *)
Lemma id_cast_conj_irr {C : Category} `{@ObjDecEq C} {x y x' y' : C}
  (p1 q1 : x = x') (p2 q2 : y = y') (f : x ~> y) :
  id_cast p2 ∘ f ∘ id_cast (eq_sym p1)
    ≈ id_cast q2 ∘ f ∘ id_cast (eq_sym q1).
Proof. rewrite (obj_uip p1 q1), (obj_uip p2 q2); reflexivity. Qed.

(** [hom_cast] does not depend on the choice of equality proofs. *)
Lemma hom_cast_irr {C : Category} `{@ObjDecEq C} {x y x' y' : C}
  (e1 e1' : x = x') (e2 e2' : y = y') (f : x ~> y) :
  hom_cast e1 e2 f = hom_cast e1' e2' f.
Proof. rewrite (obj_uip e1 e1'), (obj_uip e2 e2'); reflexivity. Qed.

(** Casting a morphism along loop equalities is the morphism itself. *)
Lemma hom_cast_loop {C : Category} `{@ObjDecEq C} {x y : C}
  (e1 : x = x) (e2 : y = y) (f : x ~> y) :
  hom_cast e1 e2 f = f.
Proof. rewrite (obj_uip e1 eq_refl), (obj_uip e2 eq_refl); reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：The reshuffle itself, both directions, [destruct] endpoint
 equalities. （已译） *)
Lemma hom_cast_transport_iff {D : Category} {a b a' b' : D}
  (ex : a = a') (ey : b = b') (f : a ~> b) (g : a' ~> b') :
  ((hom_cast ex ey f ≈ g) →
     (Logic.transport (fun z => hom a z) ey f
        ≈ Logic.transport_r (fun z => hom z b') ex g)) *
  ((Logic.transport (fun z => hom a z) ey f
      ≈ Logic.transport_r (fun z => hom z b') ex g) →
     (hom_cast ex ey f ≈ g)).
Proof. destruct ex, ey; split; intro; assumption. Qed.

(** A [hom_cast]-conjugated agreement of two functors IS their equality in
    [StrictCat]. *)
Lemma strict_of_hom_cast {C D : Category} (F G : C ⟶ D)
  (Hobj : ∀ x, fobj[F] x = fobj[G] x)
  (H : ∀ x y (f : x ~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[F] f) ≈ fmap[G] f) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G.
Proof.
  exists Hobj. intros x y f.
  exact (fst (hom_cast_transport_iff (Hobj x) (Hobj y)
                (fmap[F] f) (fmap[G] f)) (H x y f)).
Qed.

(** ...and conversely, equality 函子 [StrictCat] yields the
 对象 equalities together [hom_cast]-conjugated agreement. （已译） *)
Lemma hom_cast_of_strict {C D : Category} (F G : C ⟶ D)
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F G) :
  { Hobj : ∀ x, fobj[F] x = fobj[G] x &
      ∀ x y (f : x ~> y),
        hom_cast (Hobj x) (Hobj y) (fmap[F] f) ≈ fmap[G] f }.
Proof.
  destruct E as [Hobj Hmor].
  exists Hobj. intros x y f.
  exact (snd (hom_cast_transport_iff (Hobj x) (Hobj y)
                (fmap[F] f) (fmap[G] f)) (Hmor x y f)).
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class HomEqProp (C : Category) : Type := {
  heq : ∀ {x y : C}, (x ~> y) → (x ~> y) → Prop;
  heq_intro : ∀ {x y : C} {f g : x ~> y}, f ≈ g → heq f g;
  heq_elim : ∀ {x y : C} {f g : x ~> y}, heq f g → f ≈ g
}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition HomRel (C : Category) : Type :=
  ∀ x y : C, (x ~> y) → (x ~> y) → Prop.

Definition HomRelT (C : Category) : Type :=
  ∀ x y : C, (x ~> y) → (x ~> y) → Type.

(** A congruence: 等价 each hom containing [≈] (whence
 reflexivity) compatible 复合. （已译） *)
Class HomCongruence {C : Category} (R : HomRelT C) : Type := {
  cong_incl {x y : C} {f g : x ~> y} : f ≈ g → R x y f g;
  cong_sym {x y : C} {f g : x ~> y} : R x y f g → R x y g f;
  cong_trans {x y : C} {f g h : x ~> y} :
    R x y f g → R x y g h → R x y f h;
  cong_comp {x y z : C} {f f' : y ~> z} {g g' : x ~> y} :
    R y z f f' → R x y g g' → R x z (f ∘ g) (f' ∘ g')
}.

(** Reflexivity of a congruence, from inclusion of [≈]. *)
Lemma cong_refl {C : Category} {R : HomRelT C} `{@HomCongruence C R}
  {x y : C} (f : x ~> y) : R x y f f.
Proof. apply cong_incl; reflexivity. Qed.

(** Each hom-relation of a congruence is an equivalence. *)
Lemma Quotient_equivalence {C : Category} {R : HomRelT C}
  `{@HomCongruence C R} (x y : C) : Equivalence (R x y).
Proof.
  constructor.
  - intros f. exact (cong_refl f).
  - intros f g Hfg. exact (cong_sym Hfg).
  - intros f g k Hfg Hgk. exact (cong_trans Hfg Hgk).
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Quotient (C : Category) (R : HomRelT C)
  `{@HomCongruence C R} : Category := {|
  obj := @obj C;
  hom := @hom C;
  homset := fun x y =>
    {| equiv := R x y; setoid_equiv := Quotient_equivalence x y |};
  id := @id C;
  compose := @compose C;
  compose_respects := fun x y z f f' Hf g g' Hg => cong_comp Hf Hg;
  id_left := fun x y f => cong_incl (id_left f);
  id_right := fun x y f => cong_incl (id_right f);
  comp_assoc := fun x y z w f g h => cong_incl (comp_assoc f g h);
  comp_assoc_sym := fun x y z w f g h => cong_incl (comp_assoc_sym f g h)
|}.

(** The quotient's [≈] IS [R x y] after reduction, so both directions of
 [Prop] reflection 恒等. （已译） *)
#[export] Instance Quotient_HomEqProp (C : Category) (R : HomRel C)
  `{@HomCongruence C R} : HomEqProp (Quotient C R) :=
  Build_HomEqProp (Quotient C R)
    (fun x y f g => R x y f g)
    (fun x y f g Hfg => Hfg)
    (fun x y f g Hfg => Hfg).

(** The quotient has same 对象 [C], so decidability 对象
 equality inherited nose. （已译） *)
#[export] Instance Quotient_ObjDecEq (C : Category) (R : HomRel C)
  `{@HomCongruence C R} `{OD : @ObjDecEq C} : ObjDecEq (Quotient C R) := OD.

(* * *** The 普遍性质 quotient （已译） *)

Section QuotientUMP.

Context {C : Category} {R : HomRelT C} `{@HomCongruence C R}.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuotientProj : C ⟶ Quotient C R :=
  Build_Functor C (Quotient C R)
    (fun x => x)
    (fun x y f => f)
    (fun x y f g Hfg => cong_incl Hfg)
    (fun x => cong_refl (@id C x))
    (fun x y z f g => cong_refl (f ∘ g)).

(** Isomorphisms in [C] descend to isomorphisms in the quotient. *)
Definition Quotient_iso {x y : C} (i : x ≅[C] y) : x ≅[Quotient C R] y :=
  @Build_Isomorphism (Quotient C R) x y (to i) (from i)
    (cong_incl (iso_to_from i))
    (cong_incl (iso_from_to i)).

Context {D : Category} (F : C ⟶ D)
  (HF : ∀ x y (f g : x ~> y), R x y f g → fmap[F] f ≈ fmap[F] g).

(** A functor identifying [R]-related morphisms lifts through the
    quotient. *)
Definition QuotientLift : Quotient C R ⟶ D :=
  Build_Functor (Quotient C R) D
    (fun x => F x)
    (fun x y f => fmap[F] f)
    HF
    (fun x => @fmap_id C D F x)
    (fun x y z f g => @fmap_comp C D F x y z f g).

(** 本节：The lift factors [F] through projection — definitionally. （已译） *)
Lemma QuotientLift_proj {x y : C} (f : x ~> y) :
  fmap[QuotientLift] (fmap[QuotientProj] f) = fmap[F] f.
Proof. reflexivity. Qed.

(** The factorization, packaged single equality 函子 in
 [StrictCat] — same strength [QuotientLift_unique] below. （已译） *)
Lemma QuotientLift_factors_strict :
  @equiv _ (@Functor_StrictEq_Setoid C D) (QuotientLift ◯ QuotientProj) F.
Proof. exists (fun _ => eq_refl). intros x y f. simpl. reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma QuotientLift_unique (G : Quotient C R ⟶ D)
  (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
  (HG : ∀ x y (f : x ~{C}~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[G] (fmap[QuotientProj] f))
        ≈ fmap[F] f) :
  ∀ x y (f : x ~{Quotient C R}~> y),
    hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[QuotientLift] f.
Proof. exact HG. Qed.

End QuotientUMP.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The projection 恒等 对象, nose — honest
 reading "bijective 对象". （已译） *)
Lemma QuotientProj_obj {C : Category} (R : HomRelT C)
  `{HR : @HomCongruence C R} (x : C) : fobj[@QuotientProj C R HR] x = x.
Proof. reflexivity. Qed.

(** 本节：The sharpest form "equations merge never add": hom TYPE is
 unchanged quotient. （已译） *)
Lemma Quotient_hom_type {C : Category} (R : HomRelT C)
  `{HR : @HomCongruence C R} (x y : C) :
  (x ~{Quotient C R}~> y) = (x ~{C}~> y).
Proof. reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuotientProj_Full {C : Category} (R : HomRelT C)
  `{HR : @HomCongruence C R} : Full (@QuotientProj C R HR) :=
  @Build_Full C (Quotient C R) (@QuotientProj C R HR)
    (fun x y g => g) (fun x y g => @cong_refl C R HR x y g).

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Quotient_bifunctor {C : Category} {R : HomRelT C}
  `{@HomCongruence C R} (F : C ∏ C ⟶ C)
  (HF2 : ∀ (x y : C ∏ C) (f g : x ~{C ∏ C}~> y),
      R (fst x) (fst y) (fst f) (fst g) →
      R (snd x) (snd y) (snd f) (snd g) →
      R (F x) (F y) (fmap[F] f) (fmap[F] g)) :
  Quotient C R ∏ Quotient C R ⟶ Quotient C R :=
  Build_Functor (Quotient C R ∏ Quotient C R) (Quotient C R)
    (fun x => F x)
    (fun x y f => fmap[F] f)
    (fun x y f g Hfg => HF2 x y f g (fst Hfg) (snd Hfg))
    (fun x => cong_incl (@fmap_id _ _ F x))
    (fun x y z f g => cong_incl (@fmap_comp _ _ F x y z f g)).

(*
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   nLab: https://ncatlab.org/nlab/show/quotient+category
   nLab: https://ncatlab.org/nlab/show/congruence

   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Mac Lane's kernel congruence of a functor: the morphisms it merges.
    It is [Type]-valued because [≈] is. *)
Definition FunctorKernel {C D : Category} (F : C ⟶ D) : HomRelT C :=
  fun x y f g => fmap[F] f ≈ fmap[F] g.

(*
   本节说明函子、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FunctorKernel_Congruence {C D : Category} (F : C ⟶ D) :
  @HomCongruence C (FunctorKernel F).
Proof.
  unshelve econstructor; unfold FunctorKernel.
  - intros x y f g Hfg. now rewrite Hfg.
  - intros x y f g Hc. now symmetry.
  - intros x y f g h H1 H2. now transitivity (fmap[F] g).
  - intros x y z f f' g g' H1 H2. rewrite !fmap_comp. now rewrite H1, H2.
Defined.

Section CongruenceClosure.

Context {C : Category}.
Variable R : HomRelT C.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive CongClosure : ∀ x y : C, (x ~> y) → (x ~> y) → Type :=
  | cc_gen {x y : C} {f g : x ~> y} : R x y f g → CongClosure x y f g
  | cc_equiv {x y : C} {f g : x ~> y} : f ≈ g → CongClosure x y f g
  | cc_sym {x y : C} {f g : x ~> y} :
      CongClosure x y f g → CongClosure x y g f
  | cc_trans {x y : C} {f g h : x ~> y} :
      CongClosure x y f g → CongClosure x y g h → CongClosure x y f h
  | cc_comp {x y z : C} {f f' : y ~> z} {g g' : x ~> y} :
      CongClosure y z f f' → CongClosure x y g g' →
      CongClosure x z (f ∘ g) (f' ∘ g').

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CongClosure_Congruence : @HomCongruence C CongClosure :=
  @Build_HomCongruence C CongClosure
    (fun x y f g H => cc_equiv H)
    (fun x y f g H => cc_sym H)
    (fun x y f g h H1 H2 => cc_trans H1 H2)
    (fun x y z f f' g g' H1 H2 => cc_comp H1 H2).

(** Reflexivity, derived rather than assumed. *)
Definition cc_refl {x y : C} (f : x ~> y) : CongClosure x y f f :=
  cc_equiv (reflexivity f).

(** Leastness: the closure is contained in every congruence containing
    [R].  Because [HomCongruence] is stated over [HomRelT], a [Prop]-valued
    target congruence is covered by the same statement, through
    [Prop ⊆ Type] cumulativity. *)
Lemma cc_least (S : HomRelT C) `{@HomCongruence C S}
  (HRS : ∀ x y (f g : x ~> y), R x y f g → S x y f g)
  {x y : C} {f g : x ~> y} : CongClosure x y f g → S x y f g.
Proof.
  intro Hc; induction Hc.
  - now apply HRS.
  - now apply cong_incl.
  - now apply cong_sym.
  - now apply (cong_trans IHHc1 IHHc2).
  - now apply cong_comp.
Qed.

(*
   本节说明函子、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cc_kernel {D : Category} (F : C ⟶ D)
  (HF : ∀ x y (f g : x ~> y), R x y f g → fmap[F] f ≈ fmap[F] g)
  {x y : C} {f g : x ~> y} :
  CongClosure x y f g → fmap[F] f ≈ fmap[F] g :=
  @cc_least (FunctorKernel F) (FunctorKernel_Congruence F) HF x y f g.

End CongruenceClosure.

Arguments CongClosure {C} R x y f g.
Arguments cc_gen {C R x y f g} _.
Arguments cc_equiv {C R x y f g} _.
Arguments cc_sym {C R x y f g} _.
Arguments cc_trans {C R x y f g h} _ _.
Arguments cc_comp {C R x y z f f' g g'} _ _.
Arguments cc_refl {C} R {x y} f.
Arguments CongClosure_Congruence {C} R.

(** The quotient congruence GENERATED arbitrary 关系
 family — Mac Lane §II.8 Proposition 1's 范畴. （已译） *)
Definition QuotientCong (C : Category) (R : HomRelT C) : Category :=
  @Quotient C (CongClosure R) (CongClosure_Congruence R).

(** Its projection. *)
Definition QuotientCongProj {C : Category} (R : HomRelT C) :
  C ⟶ QuotientCong C R :=
  @QuotientProj C (CongClosure R) (CongClosure_Congruence R).

(** 本节：Proposition 1, clause (i): related arrows identified the
 projection. （已译） *)
Lemma cong_identifies {C : Category} (R : HomRelT C) {x y : C}
  {f g : x ~> y} (Hr : R x y f g) :
  fmap[QuotientCongProj R] f ≈ fmap[QuotientCongProj R] g.
Proof. exact (cc_gen Hr). Qed.

(** Proposition 1, clause (ii): any 函子 merging [R] factors through the
 projection, no side condition target [D]. （已译） *)
Definition QuotientCongLift {C D : Category} (R : HomRelT C) (F : C ⟶ D)
  (HF : ∀ x y (f g : x ~> y), R x y f g → fmap[F] f ≈ fmap[F] g) :
  QuotientCong C R ⟶ D :=
  @QuotientLift C (CongClosure R) (CongClosure_Congruence R) D F
    (fun x y f g Hc => @cc_kernel C R D F HF x y f g Hc).
