Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * The fibre product 范畴, pullbacks 范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/comma+object
 nLab:      https://ncatlab.org/nlab/show/pseudopullback
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories

   本文件给出拉回实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A small transport kit *)

(* Functors commute [hom_cast], endpoints being relabelled by
 [f_equal] 对象 map. Both sides become [fmap[P] f] once two
 equalities eliminated. （已译） *)
Lemma fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(* Reading [hom_cast] equation conjugation, orientation the
 natural-同构 coherence [Functor_Setoid] wants. （已译） *)
Lemma hom_cast_shift {X : Category} {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) (g : a' ~> b') :
  hom_cast ea eb f ≈ g → f ≈ id_cast (eq_sym eb) ∘ g ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite <- Hg; cat. Qed.

(* Under uniqueness of identity proofs on objects a [hom_cast] does not
   depend on WHICH proofs of its two endpoint equations it is given. *)
Lemma fp_hom_cast_irr {X : Category} (uip : ObjUIP X) {a b a' b' : X}
      (e1 e1' : a = a') (e2 e2' : b = b') (f : a ~> b) :
  hom_cast e1 e2 f = hom_cast e1' e2' f.
Proof. now rewrite (uip _ _ e1 e1'), (uip _ _ e2 e2'). Qed.

(* One [hom_cast] equation, read as a commuting square of [id_cast]s. *)
Lemma cast_of_hom_cast {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → id_cast eb ∘ g ≈ h ∘ id_cast ea.
Proof. destruct ea, eb; simpl; intros Hg; rewrite id_left, id_right; auto. Qed.

(* 相关说明。 （已译） *)
Lemma hom_cast_left_refl {X : Category} {a b b' : X} (eb : b = b')
      (g : a ~> b) : hom_cast eq_refl eb g ≈ id_cast eb ∘ g.
Proof. destruct eb; cat. Qed.

(* An equality of comma objects transports the morphism they carry. *)
Lemma comma_obj_eq_inv {A B D : Category} {S : A ⟶ D} {T : B ⟶ D}
      {x y : (S ↓ T)} (E : x = y) :
  hom_cast (f_equal (fun z => fobj[S] (fst ``z)) E)
           (f_equal (fun z => fobj[T] (snd ``z)) E) (`2 x) = `2 y.
Proof. destruct E; reflexivity. Qed.

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma slice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : snd ``h = d) :
  ((fst ``h, d); hom_cast eq_refl eh (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* 相关说明。 （已译） *)
Lemma hom_cast_right_refl {X : Category} {a a' b : X} (ea : a = a')
      (g : a ~> b) : hom_cast ea eq_refl g ≈ g ∘ id_cast (eq_sym ea).
Proof. destruct ea; cat. Qed.

(* An arrow whose domain is [d] IS the coslice object under [d] it
   determines. *)
Lemma coslice_arrow_eta {D : Category} (d : D) (h : @Arrow D)
      (eh : fst ``h = d) :
  ((d, snd ``h); hom_cast eh eq_refl (`2 h)) = h.
Proof. destruct h as [[a b] g]; simpl in *; destruct eh; reflexivity. Defined.

(* Turning a [hom_cast] equation around. *)
Lemma hom_cast_flip {X : Category} {a a' b b' : X}
      (ea : a = a') (eb : b = b') (g : a ~> b) (h : a' ~> b') :
  hom_cast ea eb g ≈ h → hom_cast (eq_sym ea) (eq_sym eb) h ≈ g.
Proof. destruct ea, eb; simpl; intros Hg; now symmetry. Qed.

Section FibreProduct.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition FibreProduct : Category := {|
  obj    := ∃ p : A ∏ B, F (fst p) = G (snd p);
  hom    := fun x y =>
    ∃ f : (fst ``x ~{A}~> fst ``y) * (snd ``x ~{B}~> snd ``y),
      hom_cast (`2 x) (`2 y) (fmap[F] (fst f)) ≈ fmap[G] (snd f);
  homset := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros x; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.
Next Obligation.
  intros x y z f g; simpl.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp (`2 x) (`2 y) (`2 z)).
  rewrite (`2 f), (`2 g).
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation. intros; simpl; split; now rewrite id_left. Qed.
Next Obligation. intros; simpl; split; now rewrite id_right. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc. Qed.
Next Obligation. intros; simpl; split; apply comp_assoc_sym. Qed.

Program Instance FP_fst : FibreProduct ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance FP_snd : FibreProduct ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma FP_obj_eq (uip : ObjUIP C) (x y : FibreProduct)
      (e1 : fst ``x = fst ``y) (e2 : snd ``x = snd ``y) :
  { e : x = y & (f_equal (fobj[FP_fst]) e = e1)
              * (f_equal (fobj[FP_snd]) e = e2) }.
Proof.
  destruct x as [[a b] p], y as [[a' b'] p']; simpl in *.
  destruct e1, e2, (uip _ _ p p').
  exists eq_refl; split; reflexivity.
Defined.

(* * ** The projection square commutes, both ambient 范畴 （已译） *)

(* Strictly: 对象 component IS equality carried 对象, and
 态射 component IS equation carried 态射. （已译） *)
Definition FP_commutes_strict :
  F ∘[StrictCat] FP_fst ≈[StrictCat] G ∘[StrictCat] FP_snd :=
  @Build_strict_eq FibreProduct C (F ◯ FP_fst) (G ◯ FP_snd)
                   (fun x : FibreProduct => `2 x)
                   (fun (x y : FibreProduct) (f : x ~> y) => `2 f).

(* Weakly: same data read natural 同构, each component the
 [id_cast] 对象's equality. （已译） *)
Program Definition FP_commutes_cat :
  F ∘[Cat] FP_fst ≈[Cat] G ∘[Cat] FP_snd :=
  (fun x => id_cast_iso (`2 x); _).
Next Obligation.
  intros x y f.
  pose proof (`2 f) as Hf; cbv beta in Hf.
  simpl.
  now apply hom_cast_shift.
Qed.

(* 相关说明。 （已译） *)

Section Mediator.

Context {Q : Category}.
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

Program Definition FP_med : Q ⟶ FibreProduct := {|
  fobj := fun x => ((q1 x, q2 x); `1 Hsq x);
  fmap := fun x y f => ((fmap[q1] f, fmap[q2] f); strict_fmap_cast Hsq f)
|}.
Next Obligation. intros x y f g Hfg; split; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(* Both triangles hold [eq_refl] 对象 component: mediator's
 first coordinate IS [q1] second IS [q2], definitionally. （已译） *)
Definition FP_med_fst : FP_fst ∘[StrictCat] FP_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q A (FP_fst ◯ FP_med) q1 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition FP_med_snd : FP_snd ∘[StrictCat] FP_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q B (FP_snd ◯ FP_med) q2 (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma FP_med_unique (uip : ObjUIP C) (v : Q ⟶ FibreProduct)
      (H1 : FP_fst ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : FP_snd ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] FP_med.
Proof.
  refine (@Build_strict_eq Q FibreProduct v FP_med
            (fun x => `1 (FP_obj_eq uip (v x) (FP_med x)
                                    (`1 H1 x) (`1 H2 x))) _).
  intros x y f.
  pose proof (`2 (FP_obj_eq uip (v x) (FP_med x) (`1 H1 x) (`1 H2 x)))
    as [P1x P2x].
  pose proof (`2 (FP_obj_eq uip (v y) (FP_med y) (`1 H1 y) (`1 H2 y)))
    as [P1y P2y].
  split.
  - etransitivity;
      [ exact (fmap_hom_cast FP_fst _ _ (fmap[v] f)) | ].
    rewrite P1x, P1y.
    exact (strict_fmap_cast H1 f).
  - etransitivity;
      [ exact (fmap_hom_cast FP_snd _ _ (fmap[v] f)) | ].
    rewrite P2x, P2y.
    exact (strict_fmap_cast H2 f).
Qed.

End Mediator.

(** ** The strict pullback *)

Definition FibreProduct_IsPullback (uip : ObjUIP C) :
  @IsPullback StrictCat A B C F G FibreProduct FP_fst FP_snd.
Proof.
  unshelve refine {| is_pullback_commutes := FP_commutes_strict |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := FP_med q1 q2 Hsq |}.
  - split; [ exact (FP_med_fst q1 q2 Hsq) | exact (FP_med_snd q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry.
    exact (FP_med_unique q1 q2 Hsq uip v Hv1 Hv2).
Defined.

Definition FibreProduct_Pullback (uip : ObjUIP C) :
  @Pullback StrictCat A B C F G :=
  is_pullback_pullback (FibreProduct_IsPullback uip).

End FibreProduct.

(* * ** Packaging: all pullbacks StrictCat, under blanket 假设 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ObjUIP_of_ObjDecEq {C : Category} `{@ObjDecEq C} : ObjUIP C :=
  fun x y p q => @obj_uip C _ x y p q.

Definition FibreProduct_IsPullback_dec {A B C : Category}
           (F : A ⟶ C) (G : B ⟶ C) `{@ObjDecEq C} :
  @IsPullback StrictCat A B C F G (FibreProduct F G) (FP_fst F G) (FP_snd F G)
  := FibreProduct_IsPullback F G ObjUIP_of_ObjDecEq.

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StrictCat_HasPullbacks (uip : ∀ C : Category, ObjUIP C) :
  HasPullbacks StrictCat.
Proof.
  constructor; intros A B C F G.
  exact (FibreProduct_Pullback F G (uip C)).
Defined.

(* 相关说明。 （已译） *)

Section CatMeasurement.

(* Any two 函子 进入 terminal 范畴 naturally isomorphic; this
 [one_unique] at [Cat_Terminal], it all 普遍性质 of
 cospans below needs. （已译） *)
Lemma one_functors_equiv {Q : Category} (u v : Q ⟶ _1) : u ≈[Cat] v.
Proof. now apply (@one_unique Cat Cat_Terminal). Qed.

(* A cospan two points C, 同构 between them supplying
 交换方块 Cat. （已译） *)
Program Definition point_cospan_square {C : Category} {x y : C} (i : x ≅ y) :
  Diagonal _1 x ∘[Cat] Id[_1] ≈[Cat] Diagonal _1 y ∘[Cat] Id[_1] :=
  (fun _ => i; _).
Next Obligation.
  rewrite id_right.
  symmetry; apply iso_from_to.
Qed.

(* Such a cospan DOES have a pullback in Cat, namely the terminal category:
   every competing square factors through [Erase], uniquely up to natural
   isomorphism, because [Cat(Q, 1)] is a singleton up to [≈]. *)
Definition point_cospan_Cat_IsPullback {C : Category} {x y : C} (i : x ≅ y) :
  @IsPullback Cat _1 _1 C (Diagonal _1 x) (Diagonal _1 y) _1 Id[_1] Id[_1].
Proof.
  unshelve refine {| is_pullback_commutes := point_cospan_square i |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Erase Q |}.
  - split; apply one_functors_equiv.
  - intros v _; apply one_functors_equiv.
Defined.

(* The witness: two 对象 范畴 that are isomorphic without being
 equal. [Indiscrete bool] has exactly one arrow between any two points, so
 [true ≅ false] there, while [true = false] is empty.（已译） *)
Definition IB : Category := Indiscrete bool.

Program Definition IB_iso : @Isomorphism IB true false := {| to := tt;
                                                             from := tt |}.

Definition IBtrue  : _1 ⟶ IB := @Diagonal IB _1 true.
Definition IBfalse : _1 ⟶ IB := @Diagonal IB _1 false.

(* The strict fibre product cospan has NO 对象 at all. （已译） *)
Lemma IB_FibreProduct_empty : obj[FibreProduct IBtrue IBfalse] → False.
Proof. intros x; pose proof (`2 x) as Hx; simpl in Hx; discriminate. Qed.

(*
   本节说明函子、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem FibreProduct_not_Cat_pullback :
  @IsPullback Cat _1 _1 IB IBtrue IBfalse
              (FibreProduct IBtrue IBfalse)
              (FP_fst IBtrue IBfalse) (FP_snd IBtrue IBfalse) → False.
Proof.
  intros HP.
  destruct (is_pullback_ump HP _1 Id[_1] Id[_1] (point_cospan_square IB_iso))
    as [u _ _].
  exact (IB_FibreProduct_empty (u ttt)).
Qed.

End CatMeasurement.

(* * ** Necessity: uniform uniqueness IS 假设 （已译） *)

Section Necessity.

(* The indiscrete 范畴 X has 对象 type X, so loop at point X
 literally loop at 对象. Its homs [unit], keeps every
 态射 obligation below trivial. （已译） *)
Definition IX (X : Type) : Category := Indiscrete X.

Lemma punit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition IXpt {X : Type} (x : X) : _1 ⟶ IX X := @Diagonal (IX X) _1 x.

(* Each loop [p : x = x] names 函子 进入 fibre product cospan
 1 --x--> IX X <--x-- 1, every such 函子 satisfies both triangles. （已译） *)
Program Definition loop_functor {X : Type} {x : X} (p : x = x) :
  _1 ⟶ FibreProduct (IXpt x) (IXpt x) := {|
  fobj := fun _ => ((ttt, ttt); p);
  fmap := fun _ _ _ => ((id, id); _)
|}.
Next Obligation.
  intros; simpl.
  match goal with |- ?a = ?b => now destruct a, b end.
Qed.

Lemma loop_functor_fst {X : Type} {x : X} (p : x = x) :
  FP_fst (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_fst (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma loop_functor_snd {X : Type} {x : X} (p : x = x) :
  FP_snd (IXpt x) (IXpt x) ∘[StrictCat] loop_functor p ≈[StrictCat] Id[_1].
Proof.
  refine (@Build_strict_eq _1 _1
            (FP_snd (IXpt x) (IXpt x) ◯ loop_functor p) Id[_1]
            (fun o => punit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Definition punit_pair_dec (a b : poly_unit * poly_unit) : {a = b} + {a <> b}.
Proof. destruct a as [[] []], b as [[] []]; now left. Defined.

(*
   本节说明拉回/推出、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem FP_uniqueness_forces_UIP
        (K : ∀ (A B C : Category) (F : A ⟶ C) (G : B ⟶ C),
               @IsPullback StrictCat A B C F G (FibreProduct F G)
                           (FP_fst F G) (FP_snd F G)) :
  ∀ (X : Type) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (is_pullback_ump (K _1 _1 (IX X) (IXpt x) (IXpt x))
                  _1 Id[_1] Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (loop_functor p)
                  (loop_functor_fst p, loop_functor_snd p)) as Up.
    pose proof (uniqueness U (loop_functor (@eq_refl _ x))
                  (loop_functor_fst eq_refl, loop_functor_snd eq_refl)) as Ur.
    assert (Hpq : loop_functor p ≈[StrictCat] loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ punit_pair_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End Necessity.


(* * ** Comma 范畴 pullbacks arrow-范畴 projections （已译） *)

Section SliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Set Default Proof Using "All".

(* 相关说明。 （已译） *)
Program Definition Slice_proj : Slice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: 对象 slice IS arrow codomain c. （已译） *)
Program Definition Slice_Arrow : Slice C c ⟶ @Arrow C := {|
  fobj := fun x => ((`1 x, c); `2 x);
  fmap := fun _ _ f => ((`1 f, id); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_left; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ exact Hfg | reflexivity ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ reflexivity | now rewrite id_left ].
Qed.

(* A strict 函子 equality 进入 slice settled [Slice_proj]
 reading, slice hom-setoid being C underlying arrow. （已译） *)
Lemma slice_strict_eq {Q : Category} (u v : Q ⟶ Slice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Slice_proj]) (eo z))
                       (f_equal (fobj[Slice_proj]) (eo w))
                       (fmap[Slice_proj] (fmap[u] f))
                ≈ fmap[Slice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Slice C c) u v eo _).
  intros z w f.
  change (fmap[Slice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Slice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Slice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma slice_arrow_reflect (x y : Slice C c)
      (E : Slice_Arrow x = Slice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e2 (@eq_refl _ c)) in HE.
  destruct e1, HE; reflexivity.
Qed.

Section SliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_cod ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Slice_med : Q ⟶ Slice C c := {|
  fobj := fun z => (fst ``(q1 z); hom_cast eq_refl (`1 Hsq z) (`2 (q1 z)));
  fmap := fun z w f => (fst ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; simpl.
  rewrite !hom_cast_left_refl.
  rewrite <- comp_assoc.
  transitivity (id_cast (`1 Hsq w)
                  ∘ (fmap[Arrow_cod] (fmap[q1] f) ∘ `2 (q1 z))).
  { apply compose_respects;
      [ reflexivity | exact (Arrow_square _ _ (fmap[q1] f)) ]. }
  rewrite comp_assoc.
  apply compose_respects; [ | reflexivity ].
  etransitivity;
    [ exact (cast_of_hom_cast _ _ _ _ (strict_fmap_cast Hsq f)) | ].
  exact (id_left (id_cast (`1 Hsq z))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (fst (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (fst (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (fst (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Slice_med_arrow :
  Slice_Arrow ∘[StrictCat] Slice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Slice_Arrow ◯ Slice_med) q1
            (fun z => slice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Slice_Arrow ◯ Slice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
Qed.

Lemma Slice_med_erase :
  Erase (Slice C c) ∘[StrictCat] Slice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Slice C c) ◯ Slice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Slice_med_unique (v : Q ⟶ Slice C c)
      (H1 : Slice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Slice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Slice_med.
Proof.
  refine (slice_strict_eq v Slice_med
            (fun z => slice_arrow_reflect (v z) (Slice_med z)
                        (eq_trans (`1 H1 z) (eq_sym (`1 Slice_med_arrow z))))
            _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_dom]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_dom]) (`1 H1 w))).
  transitivity (fmap[Arrow_dom]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Slice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_dom _ _ (fmap[Slice_Arrow ◯ v] f)). }
  exact (fst (strict_fmap_cast H1 f)).
Qed.

End SliceMediator.

Definition Slice_commutes :
  Arrow_cod ∘[StrictCat] Slice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Slice C c).
Proof.
  refine (@Build_strict_eq (Slice C c) C
            (Arrow_cod ◯ Slice_Arrow) (Diagonal _1 c ◯ Erase (Slice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Slice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_cod (Diagonal _1 c)
              (Slice C c) Slice_Arrow (Erase (Slice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Slice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Slice_med q1 q2 Hsq |}.
  - split; [ exact (Slice_med_arrow q1 q2 Hsq)
           | exact (Slice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Slice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End SliceAsPullback.

Section CosliceAsPullback.

Context {C : Category}.
Context (c : C).
Context (uip : ObjUIP C).

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.
Local Set Default Proof Using "All".

Program Definition Coslice_proj : Coslice C c ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.
Next Obligation. now repeat intro. Qed.
Next Obligation. now intros. Qed.
Next Obligation. now intros. Qed.

(* The first leg: 对象 coslice IS arrow domain c. （已译） *)
Program Definition Coslice_Arrow : Coslice C c ⟶ @Arrow C := {|
  fobj := fun x => ((c, `1 x); `2 x);
  fmap := fun _ _ f => ((id, `1 f); _)
|}.
Next Obligation. intros x y f; simpl; rewrite id_right; apply (`2 f). Qed.
Next Obligation. intros x y f g Hfg; split; [ reflexivity | exact Hfg ]. Qed.
Next Obligation. intros x; split; reflexivity. Qed.
Next Obligation.
  intros x y z f g; split; simpl; [ now rewrite id_left | reflexivity ].
Qed.

Lemma coslice_strict_eq {Q : Category} (u v : Q ⟶ Coslice C c)
      (eo : ∀ z, u z = v z)
      (em : ∀ z w (f : z ~> w),
              hom_cast (f_equal (fobj[Coslice_proj]) (eo z))
                       (f_equal (fobj[Coslice_proj]) (eo w))
                       (fmap[Coslice_proj] (fmap[u] f))
                ≈ fmap[Coslice_proj] (fmap[v] f)) :
  u ≈[StrictCat] v.
Proof.
  refine (@Build_strict_eq Q (Coslice C c) u v eo _).
  intros z w f.
  change (fmap[Coslice_proj] (hom_cast (eo z) (eo w) (fmap[u] f))
            ≈ fmap[Coslice_proj] (fmap[v] f)).
  etransitivity;
    [ exact (fmap_hom_cast Coslice_proj (eo z) (eo w) (fmap[u] f)) | ].
  exact (em z w f).
Qed.

Lemma coslice_arrow_reflect (x y : Coslice C c)
      (E : Coslice_Arrow x = Coslice_Arrow y) : x = y.
Proof.
  pose proof (comma_obj_eq_inv E) as HE.
  set (e1 := f_equal (fun z => fobj[Id[C]] (fst ``z)) E) in HE.
  set (e2 := f_equal (fun z => fobj[Id[C]] (snd ``z)) E) in HE.
  clearbody e1 e2; clear E.
  destruct x as [a f], y as [a' g]; simpl in *.
  rewrite (uip _ _ e1 (@eq_refl _ c)) in HE.
  destruct e2, HE; reflexivity.
Qed.

Section CosliceMediator.

Context {Q : Category}.
Context (q1 : Q ⟶ @Arrow C) (q2 : Q ⟶ _1).
Context (Hsq : Arrow_dom ∘[StrictCat] q1
                 ≈[StrictCat] Diagonal _1 c ∘[StrictCat] q2).

Program Definition Coslice_med : Q ⟶ Coslice C c := {|
  fobj := fun z => (snd ``(q1 z); hom_cast (`1 Hsq z) eq_refl (`2 (q1 z)));
  fmap := fun z w f => (snd ``(fmap[q1] f); _)
|}.
Next Obligation.
  intros z w f; cbv beta.
  transitivity (`2 (q1 w) ∘ id_cast (eq_sym (`1 Hsq w))).
  { exact (hom_cast_right_refl _ _). }
  transitivity (snd ``(fmap[q1] f)
                  ∘ (`2 (q1 z) ∘ id_cast (eq_sym (`1 Hsq z)))).
  2: { apply compose_respects;
         [ reflexivity | symmetry; exact (hom_cast_right_refl _ _) ]. }
  rewrite comp_assoc.
  transitivity ((`2 (q1 w) ∘ fmap[Arrow_dom] (fmap[q1] f))
                  ∘ id_cast (eq_sym (`1 Hsq z))).
  2: { apply compose_respects;
         [ exact (Arrow_square _ _ (fmap[q1] f)) | reflexivity ]. }
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity | ].
  etransitivity;
    [ symmetry; exact (id_right (id_cast (eq_sym (`1 Hsq w)))) | ].
  exact (cast_of_hom_cast _ _ _ _
           (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f))).
Qed.
Next Obligation.
  intros z w f g Hfg.
  exact (snd (@fmap_respects _ _ q1 z w f g Hfg)).
Qed.
Next Obligation. intros z; exact (snd (@fmap_id _ _ q1 z)). Qed.
Next Obligation.
  intros z w u f g; exact (snd (@fmap_comp _ _ q1 z w u f g)).
Qed.

Lemma Coslice_med_arrow :
  Coslice_Arrow ∘[StrictCat] Coslice_med ≈[StrictCat] q1.
Proof.
  refine (@Build_strict_eq Q (@Arrow C) (Coslice_Arrow ◯ Coslice_med) q1
            (fun z => coslice_arrow_eta c (q1 z) (`1 Hsq z)) _).
  intros z w f; split.
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_dom _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ (eq_sym (`1 Hsq z))
                            _ (eq_sym (`1 Hsq w))).
    exact (hom_cast_flip _ _ _ _ (strict_fmap_cast Hsq f)).
  - etransitivity;
      [ exact (fmap_hom_cast Arrow_cod _ _
                 (fmap[Coslice_Arrow ◯ Coslice_med] f)) | ].
    rewrite (fp_hom_cast_irr uip _ eq_refl _ eq_refl).
    reflexivity.
Qed.

Lemma Coslice_med_erase :
  Erase (Coslice C c) ∘[StrictCat] Coslice_med ≈[StrictCat] q2.
Proof.
  refine (@Build_strict_eq Q _1
            (Erase (Coslice C c) ◯ Coslice_med) q2
            (fun z => punit_eq (q2 z)) _).
  intros z w f; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

Lemma Coslice_med_unique (v : Q ⟶ Coslice C c)
      (H1 : Coslice_Arrow ∘[StrictCat] v ≈[StrictCat] q1)
      (H2 : Erase (Coslice C c) ∘[StrictCat] v ≈[StrictCat] q2) :
  v ≈[StrictCat] Coslice_med.
Proof.
  refine (coslice_strict_eq v Coslice_med
            (fun z => coslice_arrow_reflect (v z) (Coslice_med z)
                        (eq_trans (`1 H1 z)
                                  (eq_sym (`1 Coslice_med_arrow z)))) _).
  intros z w f.
  rewrite (fp_hom_cast_irr uip _ (f_equal (fobj[Arrow_cod]) (`1 H1 z))
                          _ (f_equal (fobj[Arrow_cod]) (`1 H1 w))).
  transitivity (fmap[Arrow_cod]
                  (hom_cast (`1 H1 z) (`1 H1 w) (fmap[Coslice_Arrow ◯ v] f))).
  { symmetry;
      exact (fmap_hom_cast Arrow_cod _ _ (fmap[Coslice_Arrow ◯ v] f)). }
  exact (snd (strict_fmap_cast H1 f)).
Qed.

End CosliceMediator.

Definition Coslice_commutes :
  Arrow_dom ∘[StrictCat] Coslice_Arrow
    ≈[StrictCat] Diagonal _1 c ∘[StrictCat] Erase (Coslice C c).
Proof.
  refine (@Build_strict_eq (Coslice C c) C
            (Arrow_dom ◯ Coslice_Arrow)
            (Diagonal _1 c ◯ Erase (Coslice C c))
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

Definition Coslice_IsPullback :
  @IsPullback StrictCat (@Arrow C) _1 C Arrow_dom (Diagonal _1 c)
              (Coslice C c) Coslice_Arrow (Erase (Coslice C c)).
Proof.
  unshelve refine {| is_pullback_commutes := Coslice_commutes |}.
  intros Q q1 q2 Hsq.
  unshelve refine {| unique_obj := Coslice_med q1 q2 Hsq |}.
  - split; [ exact (Coslice_med_arrow q1 q2 Hsq)
           | exact (Coslice_med_erase q1 q2 Hsq) ].
  - intros v [Hv1 Hv2].
    symmetry; exact (Coslice_med_unique q1 q2 Hsq v Hv1 Hv2).
Defined.

End CosliceAsPullback.
