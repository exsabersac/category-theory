Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * A 范畴 幺半群 composable pairs (Mac Lane, CWM I.2, Remark 1) （已译） *)

(*
 nLab:  https://ncatlab.org/nlab/show/internal+category
   nLab:  https://ncatlab.org/nlab/show/span
   Book:  Mac Lane, Categories for the Working Mathematician, 2nd ed.,

   本文件给出幺半范畴中的幺半群对象：乘法 μ、单位 η，以及结合律与左右单位律（插入结合子/单位子使态射可复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、拉回/推出、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Two-sorted graphs *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Graph := {
  gobj : Type;                          (* the object sort O *)
  garr : Type;                          (* the arrow sort A *)
  garr_setoid : Setoid garr;            (* arrows are compared up to ≈ *)

  gdom : garr → gobj;                   (* dom : A → O *)
  gcod : garr → gobj;                   (* cod : A → O *)

  gdom_respects (a b : garr) :          (* ≈-equal arrows share a domain *)
    @equiv _ garr_setoid a b → gdom a = gdom b;
  gcod_respects (a b : garr) :          (* ≈-equal arrows share a codomain *)
    @equiv _ garr_setoid a b → gcod a = gcod b
}.

Arguments gdom {_} _.
Arguments gcod {_} _.
Arguments gdom_respects {_ _ _} _.
Arguments gcod_respects {_ _ _} _.

#[export] Existing Instance garr_setoid.

(** ** The composable pairs A ×_O A *)

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Composable (G : Graph) := {
  cp_outer : garr G;                             (* g *)
  cp_inner : garr G;                             (* f *)
  cp_match : gdom cp_outer = gcod cp_inner       (* the composability equation *)
}.

Arguments cp_outer {_} _.
Arguments cp_inner {_} _.
Arguments cp_match {_} _.
Arguments Build_Composable {_} _ _ _.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Composable_equiv {G : Graph} (p q : Composable G) : Type :=
  (cp_outer p ≈ cp_outer q) ∧ (cp_inner p ≈ cp_inner q).

Definition Composable_Setoid (G : Graph) : Setoid (Composable G).
Proof.
  refine {| equiv := @Composable_equiv G; setoid_equiv := _ |}.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct X; split; now symmetry.
  - destruct X, X0; split; etransitivity; eassumption.
Defined.

(* Both projections respect that equivalence, so each is a setoid map
   `A ×_O A → A`. *)
Lemma cp_outer_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_outer p ≈ cp_outer q.
Proof. now intros [H _]. Qed.

Lemma cp_inner_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_inner p ≈ cp_inner q.
Proof. now intros [_ H]. Qed.

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Composable_med {G : Graph} {X : Type}
           (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x))
           (x : X) : Composable G :=
  Build_Composable (u x) (v x) (H x).

Lemma Composable_med_outer {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_outer (Composable_med u v H x) = u x.
Proof. reflexivity. Qed.

Lemma Composable_med_inner {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_inner (Composable_med u v H x) = v x.
Proof. reflexivity. Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Composable_ump_unique {G : Graph} {X : Type} (k k' : X → Composable G) :
  (∀ x, cp_outer (k x) ≈ cp_outer (k' x)) →
  (∀ x, cp_inner (k x) ≈ cp_inner (k' x)) →
  ∀ x, Composable_equiv (k x) (k' x).
Proof. intros Ho Hi x; split; [ apply Ho | apply Hi ]. Qed.

(* * ** The 幺半群 structure graph （已译） *)

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SpanMonoid (G : Graph) := {
  sm_unit : gobj G → garr G;                     (* e : O → A *)
  sm_unit_dom : ∀ x, gdom (sm_unit x) = x;       (* dom (e x) = x *)
  sm_unit_cod : ∀ x, gcod (sm_unit x) = x;       (* cod (e x) = x *)

  sm_mul (g f : garr G) : gdom g = gcod f → garr G;   (* m : A ×_O A → A *)

  sm_mul_dom : ∀ g f p, gdom (sm_mul g f p) = gdom f;  (* dom (m (g,f)) = dom f *)
  sm_mul_cod : ∀ g f p, gcod (sm_mul g f p) = gcod g;  (* cod (m (g,f)) = cod g *)

  (* 相关说明。 （已译） *)
  sm_mul_respects : ∀ g g' f f' p p',
    g ≈ g' → f ≈ f' → sm_mul g f p ≈ sm_mul g' f' p';

  sm_id_left  : ∀ f p, sm_mul (sm_unit (gcod f)) f p ≈ f;   (* e ∘ f = f *)
  sm_id_right : ∀ f p, sm_mul f (sm_unit (gdom f)) p ≈ f;   (* f ∘ e = f *)

  (* Associativity, in the orientation of [comp_assoc]. *)
  sm_assoc : ∀ h g f (p : gdom h = gcod g) (q : gdom g = gcod f)
               (pl : gdom (sm_mul h g p) = gcod f)
               (pr : gdom h = gcod (sm_mul g f q)),
    sm_mul h (sm_mul g f q) pr ≈ sm_mul (sm_mul h g p) f pl
}.

Arguments sm_unit {_} _ _.
Arguments sm_unit_dom {_} _ _.
Arguments sm_unit_cod {_} _ _.
Arguments sm_mul {_} _ _ _ _.
Arguments sm_mul_dom {_} _ _ _ _.
Arguments sm_mul_cod {_} _ _ _ _.
Arguments sm_mul_respects {_} _ {_ _ _ _} _ _ _ _.
Arguments sm_id_left {_} _ _ _.
Arguments sm_id_right {_} _ _ _.
Arguments sm_assoc {_} _ _ _ _ _ _ _ _.

(* 相关说明。 （已译） *)
Definition sm_pair_mul {G : Graph} (M : SpanMonoid G) (p : Composable G) : garr G :=
  sm_mul M (cp_outer p) (cp_inner p) (cp_match p).

(* ...and 柯里化的 respectfulness field precisely respectfulness the
 pullback setoid. Both directions, so neither presentation is
 privileged. （已译） *)
Lemma sm_pair_mul_respects {G : Graph} (M : SpanMonoid G) (p q : Composable G) :
  Composable_equiv p q → sm_pair_mul M p ≈ sm_pair_mul M q.
Proof.
  intros [Ho Hi]; unfold sm_pair_mul.
  now apply (sm_mul_respects M).
Qed.

Lemma sm_mul_of_pair {G : Graph} (M : SpanMonoid G)
      (m : Composable G → garr G)
      (Hm : ∀ p q, Composable_equiv p q → m p ≈ m q)
      (g g' f f' : garr G) (p : gdom g = gcod f) (p' : gdom g' = gcod f') :
  g ≈ g' → f ≈ f' → m (Build_Composable g f p) ≈ m (Build_Composable g' f' p').
Proof. intros Hg Hf; now apply Hm; split. Qed.

(* * ** From 幺半群 presentation [Category] （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SMHom (G : Graph) (x y : gobj G) : Type :=
  { a : garr G & (gdom a = x) ∧ (gcod a = y) }.

Definition sa_arr {G : Graph} {x y : gobj G} (f : SMHom G x y) : garr G := `1 f.
Definition sa_dom {G : Graph} {x y : gobj G} (f : SMHom G x y)
  : gdom (sa_arr f) = x := fst (`2 f).
Definition sa_cod {G : Graph} {x y : gobj G} (f : SMHom G x y)
  : gcod (sa_arr f) = y := snd (`2 f).

(* 相关说明。 （已译） *)
Definition SpanArrow_equiv {G : Graph} {x y : gobj G}
           (f g : SMHom G x y) : Type := sa_arr f ≈ sa_arr g.

Definition SpanArrow_Setoid (G : Graph) (x y : gobj G)
  : Setoid (SMHom G x y).
Proof.
  refine {| equiv := @SpanArrow_equiv G x y; setoid_equiv := _ |}.
  unfold SpanArrow_equiv.
  constructor.
  - intros f; reflexivity.
  - intros f g H; symmetry; exact H.
  - intros f g h H1 H2; transitivity (sa_arr g); assumption.
Defined.

(* The 恒等 at x unit e x, carrying two boundary laws. （已译） *)
Definition smc_id {G : Graph} (M : SpanMonoid G) (x : gobj G) : SMHom G x x :=
  (sm_unit M x; (sm_unit_dom M x, sm_unit_cod M x)).

(* 相关说明。 （已译） *)
Definition smc_match {G : Graph} {x y z : gobj G}
           (g : SMHom G y z) (f : SMHom G x y)
  : gdom (sa_arr g) = gcod (sa_arr f) :=
  eq_trans (sa_dom g) (eq_sym (sa_cod f)).

(* Composition 幺半群 multiplication; boundary laws the
 multiplication supply endpoint proofs result. （已译） *)
Definition smc_compose {G : Graph} (M : SpanMonoid G) {x y z : gobj G}
           (g : SMHom G y z) (f : SMHom G x y) : SMHom G x z :=
  (sm_mul M (sa_arr g) (sa_arr f) (smc_match g f);
    (eq_trans (sm_mul_dom M _ _ _) (sa_dom f),
     eq_trans (sm_mul_cod M _ _ _) (sa_cod g))).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Category_from_SpanMonoid {G : Graph} (M : SpanMonoid G) : Category.
Proof.
  unshelve refine (Build_Category' (SMHom G) (smc_id M) (@smc_compose G M)).
  - exact (SpanArrow_Setoid G).
  - proper.
    unfold smc_compose, sa_arr; simpl.
    now apply (sm_mul_respects M).
  - intros x y f.
    unfold smc_compose, smc_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pc.
    now apply (sm_id_left M).
  - intros x y f.
    unfold smc_compose, smc_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pd.
    now apply (sm_id_right M).
  - intros x y z w f g h.
    unfold smc_compose, sa_arr; simpl.
    apply (sm_assoc M).
Defined.

(* * ** Bundled arrows, transport along 对象 equalities （已译） *)

(* The bundled-arrow sigma ∃ x y, x ~> y, as a record. *)
Record BundledArrow (C : Category) := {
  asrc : C;
  atgt : C;
  aarr : asrc ~> atgt
}.

Arguments asrc {_} _.
Arguments atgt {_} _.
Arguments aarr {_} _.
Arguments Build_BundledArrow {_} _ _ _.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eq_trans_id_l {A : Type} {x y : A} (e : x = y) : eq_trans eq_refl e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_id_r {A : Type} {x y : A} (e : x = y) : eq_trans e eq_refl = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_sym_l {A : Type} {x y : A} (e : x = y) :
  eq_trans (eq_sym e) e = eq_refl.
Proof. destruct e; reflexivity. Qed.

(* Transport of a morphism along equalities of its two endpoints.  Everything
   in this section is proved by [destruct]ing the equalities in their general
   form (both endpoints universally quantified), so none of it uses UIP. *)
Definition hom_transport {C : Category} {x x' y y' : C}
           (p : x = x') (q : y = y') (f : x ~> y) : x' ~> y' :=
  match p in (_ = X) return (X ~> y') with
  | eq_refl => match q in (_ = Y) return (x ~> Y) with
               | eq_refl => f
               end
  end.

(* 相关说明。 （已译） *)
Arguments hom_transport : simpl never.

#[export]
Instance hom_transport_respects {C : Category} {x x' y y' : C}
         (p : x = x') (q : y = y') :
  Proper (equiv ==> equiv) (hom_transport p q).
Proof. destruct p, q; repeat intro; assumption. Qed.

Lemma hom_transport_refl {C : Category} {x y : C} (f : x ~> y) :
  hom_transport eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

Lemma hom_transport_trans {C : Category} {x1 x2 x3 y1 y2 y3 : C}
      (p : x1 = x2) (p' : x2 = x3) (q : y1 = y2) (q' : y2 = y3) (f : x1 ~> y1) :
  hom_transport p' q' (hom_transport p q f)
    = hom_transport (eq_trans p p') (eq_trans q q') f.
Proof. destruct p, p', q, q'; reflexivity. Qed.

Lemma hom_transport_sym_inv {C : Category} {x x' y y' : C}
      (p : x = x') (q : y = y') (f : x ~> y) :
  hom_transport (eq_sym p) (eq_sym q) (hom_transport p q f) = f.
Proof. destruct p, q; reflexivity. Qed.

Lemma hom_transport_id {C : Category} {x x' : C} (u : x = x') :
  hom_transport u u (id[x]) = id[x'].
Proof. destruct u; reflexivity. Qed.

(* Transport 复合 splits transport two outer endpoints;
 shared middle 对象 untouched. （已译） *)
Lemma hom_transport_comp {C : Category} {x x' y z z' : C}
      (p : x = x') (r : z = z') (f : y ~> z) (g : x ~> y) :
  hom_transport p r (f ∘ g)
    = hom_transport eq_refl r f ∘ hom_transport p eq_refl g.
Proof. destruct p, r; reflexivity. Qed.

(* Transport at the middle object slides across a composite. *)
Lemma hom_transport_slide {C : Category} {w x x' y : C}
      (u : x = x') (f : x ~> y) (g : w ~> x) :
  f ∘ g = hom_transport u eq_refl f ∘ hom_transport eq_refl u g.
Proof. destruct u; reflexivity. Qed.

(** ** The graph of a category *)

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition BundledArrow_equiv {C : Category} (a b : BundledArrow C) : Type :=
  { p : asrc a = asrc b &
  { q : atgt a = atgt b & hom_transport p q (aarr a) ≈ aarr b }}.

Definition BundledArrow_Setoid (C : Category) : Setoid (BundledArrow C).
Proof.
  refine {| equiv := @BundledArrow_equiv C; setoid_equiv := _ |}.
  constructor; repeat intro.
  - exists eq_refl, eq_refl; reflexivity.
  - destruct X as [p [q H]].
    exists (eq_sym p), (eq_sym q).
    rewrite <- H, hom_transport_sym_inv.
    reflexivity.
  - destruct X as [p [q H]], X0 as [p' [q' H']].
    exists (eq_trans p p'), (eq_trans q q').
    rewrite <- hom_transport_trans, H.
    exact H'.
Defined.

Definition Category_Graph (C : Category) : Graph.
Proof.
  unshelve refine {| gobj := obj[C]
                   ; garr := BundledArrow C
                   ; garr_setoid := BundledArrow_Setoid C
                   ; gdom := @asrc C
                   ; gcod := @atgt C |}.
  - intros a b H; exact (`1 H).
  - intros a b H; exact (`1 (`2 H)).
Defined.

(* * ** Rigidity: transport does not see 证明 it travelled along （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HomRigid (C : Category) : Type :=
  ∀ (x x' y y' : C) (p p' : x = x') (q q' : y = y') (f : x ~> y),
    hom_transport p q f ≈ hom_transport p' q' f.

Definition ObjUIP (C : Category) : Type :=
  ∀ (x y : C) (p q : x = y), p = q.

(* UIP on objects gives rigidity.  [ObjUIP] is axiom-free for every category
   whose object equality is decidable, by Hedberg's argument -- the discipline
   already used in Instance/FinSet.v and Theory/Multicategory/Endomorphism.v. *)
Lemma HomRigid_of_ObjUIP {C : Category} : ObjUIP C → HomRigid C.
Proof.
  intros U x x' y y' p p' q q' f.
  rewrite (U _ _ p p'), (U _ _ q q').
  reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_transport_compose_compare {C : Category} (rigid : HomRigid C)
      {xa ya xb yb x y z : C} (α : xa ~> ya) (β : xb ~> yb)
      (da : xa = y) (ca : ya = z) (db : xb = x) (cb : yb = y)
      (P : xa = yb) (dc : xb = x) (cc : ya = z) :
  hom_transport dc cc (α ∘ hom_transport eq_refl (eq_sym P) β)
    ≈ hom_transport da ca α ∘ hom_transport db cb β.
Proof.
  rewrite hom_transport_comp, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r.
  rewrite (hom_transport_slide da (hom_transport eq_refl cc α)
                                  (hom_transport dc (eq_sym P) β)).
  rewrite !hom_transport_trans, !eq_trans_id_l, !eq_trans_id_r.
  now rewrite (rigid _ _ _ _ da da cc ca α),
              (rigid _ _ _ _ dc db (eq_trans (eq_sym P) da) cb β).
Qed.

(* * ** From [Category] 幺半群 presentation （已译） *)

(* The unit 恒等箭头; multiplication 复合, after
 transporting inner arrow's codomain outer arrow's domain along
 composability 证明. （已译） *)
Definition arrow_unit {C : Category} (x : C) : BundledArrow C :=
  Build_BundledArrow x x (id[x]).

Definition arrow_mul {C : Category} (g f : BundledArrow C) (p : asrc g = atgt f)
  : BundledArrow C :=
  Build_BundledArrow (asrc f) (atgt g)
    (aarr g ∘ hom_transport eq_refl (eq_sym p) (aarr f)).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma arrow_mul_id_left {C : Category} (f : BundledArrow C) (p : atgt f = atgt f) :
  BundledArrow_equiv (arrow_mul (arrow_unit (atgt f)) f p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul, arrow_unit; simpl.
  exists eq_refl, p.
  rewrite id_left, hom_transport_trans, eq_trans_sym_l, eq_trans_id_l.
  now rewrite hom_transport_refl.
Qed.

Lemma arrow_mul_id_right {C : Category} (f : BundledArrow C) (p : asrc f = asrc f) :
  BundledArrow_equiv (arrow_mul f (arrow_unit (asrc f)) p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul, arrow_unit; simpl.
  exists (eq_sym p), eq_refl.
  rewrite hom_transport_comp, hom_transport_refl, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r, hom_transport_id.
  now rewrite id_right.
Qed.

(*
   本节说明等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma arrow_mul_respects {C : Category} (rigid : HomRigid C)
      (g g' f f' : BundledArrow C) (p : asrc g = atgt f) (p' : asrc g' = atgt f') :
  BundledArrow_equiv g g' → BundledArrow_equiv f f' →
  BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p').
Proof.
  destruct g as [xg yg φg], g' as [xg' yg' φg'],
           f as [xf yf φf], f' as [xf' yf' φf']; simpl in *.
  intros [pg [qg Hg]] [pf [qf Hf]]; simpl in *.
  destruct pg, qg, pf, qf.
  rewrite hom_transport_refl in Hg.
  rewrite hom_transport_refl in Hf.
  unfold BundledArrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl, Hg, Hf.
  now rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym p) (eq_sym p') φf').
Qed.

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma arrow_mul_assoc {C : Category} (rigid : HomRigid C)
      (h g f : BundledArrow C) (p : asrc h = atgt g) (q : asrc g = atgt f)
      (pl : asrc g = atgt f) (pr : asrc h = atgt g) :
  BundledArrow_equiv (arrow_mul h (arrow_mul g f q) pr)
              (arrow_mul (arrow_mul h g p) f pl).
Proof.
  destruct h as [xh yh χ], g as [xg yg γ], f as [xf yf φ]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl.
  rewrite (rigid xf xf yg xh eq_refl eq_refl (eq_sym pr) (eq_sym p)
                 (γ ∘ hom_transport eq_refl (eq_sym q) φ)).
  rewrite hom_transport_comp, hom_transport_refl.
  rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym q) (eq_sym pl) φ).
  apply comp_assoc.
Qed.

Definition Category_SpanMonoid (C : Category) (rigid : HomRigid C)
  : SpanMonoid (Category_Graph C).
Proof.
  unshelve refine (Build_SpanMonoid (Category_Graph C)
                     (@arrow_unit C) _ _ (@arrow_mul C) _ _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros g g' f f' pp pp' Hg Hf.
    exact (arrow_mul_respects rigid g g' f f' pp pp' Hg Hf).
  - intros f pp; exact (arrow_mul_id_left f pp).
  - intros f pp; exact (arrow_mul_id_right f pp).
  - intros h g f pp qq pl pr.
    exact (arrow_mul_assoc rigid h g f pp qq pl pr).
Defined.

(* * ** Round trip I: starting 幺半群 presentation （已译） *)

Section MonoidRoundTrip.

Context {G : Graph}.
Context (M : SpanMonoid G).

Notation C' := (Category_from_SpanMonoid M).

(* 相关说明。 （已译） *)
Lemma SpanMonoid_roundtrip_obj : obj[C'] = gobj G.
Proof. reflexivity. Qed.

(* Two homs constructed 范畴 identified exactly their
 underlying arrows are: endpoint proofs invisible. （已译） *)
Lemma span_hom_equiv {x y : gobj G} (f g : x ~{C'}~> y) :
  sa_arr f ≈ sa_arr g → f ≈ g.
Proof. intro H; exact H. Qed.

(* The 恒等 constructed 范畴 IS unit M ... （已译） *)
Lemma span_id_arr (x : gobj G) : sa_arr (@id C' x) = sm_unit M x.
Proof. reflexivity. Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma span_compose_arr {x y z : gobj G} (g : y ~{C'}~> z) (f : x ~{C'}~> y)
      (pf : gdom (sa_arr g) = gcod (sa_arr f)) :
  sa_arr (g ∘ f) ≈ sm_mul M (sa_arr g) (sa_arr f) pf.
Proof. apply (sm_mul_respects M); reflexivity. Qed.

(* 相关说明。 （已译） *)
Definition sm_bundle (a : garr G) : garr (Category_Graph C') :=
  @Build_BundledArrow (Category_from_SpanMonoid M)
    (gdom a) (gcod a) (a; (eq_refl, eq_refl)).

Definition sm_unbundle (u : garr (Category_Graph C')) : garr G := sa_arr (aarr u).

Lemma sm_bundle_dom (a : garr G) : gdom (sm_bundle a) = gdom a.
Proof. reflexivity. Qed.

Lemma sm_bundle_cod (a : garr G) : gcod (sm_bundle a) = gcod a.
Proof. reflexivity. Qed.

Lemma sm_unbundle_dom (u : garr (Category_Graph C')) :
  gdom (sm_unbundle u) = gdom u.
Proof. exact (sa_dom (aarr u)). Qed.

Lemma sm_unbundle_cod (u : garr (Category_Graph C')) :
  gcod (sm_unbundle u) = gcod u.
Proof. exact (sa_cod (aarr u)). Qed.

(* Transporting hom C' along 对象 equalities leaves underlying
 arrow alone -- C' stores endpoints separately arrow. （已译） *)
Lemma sa_arr_transport {x y x' y' : gobj G} (p : x = x') (q : y = y')
      (h : x ~{C'}~> y) :
  sa_arr (@hom_transport (Category_from_SpanMonoid M) x x' y y' p q h)
    = sa_arr h.
Proof. destruct p, q; reflexivity. Qed.

(* ONE 复合 round trip 恒等 nose. （已译） *)
Lemma sm_unbundle_bundle (a : garr G) : sm_unbundle (sm_bundle a) = a.
Proof. reflexivity. Qed.

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sm_bundle_unbundle (u : garr (Category_Graph C')) :
  sm_bundle (sm_unbundle u) ≈ u.
Proof.
  destruct u as [x y h].
  exists (sa_dom h), (sa_cod h).
  apply span_hom_equiv.
  now rewrite sa_arr_transport.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sm_bundle_respects (a b : garr G) : a ≈ b → sm_bundle a ≈ sm_bundle b.
Proof.
  intro H.
  exists (gdom_respects H), (gcod_respects H).
  apply span_hom_equiv.
  rewrite sa_arr_transport.
  exact H.
Qed.

Lemma sm_unbundle_respects (u v : garr (Category_Graph C')) :
  u ≈ v → sm_unbundle u ≈ sm_unbundle v.
Proof.
  intros [p [q H]]; unfold sm_unbundle.
  rewrite <- (sa_arr_transport p q (aarr u)).
  exact H.
Qed.

End MonoidRoundTrip.

(* Conjugating by identity isomorphisms does nothing.  This is the shape
   [Functor_Setoid]'s naturality condition takes when the two functors agree
   on objects definitionally, as both comparisons below do. *)
Lemma iso_id_conj {D : Category} {x y : D} (h : x ~> y) :
  from (@iso_id D y) ∘ h ∘ to (@iso_id D x) ≈ h.
Proof. simpl; now rewrite id_right, id_left. Qed.

(* 相关说明。 （已译） *)

Section CategoryRoundTrip.

Context (C : Category).
Context (rigid : HomRigid C).

Notation Rebuilt := (Category_from_SpanMonoid (Category_SpanMonoid C rigid)).

(* 相关说明。 （已译） *)
Lemma Category_roundtrip_obj : obj[Rebuilt] = obj[C].
Proof. reflexivity. Qed.

Definition rb_to {x y : C} (f : x ~> y) : x ~{Rebuilt}~> y :=
  (Build_BundledArrow x y f; (eq_refl, eq_refl)).

Definition rb_from {x y : C} (h : x ~{Rebuilt}~> y) : x ~> y :=
  @hom_transport C _ _ _ _ (sa_dom h) (sa_cod h) (aarr (sa_arr h)).

(* ONE 复合 恒等 nose. （已译） *)
Lemma rb_from_to {x y : C} (f : x ~> y) : rb_from (rb_to f) = f.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma rb_to_from {x y : C} (h : x ~{Rebuilt}~> y) : rb_to (rb_from h) ≈ h.
Proof.
  apply (span_hom_equiv (Category_SpanMonoid C rigid)).
  exists (eq_sym (sa_dom h)), (eq_sym (sa_cod h)).
  unfold rb_to, rb_from; simpl.
  now rewrite hom_transport_sym_inv.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Rebuild_to : C ⟶ Rebuilt.
Proof.
  unshelve refine (@Build_Functor C Rebuilt
                    (λ x : C, x)
                    (λ (x y : C) (f : x ~> y), rb_to f) _ _ _).
  - intros x y f g Hfg.
    apply (span_hom_equiv (Category_SpanMonoid C rigid)).
    exists eq_refl, eq_refl.
    now rewrite hom_transport_refl.
  - reflexivity.
  - reflexivity.
Defined.

Definition Rebuild_from : Rebuilt ⟶ C.
Proof.
  unshelve refine (@Build_Functor Rebuilt C
                    (λ x : Rebuilt, x)
                    (λ (x y : Rebuilt) (h : x ~{Rebuilt}~> y), rb_from h) _ _ _).
  - intros x y h h' Hh.
    destruct Hh as [pp [qq HH]].
    unfold rb_from.
    rewrite <- HH, hom_transport_trans.
    apply rigid.
  - reflexivity.
  - intros x y z h h'.
    unfold rb_from; simpl.
    apply (hom_transport_compose_compare rigid).
Defined.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Category_monoid_iso : C ≅[Cat] Rebuilt.
Proof.
  unshelve refine (@Build_Isomorphism Cat C Rebuilt Rebuild_to Rebuild_from _ _).
  - exists (λ x, iso_id).
    intros x y h.
    rewrite iso_id_conj.
    apply rb_to_from.
  - exists (λ x, iso_id).
    intros x y f.
    rewrite iso_id_conj.
    reflexivity.
Defined.

End CategoryRoundTrip.

(* ------------------------------------------------------------------------ *)
(* * ** Necessity [HomRigid]: reverse-mathematics 定理 （已译） *)

(*
   本节说明 Monoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma etr_assoc {X : Type} {u v w z : X} (i : u = v) (j : v = w) (k : w = z) :
  eq_trans i (eq_trans j k) = eq_trans (eq_trans i j) k.
Proof. destruct i, j, k; reflexivity. Qed.

#[local] Set Default Proof Using "All".

Section Countermodel.

(* An arbitrary type with an arbitrary point. *)
Context (A : Type) (a : A).

(* Objects: [option A].  [None] is a RIGID point -- its loop space is
   provably contractible ([none_loop]) whatever A is -- while [Some a] is
   FLOPPY: its loops are exactly the loops of A at a. *)
Definition ob : Type := option A.
Definition pt (x : ob) : A := match x with None => a | Some b => b end.

Definition PtCat : Category.
Proof.
  unshelve refine (Build_Category' (fun x y : ob => pt x = pt y)
                     (fun _ => eq_refl)
                     (fun x y z (g : pt y = pt z) (f : pt x = pt y) =>
                        eq_trans f g)).
  - intros x y.
    exact {| equiv := @eq (pt x = pt y); setoid_equiv := eq_equivalence |}.
  - intros x y z g g2 Hg f f2 Hf; simpl in *; now subst.
  - intros; apply eq_trans_id_r.
  - intros; apply eq_trans_id_l.
  - intros; symmetry; apply etr_assoc.
Defined.

(** 本节：The loop space [None] contractible, constructively, every A. （已译） *)
Definition ocode (y : ob) : Type :=
  match y with None => unit | Some _ => Empty_set end.

Definition oenc {y : ob} (e : @eq ob None y) : ocode y :=
  match e in (_ = z) return ocode z with eq_refl => tt end.

Definition odec {y : ob} (c : ocode y) : @eq ob None y :=
  match y return ocode y -> @eq ob None y with
  | None   => fun _ => eq_refl
  | Some _ => fun c => match c with end
  end c.

Lemma odec_oenc {y : ob} (e : @eq ob None y) : odec (oenc e) = e.
Proof. destruct e; reflexivity. Qed.

Lemma none_loop (e : @eq ob None None) : e = eq_refl.
Proof. exact (eq_sym (odec_oenc e)). Qed.

(** [f_equal pt] undoes [f_equal Some]; general in both endpoints. *)
Lemma pt_Some {u v : A} (w : u = v) : f_equal pt (f_equal (@Some A) w) = w.
Proof. destruct w; reflexivity. Qed.

Lemma pt_sym {x y : ob} (w : x = y) :
  f_equal pt (eq_sym w) = eq_sym (f_equal pt w).
Proof. destruct w; reflexivity. Qed.

(** How [hom_transport] computes in PtCat. *)
Lemma ht_pt {x y y' : ob} (q : y = y') (h : x ~{PtCat}~> y) :
  @hom_transport PtCat x x y y' eq_refl q h = eq_trans h (f_equal pt q).
Proof. destruct q; reflexivity. Qed.

(** The two test arrows: [fA : None -> Some a] [gA : Some -> None].
 Their 复合 lands RIGID corner [None -> None]. （已译） *)
Definition fA : BundledArrow PtCat := @Build_BundledArrow PtCat None (Some a) eq_refl.
Definition gA : BundledArrow PtCat := @Build_BundledArrow PtCat (Some a) None eq_refl.

Lemma fA_self : BundledArrow_equiv fA fA.
Proof. exists eq_refl, eq_refl; reflexivity. Qed.

Lemma gA_self : BundledArrow_equiv gA gA.
Proof. exists eq_refl, eq_refl; reflexivity. Qed.

Lemma forces_loop
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p'))
  (e : a = a) : e = eq_refl.
Proof.
  pose (p  := f_equal (@Some A) e : @eq ob (Some a) (Some a)).
  pose (p' := eq_refl : @eq ob (Some a) (Some a)).
  specialize (K PtCat gA gA fA fA p p' gA_self fA_self).
  destruct K as [P [Q H]].
  rewrite (none_loop P), (none_loop Q) in H.
  assert (H2 :
    eq_trans (@hom_transport PtCat None None (Some a) (Some a)
                eq_refl (eq_sym p) (eq_refl : pt None = pt (Some a)))
             (eq_refl : pt (Some a) = pt None)
  = eq_trans (@hom_transport PtCat None None (Some a) (Some a)
                eq_refl (eq_sym p') (eq_refl : pt None = pt (Some a)))
             (eq_refl : pt (Some a) = pt None)) by exact H.
  rewrite !(ht_pt _ (eq_refl : pt None = pt (Some a))) in H2.
  rewrite !eq_trans_id_l, !eq_trans_id_r in H2.
  rewrite !pt_sym in H2.
  unfold p, p' in H2.
  rewrite pt_Some in H2.
  simpl in H2.
  rewrite <- (eq_sym_involutive e), H2.
  reflexivity.
Qed.

End Countermodel.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem arrow_mul_respects_forces_UIP
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p')) :
  forall (A : Type) (a : A) (e : a = a), e = eq_refl.
Proof. intros A a e; exact (forces_loop A a K e). Qed.

(* ... hence full UIP / HomRigid every 范畴. （已译） *)
Corollary arrow_mul_respects_forces_UIP'
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p')) :
  forall (A : Type) (x y : A) (u v : x = y), u = v.
Proof.
  intros A x y u v.
  destruct u.
  symmetry; apply (arrow_mul_respects_forces_UIP K).
Qed.
