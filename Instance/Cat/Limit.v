(*
   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** ** Cat has set-indexed products *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PiCat_IsIndexedProduct@{i so sh +} {I : Type@{i}}
  (C : I → Category@{so sh sh}) :
  @IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C) :=
  @Build_IsIndexedProduct Cat I C (PiCat C) (PiCat_Proj C)
    (fun D R => PiCat_ump R).

#[export]
Instance Cat_HasIndexedProducts@{i so sh +} : @HasIndexedProducts Cat :=
  @Build_HasIndexedProducts Cat
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) => PiCat C)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) a => PiCat_Proj C a)
    (fun (A : Type@{i}) (C : A → Category@{so sh sh}) =>
       PiCat_IsIndexedProduct C).

(** ** A small cast kit *)

(*
   本节说明函子、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eq_fmap_hom_cast {X Y : Category} (P : X ⟶ Y) {a b a' b' : X}
      (ea : a = a') (eb : b = b') (f : a ~> b) :
  fmap[P] (hom_cast ea eb f)
    ≈ hom_cast (f_equal (fobj[P]) ea) (f_equal (fobj[P]) eb) (fmap[P] f).
Proof. destruct ea, eb; reflexivity. Qed.

(* A [hom_cast] in a product category, read at one index. *)
Lemma hom_cast_pi {I : Type} (C : I → Category) {a b a' b' : PiCat C}
      (ea : a = a') (eb : b = b') (η : a ~> b) (i : I) :
  hom_cast ea eb η i
    = hom_cast (f_equal (fun g => g i) ea) (f_equal (fun g => g i) eb) (η i).
Proof. destruct ea, eb; reflexivity. Qed.

(* A Leibniz equality of morphisms followed by a setoid equation. *)
Definition eq_then_equiv {X : Category} {a b : X} {p q r : a ~> b}
  (e : p = q) (h : q ≈ r) : p ≈ r :=
  match e in _ = q' return q' ≈ r → p ≈ r with eq_refl => fun h => h end h.

(** ** Equalizers in StrictCat *)

Section Equalizer.

Context {C D : Category}.
Context (F G : C ⟶ D).

#[local] Obligation Tactic := idtac.

(* The subcategory of C on the objects where F and G agree, and the arrows
   on which they agree up to the cast along those object agreements. *)
Program Definition EqSub : Subcategory C := {|
  sobj := fun c => F c = G c;
  shom := fun c c' (p : F c = G c) (p' : F c' = G c') (f : c ~> c') =>
            hom_cast p p' (fmap[F] f) ≈ fmap[G] f
|}.
Next Obligation.
  intros x y z ox oy oz f g Hf Hg; simpl in *.
  rewrite !fmap_comp.
  rewrite <- (hom_cast_comp ox oy oz).
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  intros x ox; simpl.
  rewrite !fmap_id.
  apply hom_cast_id.
Qed.

Definition EqCat : Category := Sub C EqSub.
Definition EqIncl : EqCat ⟶ C := Incl C EqSub.

(* The inclusion equalizes F and G, strictly: the object component IS the
   membership equality each object carries, the morphism component IS the
   equation each morphism carries. *)
Definition Eq_commutes :
  F ∘[StrictCat] EqIncl ≈[StrictCat] G ∘[StrictCat] EqIncl :=
  @Build_strict_eq EqCat D (F ◯ EqIncl) (G ◯ EqIncl)
                   (fun x : EqCat => `2 x)
                   (fun (x y : EqCat) (f : x ~> y) => `2 f).

(* Two objects of the equalizer with the same underlying object are equal --
   PROVIDED the two membership proofs can be identified, which is [ObjUIP D]. *)
Lemma Eq_obj_eq (uip : ObjUIP D) (x y : EqCat) (e : `1 x = `1 y) :
  { E : x = y & f_equal (fobj[EqIncl]) E = e }.
Proof.
  destruct x as [a p], y as [a' p']; simpl in *.
  destruct e, (uip _ _ p p').
  exists eq_refl; reflexivity.
Defined.

Section Mediator.

Context {Z : Category} (h : Z ⟶ C).
Context (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Program Definition Eq_med : Z ⟶ EqCat := {|
  fobj := fun z => (h z; `1 Hh z);
  fmap := fun x y f => (fmap[h] f; strict_fmap_cast Hh f)
|}.
Next Obligation. intros x y f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros x; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; simpl; apply fmap_comp. Qed.

Definition Eq_med_incl : EqIncl ∘[StrictCat] Eq_med ≈[StrictCat] h.
Proof.
  refine (@Build_strict_eq Z C (EqIncl ◯ Eq_med) h (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(* [EqCat]'s hom-setoid compares underlying morphisms, so an equation between
   the inclusion's images IS an equation in [EqCat]; the proof is the
   identity. *)
Definition EqCat_equiv_of_incl {x y : EqCat} (f g : x ~> y)
  (H : fmap[EqIncl] f ≈ fmap[EqIncl] g) : f ≈ g := H.

Lemma Eq_med_unique (uip : ObjUIP D) (v : Z ⟶ EqCat)
      (Hv : EqIncl ∘[StrictCat] v ≈[StrictCat] h) :
  v ≈[StrictCat] Eq_med.
Proof.
  refine (@Build_strict_eq Z EqCat v Eq_med
            (fun x => `1 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) _).
  intros x y f.
  pose proof (`2 (Eq_obj_eq uip (v x) (Eq_med x) (`1 Hv x))) as Px.
  pose proof (`2 (Eq_obj_eq uip (v y) (Eq_med y) (`1 Hv y))) as Py.
  apply EqCat_equiv_of_incl.
  etransitivity; [ exact (eq_fmap_hom_cast EqIncl _ _ (fmap[v] f)) | ].
  rewrite Px, Py.
  exact (strict_fmap_cast Hv f).
Qed.

End Mediator.

Definition Eq_IsEqualizer (uip : ObjUIP D) :
  @IsEqualizer StrictCat C D F G EqCat EqIncl.
Proof.
  unshelve refine {| fork_eq := Eq_commutes |}.
  intros Z h Hh.
  unshelve refine {| unique_obj := Eq_med h Hh |}.
  - exact (Eq_med_incl h Hh).
  - intros v Hv; symmetry.
    exact (Eq_med_unique h Hh uip v Hv).
Defined.

End Equalizer.

Definition StrictCat_HasEqualizers (uip : ∀ C : Category, ObjUIP C) :
  HasEqualizers StrictCat.
Proof.
  constructor; intros C D F G.
  exists (EqCat F G), (EqIncl F G).
  exact (Eq_IsEqualizer F G (uip D)).
Defined.

(** ** Indexed products in StrictCat *)

(* Dependent function extensionality, at one pair of universes. *)
Definition DepFunext@{i o} : Type@{max(i+1,o+1)} :=
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i : I, P i),
    (∀ i : I, f i = g i) → f = g.

Section StrictProduct.

Context {I : Type} (C : I → Category).

(* The triangle holds on the nose: projecting the pairing IS the component,
   on objects and on arrows. *)
Definition PiCat_Pair_Proj_strict {D : Category} (R : ∀ i : I, D ⟶ C i)
  (i : I) : PiCat_Proj C i ∘[StrictCat] PiCat_Pair R ≈[StrictCat] R i.
Proof.
  refine (@Build_strict_eq D (C i) (PiCat_Proj C i ◯ PiCat_Pair R) (R i)
            (fun _ => eq_refl) _).
  intros x y f; reflexivity.
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pi_obj_eq
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  (a b : PiCat C) (e : ∀ i : I, a i = b i) :
  { E : a = b & ∀ i : I, f_equal (fun g => g i) E = e i }.
Proof.
  exists (fe a b e).
  intro i; apply uip.
Defined.

(* A cast in the product, read at one index, once the two whole-family
   equalities are known to project to given component equalities. *)
Lemma hom_cast_pi_ext {a b a' b' : PiCat C} (ea : a = a') (eb : b = b')
  (e1 : ∀ i : I, a i = a' i) (e2 : ∀ i : I, b i = b' i)
  (H1 : ∀ i : I, f_equal (fun g => g i) ea = e1 i)
  (H2 : ∀ i : I, f_equal (fun g => g i) eb = e2 i)
  (η : a ~> b) (i : I) :
  hom_cast ea eb η i = hom_cast (e1 i) (e2 i) (η i).
Proof. rewrite hom_cast_pi, H1, H2; reflexivity. Qed.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PiCat_ump_unique_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g)
  {D : Category} (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C)
  (HP : ∀ i : I, PiCat_Proj C i ∘[StrictCat] H ≈[StrictCat] R i) :
  H ≈[StrictCat] PiCat_Pair R.
Proof.
  refine (@Build_strict_eq D (PiCat C) H (PiCat_Pair R)
            (fun d => `1 (pi_obj_eq uip fe (H d) (fun i => R i d)
                                    (fun i => `1 (HP i) d))) _).
  intros x y f i.
  exact (eq_then_equiv
           (hom_cast_pi_ext _ _ _ _
              (`2 (pi_obj_eq uip fe (H x) (fun i => R i x)
                              (fun i => `1 (HP i) x)))
              (`2 (pi_obj_eq uip fe (H y) (fun i => R i y)
                              (fun i => `1 (HP i) y)))
              (fmap[H] f) i)
           (strict_fmap_cast (HP i) f)).
Qed.

Definition PiCat_IsIndexedProduct_strict
  (uip : ∀ i : I, ObjUIP (C i))
  (fe : ∀ (f g : ∀ i : I, C i), (∀ i, f i = g i) → f = g) :
  @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C).
Proof.
  constructor; intros D R.
  unshelve refine {| unique_obj := PiCat_Pair R |}.
  - exact (PiCat_Pair_Proj_strict R).
  - intros H HP; symmetry.
    exact (PiCat_ump_unique_strict uip fe R H HP).
Defined.

End StrictProduct.

Definition StrictCat_HasIndexedProducts
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) :
  HasIndexedProducts StrictCat :=
  @Build_HasIndexedProducts StrictCat
    (fun A C => PiCat C)
    (fun A C a => PiCat_Proj C a)
    (fun A C => PiCat_IsIndexedProduct_strict C (fun i => uip (C i))
                  (fe A (fun i => obj[C i]))).

(** ** StrictCat is small-complete *)

Definition StrictCat_Complete
  (uip : ∀ C : Category, ObjUIP C) (fe : DepFunext) : @Complete StrictCat :=
  Complete_from_products_equalizers
    (StrictCat_HasIndexedProducts uip fe) (StrictCat_HasEqualizers uip).

(** ** The two hypotheses are necessary *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Chaotic@{o h p} (X : Type@{o}) : Category@{o h p}.
Proof.
  unshelve refine {|
    obj     := X;
    hom     := fun _ _ => poly_unit@{h};
    homset  := Morphism_equality@{o h p};
    id      := fun _ => ttt;
    compose := fun _ _ _ _ _ => ttt
  |}.
  all: repeat intro; simpl;
    first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].
Defined.

Lemma chaotic_unit_eq (u : poly_unit) : ttt = u.
Proof. now destruct u. Defined.

Definition chaotic_unit_dec (a b : poly_unit) : {a = b} + {a <> b}.
Proof. destruct a, b; now left. Defined.

Section NecessityUIP.

(* One ambient [StrictCat]: its small categories are [Category@{o h h}]. *)
Universe o h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(* The functor out of the terminal category picking a point. *)
Program Definition ChaoticPt {X : Type@{o}} (x : X) :
  _1@{o h h} ⟶ Chaotic@{o h h} X := {|
  fobj := fun _ => x;
  fmap := fun _ _ _ => ttt
|}.

(* Each loop [p : x = x] names a functor into the equalizer of [ChaoticPt x]
   with itself, and every such functor satisfies the triangle. *)
Program Definition eq_loop_functor {X : Type@{o}} {x : X} (p : x = x) :
  _1@{o h h} ⟶ EqCat (ChaoticPt x) (ChaoticPt x) := {|
  fobj := fun _ => (ttt; p);
  fmap := fun _ _ _ => (ttt; _)
|}.

Lemma eq_loop_functor_incl {X : Type@{o}} {x : X} (p : x = x) :
  EqIncl (ChaoticPt x) (ChaoticPt x) ∘[StrictCat] eq_loop_functor p
    ≈[StrictCat] Id[_1@{o h h}].
Proof.
  refine (@Build_strict_eq _1 _1
            (EqIncl (ChaoticPt x) (ChaoticPt x) ◯ eq_loop_functor p) Id[_1]
            (fun o => chaotic_unit_eq o) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(*
   本节说明拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Eq_uniqueness_forces_UIP
  (K : ∀ (C D : Category@{o h h}) (F G : C ⟶ D),
         @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)) :
  ∀ (X : Type@{o}) (x y : X) (p q : x = y), p = q.
Proof.
  assert (loops : ∀ (X : Type@{o}) (x : X) (p : x = x), p = eq_refl).
  { intros X x p.
    pose proof (eq_desc (K _1 (Chaotic X) (ChaoticPt x) (ChaoticPt x))
                  Id[_1] (reflexivity _)) as U.
    pose proof (uniqueness U (eq_loop_functor p) (eq_loop_functor_incl p))
      as Up.
    pose proof (uniqueness U (eq_loop_functor (@eq_refl _ x))
                  (eq_loop_functor_incl eq_refl)) as Ur.
    assert (Hpq : eq_loop_functor p ≈[StrictCat] eq_loop_functor (@eq_refl _ x))
      by (rewrite <- Up; exact Ur).
    exact (inj_pair2_eq_dec _ chaotic_unit_dec _ _ _ _ (`1 Hpq ttt)). }
  intros X x y p q; destruct p; symmetry; apply loops.
Qed.

End NecessityUIP.

Section NecessityFunext.

(* The same ambient, with the index types of its products at [i]. *)
Universe i o h.
Constraint i <= o.
Constraint i <= h.

#[local] Obligation Tactic :=
  repeat intro; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

(* A family [f : ∀ i, P i] names a functor from the terminal category into
   the product of the chaotic categories on the [P i]. *)
Program Definition pi_point {I : Type@{i}} {P : I → Type@{o}} (f : ∀ i, P i) :
  _1@{o h h} ⟶ PiCat (fun i => Chaotic@{o h h} (P i)) := {|
  fobj := fun _ => f;
  fmap := fun _ _ _ i => ttt
|}.

Lemma pi_point_proj {I : Type@{i}} {P : I → Type@{o}} (f g : ∀ i, P i)
  (e : ∀ i, f i = g i) (i : I) :
  PiCat_Proj (fun i => Chaotic@{o h h} (P i)) i ∘[StrictCat] pi_point f
    ≈[StrictCat] ChaoticPt (g i).
Proof.
  refine (@Build_strict_eq _1 (Chaotic (P i))
            (PiCat_Proj (fun i => Chaotic (P i)) i ◯ pi_point f)
            (ChaoticPt (g i)) (fun _ => e i) _).
  intros a b k; simpl.
  match goal with |- ?u = ?v => now destruct u, v end.
Qed.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem PiCat_uniqueness_forces_funext
  (K : ∀ (I : Type@{i}) (C : I → Category@{o h h}),
         @IsIndexedProduct StrictCat I C (PiCat C) (PiCat_Proj C)) :
  ∀ (I : Type@{i}) (P : I → Type@{o}) (f g : ∀ i, P i),
    (∀ i, f i = g i) → f = g.
Proof.
  intros I P f g e.
  pose proof (iprod_desc (K I (fun i => Chaotic (P i)))
                (fun i => ChaoticPt (g i))) as U.
  pose proof (uniqueness U (pi_point f) (pi_point_proj f g e)) as Uf.
  pose proof (uniqueness U (pi_point g) (pi_point_proj g g (fun _ => eq_refl)))
    as Ug.
  assert (Hfg : pi_point f ≈[StrictCat] pi_point g)
    by (rewrite <- Uf; exact Ug).
  exact (`1 Hfg ttt).
Qed.

End NecessityFunext.

(** ** The weak ambient: the strict equalizer is not an equalizer in Cat *)

Section WeakAmbient.

#[local] Obligation Tactic :=
  intros; simpl;
  first [ reflexivity | match goal with |- ?a = ?b => now destruct a, b end ].

Definition ChaoticBool : Category := Chaotic bool.
Definition ChaoticBool_true  : _1 ⟶ ChaoticBool := ChaoticPt true.
Definition ChaoticBool_false : _1 ⟶ ChaoticBool := ChaoticPt false.

(* In Ho(Cat) the two points are the SAME morphism: every hom-set of the
   chaotic category is a singleton, so the family of its unique arrows is a
   natural isomorphism. *)
Program Definition ChaoticBool_points_equiv :
  ChaoticBool_true ≈[Cat] ChaoticBool_false :=
  (fun _ => {| to := ttt; from := ttt |}; _).

Lemma EqCat_ChaoticBool_empty :
  obj[EqCat ChaoticBool_true ChaoticBool_false] → False.
Proof. intros [o e]; simpl in e; discriminate e. Qed.

(*
   本节说明函子、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem EqCat_not_Cat_equalizer :
  @IsEqualizer Cat _1 ChaoticBool ChaoticBool_true ChaoticBool_false
    (EqCat ChaoticBool_true ChaoticBool_false)
    (EqIncl ChaoticBool_true ChaoticBool_false)
  → False.
Proof.
  intros K.
  assert (Hc : ChaoticBool_true ∘[Cat] Id[_1]
                 ≈[Cat] ChaoticBool_false ∘[Cat] Id[_1])
    by (rewrite ChaoticBool_points_equiv; reflexivity).
  exact (EqCat_ChaoticBool_empty (fobj[unique_obj (eq_desc K Id[_1] Hc)] ttt)).
Qed.

End WeakAmbient.
