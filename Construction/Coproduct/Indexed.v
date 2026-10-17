(* * * Set-indexed coproducts 范畴 （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

(*
   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Logic.EqdepFacts.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", 2nd ed., §3.6 —
   nLab:      https://ncatlab.org/nlab/show/coproduct

   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* Transport 对象 [C i] [C j] along [e : i = j]. Every
 dependency index equality file goes through one
 定义. （已译） *)
Definition ob_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} (e : i = j) (x : C i) : C j :=
  match e in _ = k return C k with eq_refl => x end.

(* Transport 态射 along equality BETWEEN two index equalities.
 This is what hom-setoid needs order compare two 态射
 whose index components are only propositionally equal.（已译） *)
Definition mor_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  ob_cast C e2 x ~> y :=
  match p in _ = e return ob_cast C e x ~> y with eq_refl => f end.

(*
   本节说明 Indexed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mor_cast_sym@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  mor_cast C (eq_sym p) (mor_cast C p f) = f.
Proof. destruct p; reflexivity. Qed.

(* * ** The data coproduct 范畴 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sigma_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Type@{us} := ∃ i : I, C i.

Definition sigma_hom@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Type@{oh} := ∃ e : `1 X = `1 Y, ob_cast C e (`2 X) ~> `2 Y.

Definition sigma_equiv@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) : Type@{op} :=
  ∃ p : `1 f = `1 g, mor_cast C p (`2 f) ≈ `2 g.

Definition sigma_id@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X : sigma_obj@{ui uo oh op us} C) :
  sigma_hom X X := (eq_refl; id).

(*
   本节说明 Indexed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sigma_compose@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) : sigma_hom X Z :=
  (match `1 f as e0 in _ = m
     return ∀ z0 : C m, (ob_cast C e0 (`2 Y) ~> z0) →
            (∃ e : `1 X = m, ob_cast C e (`2 X) ~> z0)
   with
   | eq_refl => fun z0 h => (`1 g; h ∘ `2 g)
   end) (`2 Z) (`2 f).

(** ** The category laws *)

Lemma sigma_equiv_Equivalence@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Equivalence (@sigma_equiv@{ui uo oh op us} I C X Y).
Proof.
  constructor.
  - intros [e f]; exists eq_refl; reflexivity.
  - intros [e1 f] [e2 g] [p Hp]; simpl in *.
    destruct p; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [e1 f] [e2 g] [e3 h] [p Hp] [q Hq]; simpl in *.
    destruct p, q; simpl in *.
    exists eq_refl; simpl; now transitivity g.
Qed.

Lemma sigma_compose_respects@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f f' : sigma_hom Y Z) (Hf : sigma_equiv f f')
  (g g' : sigma_hom X Y) (Hg : sigma_equiv g g') :
  sigma_equiv (sigma_compose f g) (sigma_compose f' g').
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f1], f' as [e2 f2], Hf as [p Hp].
  destruct g as [d1 g1], g' as [d2 g2], Hg as [q Hq]; simpl in *.
  destruct p, q; simpl in *.
  destruct e1; simpl in *.
  exists eq_refl; simpl.
  now rewrite Hp, Hq.
Qed.

(* [id ∘ f] REDUCES, because [sigma_compose] matches index 证明
 first 论元 恒等's [eq_refl]. （已译） *)
Lemma sigma_id_left@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose (sigma_id Y) f) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  exists eq_refl; simpl; apply id_left.
Qed.

Lemma sigma_id_right@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose f (sigma_id X)) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  destruct e; simpl in *.
  exists eq_refl; simpl; apply id_right.
Qed.

Lemma sigma_comp_assoc@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose f (sigma_compose g h))
              (sigma_compose (sigma_compose f g) h).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc.
Qed.

Lemma sigma_comp_assoc_sym@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose (sigma_compose f g) h)
              (sigma_compose f (sigma_compose g h)).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc_sym.
Qed.

(** ** The coproduct category *)

(* 相关说明。 （已译） *)
Definition SigmaCat@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Category@{us oh op} := {|
  obj := sigma_obj@{ui uo oh op us} C;
  hom := @sigma_hom@{ui uo oh op us} I C;
  homset := fun X Y =>
    {| equiv := @sigma_equiv@{ui uo oh op us} I C X Y
     ; setoid_equiv := sigma_equiv_Equivalence@{ui uo oh op us} X Y |};
  id := @sigma_id@{ui uo oh op us} I C;
  compose := @sigma_compose@{ui uo oh op us} I C;
  compose_respects := fun X Y Z f f' Hf g g' Hg =>
    sigma_compose_respects f f' Hf g g' Hg;
  id_left := @sigma_id_left@{ui uo oh op us} I C;
  id_right := @sigma_id_right@{ui uo oh op us} I C;
  comp_assoc := @sigma_comp_assoc@{ui uo oh op us} I C;
  comp_assoc_sym := @sigma_comp_assoc_sym@{ui uo oh op us} I C
|}.

(** ** The injections *)

Definition sigma_inj_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_obj@{ui uo oh op us} C := (i; x).

Definition sigma_inj_map@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f : x ~> y) :
  sigma_hom (sigma_inj_obj@{ui uo oh op us} C i x)
            (sigma_inj_obj@{ui uo oh op us} C i y) := (eq_refl; f).

Lemma sigma_inj_map_respects@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f g : x ~> y) :
  f ≈ g → sigma_equiv (sigma_inj_map@{ui uo oh op us} C i f)
                      (sigma_inj_map@{ui uo oh op us} C i g).
Proof. intros H; exists eq_refl; exact H. Qed.

Lemma sigma_inj_map_id@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (@id (C i) x))
              (sigma_id (sigma_inj_obj@{ui uo oh op us} C i x)).
Proof. exists eq_refl; reflexivity. Qed.

Lemma sigma_inj_map_comp@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y z : C i}
  (f : y ~> z) (g : x ~> y) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (f ∘ g))
              (sigma_compose (sigma_inj_map@{ui uo oh op us} C i f)
                             (sigma_inj_map@{ui uo oh op us} C i g)).
Proof. exists eq_refl; reflexivity. Qed.

Definition SigmaCat_inj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) :
  C i ⟶ SigmaCat@{ui uo oh op us} C :=
  @Build_Functor (C i) (SigmaCat@{ui uo oh op us} C)
    (sigma_inj_obj@{ui uo oh op us} C i)
    (fun x y f => sigma_inj_map@{ui uo oh op us} C i f)
    (fun x y f g H => sigma_inj_map_respects C i f g H)
    (fun x => sigma_inj_map_id C i x)
    (fun x y z f g => sigma_inj_map_comp C i f g).

(* 相关说明。 （已译） *)
Lemma sigma_hom_cross_empty {I : Type} (C : I → Category)
  {X Y : SigmaCat C} (H : `1 X = `1 Y → False) : (X ~> Y) → False.
Proof. intros [e _]; exact (H e). Qed.

(* An empty index leaves coproduct no 对象 at all. （已译） *)
Lemma SigmaCat_empty_no_obj (C : Empty_set → Category) :
  obj[SigmaCat C] → False.
Proof. intros [i _]; destruct i. Qed.

(* * ** The case 函子 普遍性质 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sigma_case_obj@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) : D :=
  F (`1 X) (`2 X).

Definition sigma_case_map@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) :
  sigma_case_obj@{ui uo oh op us do dh dp} F X ~>
  sigma_case_obj@{ui uo oh op us do dh dp} F Y :=
  (match `1 f as e0 in _ = m
     return ∀ y0 : C m, (ob_cast C e0 (`2 X) ~> y0) →
            (F (`1 X) (`2 X) ~> F m y0)
   with
   | eq_refl => fun y0 h => fmap[F (`1 X)] h
   end) (`2 Y) (`2 f).

Lemma sigma_case_map_respects@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) (H : sigma_equiv f g) :
  sigma_case_map@{ui uo oh op us do dh dp} F f
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y]; simpl in *.
  destruct f as [e1 f], g as [e2 g], H as [p Hp]; simpl in *.
  destruct p; simpl in *.
  destruct e1; simpl in *.
  exact (@fmap_respects _ _ (F i) x y f g Hp).
Qed.

Lemma sigma_case_map_id@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_id X) ≈ id.
Proof. destruct X as [i x]; simpl; apply fmap_id. Qed.

Lemma sigma_case_map_comp@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_compose f g)
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F f
        ∘ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f], g as [e2 g]; simpl in *.
  destruct e1, e2; simpl in *.
  apply fmap_comp.
Qed.

Definition SigmaCat_case@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) : SigmaCat@{ui uo oh op us} C ⟶ D :=
  @Build_Functor (SigmaCat@{ui uo oh op us} C) D
    (sigma_case_obj@{ui uo oh op us do dh dp} F)
    (fun X Y f => sigma_case_map@{ui uo oh op us do dh dp} F f)
    (fun X Y f g H => sigma_case_map_respects F f g H)
    (fun X => sigma_case_map_id F X)
    (fun X Y Z f g => sigma_case_map_comp F f g).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sigma_case_inj_fobj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  fobj[SigmaCat_case F ◯ SigmaCat_inj C i] = fobj[F i] := eq_refl.

Example sigma_case_inj_fmap {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) (x y : C i) (f : x ~> y) :
  fmap[SigmaCat_case F ◯ SigmaCat_inj C i] f = fmap[F i] f := eq_refl.

(* The whole 函子 RECORD not recovered, however: 复合
 rebuilds three law fields, they distinct opaque terms.
 Measured, not assumed. （已译） *)
Fail Example sigma_case_inj_strict {I : Type} {C : I → Category}
  {D : Category} (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i = F i := eq_refl.

Lemma SigmaCat_case_inj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i ≈ F i.
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma SigmaCat_case_unique {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (G : SigmaCat C ⟶ D) :
  (∀ i : I, G ◯ SigmaCat_inj C i ≈ F i) → G ≈ SigmaCat_case F.
Proof.
  intros H.
  unshelve eexists.
  - intros [i x]; exact (`1 (H i) x).
  - intros [i x] [j y] [e f]; simpl in *.
    destruct e; simpl in *.
    exact (`2 (H i) x y f).
Qed.

(* The 普遍性质, bundled: existence case 函子 with
 triangle, uniqueness 引理 above. （已译） *)
Lemma SigmaCat_ump {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) :
  ∃! G : SigmaCat C ⟶ D, ∀ i : I, G ◯ SigmaCat_inj C i ≈ F i.
Proof.
  unshelve eapply Build_Unique.
  - exact (SigmaCat_case F).
  - exact (SigmaCat_case_inj F).
  - intros G HG; symmetry; exact (SigmaCat_case_unique F G HG).
Qed.

(* 相关说明。 （已译） *)

(* Uniqueness 恒等 proofs index, Streicher-K form
 Theory/OGraph.v's [NodeUIP] uses — form the
 stdlib's [UIP_shift] 所消耗. （已译） *)
Definition IdxUIP (I : Type) : Type := ∀ (i : I) (p : i = i), p = eq_refl.

Lemma IdxUIP_pair {I : Type} (U : IdxUIP I) {i j : I} (p q : i = j) : p = q.
Proof. destruct p; symmetry; apply U. Qed.

(*
   本节说明 Indexed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SigmaCat_inj_Faithful {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Faithful (SigmaCat_inj C i) := {|
  fmap_inj := _
|}.
Next Obligation.
  intros I C U i x y f g [p Hp]; simpl in *.
  rewrite (UIP_shift I U i eq_refl p) in Hp.
  exact Hp.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Faithful_cancel {C D E : Category} (F : C ⟶ D) (G : D ⟶ E) :
  Faithful (G ◯ F) → Faithful F.
Proof.
  intros H; construct.
  apply (@fmap_inj _ _ (G ◯ F) H); simpl.
  now rewrite X.
Qed.

Definition SigmaCat_const_retract {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_case (fun _ : I => Id[D])
              ◯ SigmaCat_inj (fun _ : I => D) i).
Proof.
  constructor; intros x y f g H; exact H.
Defined.

Definition SigmaCat_const_inj_Faithful {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_inj (fun _ : I => D) i) :=
  Faithful_cancel _ _ (SigmaCat_const_retract D i).

(* Fullness needs [IdxUIP] outright: chosen preimage 态射
 second component read back through index 证明's collapse
 [eq_refl]. （已译） *)
Program Definition SigmaCat_inj_Full {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Full (SigmaCat_inj C i) := {|
  prefmap := fun x y g => mor_cast C (U i (`1 g)) (`2 g)
|}.
Next Obligation.
  intros I C U i x y g; simpl.
  exists (eq_sym (U i (`1 g))); simpl.
  rewrite mor_cast_sym; reflexivity.
Qed.

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sigma_inj_Full_forces_UIP {I : Type} (C : I → Category) (i : I)
  (x : C i) (pt : ∀ e : i = i, ob_cast C e x ~> x)
  (H : Full (SigmaCat_inj C i)) : ∀ e : i = i, e = eq_refl.
Proof.
  intros e.
  exact (eq_sym (`1 (@fmap_sur _ _ _ H x x (e; pt e)))).
Qed.

(** ** The singleton index *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SigmaCat_unit_collapse {D : Category} :
  SigmaCat (fun _ : poly_unit => D) ⟶ D := SigmaCat_case (fun _ => Id[D]).

Definition SigmaCat_unit_expand {D : Category} :
  D ⟶ SigmaCat (fun _ : poly_unit => D) :=
  SigmaCat_inj (fun _ : poly_unit => D) ttt.

Definition sigma_poly_unit_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  match x, y with ttt, ttt => left eq_refl end.

Definition poly_unit_IdxUIP : IdxUIP poly_unit :=
  fun i p => Eqdep_dec.UIP_dec sigma_poly_unit_dec p eq_refl.

Lemma SigmaCat_unit_round_l {D : Category} :
  SigmaCat_unit_collapse ◯ SigmaCat_unit_expand ≈ Id[D].
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

Lemma SigmaCat_unit_round_r {D : Category} :
  SigmaCat_unit_expand ◯ SigmaCat_unit_collapse
    ≈ Id[SigmaCat (fun _ : poly_unit => D)].
Proof.
  unshelve eexists.
  - intros [u x]; destruct u; exact iso_id.
  - intros [u x] [v y] [e f]; destruct u, v; simpl in *.
    assert (He : e = eq_refl) by apply poly_unit_IdxUIP.
    subst e; simpl.
    exists eq_refl; simpl.
    rewrite id_left, id_right; reflexivity.
Qed.
