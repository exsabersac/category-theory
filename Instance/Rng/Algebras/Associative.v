Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Mac Lane, ibid., §I.8, printed p. 28 — Ab-categories and the
 nLab:      https://ncatlab.org/nlab/show/associative+algebra
 nLab:      https://ncatlab.org/nlab/show/tensor+algebra
 Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Objects *)

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record AAlgObject (K : CRng) := {
  aalg_ring : RingObject;
  aalg_unit : `1 K ~{Rng}~> aalg_ring;
  aalg_central : ∀ k a,
    rig_mul aalg_ring (rig_map aalg_unit k) a
      ≈ rig_mul aalg_ring a (rig_map aalg_unit k)
}.

Arguments aalg_ring {K} _.
Arguments aalg_unit {K} _.
Arguments aalg_central {K} _ _ _.

(* A 态射 K-algebras ring homomorphism commuting two
 structure maps. The orientation triangle [KAlgHom]'s, hence
 [Coslice]'s (Construction/Slice.v). （已译） *)
Definition AAlgHom {K : CRng} (A B : AAlgObject K) : Type :=
  ∃ f : aalg_ring A ~{Rng}~> aalg_ring B, aalg_unit B ≈ f ∘ aalg_unit A.

(* Two algebra 态射 equal underlying ring
 homomorphisms are; triangle 证明 irrelevant, [KAlgHom]. （已译） *)
Program Definition AAlgHom_Setoid {K : CRng} (A B : AAlgObject K) :
  Setoid (AAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  intros K A B.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Qed.

Lemma aalg_id_triangle {K : CRng} (A : AAlgObject K) :
  aalg_unit A ≈ id ∘ aalg_unit A.
Proof. now rewrite id_left. Qed.

Lemma aalg_comp_triangle {K : CRng} {A B C : AAlgObject K}
      (f : AAlgHom B C) (g : AAlgHom A B) :
  aalg_unit C ≈ (`1 f ∘ `1 g) ∘ aalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Qed.

Program Definition AAlg (K : CRng) : Category := {|
  obj     := AAlgObject K;
  hom     := @AAlgHom K;
  homset  := @AAlgHom_Setoid K;
  id      := fun A => (id; aalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; aalg_comp_triangle f g)
|}.
Next Obligation.
  intros K A B C f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B f a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C D f g h a; simpl; reflexivity. Qed.

(** ** The underlying set *)

Program Definition AAlg_Forget (K : CRng) : AAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (aalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(*
   本节说明分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition AAlg_RMod {K : CRng} (A : AAlgObject K)
  : RModObject (`1 K) := {|
  rm_ab   := ring_ab (aalg_ring A);
  rm_smul := fun r a => rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) a
|}.
Next Obligation.
  intros K A r r' Hr a a' Ha; simpl.
  apply rig_mul_respects; [| exact Ha ].
  now apply (proper_morphism (rig_map (aalg_unit A))).
Qed.
Next Obligation. intros K A r m n; simpl; apply rig_distr_l. Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_add (aalg_unit A) r s).
  apply rig_distr_r.
Qed.
Next Obligation.
  intros K A r s m; simpl.
  rewrite (rig_map_mul (aalg_unit A) r s).
  apply rig_mul_assoc.
Qed.
Next Obligation.
  intros K A m; simpl.
  rewrite (rig_map_one (aalg_unit A)).
  apply rig_mul_one_l.
Qed.

(* A K-algebra map is K-linear: the triangle turns [f (u_A r · a)] into
   [u_B r · f a]. *)
Program Definition AAlg_RModHom {K : CRng} {A B : AAlgObject K}
  (f : AAlgHom A B) : RModHom (AAlg_RMod A) (AAlg_RMod B) := {|
  rm_hom := {| cmon_map := rig_map (`1 f);
               cmon_map_zero := rig_map_zero (`1 f);
               cmon_map_plus := rig_map_add (`1 f) |}
|}.
Next Obligation.
  intros K A B f r m; simpl.
  rewrite (rig_map_mul (`1 f)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 f r).
Qed.

Program Definition AAlg_Forget_Mod (K : CRng) : AAlg K ⟶ RMod (`1 K) := {|
  fobj := @AAlg_RMod K;
  fmap := fun A B f => AAlg_RModHom f
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example aalg_forget_agree (K : CRng) (A : AAlg K) :
  fobj[RMod_Forget (`1 K)] (fobj[AAlg_Forget_Mod K] A) = fobj[AAlg_Forget K] A
  := eq_refl.

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record AAlgLinear {K : CRng} (V : RModObject (`1 K)) (A : AAlgObject K) := {
  alin_map :> SetoidMorphism (cmon_setoid V) (rig_setoid (aalg_ring A));

  alin_add : ∀ v w,
    alin_map (cmon_plus V v w)
      ≈ rig_add (aalg_ring A) (alin_map v) (alin_map w);
  alin_smul : ∀ r v,
    alin_map (rm_smul V r v)
      ≈ rig_mul (aalg_ring A) (rig_map (aalg_unit A) r) (alin_map v)
}.

Arguments alin_map {K V A} _.
Arguments alin_add {K V A} _ _ _.
Arguments alin_smul {K V A} _ _ _.

Program Definition AAlgLinear_Setoid {K : CRng} (V : RModObject (`1 K))
  (A : AAlgObject K) : Setoid (AAlgLinear V A) := {|
  equiv := fun f g => ∀ v, alin_map f v ≈ alin_map g v
|}.
Next Obligation.
  intros K V A.
  constructor.
  - intros f v; reflexivity.
  - intros f g Hfg v; symmetry; apply Hfg.
  - intros f g h Hfg Hgh v; transitivity (alin_map g v);
      [ apply Hfg | apply Hgh ].
Qed.

(* An additive map is zero at zero, by cancellation in the target's
   additive group. *)
Lemma alin_zero {K : CRng} {V : RModObject (`1 K)} {A : AAlgObject K}
  (f : AAlgLinear V A) :
  alin_map f (cmon_zero V) ≈ rig_zero (aalg_ring A).
Proof.
  apply (ab_cancel_l (ring_ab (aalg_ring A)) (alin_map f (cmon_zero V))).
  simpl.
  rewrite <- (alin_add f (cmon_zero V) (cmon_zero V)).
  rewrite (proper_morphism (alin_map f) _ _
             (cmon_plus_zero_l V (cmon_zero V))).
  symmetry; apply rig_add_zero_r.
Qed.

Definition aalg_linear_of_module_hom {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) : AAlgLinear V A := {|
  alin_map   := cmon_map (rm_hom h);
  alin_add   := cmon_map_plus (rm_hom h);
  alin_smul  := rm_map_smul h
|}.

Program Definition module_hom_of_aalg_linear {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) : RModHom V (AAlg_RMod A) := {|
  rm_hom := {| cmon_map := alin_map f;
               cmon_map_zero := alin_zero f;
               cmon_map_plus := alin_add f |};
  rm_map_smul := alin_smul f
|}.

(* 相关说明。 （已译） *)
Example aalg_linear_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (f : AAlgLinear V A) :
  alin_map (aalg_linear_of_module_hom (module_hom_of_aalg_linear f))
    = alin_map f := eq_refl.

Example module_hom_round_map {K : CRng} {V : RModObject (`1 K)}
  {A : AAlgObject K} (h : RModHom V (AAlg_RMod A)) :
  cmon_map (rm_hom (module_hom_of_aalg_linear (aalg_linear_of_module_hom h)))
    = cmon_map (rm_hom h) := eq_refl.

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition alin_id {K : CRng} (A : AAlgObject K)
  : AAlgLinear (AAlg_RMod A) A := {|
  alin_map := setoid_morphism_id
|}.
Next Obligation. intros K A v w; simpl; reflexivity. Qed.
Next Obligation. intros K A r v; simpl; reflexivity. Qed.

Example alin_id_computes {K : CRng} (A : AAlgObject K)
  (a : carrier (rig_setoid (aalg_ring A))) :
  alin_map (alin_id A) a = a := eq_refl.

(* Postcomposition algebra map carries linear map linear
 map — action 普遍性质 stated. （已译） *)
Program Definition alin_compose {K : CRng} {V : RModObject (`1 K)}
  {A B : AAlgObject K} (g : AAlgHom A B) (f : AAlgLinear V A)
  : AAlgLinear V B := {|
  alin_map := setoid_morphism_compose (rig_map (`1 g)) (alin_map f)
|}.
Next Obligation.
  intros K V A B g f v w; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_add f v w)).
  apply (rig_map_add (`1 g)).
Qed.
Next Obligation.
  intros K V A B g f r v; simpl.
  rewrite (proper_morphism (rig_map (`1 g)) _ _ (alin_smul f r v)).
  rewrite (rig_map_mul (`1 g)).
  apply rig_mul_respects; [| reflexivity ].
  symmetry; exact (`2 g r).
Qed.

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AAlg_of_KAlg {K : CRng} (A : KAlgObject K) : AAlgObject K := {|
  aalg_ring := kalg_ring A;
  aalg_unit := kalg_unit A;
  aalg_central := fun k a => kalg_comm A (rig_map (kalg_unit A) k) a
|}.

Program Definition KAlg_AAlg (K : CRng) : KAlg K ⟶ AAlg K := {|
  fobj := @AAlg_of_KAlg K;
  fmap := fun A B f => (`1 f; `2 f)
|}.
Next Obligation. intros K A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros K A a; simpl; reflexivity. Qed.
Next Obligation. intros K A B C f g a; simpl; reflexivity. Qed.

#[export] Instance KAlg_AAlg_Faithful (K : CRng) : Faithful (KAlg_AAlg K).
Proof. constructor; intros A B f g E; exact E. Qed.

#[export] Instance KAlg_AAlg_Full (K : CRng) : Full (KAlg_AAlg K).
Proof.
  unshelve econstructor.
  - intros A B g; exact (`1 g; `2 g).
  - intros A B g a; simpl; reflexivity.
Qed.

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Base_AAlg (K : CRng) : AAlgObject K := {|
  aalg_ring := `1 K;
  aalg_unit := @id Rng (`1 K);
  aalg_central := fun k a => `2 K k a
|}.

Example Base_AAlg_unit (K : CRng) (k : carrier (rig_setoid (`1 K))) :
  rig_map (aalg_unit (Base_AAlg K)) k = k := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ut2 : Type := (Z * Z * Z)%type.

Definition ut2_eqT (x y : ut2) : Type := x = y.

Lemma ut2_eqT_Equivalence : Equivalence ut2_eqT.
Proof.
  constructor; unfold ut2_eqT.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition ut2_setoid_object : SetoidObject := {|
  carrier := ut2;
  is_setoid := {| equiv := ut2_eqT; setoid_equiv := ut2_eqT_Equivalence |}
|}.

Definition ut2_zero : ut2 := (0, 0, 0)%Z.
Definition ut2_one : ut2 := (1, 0, 1)%Z.

Definition ut2_add (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') => ((a + a')%Z, (b + b')%Z, (c + c')%Z)
  end.

Definition ut2_neg (x : ut2) : ut2 :=
  match x with (a, b, c) => ((- a)%Z, (- b)%Z, (- c)%Z) end.

(* [[a,b],[0,c]] · [[a',b'],[0,c']] = [[a a', a b' + b c'], [0, c c']] *)
Definition ut2_mul (x y : ut2) : ut2 :=
  match x, y with
  | (a, b, c), (a', b', c') =>
      ((a * a')%Z, (a * b' + b * c')%Z, (c * c')%Z)
  end.

(* The scalar diagonal r ↦ [[r, 0], [0, r]]. *)
Definition ut2_scal (r : Z) : ut2 := (r, 0, r)%Z.

Lemma ut2_eq3 (a b c a' b' c' : Z) :
  a = a' → b = b' → c = c' → ((a, b, c) : ut2) = (a', b', c').
Proof. intros H1 H2 H3; now subst. Qed.

Ltac ut2_crunch :=
  cbv beta iota delta [ut2_eqT ut2_add ut2_neg ut2_mul ut2_zero ut2_one ut2_scal];
  apply ut2_eq3; ring.

Ltac ut2_1 := intros [[? ?] ?]; ut2_crunch.
Ltac ut2_2 := intros [[? ?] ?] [[? ?] ?]; ut2_crunch.
Ltac ut2_3 := intros [[? ?] ?] [[? ?] ?] [[? ?] ?]; ut2_crunch.

Lemma ut2_add_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_add.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Lemma ut2_mul_respects : Proper (ut2_eqT ==> ut2_eqT ==> ut2_eqT) ut2_mul.
Proof. intros x y Hxy z w Hzw; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2_Rig : RigObject := {|
  rig_setoid := ut2_setoid_object;
  rig_zero := ut2_zero;
  rig_add := ut2_add;
  rig_one := ut2_one;
  rig_mul := ut2_mul;
  rig_add_respects := ut2_add_respects;
  rig_mul_respects := ut2_mul_respects;
  (*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid ut2_setoid_object)
                (@eq ut2) (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_2. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_3. Qed.
Next Obligation. ut2_1. Qed.
Next Obligation. ut2_1. Qed.

Lemma ut2_neg_respects : Proper (ut2_eqT ==> ut2_eqT) ut2_neg.
Proof. intros x y Hxy; unfold ut2_eqT in *; now subst. Qed.

Program Definition UT2 : RingObject := {|
  ring_rig := UT2_Rig;
  ring_neg := ut2_neg;
  ring_neg_respects := ut2_neg_respects
|}.
Next Obligation. ut2_1. Qed.

(* The scalar diagonal ℤ → UT2, whose image is central because ℤ is
   commutative. *)
(* The respectfulness witness is written out as a pointwise term rather
   than left to instance resolution — the engineering finding recorded in
   Theory/Universal/Element.v, where resolving [Proper] at a concrete
   setoid pinned a carrier universe. *)
Definition ut2_scal_proper
  : Proper (@equiv _ (is_setoid Z_setoid_object)
              ==> @equiv _ (is_setoid ut2_setoid_object)) ut2_scal :=
  fun r s H => f_equal (fun z : Z => ((z, 0, z) : ut2)%Z) H.

Definition ut2_scal_morphism
  : SetoidMorphism (is_setoid Z_setoid_object) (is_setoid ut2_setoid_object) :=
  {| morphism := ut2_scal; proper_morphism := ut2_scal_proper |}.

(*
   本节说明 Associative 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ut2_scal_add (a b : Z) :
  ut2_scal (a + b)%Z = ut2_add (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_add; apply ut2_eq3; ring. Qed.

Lemma ut2_scal_mul (a b : Z) :
  ut2_scal (a * b)%Z = ut2_mul (ut2_scal a) (ut2_scal b).
Proof. unfold ut2_scal, ut2_mul; apply ut2_eq3; ring. Qed.

Program Definition ut2_scalar : Int_Ring ~{Rng}~> UT2 := {|
  rig_map := ut2_scal_morphism
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_add a b). Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; exact (ut2_scal_mul a b). Qed.

Lemma ut2_scalar_central : ∀ (k : Z) (a : ut2),
  rig_mul UT2 (rig_map ut2_scalar k) a ≈ rig_mul UT2 a (rig_map ut2_scalar k).
Proof. intros k [[x y] z]; ut2_crunch. Qed.

Definition UT2_AAlg : AAlgObject Int_CRng :=
  Build_AAlgObject Int_CRng UT2 ut2_scalar ut2_scalar_central.

(* 相关说明。 （已译） *)
Definition ut2_e11 : ut2 := (1, 0, 0)%Z.
Definition ut2_e12 : ut2 := (0, 1, 0)%Z.

Example ut2_e11_e12 : rig_mul UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.
Example ut2_e12_e11 : rig_mul UT2 ut2_e12 ut2_e11 = ut2_zero := eq_refl.

Theorem UT2_not_commutative :
  rig_mul UT2 ut2_e11 ut2_e12 ≈ rig_mul UT2 ut2_e12 ut2_e11 → False.
Proof. unfold ut2_eqT; simpl; discriminate. Qed.

(* Hence [AAlg] does not consist of commutative algebras: the witness is
   an object of [AAlg Int_CRng] whose ring is not commutative. *)
Theorem AAlg_not_all_commutative :
  (∀ (A : AAlgObject Int_CRng) a b,
     rig_mul (aalg_ring A) a b ≈ rig_mul (aalg_ring A) b a) → False.
Proof.
  intro H.
  exact (UT2_not_commutative (H UT2_AAlg ut2_e11 ut2_e12)).
Qed.

(* 相关说明。 （已译） *)
Theorem UT2_not_in_KAlg (A : KAlgObject Int_CRng) :
  kalg_ring A = UT2 → False.
Proof.
  destruct A as [Ar Acomm Aunit]; simpl; intro HA; subst Ar.
  exact (UT2_not_commutative (Acomm ut2_e11 ut2_e12)).
Qed.

(** The base-ring algebra matrix algebra both 对象, so
 [AAlg Int_CRng] has at least two, 态射 between them: the
 scalar diagonal itself map ℤ-algebras. （已译） *)
Lemma ut2_scalar_triangle :
  aalg_unit UT2_AAlg ≈ ut2_scalar ∘ aalg_unit (Base_AAlg Int_CRng).
Proof. intro r; simpl; reflexivity. Qed.

Definition Base_to_UT2 : Base_AAlg Int_CRng ~{AAlg Int_CRng}~> UT2_AAlg :=
  (ut2_scalar; ut2_scalar_triangle).

(* 相关说明。 （已译） *)
Example ut2_module_action :
  rm_smul (AAlg_RMod UT2_AAlg) 3%Z (2, 5, 7)%Z = (6, 15, 21)%Z := eq_refl.
