Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Preadditive.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/rig
 Wikipedia: https://en.wikipedia.org/wiki/Semiring

   本文件给出 rig（半环）对象相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Rigs over a setoid carrier *)

(* Definition 5.36, clause for clause.  Multiplication is NOT commutative:
   clause (b) is a bare monoid. *)
Record RigObject := {
  rig_setoid :> SetoidObject;

  rig_zero : carrier rig_setoid;
  rig_add  : carrier rig_setoid → carrier rig_setoid → carrier rig_setoid;
  rig_one  : carrier rig_setoid;
  rig_mul  : carrier rig_setoid → carrier rig_setoid → carrier rig_setoid;

  rig_add_respects : Proper (equiv ==> equiv ==> equiv) rig_add;
  rig_mul_respects : Proper (equiv ==> equiv ==> equiv) rig_mul;

  (* (a) (0, +) is a commutative monoid *)
  rig_add_assoc : ∀ a b c,
    rig_add (rig_add a b) c ≈ rig_add a (rig_add b c);
  rig_add_comm : ∀ a b, rig_add a b ≈ rig_add b a;
  rig_add_zero_l : ∀ a, rig_add rig_zero a ≈ a;

  (* (b) (1, ·) is a monoid — not assumed commutative *)
  rig_mul_assoc : ∀ a b c,
    rig_mul (rig_mul a b) c ≈ rig_mul a (rig_mul b c);
  rig_mul_one_l : ∀ a, rig_mul rig_one a ≈ a;
  rig_mul_one_r : ∀ a, rig_mul a rig_one ≈ a;

  (* (c) · distributes over + on both sides *)
  rig_distr_l : ∀ a b c,
    rig_mul a (rig_add b c) ≈ rig_add (rig_mul a b) (rig_mul a c);
  rig_distr_r : ∀ a b c,
    rig_mul (rig_add a b) c ≈ rig_add (rig_mul a c) (rig_mul b c);

  (* (d) 0 annihilates on both sides *)
  rig_mul_zero_l : ∀ a, rig_mul rig_zero a ≈ rig_zero;
  rig_mul_zero_r : ∀ a, rig_mul a rig_zero ≈ rig_zero;

  (*
   （本文件文首说明见 nLab/Wikipedia 链接。）承运人是萌芽型球体:其Z/WP 我就等于 秘书处的说明
者提供骤 等至少在肤的的的与委员会的的的历次的的的的的的的 26.的,的的,的的的,的最长的س 你说什么的的′矛的,的,的 快点 当我们仍处于 và的,我已经的的,适合于的,的, 我们正在的所做的工作的,的成为一种的的,ủ的的结果表明的社团的的的ض解决问题社区的渊源的,的的条的在此方面的的,的 的采取协调一致的ئ的 马上的,的的的的增强其的,的,的的,的的即便是的,的的的
定义5.36;是同一身份承诺人 不过我应当是:另行确定。

   （英文长注释已压缩为中文导言；Coq 标识符未改。）
*)
  rig_prop : PropEquiv (is_setoid rig_setoid)
}.

#[export] Existing Instance rig_add_respects.
#[export] Existing Instance rig_mul_respects.
#[export] Existing Instance rig_prop.

(* The right additive unit law follows by commutativity, as in CMon. *)
Corollary rig_add_zero_r (R : RigObject) (a : carrier (rig_setoid R)) :
  rig_add R a (rig_zero R) ≈ a.
Proof.
  rewrite rig_add_comm.
  apply rig_add_zero_l.
Qed.

(* The additive half of a rig, as a commutative monoid object. *)
Definition rig_cmon (R : RigObject) : CMonObject := {|
  cmon_setoid := rig_setoid R;
  cmon_zero := rig_zero R;
  cmon_plus := rig_add R;
  cmon_plus_respects := rig_add_respects R;
  cmon_plus_assoc := rig_add_assoc R;
  cmon_plus_comm := rig_add_comm R;
  cmon_plus_zero_l := rig_add_zero_l R;
  cmon_prop := rig_prop R
|}.

(* * ** Rig homomorphisms 范畴 Rig （已译） *)

(* Exercise 6.7 part 1: a rig homomorphism preserves 0, +, 1 and ·. *)
Record RigHom (R S : RigObject) := {
  rig_map :> SetoidMorphism (rig_setoid R) (rig_setoid S);

  rig_map_zero : rig_map (rig_zero R) ≈ rig_zero S;
  rig_map_add : ∀ a b,
    rig_map (rig_add R a b) ≈ rig_add S (rig_map a) (rig_map b);
  rig_map_one : rig_map (rig_one R) ≈ rig_one S;
  rig_map_mul : ∀ a b,
    rig_map (rig_mul R a b) ≈ rig_mul S (rig_map a) (rig_map b)
}.

Arguments rig_map {R S} _.
Arguments rig_map_zero {R S} _.
Arguments rig_map_add {R S} _ _ _.
Arguments rig_map_one {R S} _.
Arguments rig_map_mul {R S} _ _ _.

#[local] Obligation Tactic := idtac.

(* Homomorphisms are compared by their underlying maps, pointwise. *)
#[export]
Program Instance RigHom_Setoid {R S : RigObject} : Setoid (RigHom R S) := {|
  equiv := fun f g => ∀ a, rig_map f a ≈ rig_map g a
|}.
Next Obligation.
  intros R S.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (rig_map g a); [ apply Hfg | apply Hgh ].
Qed.

Program Definition rig_hom_id {R : RigObject} : RigHom R R := {|
  rig_map := setoid_morphism_id
|}.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.

Program Definition rig_hom_compose {R S T : RigObject}
  (f : RigHom S T) (g : RigHom R S) : RigHom R T := {|
  rig_map := setoid_morphism_compose (rig_map f) (rig_map g)
|}.
Next Obligation.
  intros R S T f g; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_zero g)).
  apply rig_map_zero.
Qed.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_add g a b)).
  apply rig_map_add.
Qed.
Next Obligation.
  intros R S T f g; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_one g)).
  apply rig_map_one.
Qed.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_mul g a b)).
  apply rig_map_mul.
Qed.

Lemma rig_hom_compose_respects {R S T : RigObject} :
  Proper (equiv ==> equiv ==> equiv) (@rig_hom_compose R S T).
Proof.
  intros f1 f2 Hf g1 g2 Hg a; simpl.
  rewrite (Hf (rig_map g1 a)).
  apply (proper_morphism (rig_map f2)), Hg.
Qed.

(* The 范畴 rigs rig homomorphisms. （已译） *)
(*
   本节说明 Rig 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rig@{u p} : Category@{u p p} := {|
  obj     := RigObject@{p p p};
  hom     := RigHom@{p};
  homset  := @RigHom_Setoid@{p};
  id      := @rig_hom_id@{p};
  compose := @rig_hom_compose@{u p};

  compose_respects := @rig_hom_compose_respects@{u p}
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** The forgetful functors *)

(* To commutative monoids: keep the additive half. *)
Program Definition Rig_Forget_CMon : Rig ⟶ CMon := {|
  fobj := rig_cmon;
  fmap := fun R S f => {|
    cmon_map := rig_map f;
    cmon_map_zero := rig_map_zero f;
    cmon_map_plus := rig_map_add f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(* The multiplicative half, internal 幺半群 (Sets, ∏): the
 multiplication 未柯里化的 over product setoid, unit selected
 terminal setoid. （已译） *)
Program Definition rig_mult_monoid (R : RigObject) :
  @Monoid Sets Sets_Product_Monoidal (rig_setoid R) := {|
  mu := {| morphism := fun p => rig_mul R (fst p) (snd p) |};
  eta := {| morphism := fun _ => rig_one R |}
|}.
Next Obligation.
  intros R p q [Hp Hq]; simpl.
  now rewrite Hp, Hq.
Qed.
Next Obligation.
  intros R [[a b] c]; simpl.
  apply rig_mul_assoc.
Qed.
Next Obligation.
  intros R [u a]; simpl.
  apply rig_mul_one_l.
Qed.
Next Obligation.
  intros R [a u]; simpl.
  apply rig_mul_one_r.
Qed.

(* To internal monoids in Sets: keep the multiplicative half. *)
Program Definition Rig_Forget_Mon : Rig ⟶ @Mon Sets Sets_Product_Monoidal := {|
  fobj := fun R => (rig_setoid R : obj[Sets]; rig_mult_monoid R);
  fmap := fun R S f => (rig_map f; _)
|}.
Next Obligation.
  intros R S f.
  unshelve econstructor.
  - intro p; simpl.
    apply rig_map_mul.
  - intro u; simpl.
    apply rig_map_one.
Qed.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(* * ** The one-对象 Preadditive bridge （已译） *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DeloopRig (R : RigObject) : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => carrier (rig_setoid R);
  homset  := fun _ _ => is_setoid (rig_setoid R);
  id      := fun _ => rig_one R;
  compose := fun _ _ _ f g => rig_mul R f g;

  compose_respects := fun _ _ _ => rig_mul_respects R
|}.
Next Obligation. intros R x y f; simpl; apply rig_mul_one_l. Qed.
Next Obligation. intros R x y f; simpl; apply rig_mul_one_r. Qed.
Next Obligation.
  intros R x y z w f g h; simpl; symmetry; apply rig_mul_assoc.
Qed.
Next Obligation.
  intros R x y z w f g h; simpl; apply rig_mul_assoc.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance DeloopRig_LocallyPropositional (R : RigObject) :
  LocallyPropositional (DeloopRig R).
Proof.
  constructor.
  intros x y.
  exact (rig_prop R).
Defined.

(* The additive structure rig Preadditive enrichment its
 delooping: four clauses Definition 5.36 exactly the
 Preadditive fields one 对象. （已译） *)
Program Definition DeloopRig_Preadditive (R : RigObject) :
  Preadditive (DeloopRig R) := {|
  padd := fun _ _ => rig_add R;
  pzero := fun _ _ => rig_zero R
|}.
Next Obligation. intros R x y f g h; apply rig_add_assoc. Qed.
Next Obligation. intros R x y f g; apply rig_add_comm. Qed.
Next Obligation. intros R x y f; apply rig_add_zero_l. Qed.
Next Obligation. intros R x y z h f g; apply rig_distr_l. Qed.
Next Obligation. intros R x y z f g h; apply rig_distr_r. Qed.
Next Obligation. intros R x y z f; apply rig_mul_zero_l. Qed.
Next Obligation. intros R x y z f; apply rig_mul_zero_r. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition EndRig {C : Category} {LP : LocallyPropositional C}
  (P : Preadditive C) (c : C) :
  RigObject := {|
  rig_setoid := {| carrier := c ~> c; is_setoid := @homset C c c |};
  rig_zero := pzero;
  rig_add := padd;
  rig_one := id;
  rig_mul := fun f g => f ∘ g;

  rig_add_respects := @padd_respects C P c c;
  rig_mul_respects := @compose_respects C c c c;

  rig_add_assoc := @padd_assoc C P c c;
  rig_add_comm := @padd_comm C P c c;
  rig_add_zero_l := @padd_zero_left C P c c;

  rig_distr_l := @compose_padd_left C P c c c;
  rig_distr_r := fun a b c0 => @compose_padd_right C P c c c a b c0;

  rig_mul_zero_l := fun f => @compose_pzero_left C P c c c f;
  rig_mul_zero_r := fun f => @compose_pzero_right C P c c c f;

  rig_prop := locally_prop c c
|}.
Next Obligation. intros C LP P c f g h; simpl; symmetry; apply comp_assoc. Qed.
Next Obligation. intros C LP P c f; simpl; apply id_left. Qed.
Next Obligation. intros C LP P c f; simpl; apply id_right. Qed.

(* 相关说明。 （已译） *)
Example EndRig_DeloopRig_zero (R : RigObject) :
  rig_zero (EndRig (DeloopRig_Preadditive R) ttt) = rig_zero R := eq_refl.
Example EndRig_DeloopRig_add (R : RigObject) :
  rig_add (EndRig (DeloopRig_Preadditive R) ttt) = rig_add R := eq_refl.
Example EndRig_DeloopRig_one (R : RigObject) :
  rig_one (EndRig (DeloopRig_Preadditive R) ttt) = rig_one R := eq_refl.
Example EndRig_DeloopRig_mul (R : RigObject) :
  rig_mul (EndRig (DeloopRig_Preadditive R) ttt) = rig_mul R := eq_refl.

(* Packaged 同构 [Rig]: both directions 恒等
 carrier. (The full record equality blocked the
 证明-carrying law fields — see header.) （已译） *)
Program Definition EndRig_DeloopRig (R : RigObject) :
  EndRig (DeloopRig_Preadditive R) ttt ≅[Rig] R := {|
  to := {| rig_map := setoid_morphism_id |};
  from := {| rig_map := setoid_morphism_id |}
|}.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rig_iff_one_object_preadditive :=
  (@DeloopRig_Preadditive, @EndRig, @EndRig_DeloopRig).

(** ** The naturals (Example 5.37) *)

Definition nat_setoid_object : SetoidObject := {|
  carrier := nat;
  is_setoid := {| equiv := @eq nat; setoid_equiv := eq_equivalence |}
|}.

Program Definition Nat_Rig : RigObject := {|
  rig_setoid := nat_setoid_object;
  rig_zero := 0%nat;
  rig_add := Nat.add;
  rig_one := 1%nat;
  rig_mul := Nat.mul;

  (*
   本节说明 Rig 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid nat_setoid_object) (@eq nat)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros a b c; simpl; now rewrite Nat.add_assoc. Qed.
Next Obligation. intros a b; simpl; apply Nat.add_comm. Qed.
Next Obligation. intros a; simpl; reflexivity. Qed.
Next Obligation. intros a b c; simpl; now rewrite Nat.mul_assoc. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_1_l. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_1_r. Qed.
Next Obligation. intros a b c; simpl; apply Nat.mul_add_distr_l. Qed.
Next Obligation. intros a b c; simpl; apply Nat.mul_add_distr_r. Qed.
Next Obligation. intros a; simpl; reflexivity. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_0_r. Qed.

(** ** The booleans (Example 5.38) *)

Definition bool_setoid_object : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

Program Definition Bool_Rig : RigObject := {|
  rig_setoid := bool_setoid_object;
  rig_zero := false;
  rig_add := orb;
  rig_one := true;
  rig_mul := andb;

  rig_prop := @PropEquiv_of_relation _ (is_setoid bool_setoid_object) (@eq bool)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Record RingObject := {
  ring_rig :> RigObject;

  ring_neg : carrier (rig_setoid ring_rig) → carrier (rig_setoid ring_rig);
  ring_neg_respects : Proper (equiv ==> equiv) ring_neg;
  ring_neg_l : ∀ a,
    rig_add ring_rig (ring_neg a) a ≈ rig_zero ring_rig
}.

#[export] Existing Instance ring_neg_respects.

(* Ring homomorphisms are just rig homomorphisms: preservation of
   negation is a theorem, by uniqueness of additive inverses. *)
Lemma RigHom_neg (R S : RingObject) (f : RigHom R S)
  (a : carrier (rig_setoid R)) :
  rig_map f (ring_neg R a) ≈ ring_neg S (rig_map f a).
Proof.
  (* f(-a) = f(-a) + 0 = f(-a) + (f a + -f a) = (f(-a) + f a) + -f a
           = f(-a + a) + -f a = f 0 + -f a = -f a *)
  rewrite <- (rig_add_zero_r S (rig_map f (ring_neg R a))).
  rewrite <- (ring_neg_l S (rig_map f a)).
  rewrite (rig_add_comm S (ring_neg S (rig_map f a)) (rig_map f a)).
  rewrite <- rig_add_assoc.
  rewrite <- rig_map_add.
  rewrite (proper_morphism (rig_map f) _ _ (ring_neg_l R a)).
  rewrite rig_map_zero.
  now rewrite rig_add_zero_l.
Qed.

(* The 范畴 rings, forgetful 函子 rigs: full the
 nose, since homomorphisms coincide. （已译） *)
(* 相关说明。 （已译） *)
Program Definition Ring@{u p} : Category@{u p p} := {|
  obj     := RingObject@{p p p};
  hom     := fun R S => RigHom@{p} R S;
  homset  := fun R S => @RigHom_Setoid@{p} R S;
  id      := fun R => @rig_hom_id@{p} R;
  compose := fun _ _ _ f g => rig_hom_compose@{u p} f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects@{u p} _ _ _
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

Program Definition Ring_Forget_Rig : Ring ⟶ Rig := {|
  fobj := fun R => ring_rig R;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Z_eqT (x y : Z) : Type := x = y.

Lemma Z_eqT_Equivalence : Equivalence Z_eqT.
Proof.
  constructor; unfold Z_eqT.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition Z_setoid_object : SetoidObject := {|
  carrier := Z;
  is_setoid := {| equiv := Z_eqT; setoid_equiv := Z_eqT_Equivalence |}
|}.

Lemma Z_add_respectful : ∀ a b : Z, Z_eqT a b →
  ∀ c d : Z, Z_eqT c d → Z_eqT (Z.add a c) (Z.add b d).
Proof.
  intros a b Hab c d Hcd; unfold Z_eqT in *; now subst.
Qed.

Lemma Z_mul_respectful : ∀ a b : Z, Z_eqT a b →
  ∀ c d : Z, Z_eqT c d → Z_eqT (Z.mul a c) (Z.mul b d).
Proof.
  intros a b Hab c d Hcd; unfold Z_eqT in *; now subst.
Qed.

Lemma Z_opp_respectful : ∀ a b : Z, Z_eqT a b → Z_eqT (Z.opp a) (Z.opp b).
Proof.
  intros a b Hab; unfold Z_eqT in *; now subst.
Qed.

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Rig 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Int_Rig@{o p q | o <= q, p <= q +} : RigObject@{q o p} := {|
  rig_setoid := Z_setoid_object@{o p};
  rig_zero := 0%Z;
  rig_add := Z.add;
  rig_one := 1%Z;
  rig_mul := Z.mul;
  rig_add_respects := Z_add_respectful;
  rig_mul_respects := Z_mul_respectful;
  rig_add_assoc := fun a b c => eq_sym (Z.add_assoc a b c);
  rig_add_comm := Z.add_comm;
  rig_add_zero_l := Z.add_0_l;
  rig_mul_assoc := fun a b c => eq_sym (Z.mul_assoc a b c);
  rig_mul_one_l := Z.mul_1_l;
  rig_mul_one_r := Z.mul_1_r;
  rig_distr_l := Z.mul_add_distr_l;
  rig_distr_r := Z.mul_add_distr_r;
  rig_mul_zero_l := Z.mul_0_l;
  rig_mul_zero_r := Z.mul_0_r;

  (*
   本节说明 Rig 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid Z_setoid_object@{o p}) (@eq Z)
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition Int_Ring@{o p q | o <= q, p <= q +} : RingObject@{q o p} := {|
  ring_rig := Int_Rig@{o p q};
  ring_neg := Z.opp;
  ring_neg_respects := Z_opp_respectful;
  ring_neg_l := Z.add_opp_diag_l
|}.

(* 相关说明。 （已译） *)

(* The n-fold sum of 1. *)
Fixpoint rig_iter (R : RigObject) (n : nat) : carrier (rig_setoid R) :=
  match n with
  | O => rig_zero R
  | S k => rig_add R (rig_one R) (rig_iter R k)
  end.

Lemma rig_iter_add (R : RigObject) (a b : nat) :
  rig_iter R (a + b) ≈ rig_add R (rig_iter R a) (rig_iter R b).
Proof.
  induction a; simpl.
  - now rewrite rig_add_zero_l.
  - now rewrite IHa, rig_add_assoc.
Qed.

Lemma rig_iter_mul (R : RigObject) (a b : nat) :
  rig_iter R (a * b) ≈ rig_mul R (rig_iter R a) (rig_iter R b).
Proof.
  induction a; simpl.
  - now rewrite rig_mul_zero_l.
  - rewrite rig_iter_add, IHa.
    rewrite rig_distr_r.
    now rewrite rig_mul_one_l.
Qed.

Program Definition rig_from_nat (R : RigObject) : RigHom Nat_Rig R := {|
  rig_map := {| morphism := rig_iter R |}
|}.
Next Obligation. intros R; proper. Qed.
Next Obligation. intros R a b; apply rig_iter_add. Qed.
Next Obligation.
  intros R; simpl.
  now rewrite rig_add_zero_r.
Qed.
Next Obligation. intros R a b; apply rig_iter_mul. Qed.

Lemma rig_from_nat_unique (R : RigObject) (h : RigHom Nat_Rig R) (n : nat) :
  rig_map h n ≈ rig_iter R n.
Proof.
  induction n; simpl.
  - apply (rig_map_zero h).
  - change (S n) with (1 + n)%nat.
    rewrite (rig_map_add h 1%nat n).
    rewrite IHn.
    apply rig_add_respects; [| reflexivity ].
    (* h 1 ≈ 1: the multiplicative unit clause *)
    apply (rig_map_one h).
Qed.

#[export] Program Instance Rig_Initial : @Initial Rig := {
  terminal_obj := Nat_Rig;
  one := rig_from_nat
}.
Next Obligation.
  intros R f g n; simpl.
  rewrite (rig_from_nat_unique R f n).
  now rewrite (rig_from_nat_unique R g n).
Qed.

(** ** Acceptance tests *)

(* 相关说明。 （已译） *)
Example nat_rig_distr :
  rig_mul Nat_Rig 2%nat (rig_add Nat_Rig 3%nat 4%nat) = 14%nat
  := eq_refl.
Example bool_rig_annihilation :
  rig_mul Bool_Rig (rig_zero Bool_Rig) true = false := eq_refl.
Example int_ring_neg : rig_add Int_Rig (ring_neg Int_Ring 7%Z) 7%Z = 0%Z
  := eq_refl.

(* The initial homomorphism computes: 3 goes to 1 + (1 + (1 + 0)). *)
Example rig_iter_nat_3 :
  rig_map (rig_from_nat Nat_Rig) 3%nat = 3%nat := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example rig_forget_cmon_carrier (R : RigObject) :
  cmon_setoid (Rig_Forget_CMon R) = rig_setoid R := eq_refl.
Example rig_forget_cmon_sets (R : RigObject) :
  CMon_Forget (Rig_Forget_CMon R) = rig_setoid R := eq_refl.
Example rig_forget_mon_sets (R : RigObject) :
  Mon_Forget (Rig_Forget_Mon R) = rig_setoid R := eq_refl.
