Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Wikipedia: https://en.wikipedia.org/wiki/Center_(group_theory)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition IsCentral (G : GrpObject) (z : carrier G) : Type :=
  ∀ g : carrier G, grp_mul G z g ≈ grp_mul G g z.

Lemma central_unit (G : GrpObject) : IsCentral G (grp_unit G).
Proof.
  intro g.
  rewrite grp_mul_unit_l, grp_mul_unit_r.
  reflexivity.
Qed.

Lemma central_mul (G : GrpObject) (z w : carrier G) :
  IsCentral G z → IsCentral G w → IsCentral G (grp_mul G z w).
Proof.
  intros Hz Hw g.
  rewrite grp_mul_assoc.
  rewrite (Hw g).
  rewrite <- grp_mul_assoc.
  rewrite (Hz g).
  rewrite grp_mul_assoc.
  reflexivity.
Qed.

Lemma central_inv (G : GrpObject) (z : carrier G) :
  IsCentral G z → IsCentral G (grp_inv G z).
Proof.
  intros Hz g.
  rewrite <- (grp_mul_unit_r G (grp_mul G (grp_inv G z) g)).
  rewrite <- (grp_mul_inv_r G z).
  rewrite <- grp_mul_assoc.
  rewrite (grp_mul_assoc G (grp_inv G z) g z).
  rewrite <- (Hz g).
  rewrite <- (grp_mul_assoc G (grp_inv G z) z g).
  rewrite grp_mul_inv_l, grp_mul_unit_l.
  reflexivity.
Qed.

(*
   本节说明 Center 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition center_carrier (G : GrpObject) : Type :=
  { z : carrier G & IsCentral G z }.

Definition mk_central (G : GrpObject) (z : carrier G)
  (Hz : IsCentral G z) : center_carrier G :=
  existT (fun z : carrier G => IsCentral G z) z Hz.

Program Definition center_setoid (G : GrpObject) : SetoidObject := {|
  carrier := center_carrier G;
  is_setoid := {| equiv := fun a b => `1 a ≈ `1 b |}
|}.
Next Obligation.
  intro G; equivalence.
Qed.

Program Definition CenterGrp (G : GrpObject) : GrpObject := {|
  grp_setoid := center_setoid G;
  grp_unit := mk_central G (grp_unit G) (central_unit G);
  grp_mul := fun a b =>
    mk_central G (grp_mul G (`1 a) (`1 b))
      (central_mul G (`1 a) (`1 b) (`2 a) (`2 b));
  grp_inv := fun a =>
    mk_central G (grp_inv G (`1 a)) (central_inv G (`1 a) (`2 a));
  (* The centre's `≈` compares first projections in [G], so it is
     propositional exactly when [G]'s own `≈` is. *)
  grp_prop :=
    sigma_first_PropEquiv (is_setoid (center_setoid G))
      (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *.
  now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

(* The center abelian construction: commutation two central
 elements first one's 中心性 at second. （已译） *)
Lemma CenterGrp_abelian (G : GrpObject) (a b : carrier (CenterGrp G)) :
  grp_mul (CenterGrp G) a b ≈ grp_mul (CenterGrp G) b a.
Proof. exact (`2 a (`1 b)). Qed.

(*
   本节说明 Center 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CenterAb (G : GrpObject) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := center_setoid G;
    cmon_zero := mk_central G (grp_unit G) (central_unit G);
    cmon_plus := fun a b =>
      mk_central G (grp_mul G (`1 a) (`1 b))
        (central_mul G (`1 a) (`1 b) (`2 a) (`2 b));
    cmon_prop :=
      sigma_first_PropEquiv (is_setoid (center_setoid G))
        (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
  |};
  ab_neg := fun a =>
    mk_central G (grp_inv G (`1 a)) (central_inv G (`1 a) (`2 a))
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *.
  now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a b; simpl; exact (`2 a (`1 b)). Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation.
  intros G a a' Ha; simpl in *.
  now rewrite Ha.
Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

(* The center includes 进入 group. （已译） *)
Program Definition Center_incl (G : GrpObject) :
  CenterGrp G ~{Grp}~> G := {|
  grp_map := {| morphism := fun a => `1 a |}
|}.
Next Obligation. intros G a b H; exact H. Qed.
Next Obligation. intros G; simpl; reflexivity. Qed.
Next Obligation. intros G a b; simpl; reflexivity. Qed.

(** ** Z(S₂) is all of S₂ *)

Lemma GrpTwo_abelian (a b : carrier GrpTwo) :
  grp_mul GrpTwo a b ≈ grp_mul GrpTwo b a.
Proof.
  destruct a as [[]|[]], b as [[]|[]]; exact ttt.
Qed.

Program Definition Center_GrpTwo_iso : CenterGrp GrpTwo ≅[Grp] GrpTwo := {|
  to := Center_incl GrpTwo;
  from := {| grp_map := {| morphism := fun x =>
    mk_central GrpTwo x (fun g => GrpTwo_abelian x g) |} |}
|}.
Next Obligation. intros a b H; exact H. Qed.
Next Obligation. simpl; exact ttt. Qed.
Next Obligation. intros a b; simpl; destruct a as [[]|[]], b as [[]|[]]; exact ttt. Qed.
Next Obligation. intros a; simpl; destruct a as [[]|[]]; exact ttt. Qed.
Next Obligation.
  intros a; simpl; destruct a as [z Hz]; simpl;
    destruct z as [[]|[]]; exact ttt.
Qed.

(** ** Z(S₃) is trivial *)

(* Only 恒等 commutes both generators: case analysis over
 six elements, testing 中心性 at rotation r = (rot1,
 false) reflection s = (rot0, true). （已译） *)
Lemma S3_center_trivial (z : carrier S3) :
  IsCentral S3 z → z = s3_unit.
Proof.
  intros Hz.
  destruct z as [[| |] [|]]; try reflexivity.
  all: try (pose proof (Hz S3_r) as E; vm_compute in E; discriminate E).
  all: pose proof (Hz S3_s) as E; vm_compute in E; discriminate E.
Qed.

(** ** The sign retract S₂ → S₃ → S₂ *)

(* ℤ/2 includes as the rotation-free permutations... *)
Program Definition grp_two_s3 : GrpTwo ~{Grp}~> S3 := {|
  grp_map := {| morphism := fun x : carrier GrpTwo =>
    ((rot0, if x then false else true) : carrier S3) |}
|}.
Next Obligation.
  intros a b H; destruct a as [[]|[]], b as [[]|[]];
    (reflexivity + contradiction).
Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation.
  intros a b; destruct a as [[]|[]], b as [[]|[]]; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Program Definition s3_sign : S3 ~{Grp}~> GrpTwo := {|
  grp_map := {| morphism := fun p : carrier S3 =>
    if snd p then grp_two_one else grp_two_zero |}
|}.
Next Obligation. simpl; exact ttt. Qed.
Next Obligation.
  intros a b; destruct a as [ra [|]], b as [rb [|]]; simpl; exact ttt.
Qed.

(* The retract law: sign after 含入 恒等 ℤ/2. （已译） *)
Lemma sign_retract :
  s3_sign ∘[Grp] grp_two_s3 ≈ @id Grp GrpTwo.
Proof.
  intros x; destruct x as [[]|[]]; exact ttt.
Qed.

(* Mac Lane's remark, before the exercise: a homomorphism need not
   carry central elements to central elements.  The inclusion sends
   ℤ/2's central nonidentity to the reflection s, which S₃'s trivial
   center excludes. *)
Lemma central_not_preserved :
  IsCentral GrpTwo grp_two_one *
  (IsCentral S3 (grp_map grp_two_s3 grp_two_one) → False).
Proof.
  split.
  - intro g; apply GrpTwo_abelian.
  - intro Hz.
    pose proof (S3_center_trivial _ Hz) as E.
    vm_compute in E; discriminate E.
Qed.

(** ** The no-functor theorem *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_center_functor (T : Grp ⟶ Ab)
  (HT : ∀ G : GrpObject, fobj[T] G = CenterAb G) : False.
Proof.
  (* The retract factors 恒等 T S₂ through T S₃. （已译） *)
  assert (Hrt : ∀ x : carrier (fobj[T] GrpTwo),
             cmon_map (fmap[T] s3_sign) (cmon_map (fmap[T] grp_two_s3) x)
               ≈ x).
  { intro x.
    pose proof (@fmap_comp _ _ T GrpTwo S3 GrpTwo s3_sign grp_two_s3)
      as Hc.
    pose proof (@fmap_respects _ _ T GrpTwo GrpTwo
                  (s3_sign ∘[Grp] grp_two_s3) (@id Grp GrpTwo)
                  sign_retract) as Hr.
    pose proof (@fmap_id _ _ T GrpTwo) as Hi.
    specialize (Hc x); specialize (Hr x); specialize (Hi x).
    simpl in Hc, Hr, Hi.
    now rewrite <- Hc, Hr, Hi. }
  (* Every element of T S₃ is the unit, since Z(S₃) is trivial. *)
  assert (Hall : ∀ w : carrier (fobj[T] S3),
             w ≈ cmon_zero (fobj[T] S3)).
  { rewrite (HT S3).
    intros [z Hz]; simpl.
    now rewrite (S3_center_trivial z Hz). }
  (* Hence every element of T S₂ is the unit... *)
  assert (Hcollapse : ∀ x : carrier (fobj[T] GrpTwo),
             x ≈ cmon_zero (fobj[T] GrpTwo)).
  { intro x.
    rewrite <- (Hrt x).
    rewrite (Hall (cmon_map (fmap[T] grp_two_s3) x)).
    apply (cmon_map_zero (fmap[T] s3_sign)). }
  (* ...but Z(S₂) contains the nontrivial element of ℤ/2. *)
  generalize Hcollapse.
  rewrite (HT GrpTwo).
  intro Hc2.
  exact (Hc2 (mk_central GrpTwo grp_two_one
                (fun g => GrpTwo_abelian grp_two_one g))).
Qed.
