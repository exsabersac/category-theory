Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.
Open Scope category_scope.

(* 相关说明。 （已译） *)
#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/p-adic+integer
 Wikipedia: https://en.wikipedia.org/wiki/P-adic_number

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition RingComm (R : RingObject) : Type :=
  ∀ a b : carrier (rig_setoid R), rig_mul R a b ≈ rig_mul R b a.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ring_comm_is_CRng_predicate (R : RingObject) :
  RingComm R = @sobj Rng CRng_Sub R := eq_refl.

Section Principal.

Context {R : RingObject}.
Context (Rcomm : RingComm R).
Context (d : carrier (rig_setoid R)).

(* 相关说明。 （已译） *)
Definition divides (a : carrier (rig_setoid R)) : Type :=
  { k : carrier (rig_setoid R) & a ≈ rig_mul R d k }.

Program Definition PrincipalIdeal : Ideal R := {|
  idl_mem := divides
|}.
Next Obligation.
  intros a b Hab [k Hk]; exists k; now rewrite <- Hab.
Qed.
Next Obligation.
  exists (rig_zero R); now rewrite (rig_mul_zero_r R d).
Qed.
Next Obligation.
  intros a b [k Hk] [l Hl]; exists (rig_add R k l).
  rewrite Hk, Hl; now rewrite (rig_distr_l R d k l).
Qed.
Next Obligation.
  intros r a [k Hk]; exists (rig_mul R r k).
  rewrite Hk.
  rewrite <- (rig_mul_assoc R r d k).
  rewrite (Rcomm r d).
  now rewrite (rig_mul_assoc R d r k).
Qed.
Next Obligation.
  intros a r [k Hk]; exists (rig_mul R k r).
  rewrite Hk; now rewrite (rig_mul_assoc R d k r).
Qed.

(* 相关说明。 （已译） *)
Definition principal_generator : idl_mem PrincipalIdeal d.
Proof. exists (rig_one R); now rewrite (rig_mul_one_r R d). Defined.

End Principal.

Arguments PrincipalIdeal {R} Rcomm d.
Arguments divides {R} d a.

(* 相关说明。 （已译） *)

Section Tower.

Context {R : RingObject}.
Context (Rcomm : RingComm R).
Context (d : carrier (rig_setoid R)).

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint dpow (n : nat) : carrier (rig_setoid R) :=
  match n with
  | O   => rig_one R
  | S k => rig_mul R d (dpow k)
  end.

Definition ResIdeal (n : nat) : Ideal R := PrincipalIdeal Rcomm (dpow n).

Definition ResRing (n : nat) : RingObject := QuotientRing (ResIdeal n).

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma res_ideal_succ_sub (n : nat) (a : carrier (rig_setoid R)) :
  idl_mem (ResIdeal (S n)) a → idl_mem (ResIdeal n) a.
Proof.
  intros [k Hk]; exists (rig_mul R d k).
  rewrite Hk; simpl.
  rewrite (rig_mul_assoc R d (dpow n) k).
  rewrite <- (rig_mul_assoc R (dpow n) d k).
  rewrite (Rcomm (dpow n) d).
  now rewrite (rig_mul_assoc R d (dpow n) k).
Qed.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition res_kills (n : nat) : RKills (ResIdeal (S n)) (ResRing n).
Proof.
  exists (rquot_proj (ResIdeal n)).
  intros a Ha.
  exact (rquot_proj_kills (ResIdeal n) a (res_ideal_succ_sub n a Ha)).
Defined.

Definition res_proj (n : nat) : ResRing (S n) ~{Rng}~> ResRing n :=
  rquot_med (ResIdeal (S n)) (res_kills n).

(* 相关说明。 （已译） *)
Lemma res_proj_commutes (n : nat) :
  res_proj n ∘ rquot_proj (ResIdeal (S n)) ≈ rquot_proj (ResIdeal n).
Proof. exact (rquot_med_commutes (ResIdeal (S n)) (res_kills n)). Qed.

(* The action arbitrary order 证明, recursion derivation
 -- [Construction/Chain.v] idiom, one shape down. （已译） *)
Fixpoint res_hom {m n : nat} (f : le_t m n) : ResRing n ~{Rng}~> ResRing m :=
  match f with
  | le_t_n     => id
  | le_t_S f'  => res_hom f' ∘ res_proj _
  end.

Lemma res_hom_trans {m n k : nat} (a : le_t m n) (b : le_t n k) :
  res_hom (le_t_trans a b) ≈ res_hom a ∘ res_hom b.
Proof.
  induction b as [| k' b' IH].
  - cbn [res_hom le_t_trans]; now rewrite id_right.
  - cbn [res_hom le_t_trans]; rewrite IH; now rewrite comp_assoc.
Qed.

(* Stated at exactly 函子's shape, so obligation below needs no
 conversion [Omega^op]'s 复合. （已译） *)
Lemma res_hom_comp {x y z : nat}
  (f : y ~{Omega^op}~> z) (g : x ~{Omega^op}~> y) :
  res_hom (f ∘ g) ≈ res_hom f ∘ res_hom g.
Proof. exact (res_hom_trans f g). Qed.

(* [Omega]'s hom-setoid is strict equality, so respectfulness is [subst]. *)
Lemma res_hom_respects {x y : nat} (f g : x ~{Omega^op}~> y) :
  f ≈ g → res_hom f ≈ res_hom g.
Proof. intro H; simpl in H; subst; reflexivity. Qed.

Lemma res_hom_id (x : nat) :
  res_hom (@id (Omega^op) x) ≈ @id Rng (ResRing x).
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ResTower : Omega^op ⟶ Rng :=
  @Build_Functor (Omega^op) Rng ResRing (fun _ _ f => res_hom f)
    (fun x y f g H => res_hom_respects f g H)
    res_hom_id
    (fun x y z f g => res_hom_comp f g).

End Tower.

(* 相关说明。 （已译） *)

Section Limit.

Context {R : RingObject}.
Context (Rcomm : RingComm R).
Context (d : carrier (rig_setoid R)).

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition USetTower : Omega^op ⟶ Sets := Rng_Forget ◯ ResTower Rcomm d.

Example uset_tower_stage (n : nat) :
  fobj[USetTower] n = rig_setoid (ResRing Rcomm d n) := eq_refl.

Definition ZpCarrier : obj[Sets] := tower_obj USetTower.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition zp_PropEquiv : PropEquiv (is_setoid ZpCarrier) :=
  sigma_first_PropEquiv (is_setoid ZpCarrier)
    (fun _ _ h => h) (fun _ _ h => h)
    (iprod_PropEquiv (fun n : nat => fobj[USetTower] n)
       (fun n => rig_prop (ResRing Rcomm d n))).

(* 相关说明。 （已译） *)
Definition zp_zero : carrier ZpCarrier.
Proof.
  exists (fun n => rig_zero (ResRing Rcomm d n)).
  intro n; exact (rig_map_zero (res_proj Rcomm d n)).
Defined.

Definition zp_one : carrier ZpCarrier.
Proof.
  exists (fun n => rig_one (ResRing Rcomm d n)).
  intro n; exact (rig_map_one (res_proj Rcomm d n)).
Defined.

Definition zp_add (p q : carrier ZpCarrier) : carrier ZpCarrier.
Proof.
  exists (fun n => rig_add (ResRing Rcomm d n) (`1 p n) (`1 q n)).
  intro n.
  exact (transitivity
           (rig_map_add (res_proj Rcomm d n) (`1 p (S n)) (`1 q (S n)))
           (rig_add_respects (ResRing Rcomm d n) _ _ (`2 p n) _ _ (`2 q n))).
Defined.

Definition zp_mul (p q : carrier ZpCarrier) : carrier ZpCarrier.
Proof.
  exists (fun n => rig_mul (ResRing Rcomm d n) (`1 p n) (`1 q n)).
  intro n.
  exact (transitivity
           (rig_map_mul (res_proj Rcomm d n) (`1 p (S n)) (`1 q (S n)))
           (rig_mul_respects (ResRing Rcomm d n) _ _ (`2 p n) _ _ (`2 q n))).
Defined.

Definition zp_neg (p : carrier ZpCarrier) : carrier ZpCarrier.
Proof.
  exists (fun n => ring_neg (ResRing Rcomm d n) (`1 p n)).
  intro n.
  exact (transitivity
           (RigHom_neg _ _ (res_proj Rcomm d n) (`1 p (S n)))
           (ring_neg_respects (ResRing Rcomm d n) _ _ (`2 p n))).
Defined.

(* Every law stage's law read at each coordinate; file proves no
 ring 恒等 own. （已译） *)
Program Definition ZpRig : RigObject := {|
  rig_setoid := ZpCarrier;
  rig_zero   := zp_zero;
  rig_add    := zp_add;
  rig_one    := zp_one;
  rig_mul    := zp_mul;
  rig_prop   := zp_PropEquiv
|}.
Next Obligation.
  intros p q Hpq r t Hrt n; apply rig_add_respects;
    [exact (Hpq n)|exact (Hrt n)].
Qed.
Next Obligation.
  intros p q Hpq r t Hrt n; apply rig_mul_respects;
    [exact (Hpq n)|exact (Hrt n)].
Qed.
Next Obligation. intros a b c n; apply rig_add_assoc. Qed.
Next Obligation. intros a b n; apply rig_add_comm. Qed.
Next Obligation. intros a n; apply rig_add_zero_l. Qed.
Next Obligation. intros a b c n; apply rig_mul_assoc. Qed.
Next Obligation. intros a n; apply rig_mul_one_l. Qed.
Next Obligation. intros a n; apply rig_mul_one_r. Qed.
Next Obligation. intros a b c n; apply rig_distr_l. Qed.
Next Obligation. intros a b c n; apply rig_distr_r. Qed.
Next Obligation. intros a n; apply rig_mul_zero_l. Qed.
Next Obligation. intros a n; apply rig_mul_zero_r. Qed.

Program Definition Zp : RingObject := {|
  ring_rig := ZpRig;
  ring_neg := zp_neg
|}.
Next Obligation. intros p q Hpq n; apply ring_neg_respects; exact (Hpq n). Qed.
Next Obligation. intros a n; apply ring_neg_l. Qed.

(* 相关说明。 （已译） *)
Example zp_carrier_is_tower :
  rig_setoid Zp = tower_obj USetTower := eq_refl.

Example zp_carrier_is_inverse_limit :
  rig_setoid Zp = inverse_limit USetTower := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Program Definition zp_proj (n : nat) : Zp ~{Rng}~> ResRing Rcomm d n := {|
  rig_map := tower_proj USetTower n
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; reflexivity. Qed.

Program Definition zp_acone : @ACone (Omega^op) Rng Zp (ResTower Rcomm d) := {|
  vertex_map := zp_proj
|}.
Next Obligation.
  intros m n f p; exact (tower_compat_all USetTower (`1 p) (`2 p) f).
Qed.

(* 相关说明。 （已译） *)
Program Definition zp_med (N : Cone (ResTower Rcomm d)) :
  vertex_obj[N] ~{Rng}~> Zp := {|
  rig_map := {| morphism := fun e =>
    (fun n => rig_map (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n) e ;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (S n) n
                (tower_step n) e) |}
|}.
Next Obligation.
  intros N e e' Hee' n.
  exact (proper_morphism
           (rig_map (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n)) e e' Hee').
Qed.
Next Obligation. intros N n; apply rig_map_zero. Qed.
Next Obligation. intros N a b n; apply rig_map_add. Qed.
Next Obligation. intros N n; apply rig_map_one. Qed.
Next Obligation. intros N a b n; apply rig_map_mul. Qed.

Program Definition Zp_limit : IsALimit (ResTower Rcomm d) Zp := {|
  limit_acone := zp_acone;
  ump_limit := fun N => {| unique_obj := zp_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zp_zero_forced (z : ZpCarrier)
  (H : ∀ n, zp_proj n z ≈ rig_zero (ResRing Rcomm d n)) : z ≈ zp_zero.
Proof. intro n; exact (H n). Qed.

Lemma zp_one_forced (u : ZpCarrier)
  (H : ∀ n, zp_proj n u ≈ rig_one (ResRing Rcomm d n)) : u ≈ zp_one.
Proof. intro n; exact (H n). Qed.

Lemma zp_add_forced (add' : ZpCarrier → ZpCarrier → ZpCarrier)
  (H : ∀ n p q, zp_proj n (add' p q)
                ≈ rig_add (ResRing Rcomm d n) (zp_proj n p) (zp_proj n q))
  (p q : ZpCarrier) : add' p q ≈ zp_add p q.
Proof. intro n; exact (H n p q). Qed.

Lemma zp_mul_forced (mul' : ZpCarrier → ZpCarrier → ZpCarrier)
  (H : ∀ n p q, zp_proj n (mul' p q)
                ≈ rig_mul (ResRing Rcomm d n) (zp_proj n p) (zp_proj n q))
  (p q : ZpCarrier) : mul' p q ≈ zp_mul p q.
Proof. intro n; exact (H n p q). Qed.

Lemma zp_neg_forced (neg' : ZpCarrier → ZpCarrier)
  (H : ∀ n p, zp_proj n (neg' p) ≈ ring_neg (ResRing Rcomm d n) (zp_proj n p))
  (p : ZpCarrier) : neg' p ≈ zp_neg p.
Proof. intro n; exact (H n p). Qed.

End Limit.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ZComm : RingComm Int_Ring := Int_Ring_commutative.

(* Mac Lane's Z_p: the limit of Z/p <- Z/p² <- Z/p³ <- ... *)
Definition ZpTower (p : Z) : Omega^op ⟶ Rng := ResTower ZComm p.
Definition Zp_int (p : Z) : RingObject := Zp ZComm p.
Definition Zp_int_limit (p : Z) : IsALimit (ZpTower p) (Zp_int p) :=
  Zp_limit ZComm p.

Example zp_int_stage (p : Z) (n : nat) :
  fobj[ZpTower p] n
    = QuotientRing (PrincipalIdeal ZComm (@dpow Int_Ring p n))
  := eq_refl.

(* The polynomial ring is commutative BY CONSTRUCTION: [pe_mul_comm] is a
   constructor of Instance/Rng/Polynomial.v's congruence, and that file
   already packages it as [poly_comm], whose statement IS [RingComm]
   after unfolding.  Consumed, not reproved. *)
Definition ZPolyComm : RingComm ZPoly := poly_comm Int_Ring.

(* 相关说明。 （已译） *)
Definition PowerSeriesTower : Omega^op ⟶ Rng :=
  ResTower ZPolyComm (@poly_x Int_Ring).

Definition PowerSeries : RingObject := Zp ZPolyComm (@poly_x Int_Ring).

Definition PowerSeries_limit : IsALimit PowerSeriesTower PowerSeries :=
  Zp_limit ZPolyComm (@poly_x Int_Ring).

(* Both same term at two generators, what makes the
 exercise 推论 rather than second development. （已译） *)
Example padic_and_series_share_the_construction (p : Z) :
  (Zp_int p = Zp ZComm p) * (PowerSeries = Zp ZPolyComm (@poly_x Int_Ring))
  := (eq_refl, eq_refl).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Digits.

Context (p : Z).
Context (Hp : (1 < p)%Z).

Local Notation P n := (@dpow Int_Ring p n).
Local Notation Zpc := (ZpCarrier ZComm p).

(* 相关说明。 （已译） *)

(* The transition map residue tower does not move integer: the
 quotient map ℤ/d^(n+1) → ℤ/d^n induced 恒等 ℤ. （已译） *)
Example digit_transition_is_id (n : nat) (x : Z) :
  fmap[USetTower ZComm p] (tower_step n) x = x := eq_refl.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example digit_equiv_is_divides (n : nat) (x y : Z) :
  (@equiv _ (rig_setoid (ResRing ZComm p n)) x y)
    = inhabited (@divides Int_Ring (P n) (Z.add x (Z.opp y))) := eq_refl.

Example digit_divides_is_sigma (a b : Z) :
  @divides Int_Ring a b = { k : Z & b = Z.mul a k } := eq_refl.

Lemma dpow_O : P 0%nat = 1%Z. Proof. reflexivity. Qed.
Lemma dpow_S (n : nat) : P (S n) = (p * P n)%Z. Proof. reflexivity. Qed.

Lemma dpow_pos (n : nat) : (0 < P n)%Z.
Proof using Hp p.
  induction n as [|k IH].
  - rewrite dpow_O; lia.
  - rewrite dpow_S; apply Z.mul_pos_pos; lia.
Qed.

Lemma dpow_nz (n : nat) : (P n <> 0)%Z.
Proof using Hp p. pose proof (dpow_pos n); lia. Qed.

(* * *** The two directions residue 关系, integer statements （已译） *)

Lemma res_of_dvd (n : nat) (x y k : Z) (H : (x + - y)%Z = (P n * k)%Z) :
  @equiv _ (rig_setoid (ResRing ZComm p n)) x y.
Proof. exact (inhabits (existT _ k H)). Qed.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma res_dvd_dec (n : nat) (x y : Z) :
  { k : Z & (x + - y)%Z = (P n * k)%Z }
  + ({ k : Z & (x + - y)%Z = (P n * k)%Z } → False).
Proof using Hp p.
  destruct (Z.eq_dec ((x + - y) mod P n) 0) as [He|He].
  - left.
    exists ((x + - y) / P n)%Z.
    pose proof (Z.div_mod (x + - y) (P n) (dpow_nz n)) as Hq.
    lia.
  - right.
    intros [k Hk].
    apply He.
    rewrite Hk, Z.mul_comm.
    apply Z_mod_mult.
Qed.

Lemma res_to_dvd (n : nat) (x y : Z)
  (H : @equiv _ (rig_setoid (ResRing ZComm p n)) x y) :
  { k : Z & (x + - y)%Z = (P n * k)%Z }.
Proof using Hp p.
  destruct (res_dvd_dec n x y) as [Hd|Hd].
  - exact Hd.
  - exfalso.
    destruct H as [[k Hk]].
    exact (Hd (existT _ k Hk)).
Qed.

Lemma mod_eq_of_res (n : nat) (x y : Z)
  (H : @equiv _ (rig_setoid (ResRing ZComm p n)) x y) :
  (x mod P n)%Z = (y mod P n)%Z.
Proof using Hp p.
  destruct (res_to_dvd n x y H) as [k Hk].
  rewrite (Z.mul_comm (P n) k) in Hk.
  replace x with (y + k * P n)%Z by lia.
  apply Z_mod_plus_full.
Qed.

Lemma res_of_mod_eq (n : nat) (x y : Z) (H : (x mod P n)%Z = (y mod P n)%Z) :
  @equiv _ (rig_setoid (ResRing ZComm p n)) x y.
Proof using Hp p.
  apply res_of_dvd with (k := (x / P n - y / P n)%Z).
  pose proof (Z.div_mod x (P n) (dpow_nz n)) as Hx.
  pose proof (Z.div_mod y (P n) (dpow_nz n)) as Hy.
  rewrite Z.mul_sub_distr_l; lia.
Qed.

(* 相关说明。 （已译） *)
Lemma mod_mod_mul (b c x : Z) (Hb : (0 < b)%Z) (Hc : (0 < c)%Z) :
  ((x mod (c * b)) mod b)%Z = (x mod b)%Z.
Proof.
  assert (Hcb : (c * b <> 0)%Z) by (apply Z.neq_mul_0; lia).
  pose proof (Z.div_mod x (c * b) Hcb) as Hd.
  rewrite Hd at 2.
  replace (c * b * (x / (c * b)) + x mod (c * b))%Z
     with (x mod (c * b) + (c * (x / (c * b))) * b)%Z by ring.
  now rewrite Z_mod_plus_full.
Qed.

(* 相关说明。 （已译） *)

Definition zpd (f : Zpc) (i : nat) : Z :=
  (((`1 f (S i)) mod P (S i)) / P i)%Z.

Lemma zpd_bound (f : Zpc) (i : nat) : (0 <= zpd f i < p)%Z.
Proof using Hp p.
  unfold zpd.
  pose proof (dpow_pos i) as Hi.
  pose proof (dpow_pos (S i)) as HSi.
  destruct (Z.mod_pos_bound (`1 f (S i)) (P (S i)) HSi) as [Hlo Hhi].
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|].
    rewrite (Z.mul_comm (P i) p), <- dpow_S; exact Hhi.
Qed.

Fixpoint dsum (a : nat -> Z) (n : nat) : Z :=
  match n with
  | O   => 0%Z
  | S k => (dsum a k + a k * P k)%Z
  end.

Lemma dsum_bound (a : nat -> Z) (Ha : ∀ i, (0 <= a i < p)%Z) (n : nat) :
  (0 <= dsum a n < P n)%Z.
Proof using Hp p.
  induction n as [|k IH]; cbn [dsum].
  - rewrite dpow_O; lia.
  - destruct IH as [L U]; destruct (Ha k) as [Al Au].
    pose proof (dpow_pos k) as Hk.
    rewrite dpow_S; nia.
Qed.

(* 相关说明。 （已译） *)
Lemma dsum_compat (a : nat -> Z) (n : nat) :
  (dsum a (S n) + - dsum a n)%Z = (P n * a n)%Z.
Proof. cbn [dsum]; ring. Qed.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition digits_to_zp (a : nat -> Z) : Zpc.
Proof.
  exists (dsum a).
  intro n; exact (res_of_dvd n (dsum a (S n)) (dsum a n) (a n) (dsum_compat a n)).
Defined.

Example digits_to_zp_stage (a : nat -> Z) (n : nat) :
  `1 (digits_to_zp a) n = dsum a n := eq_refl.

(* 相关说明。 （已译） *)

Lemma zpd_dsum (f : Zpc) (n : nat) :
  dsum (zpd f) n = ((`1 f n) mod P n)%Z.
Proof using Hp p.
  induction n as [|k IH].
  - cbn [dsum]; rewrite dpow_O, Z.mod_1_r; reflexivity.
  - cbn [dsum]; rewrite IH; unfold zpd.
    pose proof (dpow_pos k) as Hk.
    assert (Hgm : ((`1 f (S k)) mod P (S k) mod P k)%Z
                    = ((`1 f k) mod P k)%Z).
    { rewrite dpow_S, mod_mod_mul by lia.
      exact (mod_eq_of_res k _ _ (`2 f k)). }
    pose proof (Z.div_mod ((`1 f (S k)) mod P (S k)) (P k) (dpow_nz k)) as Hq.
    rewrite Hgm in Hq.
    rewrite (Z.mul_comm (P k) _) in Hq.
    lia.
Qed.

(** *** The two round trips *)

Lemma digits_round (a : nat -> Z) (Ha : ∀ i, (0 <= a i < p)%Z) (i : nat) :
  zpd (digits_to_zp a) i = a i.
Proof using Hp p.
  unfold zpd, digits_to_zp; cbn [projT1].
  rewrite (Z.mod_small _ _ (dsum_bound a Ha (S i))).
  cbn [dsum].
  rewrite Z.div_add by exact (dpow_nz i).
  rewrite (Z.div_small _ _ (dsum_bound a Ha i)); lia.
Qed.

Lemma zp_round (f : Zpc) :
  @equiv _ Zpc (digits_to_zp (zpd f)) f.
Proof using Hp p.
  intro n.
  change (`1 (digits_to_zp (zpd f)) n) with (dsum (zpd f) n).
  rewrite (zpd_dsum f n).
  apply res_of_dvd with (k := (- ((`1 f n) / P n))%Z).
  pose proof (Z.div_mod (`1 f n) (P n) (dpow_nz n)) as Hd.
  rewrite Z.mul_opp_r; lia.
Qed.

(* 相关说明。 （已译） *)

Definition DigitCarrier : Type := { a : nat -> Z & ∀ i, (0 <= a i < p)%Z }.

Program Definition DigitSeq : obj[Sets] := {|
  carrier   := DigitCarrier;
  is_setoid := {| equiv := fun a b => ∀ i, `1 a i = `1 b i |}
|}.
Next Obligation.
  constructor.
  - intros a i; reflexivity.
  - intros a b H i; symmetry; exact (H i).
  - intros a b c Hab Hbc i; transitivity (`1 b i);
      [exact (Hab i)|exact (Hbc i)].
Qed.

Program Definition zp_to_digits : rig_setoid (Zp ZComm p) ~{Sets}~> DigitSeq
  := {| morphism := fun f => (zpd f ; zpd_bound f) |}.
Next Obligation.
  intros f g Hfg i; cbn [projT1]; unfold zpd.
  rewrite (mod_eq_of_res (S i) _ _ (Hfg (S i))); reflexivity.
Qed.

Program Definition digits_to_zp_mor
  : DigitSeq ~{Sets}~> rig_setoid (Zp ZComm p)
  := {| morphism := fun a => digits_to_zp (`1 a) |}.
Next Obligation.
  intros a b Hab n.
  apply res_of_dvd with (k := 0%Z).
  assert (Hs : dsum (`1 a) n = dsum (`1 b) n).
  { induction n as [|k IH]; cbn [dsum];
    [reflexivity | rewrite IH, (Hab k); reflexivity]. }
  change (`1 (digits_to_zp (`1 a)) n) with (dsum (`1 a) n).
  change (`1 (digits_to_zp (`1 b)) n) with (dsum (`1 b) n).
  rewrite Hs; ring.
Qed.

(* Mac Lane's Exercise 6: p-adic integers ARE digit strings below p. *)
Program Definition Zp_digits_iso
  : @Isomorphism Sets (rig_setoid (Zp ZComm p)) DigitSeq := {|
  to   := zp_to_digits;
  from := digits_to_zp_mor
|}.
Next Obligation. intros a i; exact (digits_round (`1 a) (`2 a) i). Qed.
Next Obligation. intro f; exact (zp_round f). Qed.

(* The two legs ARE named 态射, so two correspondence
 theorems below about bijection not about lookalike. （已译） *)
Example zp_digits_iso_to_leg : to Zp_digits_iso = zp_to_digits := eq_refl.

Example zp_digits_iso_from_leg :
  from Zp_digits_iso = digits_to_zp_mor := eq_refl.

Example zp_digits_iso_to (f : Zpc) (i : nat) :
  `1 (zp_to_digits f) i = zpd f i := eq_refl.

Example zp_digits_iso_from (a : DigitCarrier) :
  digits_to_zp_mor a = digits_to_zp (`1 a) := eq_refl.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint ncarry (c : nat -> Z) (n : nat) : Z :=
  match n with
  | O   => 0%Z
  | S k => ((c k + ncarry c k) / p)%Z
  end.

Definition dnorm (c : nat -> Z) (i : nat) : Z := ((c i + ncarry c i) mod p)%Z.

Lemma dnorm_bound (c : nat -> Z) (i : nat) : (0 <= dnorm c i < p)%Z.
Proof using Hp p. apply Z.mod_pos_bound; lia. Qed.

(* 相关说明。 （已译） *)
Lemma dnorm_dsum (c : nat -> Z) (n : nat) :
  (dsum (dnorm c) n + ncarry c n * P n)%Z = dsum c n.
Proof using Hp p.
  induction n as [|k IH]; cbn [dsum ncarry].
  - rewrite dpow_O; ring.
  - pose proof (Z.div_mod (c k + ncarry c k) p ltac:(lia)) as Hd.
    assert (Hn : dnorm c k = ((c k + ncarry c k) mod p)%Z) by reflexivity.
    rewrite Hn, dpow_S, <- IH.
    replace ((c k + ncarry c k) mod p)%Z
       with (c k + ncarry c k - p * ((c k + ncarry c k) / p))%Z by lia.
    ring.
Qed.

Definition dadd (a b : nat -> Z) : nat -> Z :=
  dnorm (fun i => (a i + b i)%Z).

Lemma dsum_add (a b : nat -> Z) (n : nat) :
  dsum (fun i => (a i + b i)%Z) n = (dsum a n + dsum b n)%Z.
Proof using p.
  induction n as [|k IH]; cbn [dsum]; [ring | rewrite IH; ring].
Qed.

(* 相关说明。 （已译） *)
Lemma dadd_correct (a b : nat -> Z) (n : nat) :
  @equiv _ (rig_setoid (ResRing ZComm p n))
    (dsum (dadd a b) n) (dsum a n + dsum b n)%Z.
Proof using Hp p.
  apply res_of_dvd with (k := (- ncarry (fun i => (a i + b i)%Z) n)%Z).
  pose proof (dnorm_dsum (fun i => (a i + b i)%Z) n) as H.
  rewrite dsum_add in H.
  unfold dadd; rewrite Z.mul_opp_r; lia.
Qed.

Definition dadd_seq (a b : DigitCarrier) : DigitCarrier.
Proof using Hp p.
  exists (dadd (`1 a) (`1 b)).
  intro i; exact (dnorm_bound (fun j => (`1 a j + `1 b j)%Z) i).
Defined.

Theorem Zp_digits_add (a b : DigitCarrier) :
  @equiv _ (rig_setoid (Zp ZComm p))
    (digits_to_zp_mor (dadd_seq a b))
    (rig_add (Zp ZComm p) (digits_to_zp_mor a) (digits_to_zp_mor b)).
Proof using Hp p. intro n; exact (dadd_correct (`1 a) (`1 b) n). Qed.

(* 相关说明。 （已译） *)
Example dadd_digit (a b : DigitCarrier) (i : nat) :
  `1 (dadd_seq a b) i
    = ((`1 a i + `1 b i + ncarry (fun j => (`1 a j + `1 b j)%Z) i) mod p)%Z
  := eq_refl.

Example ncarry_O (c : nat -> Z) : ncarry c 0%nat = 0%Z := eq_refl.

Example ncarry_S (c : nat -> Z) (n : nat) :
  ncarry c (S n) = ((c n + ncarry c n) / p)%Z := eq_refl.


(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint mraw (a b : nat -> Z) (n : nat) : Z :=
  match n with
  | O   => (a 0%nat * b 0%nat)%Z
  | S k => (a 0%nat * b (S k) + mraw (fun i => a (S i)) b k)%Z
  end.

(* 相关说明。 （已译） *)
Example mraw_0 (a b : nat -> Z) : mraw a b 0%nat = (a 0%nat * b 0%nat)%Z
  := eq_refl.

Example mraw_1 (a b : nat -> Z) :
  mraw a b 1%nat = (a 0%nat * b 1%nat + (a 1%nat * b 0%nat))%Z := eq_refl.

Example mraw_2 (a b : nat -> Z) :
  mraw a b 2%nat
    = (a 0%nat * b 2%nat + (a 1%nat * b 1%nat + a 2%nat * b 0%nat))%Z
  := eq_refl.

Lemma dsum_scal (c : Z) (a : nat -> Z) (n : nat) :
  dsum (fun i => (c * a i)%Z) n = (c * dsum a n)%Z.
Proof using p.
  induction n as [|k IH]; cbn [dsum]; [ring | rewrite IH; ring].
Qed.

(* Peeling units digit: 这是 what turns convolution's
 reindexing induction shifted sequence carries. （已译） *)
Lemma dsum_shift (a : nat -> Z) (n : nat) :
  dsum a (S n) = (a 0%nat + p * dsum (fun i => a (S i)) n)%Z.
Proof using p.
  induction n as [|k IH]; cbn [dsum].
  - rewrite dpow_O; ring.
  - cbn [dsum] in IH; rewrite IH, dpow_S; ring.
Qed.

(* 相关说明。 （已译） *)
Lemma mraw_correct (n : nat) : ∀ a b : nat -> Z,
  { k : Z & (dsum a n * dsum b n - dsum (mraw a b) n)%Z = (P n * k)%Z }.
Proof using Hp p.
  induction n as [|m IH]; intros a b.
  - exists 0%Z; cbn [dsum]; rewrite dpow_O; ring.
  - destruct (IH (fun i => a (S i)) b) as [k1 Hk1].
    exists (k1 + dsum (fun i => a (S i)) m * b m)%Z.
    pose proof (dsum_shift a m) as HA.
    pose proof (dsum_shift b m) as HB.
    pose proof (dsum_shift (mraw a b) m) as HM.
    assert (HS : dsum (fun i => mraw a b (S i)) m
                   = (a 0%nat * dsum (fun i => b (S i)) m
                      + dsum (mraw (fun i => a (S i)) b) m)%Z).
    { transitivity (dsum (fun i => (a 0%nat * b (S i)
                          + mraw (fun j => a (S j)) b i)%Z) m);
        [reflexivity|].
      rewrite (dsum_add (fun i => (a 0%nat * b (S i))%Z)
                        (fun i => mraw (fun j => a (S j)) b i) m).
      rewrite (dsum_scal (a 0%nat) (fun i => b (S i)) m); reflexivity. }
    rewrite HS in HM.
    assert (Hbm : dsum b m
                    = (b 0%nat + p * dsum (fun i => b (S i)) m
                       - b m * P m)%Z).
    { cbn [dsum] in HB; lia. }
    assert (HM2 : dsum (mraw (fun i => a (S i)) b) m
                    = (dsum (fun i => a (S i)) m * dsum b m - P m * k1)%Z)
      by lia.
    rewrite HA, HB, HM, dpow_S, HM2, Hbm.
    cbn [mraw]; ring.
Qed.

Definition dmul (a b : nat -> Z) : nat -> Z := dnorm (mraw a b).

Lemma dmul_correct (a b : nat -> Z) (n : nat) :
  @equiv _ (rig_setoid (ResRing ZComm p n))
    (dsum (dmul a b) n) (dsum a n * dsum b n)%Z.
Proof using Hp p.
  destruct (mraw_correct n a b) as [k Hk].
  apply res_of_dvd with (k := (- ncarry (mraw a b) n - k)%Z).
  pose proof (dnorm_dsum (mraw a b) n) as H.
  unfold dmul.
  rewrite Z.mul_sub_distr_l, Z.mul_opp_r; lia.
Qed.

Definition dmul_seq (a b : DigitCarrier) : DigitCarrier.
Proof using Hp p.
  exists (dmul (`1 a) (`1 b)).
  intro i; exact (dnorm_bound (mraw (`1 a) (`1 b)) i).
Defined.

Theorem Zp_digits_mul (a b : DigitCarrier) :
  @equiv _ (rig_setoid (Zp ZComm p))
    (digits_to_zp_mor (dmul_seq a b))
    (rig_mul (Zp ZComm p) (digits_to_zp_mor a) (digits_to_zp_mor b)).
Proof using Hp p. intro n; exact (dmul_correct (`1 a) (`1 b) n). Qed.

(* 相关说明。 （已译） *)
Example dmul_digit (a b : DigitCarrier) (i : nat) :
  `1 (dmul_seq a b) i
    = ((mraw (`1 a) (`1 b) i + ncarry (mraw (`1 a) (`1 b)) i) mod p)%Z
  := eq_refl.


(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma zp_const_compat (x : Z) (n : nat) : (x + - x)%Z = (P n * 0)%Z.
Proof using p. ring. Qed.

(*
   本节说明 Zp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition zp_const (x : Z) : Zpc.
Proof.
  exists (fun _ : nat => x).
  intro n; exact (res_of_dvd n x x 0%Z (zp_const_compat x n)).
Defined.

Lemma neg_one_mod (m : Z) (Hm : (0 < m)%Z) : ((-1) mod m)%Z = (m - 1)%Z.
Proof using Type.
  replace (-1)%Z with (m - 1 + (-1) * m)%Z by ring.
  rewrite Z_mod_plus_full; apply Z.mod_small; lia.
Qed.

Lemma zpd_neg_one (i : nat) : zpd (zp_const (-1)%Z) i = (p - 1)%Z.
Proof using Hp p.
  unfold zpd, zp_const; cbn [projT1].
  pose proof (dpow_pos i) as Hi.
  rewrite (neg_one_mod _ (dpow_pos (S i))), dpow_S.
  replace (p * P i - 1)%Z with ((p - 1) * P i + (P i - 1))%Z by ring.
  rewrite Z.div_add_l by exact (dpow_nz i).
  rewrite (Z.div_small (P i - 1) (P i)) by lia; lia.
Qed.

(* 相关说明。 （已译） *)
Lemma zp_const_neg_one_is_neg_one :
  @equiv _ (rig_setoid (Zp ZComm p))
    (zp_const (-1)%Z) (ring_neg (Zp ZComm p) (rig_one (Zp ZComm p))).
Proof using p.
  intro n; apply res_of_dvd with (k := 0%Z).
  assert (H1 : `1 (zp_const (-1)%Z) n = (-1)%Z) by reflexivity.
  assert (H2 : `1 (ring_neg (Zp ZComm p) (rig_one (Zp ZComm p))) n
                 = (-1)%Z) by reflexivity.
  rewrite H1, H2; ring.
Qed.
End Digits.

(* 相关说明。 （已译） *)

Definition d7 : nat -> Z := fun i => match i with O => 7%Z | _ => 0%Z end.
Definition d5 : nat -> Z := fun i => match i with O => 5%Z | _ => 0%Z end.

(* 相关说明。 （已译） *)
Example base_ten_add_units : dadd 10%Z d7 d5 0%nat = 2%Z := eq_refl.
Example base_ten_add_tens  : dadd 10%Z d7 d5 1%nat = 1%Z := eq_refl.
Example base_ten_add_hundreds : dadd 10%Z d7 d5 2%nat = 0%Z := eq_refl.

(* 7 * 5 = 35: units digit 5, tens digit 3. *)
Example base_ten_mul_units : dmul 10%Z d7 d5 0%nat = 5%Z := eq_refl.
Example base_ten_mul_tens  : dmul 10%Z d7 d5 1%nat = 3%Z := eq_refl.

(* 相关说明。 （已译） *)
Example base_ten_carry_one :
  ncarry 10%Z (fun i => (d7 i + d5 i)%Z) 1%nat = 1%Z := eq_refl.

(* …9999 = −1 in base ten, at the first three places. *)
Example base_ten_neg_one_0 : zpd 10%Z (zp_const 10%Z (-1)%Z) 0%nat = 9%Z
  := eq_refl.
Example base_ten_neg_one_1 : zpd 10%Z (zp_const 10%Z (-1)%Z) 1%nat = 9%Z
  := eq_refl.
Example base_ten_neg_one_2 : zpd 10%Z (zp_const 10%Z (-1)%Z) 2%nat = 9%Z
  := eq_refl.
