Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.

From Coq Require Import Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/categorification
 nLab: https://ncatlab.org/nlab/show/FinSet

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The cardinality 函子 groupoid finite sets （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Card_Groupoid : Groupoid Set_f ⟶ DiscreteCat nat := {|
  fobj := setf_cardinality;
  fmap := fun A B i => setf_cardinality_iso_invariant A B i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(** ** The skeletal companion *)

(* On skeleton 对象 action 恒等: [FinSet]'s 对象 are
 already naturals, whole 函子 [FinSet_skeletal] read an
 arrow action. （已译） *)
Program Definition Card_FinSet : Groupoid FinSet ⟶ DiscreteCat nat := {|
  fobj := fun n => n;
  fmap := fun m n i => @FinSet_skeletal m n i
|}.
Solve All Obligations with
  (try proper; apply (UIP_dec PeanoNat.Nat.eq_dec)).

(* The 对象 action 恒等 nose. （已译） *)
Example Card_FinSet_identity_on_objects (n : FinSet) :
  fobj[Card_FinSet] n = n := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition nat_exp_prod_l (x y z : nat) : (z ^ (x * y))%nat = ((z ^ y) ^ x)%nat :=
  FinSet_skeletal (@exp_prod_l FinSet _ _ x y z).

Definition nat_exp_prod_r (x y z : nat) :
  ((y * z) ^ x)%nat = (y ^ x * z ^ x)%nat :=
  FinSet_skeletal (@exp_prod_r FinSet _ _ x y z).

Definition nat_prod_coprod_r (x y z : nat) :
  (x * (y + z))%nat = (x * y + x * z)%nat :=
  FinSet_skeletal (@prod_coprod_r FinSet _ _ _ x y z).

Definition nat_exp_coprod (x y z : nat) :
  (x ^ (y + z))%nat = (x ^ y * x ^ z)%nat :=
  FinSet_skeletal (@exp_coprod FinSet _ _ _ x y z).

(* Each 恒等 IS 函子's action 同构; stated one
 four, since [fmap[Card_FinSet]] [FinSet_skeletal] by
 construction. （已译） *)
Example nat_exp_coprod_is_Card_image (x y z : nat) :
  nat_exp_coprod x y z = fmap[Card_FinSet] (@exp_coprod FinSet _ _ _ x y z)
  := eq_refl.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma DiscreteCat_nat_Thin : Thin (DiscreteCat nat).
Proof. intros x y f g; apply (UIP_dec PeanoNat.Nat.eq_dec). Qed.

Corollary Card_FinSet_squares_commute {m n : FinSet}
          (i j : m ~{Groupoid FinSet}~> n) :
  fmap[Card_FinSet] i ≈ fmap[Card_FinSet] j.
Proof. apply DiscreteCat_nat_Thin. Qed.

(* * ** Sanity: 函子 identities compute （已译） *)

(* [parity_two] (Instance/FinSet/Skeleton.v) is [nat] under equality of
   parity: an infinite carrier of cardinality 2. *)
Example card_groupoid_parity_two :
  fobj[Card_Groupoid] parity_two = 2%nat := eq_refl.

Example card_groupoid_incl_three :
  fobj[Card_Groupoid] (FinSet_Incl 3%nat) = 3%nat := eq_refl.

Example card_finset_five : fobj[Card_FinSet] 5%nat = 5%nat := eq_refl.

Example nat_exp_coprod_2_1_1 : (2 ^ (1 + 1))%nat = (2 ^ 1 * 2 ^ 1)%nat :=
  nat_exp_coprod 2%nat 1%nat 1%nat.

Example nat_exp_prod_l_2_3_2 : (2 ^ (3 * 2))%nat = ((2 ^ 2) ^ 3)%nat :=
  nat_exp_prod_l 3%nat 2%nat 2%nat.

Example nat_prod_coprod_r_4_2_3 : (4 * (2 + 3))%nat = (4 * 2 + 4 * 3)%nat :=
  nat_prod_coprod_r 4%nat 2%nat 3%nat.

Example nat_exp_prod_r_2_3_4 : ((3 * 4) ^ 2)%nat = (3 ^ 2 * 4 ^ 2)%nat :=
  nat_exp_prod_r 2%nat 3%nat 4%nat.
