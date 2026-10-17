Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * * FinSet, skeletal 范畴 finite sets （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/FinSet

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/FinSet
   nLab: https://ncatlab.org/nlab/show/Lawvere+theory

   本节说明函子、Lawvere 理论、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition FinSet : Category := {|
  obj := nat;
  hom := fun m n => Fin.t m → Fin.t n;
  homset := fun m n => fun_setoid (Fin.t m) (Fin.t n);
  id := fun _ i => i;
  compose := fun _ _ _ f g i => f (g i)
|}.
Next Obligation.
  (* compose respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i.
  rewrite (Hg i); apply Hf.
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Instance FinSet_HomEqProp : HomEqProp FinSet :=
  Build_HomEqProp FinSet
    (fun m n (f g : Fin.t m → Fin.t n) => ∀ i, f i = g i)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

#[export] Instance FinSet_ObjDecEq : ObjDecEq FinSet := Nat.eq_dec.

(*
   本节说明 FinSet 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint fin_split {m n : nat} {struct m} :
  Fin.t (m + n) -> (Fin.t m + Fin.t n)%type :=
  match m return Fin.t (m + n) -> (Fin.t m + Fin.t n)%type with
  | O => fun p => Datatypes.inr p
  | S m' => fun p =>
      Fin.caseS' p (fun _ => (Fin.t (S m') + Fin.t n)%type)
        (Datatypes.inl Fin.F1)
        (fun q =>
           match @fin_split m' n q with
           | Datatypes.inl a => Datatypes.inl (Fin.FS a)
           | Datatypes.inr b => Datatypes.inr b
           end)
  end.

Definition fin_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  Fin.t (m + n) :=
  match s with
  | Datatypes.inl a => Fin.L n a
  | Datatypes.inr b => Fin.R m b
  end.

Lemma fin_split_L {m n : nat} (a : Fin.t m) :
  fin_split (Fin.L n a) = Datatypes.inl a.
Proof.
  induction a as [m | m a IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_split_R {m n : nat} (b : Fin.t n) :
  fin_split (Fin.R m b) = Datatypes.inr b.
Proof.
  (* 相关说明。 （已译） *)
  induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_join_split {m n : nat} (p : Fin.t (m + n)) :
  fin_join (fin_split p) = p.
Proof.
  revert p; induction m as [| m IH]; intro p.
  - reflexivity.
  - apply (Fin.caseS' p
             (fun p : Fin.t (S m + n) =>
                fin_join (@fin_split (S m) n p) = p)).
    + reflexivity.
    + intro q; specialize (IH q); simpl; revert IH.
      destruct (fin_split q) as [a|b]; simpl; intro IH;
        rewrite IH; reflexivity.
Qed.

Lemma fin_split_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  fin_split (fin_join s) = s.
Proof. destruct s; [apply fin_split_L | apply fin_split_R]. Qed.

(* 相关说明。 （已译） *)
Example fin_split_computes :
  @fin_split 2 2 (Fin.FS (Fin.FS Fin.F1)) = Datatypes.inr Fin.F1 := eq_refl.

(** ** Initial and terminal objects *)

(* 相关说明。 （已译） *)
#[export] Instance FinSet_Initial : Initial FinSet :=
  @Build_Terminal (FinSet^op) 0%nat
    (fun x (v : Fin.t 0) => Fin.case0 (fun _ => Fin.t x) v)
    (fun x f g i => Fin.case0 (fun j => f j = g j) i).

(* The one-element set is a singleton: every inhabitant is [Fin.F1]. *)
Lemma fin1_unique (j : Fin.t 1) : j = Fin.F1.
Proof.
  apply (Fin.caseS' j (fun j => j = Fin.F1)).
  - reflexivity.
  - intro j'; exact (Fin.case0 (fun j' => Fin.FS j' = Fin.F1) j').
Qed.

#[export] Instance FinSet_Terminal : @Terminal FinSet :=
  @Build_Terminal FinSet 1%nat
    (fun x (_ : Fin.t x) => Fin.F1)
    (fun x f g i =>
       eq_trans (fin1_unique (f i)) (eq_sym (fin1_unique (g i)))).

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance FinSet_Cocartesian : @Cocartesian FinSet := {|
  product_obj := fun m n => (m + n)%nat;
  fork := fun x y z (f : Fin.t y → Fin.t x) (g : Fin.t z → Fin.t x) p =>
    match fin_split p with
    | Datatypes.inl a => f a
    | Datatypes.inr b => g b
    end;
  exl := fun x y => Fin.L y;
  exr := fun x y => Fin.R x
|}.
Next Obligation.
  (* The copairing respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg p.
  destruct (fin_split p); [apply Hf | apply Hg].
Qed.
Next Obligation.
  (* The 普遍性质: h ≈ f ▽ g exactly h recovers f along
 Fin.L g along Fin.R. （已译） *)
  split.
  - intros Hh; split; intro q; simpl.
    + rewrite (Hh (Fin.L _ q)), fin_split_L; reflexivity.
    + rewrite (Hh (Fin.R _ q)), fin_split_R; reflexivity.
  - intros [Hl Hr] p.
    destruct (fin_split p) as [a|b] eqn:Hs.
    + assert (Hp : p = Fin.L z a)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hl.
    + assert (Hp : p = Fin.R y b)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hr.
Qed.

(*
   本节说明 FinSet 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example merge_computes :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

Example merge_computes_inl :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    Fin.F1 = Fin.FS Fin.F1 := eq_refl.
