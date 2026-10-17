Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   本文件给出积相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：[fin_pair b] encodes pair (a, b) position a·n + b the
 canonical (m * n)-element set, structural recursion [a]. （已译） *)
Fixpoint fin_pair {m n : nat} (a : Fin.t m) : Fin.t n → Fin.t (m * n) :=
  match a in Fin.t m return Fin.t n → Fin.t (m * n) with
  | @Fin.F1 m' => fun b => Fin.L (m' * n) b
  | @Fin.FS m' a' => fun b => Fin.R n (fin_pair a' b)
  end.

(** [fin_unpair] decodes a position of the canonical (m * n)-element set
    into its quotient/remainder pair, by structural recursion on [m]:
    each step peels one n-element block off through [fin_split]. *)
Fixpoint fin_unpair {m n : nat} {struct m} :
  Fin.t (m * n) → (Fin.t m * Fin.t n)%type :=
  match m return Fin.t (m * n) → (Fin.t m * Fin.t n)%type with
  | O => fun p => Fin.case0 (fun _ => (Fin.t 0 * Fin.t n)%type) p
  | S m' => fun p =>
      match @fin_split n (m' * n) p with
      | Datatypes.inl b => (Fin.F1, b)
      | Datatypes.inr q =>
          let '(a, b) := @fin_unpair m' n q in (Fin.FS a, b)
      end
  end.

(* 相关说明。 （已译） *)
Example fin_pair_computes :
  @fin_pair 2 3 (Fin.FS Fin.F1) (Fin.FS Fin.F1)
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

Example fin_unpair_computes :
  @fin_unpair 2 3 (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = (Fin.FS Fin.F1, Fin.FS Fin.F1) := eq_refl.

(* * ** The round trips

 Equality here Leibniz equality [Fin.t] VALUES — 对象-level
 data skeletal 范畴, matching pointwise-[eq] hom-setoid
 [FinSet]. （已译） *)

Lemma fin_unpair_pair {m n : nat} (a : Fin.t m) (b : Fin.t n) :
  fin_unpair (fin_pair a b) = (a, b).
Proof.
  induction a as [m' | m' a IH]; simpl.
  - (* (F1, b) is the first block: split lands left. *)
    rewrite fin_split_L; reflexivity.
  - (* (FS a, b) skips one block: split lands right, then recurse. *)
    rewrite fin_split_R, IH; reflexivity.
Qed.

Lemma fin_pair_unpair {m n : nat} (p : Fin.t (m * n)) :
  fin_pair (fst (fin_unpair p)) (snd (fin_unpair p)) = p.
Proof.
  induction m as [| m' IH].
  - exact (Fin.case0
             (fun p : Fin.t 0 =>
                @fin_pair 0 n (fst (@fin_unpair 0 n p))
                              (snd (@fin_unpair 0 n p)) = p)
             p).
  - (* 相关说明。 （已译） *)
    simpl; destruct (@fin_split n (m' * n) p) as [b | q] eqn:Hs.
    + (* 相关说明。 （已译） *)
      simpl; rewrite <- (@fin_join_split n (m' * n) p), Hs; reflexivity.
    + (* 相关说明。 （已译） *)
      specialize (IH q).
      destruct (@fin_unpair m' n q) as [a b]; simpl in IH.
      simpl; rewrite IH, <- (@fin_join_split n (m' * n) p), Hs.
      reflexivity.
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance FinSet_Cartesian : @Cartesian FinSet := {|
  product_obj := fun m n => (m * n)%nat;
  fork := fun x y z (f : Fin.t x → Fin.t y) (g : Fin.t x → Fin.t z) i =>
    fin_pair (f i) (g i);
  exl := fun y z (p : Fin.t (y * z)) => fst (fin_unpair p);
  exr := fun y z (p : Fin.t (y * z)) => snd (fin_unpair p)
|}.
Next Obligation.
  (* The pairing respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i.
  rewrite (Hf i), (Hg i); reflexivity.
Qed.
Next Obligation.
  (* The 普遍性质: h ≈ ⟨f, g⟩ exactly two decodings of
 h recover f g — pointwise, round trips. （已译） *)
  split.
  - intros Hh; split; intro i; simpl;
      rewrite (Hh i), fin_unpair_pair; reflexivity.
  - intros [Hl Hr] i.
    rewrite <- (Hl i), <- (Hr i), fin_pair_unpair; reflexivity.
Qed.

(* Closed pairings evaluated at concrete elements, by [eq_refl]: the fork
   of the two projections out of Fin.t 6 = Fin.t (2 * 3) re-encodes each
   element to itself, checked here at position 4 = (1, 1).（标题）（已译） *)
Example fork_computes :
  @fork FinSet FinSet_Cartesian 6%nat 2%nat 3%nat
    (fun p : Fin.t 6 => fst (@fin_unpair 2 3 p))
    (fun p : Fin.t 6 => snd (@fin_unpair 2 3 p))
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))) := eq_refl.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma FinSet_prod_one_l (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    (@terminal_obj FinSet FinSet_Terminal) n = n.
Proof. apply Nat.mul_1_l. Qed.

Lemma FinSet_prod_one_r (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    n (@terminal_obj FinSet FinSet_Terminal) = n.
Proof. apply Nat.mul_1_r. Qed.
