Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   本文件给出闭结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint fin_tabulate {m n : nat} {struct m} :
  (Fin.t m → Fin.t n) → Fin.t (n ^ m) :=
  match m return (Fin.t m → Fin.t n) → Fin.t (n ^ m) with
  | O => fun _ => Fin.F1
  | S m' => fun f =>
      fin_pair (f Fin.F1) (fin_tabulate (fun i => f (Fin.FS i)))
  end.

(** [fin_apply c] decodes code [c] back function, structural
 recursion arity [m]: [fin_unpair] splits off head digit,
 [Fin.caseS'] dispatches 论元. （已译） *)
Fixpoint fin_apply {m n : nat} {struct m} :
  Fin.t (n ^ m) → Fin.t m → Fin.t n :=
  match m return Fin.t (n ^ m) → Fin.t m → Fin.t n with
  | O => fun _ i => Fin.case0 (fun _ => Fin.t n) i
  | S m' => fun c i =>
      Fin.caseS' i (fun _ => Fin.t n)
        (fst (fin_unpair c))
        (fun i' => fin_apply (snd (fin_unpair c)) i')
  end.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example fin_tabulate_computes :
  @fin_tabulate 2 3
    (fun i => Fin.caseS' i (fun _ => Fin.t 3)
                (Fin.FS (Fin.FS Fin.F1)) (fun _ => Fin.FS Fin.F1))
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
    := eq_refl.

Example fin_apply_computes :
  @fin_apply 2 3
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
    (Fin.FS Fin.F1)
    = Fin.FS Fin.F1 := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fin_apply_tabulate {m n : nat} (f : Fin.t m → Fin.t n) (i : Fin.t m) :
  fin_apply (fin_tabulate f) i = f i.
Proof.
  revert f; induction i as [m' | m' i IH]; intros f; simpl.
  - (* 相关说明。 （已译） *)
    rewrite fin_unpair_pair; reflexivity.
  - (* 相关说明。 （已译） *)
    rewrite fin_unpair_pair; simpl.
    apply (IH (fun j => f (Fin.FS j))).
Qed.

Lemma fin_tabulate_apply {m n : nat} (c : Fin.t (n ^ m)) :
  fin_tabulate (fin_apply c) = c.
Proof.
  induction m as [| m' IH]; simpl.
  - (* n ^ 0 = 1: every code is F1. *)
    symmetry; apply fin1_unique.
  - (*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    transitivity (fin_pair (fst (fin_unpair c)) (snd (fin_unpair c))).
    + f_equal.
      exact (IH (snd (fin_unpair c))).
    + apply fin_pair_unpair.
Qed.

(** Tabulation inspects 论元 pointwise, so it respects the
 pointwise hom-等价 [FinSet] — funext-free congruence
 used rewrite under [fin_tabulate] binder. （已译） *)
Lemma fin_tabulate_ext {m n : nat} (f g : Fin.t m → Fin.t n) :
  (∀ i, f i = g i) → fin_tabulate f = fin_tabulate g.
Proof.
  intros Hfg; induction m as [| m' IH]; simpl.
  - reflexivity.
  - rewrite (Hfg Fin.F1).
    rewrite (IH (fun i => f (Fin.FS i)) (fun i => g (Fin.FS i))
               (fun i => Hfg (Fin.FS i))).
    reflexivity.
Qed.

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

#[export] Program Instance FinSet_Closed : @Closed FinSet FinSet_Cartesian := {
  exponent_obj := fun m n => (n ^ m)%nat;

  exp_iso := fun x y z =>
    {| to   := {| morphism := fun (f : Fin.t (x * y) → Fin.t z)
                                  (i : Fin.t x) =>
                    fin_tabulate (fun j : Fin.t y => f (fin_pair i j)) |}
     ; from := {| morphism := fun (g : Fin.t x → Fin.t (z ^ y)%nat)
                                  (p : Fin.t (x * y)) =>
                    fin_apply (g (fst (fin_unpair p))) (snd (fin_unpair p)) |}
    |}
}.
Next Obligation.
  (* Currying respects pointwise equality, via [fin_tabulate_ext]. *)
  intros x y z f f' Hf i; simpl in Hf.
  apply fin_tabulate_ext; intro j; apply Hf.
Qed.
Next Obligation.
  (* Uncurrying respects pointwise equality. *)
  intros x y z g g' Hg p; simpl in Hg.
  rewrite (Hg (fst (fin_unpair p))); reflexivity.
Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros x y z g i; simpl.
  transitivity (fin_tabulate (fin_apply (g i))).
  - apply fin_tabulate_ext; intro j.
    rewrite fin_unpair_pair; reflexivity.
  - apply fin_tabulate_apply.
Qed.
Next Obligation.
  (* uncurry ∘ curry ≈ id: applying tabulation original function,
 then product round trip reassembles 论元. （已译） *)
  intros x y z f p; simpl.
  rewrite fin_apply_tabulate, fin_pair_unpair; reflexivity.
Qed.
Next Obligation.
  (* The beta law: eval ∘ first (curry f) ≈ f, pointwise. *)
  intros x y z f; unfold first; intro p; simpl.
  rewrite fin_unpair_pair; simpl.
  rewrite fin_apply_tabulate, fin_pair_unpair; reflexivity.
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example eval_computes :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat 2%nat
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) (Fin.F1 : Fin.t 2))
    = Fin.FS Fin.F1 := eq_refl.

Example eval_computes_snd :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat 2%nat
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) (Fin.FS Fin.F1 : Fin.t 2))
    = Fin.F1 := eq_refl.
