(*
   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Classifier.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * The equalizer: the counted sub-object of agreement *)

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_eq_pred {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t m → bool := fun x => fin_eqb (f x) (g x).

(* The equalizer object counts the agreements; the inclusion un-ranks. *)
Definition FinSet_equalizer_obj {m n : nat} (f g : Fin.t m → Fin.t n) : nat :=
  fin_countP (finset_eq_pred f g).

Definition FinSet_equalizer_incl {m n : nat} (f g : Fin.t m → Fin.t n) :
  Fin.t (FinSet_equalizer_obj f g) → Fin.t m :=
  fin_select (finset_eq_pred f g).

Lemma finset_eq_pred_true {m n : nat} (f g : Fin.t m → Fin.t n) (x : Fin.t m) :
  f x = g x → finset_eq_pred f g x = true.
Proof. intros H; unfold finset_eq_pred; rewrite H; apply fin_eqb_refl. Qed.

(* The mediator of a fork [h] ranks each value of [h], which the fork
   equation certifies to satisfy the predicate. *)
Definition FinSet_equalizer_med {m n : nat} (f g : Fin.t m → Fin.t n)
  {z : nat} (h : Fin.t z → Fin.t m) (Hh : ∀ i, f (h i) = g (h i)) :
  Fin.t z → Fin.t (FinSet_equalizer_obj f g) :=
  fun i => fin_rank (finset_eq_pred f g) (h i)
                    (finset_eq_pred_true f g (h i) (Hh i)).

Definition FinSet_IsEqualizer {m n : nat} (f g : Fin.t m → Fin.t n) :
  @IsEqualizer FinSet m n f g (FinSet_equalizer_obj f g)
    (FinSet_equalizer_incl f g).
Proof.
  unshelve refine {| fork_eq := _; eq_desc := fun z h Hh => _ |}.
  - intro i; simpl.
    apply fin_eqb_eq. exact (fin_select_sat (finset_eq_pred f g) i).
  - unshelve refine {| unique_obj := FinSet_equalizer_med f g h Hh |}.
    + intro i; simpl. exact (fin_select_rank (finset_eq_pred f g) (h i) _).
    + intros v Hv i; simpl in *.
      unfold FinSet_equalizer_med.
      apply (fin_select_inj (finset_eq_pred f g)).
      rewrite (fin_select_rank (finset_eq_pred f g) (h i)). symmetry. apply Hv.
Defined.

#[export] Instance FinSet_HasEqualizers : HasEqualizers FinSet :=
  @Build_HasEqualizers FinSet
    (fun (m n : nat) (f g : Fin.t m → Fin.t n) =>
       (FinSet_equalizer_obj f g;
        (FinSet_equalizer_incl f g; FinSet_IsEqualizer f g))).

(** * Finite completeness, by Mac Lane V.2 Corollary 1 *)

Definition FinSet_FinitelyComplete : @FinitelyComplete FinSet :=
  finitely_complete_from_generators FinSet_Terminal FinSet_Cartesian
    FinSet_HasEqualizers.

(** * Computation *)

(* A parallel pair [3 ⇉ 2] agreeing exactly at the first and third points. *)
Definition finset_eq_example_f : Fin.t 3 → Fin.t 2 := fun _ => Fin.F1.
Definition finset_eq_example_g : Fin.t 3 → Fin.t 2 :=
  fun i => match i with Fin.FS Fin.F1 => Fin.FS Fin.F1 | _ => Fin.F1 end.

Example FinSet_equalizer_obj_computes :
  FinSet_equalizer_obj finset_eq_example_f finset_eq_example_g = 2%nat
  := eq_refl.

Example FinSet_equalizer_incl_computes_0 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g Fin.F1 = Fin.F1
  := eq_refl.

Example FinSet_equalizer_incl_computes_1 :
  FinSet_equalizer_incl finset_eq_example_f finset_eq_example_g (Fin.FS Fin.F1)
  = Fin.FS (Fin.FS Fin.F1)
  := eq_refl.

Example FinSet_equalizer_readback :
  `1 (@equalizer FinSet _ _ _ finset_eq_example_f finset_eq_example_g) = 2%nat
  := eq_refl.

Definition finset_eq_example_h : Fin.t 1 → Fin.t 3 :=
  fun _ => Fin.FS (Fin.FS Fin.F1).

Example FinSet_equalizer_med_computes :
  FinSet_equalizer_med finset_eq_example_f finset_eq_example_g
    finset_eq_example_h (fun _ => eq_refl) Fin.F1
  = Fin.FS Fin.F1
  := eq_refl.

(* The terminal object recovered from the EMPTY finite limit is the numeral
   [1] by conversion on this route. *)
Example FinSet_FinitelyComplete_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat
  := eq_refl.

(*
   本节说明（余）极限、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finset_eq_example_diagram : Parallel ⟶ FinSet :=
  @APair FinSet 3%nat 2%nat finset_eq_example_f finset_eq_example_g.

Example FinSet_FinitelyComplete_parallel_computes :
  vertex_obj[@limit_cone Parallel FinSet finset_eq_example_diagram
    (FinSet_FinitelyComplete Parallel Parallel_FiniteCategory
       finset_eq_example_diagram)]
  = 2%nat
  := eq_refl.
