Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   本文件给出打包形式的等价。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CategoryEquivalence (C D : Category) : Type :=
  ∃ F : C ⟶ D, EquivalenceOfCategories F.

Notation "C ≃ D" := (CategoryEquivalence C%category D%category)
  (at level 91) : category_theory_scope.

(* Covariant accessors: underlying 函子, 等价 structure,
 chosen quasi-inverse. （已译） *)

Definition equivalence_functor {C D : Category} (E : C ≃ D) : C ⟶ D :=
  `1 E.

Definition equivalence_witness {C D : Category} (E : C ≃ D) :
  EquivalenceOfCategories (`1 E) :=
  `2 E.

Definition equivalence_quasi_inverse {C D : Category} (E : C ≃ D) :
  D ⟶ C :=
  @quasi_inverse C D (`1 E) (`2 E).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.
Context (HF : @EquivalenceOfCategories C D F).
Context (HG : @EquivalenceOfCategories D E G).

Local Notation F' := (@quasi_inverse C D F HF).
Local Notation G' := (@quasi_inverse D E G HG).

Lemma EquivalenceOfCategories_Compose_counit :
  (G ◯ F) ◯ (F' ◯ G') ≈ Id[E].
Proof.
  rewrite <- (fun_equiv_comp_assoc G F (F' ◯ G')).
  rewrite (fun_equiv_comp_assoc F F' G').
  (* 相关说明。 （已译） *)
  rewrite (@equivalence_counit C D F HF).
  rewrite (fun_equiv_id_left G').
  exact (@equivalence_counit D E G HG).
Qed.

Lemma EquivalenceOfCategories_Compose_unit :
  Id[C] ≈ (F' ◯ G') ◯ (G ◯ F).
Proof.
  rewrite <- (fun_equiv_comp_assoc F' G' (G ◯ F)).
  rewrite (fun_equiv_comp_assoc G' G F).
  (* 相关说明。 （已译） *)
  rewrite <- (@equivalence_unit D E G HG).
  rewrite (fun_equiv_id_left F).
  exact (@equivalence_unit C D F HF).
Qed.

Definition EquivalenceOfCategories_Compose :
  EquivalenceOfCategories (G ◯ F) :=
  @Build_EquivalenceOfCategories C E (G ◯ F) (F' ◯ G')
    EquivalenceOfCategories_Compose_counit
    EquivalenceOfCategories_Compose_unit.

End Compose.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Equivalence_refl (C : Category) : C ≃ C :=
  (Id[C]; @EquivalenceOfCategories_Id C).

Definition Equivalence_sym {C D : Category} (E : C ≃ D) : D ≃ C :=
  (@quasi_inverse C D (`1 E) (`2 E);
   @EquivalenceOfCategories_sym C D (`1 E) (`2 E)).

Definition Equivalence_trans {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) : C ≃ E :=
  (`1 E2 ◯ `1 E1; EquivalenceOfCategories_Compose (`2 E1) (`2 E2)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary Equivalence_sym_involutive {C D : Category} (E : C ≃ D) :
  `1 (Equivalence_sym (Equivalence_sym E)) ≈ `1 E.
Proof. reflexivity. Qed.

Corollary Equivalence_trans_functor {C D E : Category}
  (E1 : C ≃ D) (E2 : D ≃ E) :
  `1 (Equivalence_trans E1 E2) ≈ `1 E2 ◯ `1 E1.
Proof. reflexivity. Qed.
