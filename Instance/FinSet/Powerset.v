Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * The contravariant power-set 函子 skeletal [FinSet], computably （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finpow (n : nat) : nat := Nat.pow 2 n.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finpow_mem {n : nat} (S : Fin.t (finpow n)) (i : Fin.t n) : bool :=
  fin_eqb (fin_apply S i) fin_true.

(* 相关说明。 （已译） *)
Definition finpow_map {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) : Fin.t (finpow n) :=
  fin_tabulate (fun i : Fin.t n => fin_apply S (f i)).

Lemma finpow_map_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  finpow_mem (finpow_map f S) i = finpow_mem S (f i).
Proof. unfold finpow_mem, finpow_map; now rewrite fin_apply_tabulate. Qed.

(*
   本节说明函子、hom、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma finpow_map_id {n : nat} (S : Fin.t (finpow n)) :
  finpow_map (fun i : Fin.t n => i) S = S.
Proof. unfold finpow_map; apply fin_tabulate_apply. Qed.

Lemma finpow_map_comp {m n p : nat}
  (f : Fin.t n → Fin.t m) (g : Fin.t p → Fin.t n) (S : Fin.t (finpow m)) :
  finpow_map (fun i => f (g i)) S = finpow_map g (finpow_map f S).
Proof.
  unfold finpow_map.
  apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma finpow_map_ext {m n : nat} (f g : Fin.t n → Fin.t m)
  (H : ∀ i, f i = g i) (S : Fin.t (finpow m)) :
  finpow_map f S = finpow_map g S.
Proof. unfold finpow_map; apply fin_tabulate_ext; intro i; now rewrite H. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The functor, twice *)

(* Inside [FinSet].  An arrow x ~> y of [FinSet^op] is an arrow y ~> x of
   [FinSet], so the action on it lands where it should. *)
Program Definition FinPowerset : FinSet^op ⟶ FinSet := {|
  fobj := finpow ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) => finpow_map f
|}.
Next Obligation. repeat intro; now apply finpow_map_ext. Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition FinPowerset_Sets : FinSet^op ⟶ Sets := {|
  fobj := fun n => Powerset_Prop_fin_object (finpow n) ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) =>
            {| morphism := finpow_map f |}
|}.
Next Obligation.
  (* [exact] rather than [apply]: the goal is a projection out of a record
     literal, which [apply]'s unifier declines to reduce here. *)
  repeat intro; exact (finpow_map_ext x0 y0 H x1).
Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(* 相关说明。 （已译） *)
Example finpowerset_sets_agrees {x y : FinSet} (f : x ~{FinSet^op}~> y)
  (S : Fin.t (finpow x)) :
  fmap[FinPowerset_Sets] f S = fmap[FinPowerset] f S := eq_refl.

Example finpowerset_obj (n : nat) : fobj[FinPowerset] n = Nat.pow 2 n := eq_refl.

Example finpowerset_two : fobj[FinPowerset] 2%nat = 4%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finpow_truth_point : Fin.t 2 := fin_true.

Definition finpow_truth_subset : Fin.t (finpow 2) :=
  fin_tabulate (fun i : Fin.t 2 => i).

(* It really is {⊤}: ⊤ is in it and ⊥ is not, by computation. *)
Example finpow_truth_has_true :
  finpow_mem finpow_truth_subset fin_true = true := eq_refl.

Example finpow_truth_lacks_false :
  finpow_mem finpow_truth_subset fin_false = false := eq_refl.

(* ... digit at j j itself, every j — general form the
 two computations above, what 普遍性质 所消耗. （已译） *)
Lemma finpow_truth_digit (j : Fin.t 2) : fin_apply finpow_truth_subset j = j.
Proof. unfold finpow_truth_subset; apply fin_apply_tabulate. Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma finpow_fmap_is_preimage {n : nat} (k : Fin.t n → Fin.t 2)
  (i : Fin.t n) :
  fin_apply (finpow_map k finpow_truth_subset) i = k i.
Proof.
  unfold finpow_map; rewrite fin_apply_tabulate; apply finpow_truth_digit.
Qed.

Lemma finpow_preimage_iff {n : nat} (k : Fin.t n → Fin.t 2) (i : Fin.t n) :
  finpow_mem (finpow_map k finpow_truth_subset) i = fin_eqb (k i) fin_true.
Proof. unfold finpow_mem; now rewrite finpow_fmap_is_preimage. Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma finpow_preimage_of_truth {n : nat} (k : Fin.t n → Fin.t 2) :
  finpow_map k finpow_truth_subset = fin_tabulate k.
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i; apply finpow_truth_digit.
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition FinPowerset_universal_element :
  @AUniversalElement (FinSet^op) FinPowerset_Sets 2%nat := {|
  aue_elem := finpow_truth_subset ;
  aue_universal := fun n S => {| unique_obj := fin_apply S |}
|}.
Next Obligation.
  rewrite finpow_preimage_of_truth; apply fin_tabulate_apply.
Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  apply finpow_fmap_is_preimage.
Qed.

(* 相关说明。 （已译） *)
Example finpow_aue_elem :
  @aue_elem (FinSet^op) FinPowerset_Sets 2%nat FinPowerset_universal_element
    = finpow_truth_subset := eq_refl.

Example finpow_aue_med (n : nat) (S : Fin.t (finpow n)) :
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element n S)
    = fin_apply S := eq_refl.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinPowerset_representation :
  @Curried_Hom (FinSet^op) 2%nat
    ≅[[(FinSet^op), Sets]] FinPowerset_Sets :=
  ue_representation FinPowerset_Sets 2%nat FinPowerset_universal_element.

Example finpow_representation_to_is_preimage (n : nat)
  (k : n ~{FinSet}~> 2%nat) :
  transform (to FinPowerset_representation) n k
    = finpow_map k finpow_truth_subset := eq_refl.

Definition FinPowerset_Representable : Representable FinPowerset_Sets :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement FinPowerset_universal_element).

Example finpow_repr_obj :
  @repr_obj (FinSet^op) FinPowerset_Sets FinPowerset_Representable = 2%nat
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Awodey's 自然性 clause at [FinSet_Classifier] （已译） *)

(* 相关说明。 （已译） *)
Definition FinSet_Sub_natural :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) (@Curried_CoHom FinSet 2%nat)
  := @Sub_classifier_natural FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Definition FinSet_Sub_Representable : Representable (@Sub FinSet FinSet_Pullbacks)
  := @Sub_Representable FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Example FinSet_Sub_repr_obj :
  @repr_obj (FinSet^op) (@Sub FinSet FinSet_Pullbacks) FinSet_Sub_Representable
    = 2%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** The subobject presheaf [FinSet] IS power-set 函子 （已译） *)

(* The codec, natural 同构 [Hom(─,2) ≅ FinPowerset_Sets]. Its
 自然性 one application [fin_apply_tabulate]; both round trips
 codec's own Leibniz equations. （已译） *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma codec_natural_to {m n : nat} (f : Fin.t n → Fin.t m)
  (k : Fin.t m → Fin.t 2) :
  finpow_map f (fin_tabulate k) = fin_tabulate (fun i => k (f i)).
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma codec_natural_from {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  fin_apply (finpow_map f S) i = fin_apply S (f i).
Proof. unfold finpow_map; now rewrite fin_apply_tabulate. Qed.

Local Ltac codec :=
  simpl; repeat intro;
  first [ exact (codec_natural_from _ _ _)
        | symmetry; exact (codec_natural_from _ _ _)
        | exact (codec_natural_to _ _)
        | symmetry; exact (codec_natural_to _ _)
        | apply fin_tabulate_apply
        | symmetry; apply fin_tabulate_apply
        | apply fin_apply_tabulate
        | symmetry; apply fin_apply_tabulate
        | apply fin_tabulate_ext; assumption
        | symmetry; apply fin_tabulate_ext; assumption
        | subst; reflexivity
        | reflexivity ].

Program Definition finpow_codec :
  @Isomorphism ([(FinSet^op), Sets])
    (@Curried_CoHom FinSet 2%nat) FinPowerset_Sets := {|
  to   := {| transform := fun n => {| morphism := fun k : Fin.t n -> Fin.t 2 =>
                                        fin_tabulate k |} |} ;
  from := {| transform := fun n => {| morphism := fun S : Fin.t (finpow n) =>
                                        fin_apply S |} |}
|}.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.

(* 相关说明。 （已译） *)
Definition FinSet_Sub_powerset :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) FinPowerset_Sets :=
  iso_compose finpow_codec FinSet_Sub_natural.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* The subset {0, 2} ⊆ 3, as a digit string. *)
Definition finpow_sub02 : Fin.t (finpow 3) :=
  fin_tabulate (fun i : Fin.t 3 =>
    match i with
    | Fin.F1 => fin_true
    | Fin.FS Fin.F1 => fin_false
    | _ => fin_true
    end).

(* Its three membership digits, by computation. *)
Example finpow_sub02_at_0 : finpow_mem finpow_sub02 Fin.F1 = true := eq_refl.
Example finpow_sub02_at_1 :
  finpow_mem finpow_sub02 (Fin.FS Fin.F1) = false := eq_refl.
Example finpow_sub02_at_2 :
  finpow_mem finpow_sub02 (Fin.FS (Fin.FS Fin.F1)) = true := eq_refl.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finpow_char02 : Fin.t 3 → Fin.t 2 :=
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element 3%nat finpow_sub02).

Example finpow_char02_at_0 : finpow_char02 Fin.F1 = fin_true := eq_refl.
Example finpow_char02_at_1 :
  finpow_char02 (Fin.FS Fin.F1) = fin_false := eq_refl.
Example finpow_char02_at_2 :
  finpow_char02 (Fin.FS (Fin.FS Fin.F1)) = fin_true := eq_refl.

(* 相关说明。 （已译） *)
Example finpow_round02 :
  finpow_map finpow_char02 finpow_truth_subset = finpow_sub02 := eq_refl.

(* 相关说明。 （已译） *)
Definition finpow_empty : Fin.t (finpow 3) :=
  fin_tabulate (fun _ : Fin.t 3 => fin_false).

Example finpow_empty_has_nothing (i : Fin.t 3) :
  finpow_mem finpow_empty i = false.
Proof. unfold finpow_mem, finpow_empty; now rewrite fin_apply_tabulate. Qed.

Example finpow_sub02_ne_empty : finpow_sub02 = finpow_empty → False.
Proof. discriminate. Qed.

Example finpow_chars_distinct :
  fin_apply finpow_sub02 = fin_apply finpow_empty → False.
Proof.
  intro Heq.
  assert (H0 : fin_apply finpow_sub02 Fin.F1 = fin_apply finpow_empty Fin.F1)
    by now rewrite Heq.
  discriminate H0.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition finpow_const0 : Fin.t 3 → Fin.t 3 := fun _ => Fin.F1.

Example finpow_inverse_of_sub02_is_full :
  finpow_map finpow_const0 finpow_sub02
    = fin_tabulate (fun _ : Fin.t 3 => fin_true) := eq_refl.

Example finpow_inverse_of_empty_is_empty :
  finpow_map finpow_const0 finpow_empty = finpow_empty := eq_refl.

Example finpow_inverse_moves :
  finpow_map finpow_const0 finpow_sub02 = finpow_sub02 → False.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The internal power object *)

(*
   本节说明topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example finpow_is_topos_Pow (n : nat) :
  @Pow FinSet FinSet_Topos n = finpow n := eq_refl.

(* 相关说明。 （已译） *)
Example finpow_topos_Pow_two :
  @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.
