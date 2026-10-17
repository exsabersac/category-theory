Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * A universal element for the contravariant power-set functor *)

(*
 nLab:      https://ncatlab.org/nlab/show/subobject+classifier
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The inverse image, and the contravariant functor *)

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Powerset_Prop_preimage@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X)
  (T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

(* Taking inverse images is itself a setoid map on subsets. *)
Definition Powerset_Prop_comap@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y X) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ T, Powerset_Prop_preimage@{o} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_Prop_comap_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} Y X) (H : f ≈ g) :
  Powerset_Prop_comap@{o} f ≈ Powerset_Prop_comap@{o} g.
Proof.
  intros T y; split; intro Ht.
  - exact (proj1 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
  - exact (proj2 (@proper_morphism _ _ _ _ T (f y) (g y) (H y)) Ht).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_Prop_comap_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_comap@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

Lemma Powerset_Prop_comap_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Z Y) (g : SetoidMorphism@{o o o} Y X) :
  Powerset_Prop_comap@{o} (@setoid_morphism_compose@{o o o} Z Y X g f)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_comap@{o} f) (Powerset_Prop_comap@{o} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* THE CONTRAVARIANT POWER-SET FUNCTOR, at one level.  Compare
   [Powerset_op] of the donor file, whose codomain is [Sets] one universe
   up. *)
Definition Powerset_Prop_op@{o so} : @Functor (Sets@{o so})^op Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{o so}
       Powerset_Prop_obj@{o}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_Prop_comap@{o} f) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_comap_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_comap_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_comap_comp@{o} X Y Z f g).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_Prop_op_fmap_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop_op@{o so}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_Prop_preimage@{o} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** Ω, the point ⊤, and the SUBSET {⊤} *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Omega@{o} : SetoidObject@{o o} := Powerset_Prop_truth@{o}.

Example powerset_Omega_is_truth@{o} :
  Powerset_Omega@{o} = Powerset_Prop_truth@{o} := eq_refl.

(* The POINT ⊤ ∈ Ω. *)
Definition Powerset_truth_point@{o} : carrier Powerset_Omega@{o} := True.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_truth_subset@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
    Powerset_truth_point@{o}.

Example powerset_truth_subset_is_singleton@{o} :
  Powerset_truth_subset@{o}
    = Powerset_Prop_singleton_pred@{o} (X:=Powerset_Omega@{o})
        Powerset_truth_point@{o} := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The predicate "P holds", as a subset of Ω. *)
Definition Powerset_holds@{o} :
  carrier (Powerset_Prop_obj@{o} Powerset_Omega@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       Prop (is_setoid Powerset_Omega@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ P : Prop, P) _).
  intros P Q [HPQ HQP]; split; assumption.
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma powerset_squash_prop_inert@{o} (P : Prop) :
  Powerset_squash@{o} P <-> P.
Proof.
  split.
  - intro H; exact (H P (fun p => p)).
  - exact (@Powerset_squash_intro@{o} P).
Qed.

Lemma Powerset_truth_subset_intro@{o} (P : Prop) (p : P) :
  Powerset_truth_subset@{o} P.
Proof. exact (Powerset_squash_intro@{o} (conj (fun _ => p) (fun _ => I))). Qed.

Lemma Powerset_truth_subset_elim@{o} (P : Prop) (H : Powerset_truth_subset@{o} P) :
  P.
Proof. exact (H P (fun q => proj1 q I)). Qed.

Lemma powerset_truth_subset_holds@{o} :
  Powerset_truth_subset@{o} ≈ Powerset_holds@{o}.
Proof.
  intro P; split.
  - exact (@Powerset_truth_subset_elim@{o} P).
  - exact (@Powerset_truth_subset_intro@{o} P).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** A subset of A IS a map A ⟶ Ω, definitionally *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example powerset_subsets_are_maps@{o so} (A : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} A)
    = (A ~{Sets@{o so}}~> Powerset_Omega@{o}) := eq_refl.

(* The characteristic map of a subset is the subset, read across that
   identification. *)
Definition Powerset_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  A ~{Sets@{o so}}~> Powerset_Omega@{o} := S.

Example powerset_char_is_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_char@{o so} S = S := eq_refl.

(* The preimage of {⊤} along [k], which is Riehl's f⁻¹(⊤). *)
Definition Powerset_preimage_of_truth@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  carrier (Powerset_Prop_obj@{o} A) :=
  Powerset_Prop_preimage@{o} k Powerset_truth_subset@{o}.

(* ... and it IS the action of the functor on the universal element, by
   [eq_refl].  The convertibility exception again. *)
Example powerset_preimage_is_fmap@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  fmap[Powerset_Prop_op@{o so}]
    (k : Powerset_Omega@{o} ~{(Sets@{o so})^op}~> A) Powerset_truth_subset@{o}
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(* The two round trips, at [≈].  Together they are the bijection Riehl
   describes, and each is exactly one half of the universal property
   assembled in the next section. *)
Lemma powerset_preimage_char@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} S) ≈ S.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (S a)).
  - exact (@Powerset_truth_subset_intro@{o} (S a)).
Qed.

Lemma powerset_char_preimage@{o so} {A : SetoidObject@{o o}}
  (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  Powerset_char@{o so} (Powerset_preimage_of_truth@{o so} k) ≈ k.
Proof.
  intro a; split.
  - exact (@Powerset_truth_subset_elim@{o} (k a)).
  - exact (@Powerset_truth_subset_intro@{o} (k a)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane's §III.1 universal element *)

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Prop_universal_element@{o so} :
  @AUniversalElement (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Omega@{o}.
Proof.
  unshelve econstructor.
  - exact Powerset_truth_subset@{o}.
  - intros A S.
    unshelve econstructor.
    + exact (Powerset_char@{o so} S).
    + exact (powerset_preimage_char@{o so} S).
    + intros k Hk a; split.
      * intro Hs.
        exact (@Powerset_truth_subset_elim@{o} (k a) (proj2 (Hk a) Hs)).
      * intro Hka.
        exact (proj1 (Hk a) (@Powerset_truth_subset_intro@{o} (k a) Hka)).
Defined.

(* The element of the pair is {⊤}, and the mediating arrow of a subset is
   that subset — both by [eq_refl], so no reader has to trust the
   assembly above. *)
Example powerset_aue_elem@{o so} :
  @aue_elem (Sets@{o so})^op Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}
    = Powerset_truth_subset@{o} := eq_refl.

Example powerset_aue_med@{o so} (A : SetoidObject@{o o})
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  unique_obj (@aue_universal (Sets@{o so})^op Powerset_Prop_op@{o so}
                Powerset_Omega@{o} Powerset_Prop_universal_element@{o so} A S)
    = S := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The representation, and Awodey's naturality for the power set *)

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_representation@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    ≅[[(Sets@{o so})^op, Sets@{o so}]] Powerset_Prop_op@{o so} :=
  ue_representation Powerset_Prop_op@{o so} Powerset_Omega@{o}
    Powerset_Prop_universal_element@{o so}.

Example powerset_repr_source@{o so} :
  @Curried_Hom (Sets@{o so})^op Powerset_Omega@{o}
    = @Curried_CoHom Sets@{o so} Powerset_Omega@{o} := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example powerset_representation_to_is_preimage@{o so}
  (A : SetoidObject@{o o}) (k : A ~{Sets@{o so}}~> Powerset_Omega@{o}) :
  transform (to Powerset_representation@{o so}) A k
    = Powerset_preimage_of_truth@{o so} k := eq_refl.

(* ... and the backward leg is the subset read as a map, again by
   [eq_refl]. *)
Example powerset_representation_from_is_char@{o so}
  (A : SetoidObject@{o o}) (S : carrier (Powerset_Prop_obj@{o} A)) :
  transform (from Powerset_representation@{o so}) A S
    = Powerset_char@{o so} S := eq_refl.

(* The bundled form.  [Representable] is [Functor/Representable.v]'s
   class; the representing object is Ω on the nose. *)
Definition Powerset_Prop_Representable@{o so} :
  Representable Powerset_Prop_op@{o so} :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement
       Powerset_Prop_universal_element@{o so}).

Example powerset_repr_obj@{o so} :
  @repr_obj (Sets@{o so})^op Powerset_Prop_op@{o so}
    Powerset_Prop_Representable@{o so}
    = Powerset_Omega@{o} := eq_refl.

(*
   本节说明同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition powerset_truth_bijection@{o so} (A : SetoidObject@{o o}) :
  @Isomorphism Sets@{o so}
    {| carrier   := A ~{Sets@{o so}}~> Powerset_Omega@{o}
     ; is_setoid := @homset Sets@{o so} A Powerset_Omega@{o} |}
    (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine {| to := _ ; from := _ |}.
  - unshelve refine {| morphism := fun k => Powerset_preimage_of_truth@{o so} k |}.
    intros k k' Hk a.
    exact (@proper_morphism _ _ _ _ Powerset_truth_subset@{o} (k a) (k' a) (Hk a)).
  - unshelve refine {| morphism := fun S => Powerset_char@{o so} S |}.
    intros S S' HS a; exact (HS a).
  - intro S; exact (powerset_preimage_char@{o so} S).
  - intro k; exact (powerset_char_preimage@{o so} k).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity, and the degeneracies excluded by proof *)

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma powerset_Omega_nondegenerate@{o} :
  @equiv _ (is_setoid Powerset_Omega@{o}) Powerset_truth_point@{o} False
  → False.
Proof. intros [H _]; exact (H I). Qed.

Lemma powerset_truth_subset_inhabited@{o} :
  Powerset_truth_subset@{o} Powerset_truth_point@{o}.
Proof. exact (@Powerset_truth_subset_intro@{o} True I). Qed.

Lemma powerset_truth_subset_proper@{o} :
  Powerset_truth_subset@{o} False → False.
Proof. exact (@Powerset_truth_subset_elim@{o} False). Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition powerset_fin3@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 3.

Definition powerset_sub01@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1 \/ i = Fin.FS Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

Definition powerset_sub0@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin3@{o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 3) (is_setoid powerset_fin3@{o})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ i : Fin.t 3, i = Fin.F1) _).
  intros x y Hxy; rewrite Hxy; split; intro H; exact H.
Defined.

(* The two subsets are genuinely different: 1 belongs to one and not the
   other. *)
Lemma powerset_sub01_ne_sub0@{o} :
  powerset_sub01@{o} ≈ powerset_sub0@{o} → False.
Proof.
  intro H.
  assert (H1 : @Fin.FS 2 Fin.F1 = Fin.F1)
    by exact (proj1 (H (Fin.FS Fin.F1)) (or_intror eq_refl)).
  discriminate H1.
Qed.

(* ... so their characteristic maps are different: the correspondence is
   not collapsing subsets. *)
Lemma powerset_chars_distinct@{o so} :
  Powerset_char@{o so} powerset_sub01@{o}
    ≈ Powerset_char@{o so} powerset_sub0@{o} → False.
Proof. exact powerset_sub01_ne_sub0@{o}. Qed.

(* The characteristic map takes the expected values: 0 and 1 are in, 2 is
   out. *)
Lemma powerset_char_at_0@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} Fin.F1.
Proof. exact (or_introl eq_refl). Qed.

Lemma powerset_char_at_1@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS Fin.F1).
Proof. exact (or_intror eq_refl). Qed.

Lemma powerset_char_at_2@{o so} :
  Powerset_char@{o so} powerset_sub01@{o} (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate H. Qed.

(* The round trip on a concrete subset: pulling {⊤} back along the
   characteristic map of {0,1} returns {0,1}. *)
Lemma powerset_fin3_round@{o so} :
  Powerset_preimage_of_truth@{o so} (Powerset_char@{o so} powerset_sub01@{o})
    ≈ powerset_sub01@{o}.
Proof. exact (powerset_preimage_char@{o so} powerset_sub01@{o}). Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition powerset_fin2@{o} : SetoidObject@{o o} :=
  Powerset_Prop_fin_object@{o} 2.

Definition powerset_const0@{o so} : powerset_fin2@{o} ~{Sets@{o so}}~> powerset_fin2@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (Fin.t 2) (is_setoid powerset_fin2@{o})
       (λ _, Fin.F1) _).
  intros x y _; reflexivity.
Defined.

Definition powerset_sng1@{o} : carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) (Fin.FS Fin.F1).

Lemma powerset_inverse_sng1_empty@{o so} (i : Fin.t 2) :
  fmap[Powerset_Prop_op@{o so}]
    (powerset_const0@{o so} : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
    powerset_sng1@{o} i → False.
Proof.
  intro H; hnf in H.
  refine (H False _); intro Heq; discriminate Heq.
Qed.

Lemma powerset_direct_sng1_at_0@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o} Fin.F1.
Proof.
  hnf.
  apply Powerset_squash_intro@{o}.
  exists (Fin.FS Fin.F1); split.
  - apply Powerset_squash_intro@{o}; reflexivity.
  - reflexivity.
Qed.

Theorem powerset_inverse_ne_direct@{o so} :
  fmap[Powerset_Prop@{o so}] powerset_const0@{o so} powerset_sng1@{o}
    ≈ fmap[Powerset_Prop_op@{o so}]
        (powerset_const0@{o so}
           : powerset_fin2@{o} ~{(Sets@{o so})^op}~> powerset_fin2@{o})
        powerset_sng1@{o}
  → False.
Proof.
  intro H.
  exact (powerset_inverse_sng1_empty@{o so} Fin.F1
           (proj1 (H Fin.F1) powerset_direct_sng1_at_0@{o so})).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The classifier obstruction is a DIFFERENT obstruction *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_subset_setoid@{o} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : SetoidObject@{o o}.
Proof.
  unshelve refine
    {| carrier   := { a : carrier A & S a }
     ; is_setoid :=
         {| equiv := fun p q => @equiv _ (is_setoid A) (projT1 p) (projT1 q) |} |}.
  constructor.
  - intro p; reflexivity.
  - intros p q H; now symmetry.
  - intros p q r H K; now transitivity (projT1 q).
Defined.

Definition Powerset_subset_incl@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_setoid@{o} S ~{Sets@{o so}}~> A.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       { a : carrier A & S a } (is_setoid (Powerset_subset_setoid@{o} S))
       (carrier A) (is_setoid A)
       (λ p, projT1 p) _).
  intros p q Hpq; exact Hpq.
Defined.

Lemma Powerset_subset_incl_monic@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  @Monic Sets@{o so} _ _ (Powerset_subset_incl@{o so} S).
Proof.
  apply (injectivity_is_monic@{so o} (Powerset_subset_incl@{o so} S)).
  intros p q H; exact H.
Qed.

Definition Powerset_subobject_of_subset@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) : @SubObj Sets@{o so} A :=
  @Build_SubObj Sets@{o so} A
    (Powerset_subset_setoid@{o} S)
    (Powerset_subset_incl@{o so} S)
    (Powerset_subset_incl_monic@{o so} S).

(* ... and back: the truncated image of a mono is a [Prop]-valued subset.
   This is the step that discards the witness. *)
Definition Powerset_subset_of_subobject@{o so} {A : SetoidObject@{o o}}
  (u : @SubObj Sets@{o so} A) : carrier (Powerset_Prop_obj@{o} A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier A) (is_setoid A) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ a, Powerset_squash@{o}
               (∃ p : carrier (sub_dom u),
                  @equiv _ (is_setoid A) (sub_mono u p) a)) _).
  intros a a' Haa'; split; intros H Q k; apply H; intros [p Hp]; apply k;
    exists p.
  - now transitivity a.
  - transitivity a'; [ exact Hp | now symmetry ].
Defined.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Powerset_subset_roundtrip@{o so} {A : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so} (Powerset_subobject_of_subset@{o so} S)
    ≈ S.
Proof.
  intro a; split.
  - intro H; hnf in H.
    refine (H (S a) _); intros [[b Hb] Hba]; simpl in Hba.
    exact (proj1 (@proper_morphism _ _ _ _ S b a Hba) Hb).
  - intro Ha.
    hnf.
    apply Powerset_squash_intro@{o}.
    exists (existT _ a Ha); reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Where the rest of the exercise lives *)

(*
   本节说明函子、hom、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
