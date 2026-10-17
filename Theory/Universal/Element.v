Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Elements.

Generalizable All Variables.

(** * Universal elements *)

(*
 nLab: https://ncatlab.org/nlab/show/universal+element
   nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   本文件给出泛元素相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Paper: Kan, "Adjoint functors", Trans. Amer. Math. Soc. 87, 1958

   本节说明伴随、自然变换、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance Category.Structure.UniversalProperty.exists_setoid.

(** ** Global elements of a setoid *)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition global_element {X : Sets} (x : X) : SetsOne ~{Sets}~> X :=
  {| morphism := fun _ => x ; proper_morphism := fun a b _ => reflexivity x |}.

(* The element is recovered on the nose, by conversion. *)
Lemma global_element_at {X : Sets} (x : X) : global_element x ttt = x.
Proof. reflexivity. Qed.

Definition GlobalElements (X : Sets) : Sets :=
  {| carrier := SetsOne ~{Sets}~> X |}.

Definition global_elements_to (X : Sets) : GlobalElements X ~{Sets}~> X :=
  {| morphism := fun f : SetsOne ~{Sets}~> X => f ttt ;
     proper_morphism := fun f g H => H ttt |}.

Definition global_elements_from (X : Sets) : X ~{Sets}~> GlobalElements X :=
  {| morphism := @global_element X ; proper_morphism := fun x y H _ => H |}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition global_elements_iso (X : Sets)
  : @Isomorphism Sets (GlobalElements X) X.
Proof.
  unshelve refine {| to := global_elements_to X; from := global_elements_from X |}.
  - intro x; reflexivity.
  - intros f u; destruct u; reflexivity.
Defined.

Section UniversalElement.

Context {D : Category}.

(** ** The elementary definition *)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class AUniversalElement (H : D ⟶ Sets) (r : D) := {
  aue_elem : H r ;                             (* Mac Lane's e ∈ H r *)
  aue_universal (d : D) (x : H d) :            (* (H k) e ≈ x for a unique k *)
    Unique (fun k : r ~{D}~> d => fmap[H] k aue_elem ≈ x)
}.

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance AUniversalElementEquiv (H : D ⟶ Sets) (r : D) :
  Setoid (AUniversalElement H r) :=
  {| equiv := fun X Y => @aue_elem H r X ≈ @aue_elem H r Y |}.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class UniversalElement (H : D ⟶ Sets) := {
  ue_obj : D ;
  ue_elem : H ue_obj ;
  ue_universal (d : D) (x : H d) :
    Unique (fun k : ue_obj ~{D}~> d => fmap[H] k ue_elem ≈ x)
}.

(* The two encodings pass into one another by copying fields. *)
Definition AUniversalElement_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : AUniversalElement H (@ue_obj H U) :=
  {| aue_elem := @ue_elem H U ; aue_universal := @ue_universal H U |}.

Definition UniversalElement_of_AUniversalElement {H : D ⟶ Sets} {r : D}
  (U : AUniversalElement H r) : UniversalElement H :=
  {| ue_obj := r ; ue_elem := @aue_elem H r U ;
     ue_universal := @aue_universal H r U |}.

(*
   本节说明Yoneda、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary aue_of_ue_of_aue {H : D ⟶ Sets} {r : D} (U : AUniversalElement H r) :
  AUniversalElement_of_UniversalElement (UniversalElement_of_AUniversalElement U)
    = U.
Proof. reflexivity. Qed.

Corollary ue_of_aue_of_ue {H : D ⟶ Sets} (U : UniversalElement H) :
  UniversalElement_of_AUniversalElement (AUniversalElement_of_UniversalElement U)
    = U.
Proof. reflexivity. Qed.

(** ** The Yoneda mate *)

(*
   本节说明自然变换、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ue_mate (H : D ⟶ Sets) (r : D) (x : H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  from (Yoneda_Lemma (D^op) H r) x.

(* Its action, by conversion: this is the [(H k) e] of Mac Lane's clause. *)
Lemma ue_mate_at (H : D ⟶ Sets) (r : D) (x : H r) (d : D) (k : r ~{D}~> d) :
  transform (ue_mate H r x) d k = fmap[H] k x.
Proof. reflexivity. Qed.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ue_mate_covariant (H : D ⟶ Sets) (r : D) (x : H r) :
  from (Covariant_Yoneda_Lemma D H r) x ≈ ue_mate H r x.
Proof. intros d k; reflexivity. Qed.

Section MateIso.

Context (H : D ⟶ Sets).
Context (r : D).

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition aue_inverse (U : AUniversalElement H r)
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  {| transform := fun d => {| morphism := fun x => unique_obj (aue_universal d x) |} |}.
Next Obligation.
  proper.
  symmetry.
  apply (uniqueness (aue_universal d y)).
  transitivity x; [ apply (unique_property (aue_universal d x)) | exact X ].
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.
Next Obligation.
  simpl; intros.
  apply (uniqueness (aue_universal y (fmap[H] f x0))).
  transitivity (fmap[H] f (fmap[H] (unique_obj (aue_universal x x0)) aue_elem)).
  - exact (@fmap_comp _ _ H _ _ _ f (unique_obj (aue_universal x x0)) aue_elem).
  - apply proper_morphism, (unique_property (aue_universal x x0)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition aue_mate_IsIso (U : AUniversalElement H r)
  : IsIsomorphism (ue_mate H r (@aue_elem H r U)) :=
  {| two_sided_inverse := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity (unique_obj (aue_universal x (fmap[H] x0 (@aue_elem H r U)))).
  - reflexivity.
  - transitivity x0.
    + apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
    + symmetry; apply id_left.
Qed.

Definition ue_unmate (x : H r) (I : IsIsomorphism (ue_mate H r x))
  : H ~{[D, Sets]}~> @Curried_Hom D r :=
  @two_sided_inverse _ _ _ (ue_mate H r x) I.

(* ... and conversely, an invertible mate IS a universal element: the
   factorization is the inverse's component, its property is one inverse law
   and its uniqueness the other. *)
Program Definition AUniversalElement_of_mate (x : H r)
  (I : IsIsomorphism (ue_mate H r x)) : AUniversalElement H r :=
  {| aue_elem := x ;
     aue_universal := fun d y =>
       {| unique_obj := transform (ue_unmate x I) d y |} |}.
Next Obligation.
  transitivity (fmap[H] id{D} y).
  - exact (@is_right_inverse _ _ _ (ue_mate H r x) I d y).
  - exact (@fmap_id _ _ H d y).
Qed.
Next Obligation.
  transitivity (transform (ue_unmate x I) d (fmap[H] v x)).
  - apply proper_morphism; symmetry; exact X.
  - transitivity (id{D} ∘ v).
    + exact (@is_left_inverse _ _ _ (ue_mate H r x) I d v).
    + apply id_left.
Qed.

(** ** The representation, built directly *)

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ue_transform (U : AUniversalElement H r)
  : @Curried_Hom D r ~{[D, Sets]}~> H :=
  {| transform := fun d =>
       {| morphism := fun k => fmap[H] k (@aue_elem H r U) |} |}.
Next Obligation.
  proper.
  exact (@fmap_respects _ _ H _ _ x y X (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  symmetry.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.
Next Obligation.
  simpl; intros.
  exact (@fmap_comp _ _ H _ _ _ f x0 (@aue_elem H r U)).
Qed.

(* The Yoneda mate IS this transformation, pointwise by [reflexivity] -- but
   NOT as a term: the two records carry different naturality proofs.  This is
   the same seam as [ue_mate_covariant]. *)
Lemma ue_mate_is_transform (U : AUniversalElement H r) :
  ue_mate H r (@aue_elem H r U) ≈ ue_transform U.
Proof. intros d k; reflexivity. Qed.

Program Definition ue_representation (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H :=
  {| to := ue_transform U ; from := aue_inverse U |}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (unique_property (aue_universal x x0)).
  - symmetry; exact (@fmap_id _ _ H x x0).
Qed.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply (uniqueness (aue_universal x (fmap[H] x0 (@aue_elem H r U)))); reflexivity.
  - symmetry; apply id_left.
Qed.

(*
   本节说明函子、Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_eval (Phi : @Curried_Hom D r ≅[[D, Sets]] H) {d : D}
      (k : r ~{D}~> d) :
  fmap[H] k (transform (to Phi) r id{D}) ≈ transform (to Phi) d k.
Proof.
  transitivity (transform (to Phi) d (k ∘ id{D})).
  - exact (naturality (to Phi) r d k id{D}).
  - apply proper_morphism, id_right.
Qed.

Program Definition AUniversalElement_of_repr
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r :=
  {| aue_elem := transform (to Phi) r id{D} ;
     aue_universal := fun d x =>
       {| unique_obj := transform (from Phi) d x |} |}.
Next Obligation.
  transitivity (transform (to Phi) d (transform (from Phi) d x)).
  - apply repr_eval.
  - transitivity (fmap[H] id{D} x).
    + exact (iso_to_from Phi d x).
    + exact (@fmap_id _ _ H d x).
Qed.
Next Obligation.
  transitivity (transform (from Phi) d (transform (to Phi) d v)).
  - apply proper_morphism.
    transitivity (fmap[H] v (transform (to Phi) r id{D})).
    + symmetry; exact X.
    + apply repr_eval.
  - transitivity (id{D} ∘ v).
    + exact (iso_from_to Phi d v).
    + apply id_left.
Qed.

(** ** Deliverable 2: the two encodings, as an isomorphism of setoids *)

(* The anonymous sigma setoid [representability_by_yoneda] uses, named. *)
Definition ue_yoneda_obj : SetoidObject :=
  {| carrier := { x : H r & IsIsomorphism (ue_mate H r x) } |}.

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rby_agrees : @Isomorphism Sets ue_yoneda_obj
  (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := representability_by_yoneda (D^op) H r.

Program Definition ue_to_yoneda
  : Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r)
      ~{Sets}~> ue_yoneda_obj :=
  {| morphism := fun U => (@aue_elem H r U; aue_mate_IsIso U) |}.

Program Definition ue_of_yoneda
  : ue_yoneda_obj ~{Sets}~>
      Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r) :=
  {| morphism := fun p => AUniversalElement_of_mate (`1 p) (`2 p) |}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition universal_element_yoneda
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      ue_yoneda_obj :=
  {| to := ue_to_yoneda ; from := ue_of_yoneda |}.

Corollary ue_yoneda_round_elem (x : H r) (I : IsIsomorphism (ue_mate H r x)) :
  `1 (ue_to_yoneda (ue_of_yoneda (x; I))) = x.
Proof. reflexivity. Qed.

Corollary ue_yoneda_round_ue (U : AUniversalElement H r) :
  @aue_elem H r (ue_of_yoneda (ue_to_yoneda U)) = @aue_elem H r U.
Proof. reflexivity. Qed.

(*
   本节说明函子、Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition universal_element_representation
  : @Isomorphism Sets
      (Build_SetoidObject (AUniversalElement H r) (AUniversalElementEquiv H r))
      (Build_SetoidObject (Isomorphism (@Curried_Hom D r) H) _)
  := iso_compose (representability_by_yoneda (D^op) H r) universal_element_yoneda.

Definition representation_of_universal_element (U : AUniversalElement H r)
  : @Curried_Hom D r ≅[[D, Sets]] H
  := to universal_element_representation U.

Definition universal_element_of_representation
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) : AUniversalElement H r
  := from universal_element_representation Phi.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma universal_element_of_representation_at
  (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = transform (to Phi) r id{D}.
Proof. reflexivity. Qed.

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary routes_agree_elem (Phi : @Curried_Hom D r ≅[[D, Sets]] H) :
  @aue_elem H r (universal_element_of_representation Phi)
    = @aue_elem H r (AUniversalElement_of_repr Phi).
Proof. reflexivity. Qed.

Corollary routes_agree_repr (U : AUniversalElement H r) :
  to (representation_of_universal_element U) ≈ to (ue_representation U).
Proof. intros d k; reflexivity. Qed.

End MateIso.

(** ** The bundled form and [Representable] *)

(*
   本节说明函子、Yoneda、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition UniversalElement_of_Representable {H : D ⟶ Sets}
  (R : Representable H) : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_repr H (@repr_obj _ _ R) (@represented _ _ R)).

Definition Representable_of_UniversalElement {H : D ⟶ Sets}
  (U : UniversalElement H) : Representable H :=
  {| repr_obj := @ue_obj H U ;
     represented := ue_representation H (@ue_obj H U)
                      (AUniversalElement_of_UniversalElement U) |}.

Corollary ue_of_repr_obj {H : D ⟶ Sets} (R : Representable H) :
  @ue_obj H (UniversalElement_of_Representable R) = @repr_obj _ _ R.
Proof. reflexivity. Qed.

Corollary repr_of_ue_obj {H : D ⟶ Sets} (U : UniversalElement H) :
  @repr_obj _ _ (Representable_of_UniversalElement U) = @ue_obj H U.
Proof. reflexivity. Qed.

(* Mac Lane's Φ_r(id r), for the bundled form. *)
Corollary ue_of_repr_elem {H : D ⟶ Sets} (R : Representable H) :
  @ue_elem H (UniversalElement_of_Representable R)
    = transform (to (@represented _ _ R)) (@repr_obj _ _ R) id{D}.
Proof. reflexivity. Qed.

(** ** Uniqueness up to a unique isomorphism *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversalElementUnique.

Context {H : D ⟶ Sets}.

Definition ue_med {a b : D} (U1 : AUniversalElement H a)
           (U2 : AUniversalElement H b) : a ~{D}~> b :=
  unique_obj (@aue_universal H a U1 b (@aue_elem H b U2)).

Lemma ue_med_commutes {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) :
  fmap[H] (ue_med U1 U2) (@aue_elem H a U1) ≈ @aue_elem H b U2.
Proof.
  exact (unique_property (@aue_universal H a U1 b (@aue_elem H b U2))).
Qed.

Lemma ue_med_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (g : a ~{D}~> b) :
  fmap[H] g (@aue_elem H a U1) ≈ @aue_elem H b U2 → ue_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness (@aue_universal H a U1 b (@aue_elem H b U2)) g Hg).
Qed.

Lemma ue_med_id {a : D} (U1 : AUniversalElement H a) : ue_med U1 U1 ≈ id.
Proof.
  apply ue_med_unique.
  exact (@fmap_id _ _ H a (@aue_elem H a U1)).
Qed.

Lemma ue_med_comp {a b e : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (U3 : AUniversalElement H e) :
  ue_med U2 U3 ∘ ue_med U1 U2 ≈ ue_med U1 U3.
Proof.
  symmetry.
  apply ue_med_unique.
  transitivity (fmap[H] (ue_med U2 U3) (fmap[H] (ue_med U1 U2) (@aue_elem H a U1))).
  - exact (@fmap_comp _ _ H _ _ _ (ue_med U2 U3) (ue_med U1 U2) (@aue_elem H a U1)).
  - transitivity (fmap[H] (ue_med U2 U3) (@aue_elem H b U2)).
    + apply proper_morphism, ue_med_commutes.
    + apply ue_med_commutes.
Qed.

Program Definition universal_element_iso {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) : a ≅ b := {|
  to   := ue_med U1 U2;
  from := ue_med U2 U1
|}.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.
Next Obligation. rewrite ue_med_comp; apply ue_med_id. Qed.

Lemma universal_element_iso_unique {a b : D} (U1 : AUniversalElement H a)
      (U2 : AUniversalElement H b) (v : a ≅ b) :
  fmap[H] (to v) (@aue_elem H a U1) ≈ @aue_elem H b U2 →
  universal_element_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply ue_med_unique.
Qed.

Program Definition universal_element_unique {a b : D}
        (U1 : AUniversalElement H a) (U2 : AUniversalElement H b) :
  Unique (fun i : a ≅ b =>
            fmap[H] (to i) (@aue_elem H a U1) ≈ @aue_elem H b U2) := {|
  unique_obj      := universal_element_iso U1 U2;
  unique_property := ue_med_commutes U1 U2
|}.
Next Obligation. exact (universal_element_iso_unique U1 U2 v X). Qed.

End UniversalElementUnique.

(** ** Deliverable 3(a): universal elements are universal arrows from 1 *)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OnePoint.

Context (H : D ⟶ Sets).
Context (r : D).

Definition AUniversalElement_of_AUniversalArrow
  (U : AUniversalArrow SetsOne H r) : AUniversalElement H r.
Proof.
  unshelve econstructor.
  - exact (@universal_arrow _ _ SetsOne H r U ttt).
  - intros d x.
    unshelve eexists
      (unique_obj (@universal_arrow_universal _ _ SetsOne H r U d
                     (@global_element (fobj[H] d) x))).
    + exact (unique_property
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x)) ttt).
    + intros v Hv.
      apply (uniqueness
               (@universal_arrow_universal _ _ SetsOne H r U d
                  (@global_element (fobj[H] d) x))).
      intros []; exact Hv.
Defined.

Definition AUniversalArrow_of_AUniversalElement
  (U : AUniversalElement H r) : AUniversalArrow SetsOne H r.
Proof.
  unshelve econstructor.
  - exact (@global_element (fobj[H] r) (@aue_elem H r U)).
  - intros d f.
    unshelve eexists (unique_obj (aue_universal d (f ttt))).
    + intros []; exact (unique_property (aue_universal d (f ttt))).
    + intros v Hv.
      apply (uniqueness (aue_universal d (f ttt))).
      exact (Hv ttt).
Defined.

(* Both passages keep the datum on the nose. *)
Corollary aue_of_aua_elem (U : AUniversalArrow SetsOne H r) :
  @aue_elem H r (AUniversalElement_of_AUniversalArrow U)
    = @universal_arrow _ _ SetsOne H r U ttt.
Proof. reflexivity. Qed.

Corollary aua_of_aue_arrow (U : AUniversalElement H r) :
  @universal_arrow _ _ SetsOne H r (AUniversalArrow_of_AUniversalElement U)
    = @global_element (fobj[H] r) (@aue_elem H r U).
Proof. reflexivity. Qed.

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary aue_aua_round (U : AUniversalElement H r) :
  @aue_elem H r
    (AUniversalElement_of_AUniversalArrow (AUniversalArrow_of_AUniversalElement U))
    = @aue_elem H r U.
Proof. reflexivity. Qed.

Corollary aua_aue_round (U : AUniversalArrow SetsOne H r) :
  @universal_arrow _ _ SetsOne H r
    (AUniversalArrow_of_AUniversalElement (AUniversalElement_of_AUniversalArrow U))
    ≈ @universal_arrow _ _ SetsOne H r U.
Proof. intros []; reflexivity. Qed.

End OnePoint.

End UniversalElement.

(** ** Deliverable 3(b): universal arrows are universal elements of D(c, S−) *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomFunctor.

Context {C : Category}.
Context {D : Category}.
Context (S : D ⟶ C).
Context (c : C).

(* Mac Lane's D(c, S−). *)
Definition HomAfter : D ⟶ Sets := @Compose D C Sets (fobj[@Curried_Hom C] c) S.

(* The two clauses ARE the same clause. *)
Lemma hom_after_fmap (d d' : D) (k : d ~{D}~> d') (u : c ~{C}~> S d) :
  fmap[HomAfter] k u = fmap[S] k ∘ u.
Proof. reflexivity. Qed.

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AUniversalElement_of_hom {a : D} (U : AUniversalArrow c S a)
  : AUniversalElement HomAfter a :=
  @Build_AUniversalElement D HomAfter a
    (@universal_arrow C D c S a U)
    (fun d x => @universal_arrow_universal C D c S a U d x).

Definition AUniversalArrow_of_hom {a : D} (U : AUniversalElement HomAfter a)
  : AUniversalArrow c S a :=
  @Build_AUniversalArrow C D c S a
    (@aue_elem D HomAfter a U)
    (fun d f => @aue_universal D HomAfter a U d f).

Corollary aue_of_hom_round {a : D} (U : AUniversalElement HomAfter a) :
  AUniversalElement_of_hom (AUniversalArrow_of_hom U) = U.
Proof. reflexivity. Qed.

Corollary aua_of_hom_round {a : D} (U : AUniversalArrow c S a) :
  AUniversalArrow_of_hom (AUniversalElement_of_hom U) = U.
Proof. reflexivity. Qed.

End HomFunctor.

(** ** The subsumption Mac Lane asserts, as one theorem *)

(*
   本节说明 Element 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem universal_element_arrow_subsumption
  {C : Category} {D : Category} (S : D ⟶ C) (c : C) (H : D ⟶ Sets) (r : D) :
  (* (a) a universal element of H is a universal arrow from the one-point
         setoid to H, and conversely *)
  ((AUniversalArrow SetsOne H r → AUniversalElement H r) *
   (AUniversalElement H r → AUniversalArrow SetsOne H r))
  *
  (* (b) a universal arrow from c to S is a universal element of D(c, S−),
         and conversely *)
  ((AUniversalArrow c S r → AUniversalElement (HomAfter S c) r) *
   (AUniversalElement (HomAfter S c) r → AUniversalArrow c S r)).
Proof.
  split; split.
  - exact (AUniversalElement_of_AUniversalArrow H r).
  - exact (AUniversalArrow_of_AUniversalElement H r).
  - exact (@AUniversalElement_of_hom C D S c r).
  - exact (@AUniversalArrow_of_hom C D S c r).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary subsumption_composite {C D : Category} (S : D ⟶ C) (c : C) (a : D)
  (U : AUniversalArrow c S a) :
  (@universal_arrow _ _ SetsOne (HomAfter S c) a
     (AUniversalArrow_of_AUniversalElement (HomAfter S c) a
        (AUniversalElement_of_hom S c U)) ttt : c ~{C}~> fobj[S] a)
  = @universal_arrow C D c S a U.
Proof. reflexivity. Qed.

(** ** Naturality of the global-elements isomorphism *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example setsone_is_terminal :
  SetsOne = @terminal_obj Sets Sets_Terminal := eq_refl.

(* [GlobalElements] is the representable [Hom 1,─]. *)
Example global_elements_is_hom (X : obj[Sets]) :
  GlobalElements X = fobj[fobj[Curried_Hom Sets] SetsOne] X := eq_refl.

(* Riehl's first isomorphism, natural in X. *)
Program Definition global_elements_natural :
  @Isomorphism ([Sets, Sets]) (fobj[Curried_Hom Sets] SetsOne) Id[Sets] := {|
  to   := {| transform := global_elements_to |};
  from := {| transform := global_elements_from |}
|}.
(* Five of the six obligations -- both naturality squares of each
   transformation, and one inverse law -- are closed by the file's default
   obligation tactic.  The sixth is the singleton step. *)
Next Obligation.
  match goal with [ H : poly_unit |- _ ] => destruct H end; reflexivity.
Qed.

(* Its components are the pre-existing maps, on the nose. *)
Example global_elements_natural_to (X : obj[Sets]) :
  transform[to global_elements_natural] X = global_elements_to X := eq_refl.

Example global_elements_natural_from (X : obj[Sets]) :
  transform[from global_elements_natural] X = global_elements_from X
  := eq_refl.
