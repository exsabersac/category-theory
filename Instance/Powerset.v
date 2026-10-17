Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.

(* 相关说明。 （已译） *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/Galois+connection
 nLab: https://ncatlab.org/nlab/show/direct+image
 nLab: https://ncatlab.org/nlab/show/inverse+image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(mathematics)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) The 含入 order, thin 范畴 （已译） *)

(* Inclusion Prop-valued subsets. This IS [relation] carrier,
 what [Proset] [GaloisConnection] require what the
 证明-relevant carrier cannot supply. （已译） *)
Definition subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) : Prop := ∀ x, S x → T x.

Definition subset_le_preorder@{o} (X : SetoidObject@{o o}) :
  PreOrder (@subset_le@{o} X) :=
  {| PreOrder_Reflexive  := fun S x Hx => Hx
   ; PreOrder_Transitive :=
       fun S T U HST HTU x Hx => HTU x (HST x Hx) |}.

(* Mac Lane's "P(U) ... is a preorder under inclusion", as a category. *)
Definition Subsets@{o u} (X : SetoidObject@{o o}) : Category@{o u u} :=
  Proset@{o u} (subset_le_preorder@{o} X).

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Subsets_obj_carrier@{o u} (X : SetoidObject@{o o}) :
  obj[Subsets@{o u} X] = carrier (Powerset_Prop_obj@{o} X) := eq_refl.

Example Subsets_hom_is_subset_le@{o u} (X : SetoidObject@{o o})
  (S T : Subsets@{o u} X) : (S ~{Subsets@{o u} X}~> T) = subset_le S T
  := eq_refl.

(* 相关说明。 （已译） *)
Definition Subsets_thin@{o u +} (X : SetoidObject@{o o}) :
  Thin (Subsets@{o u} X) := proset_thin (subset_le_preorder@{o} X).

(* Every equivalence of parallel arrows is [True], so nothing downstream
   can be measured at [≈] inside this category. *)
Example subsets_equiv_is_True@{o u} {X : SetoidObject@{o o}}
  {S T : Subsets@{o u} X} (f g : S ~{Subsets@{o u} X}~> T) :
  (f ≈ g) = True := eq_refl.

(* Two [≈]-equal subsets DISTINCT 对象, isomorphic 范畴:
 setoid point header, construction. （已译） *)
Definition subsets_iso_of_equiv@{o u +} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)} (H : S ≈ T) :
  @Isomorphism (Subsets@{o u} X) S T.
Proof.
  unshelve econstructor.
  - exact (fun x Hx => proj1 (H x) Hx).
  - exact (fun x Hx => proj2 (H x) Hx).
  - exact I.
  - exact I.
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** (B), (C) Monotonicity, Galois connection, 伴随 （已译） *)

Section Images.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* 相关说明。 （已译） *)
Lemma image_monotone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S T →
  subset_le (Powerset_Prop_image@{o} f S) (Powerset_Prop_image@{o} f T).
Proof.
  intros H y Hy Q k.
  refine (Hy Q _); intros [x [Hx Hfx]].
  exact (k (existT _ x (H x Hx, Hfx))).
Qed.

(* The inverse image is order-preserving: there is nothing to open. *)
Lemma preimage_monotone (S T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S T →
  subset_le (Powerset_Prop_preimage@{o} f S) (Powerset_Prop_preimage@{o} f T).
Proof. intros H x Hx; exact (H (f x) Hx). Qed.

(* 相关说明。 （已译） *)
Lemma image_transpose_to (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le (Powerset_Prop_image@{o} f S) T →
  subset_le S (Powerset_Prop_preimage@{o} f T).
Proof.
  intros H x Hx.
  refine (H (f x) _).
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

(* 相关说明。 （已译） *)
Lemma image_transpose_from (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S (Powerset_Prop_preimage@{o} f T) →
  subset_le (Powerset_Prop_image@{o} f S) T.
Proof.
  intros H y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) (H x Hx)).
Qed.

(* 相关说明。 （已译） *)
Definition image_preimage_galois :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  {| gal_l := Powerset_Prop_image@{o} f
   ; gal_r := Powerset_Prop_preimage@{o} f
   ; gal_mono_l := image_monotone
   ; gal_mono_r := preimage_monotone
   ; gal_to   := image_transpose_to
   ; gal_from := image_transpose_from |}.

(* The two 函子, 伴随: #380 applied, nothing rebuilt. （已译） *)
Definition DirectImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_l (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition InverseImage : Subsets@{o u} Y ⟶ Subsets@{o u} X :=
  GaloisFunctor_r (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition image_preimage_adjunction : DirectImage ⊣ InverseImage :=
  GaloisAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

(** ** Readbacks for (C) *)

Example direct_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = Powerset_Prop_image@{o} f S := eq_refl.

Example inverse_image_obj (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T = Powerset_Prop_preimage@{o} f T := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example direct_image_is_Powerset_Prop
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = fmap[Powerset_Prop@{o so}] f S := eq_refl.

Example inverse_image_is_Powerset_Prop_op
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T
    = fmap[Powerset_Prop_op@{o so}]
        (f : Y ~{(Sets@{o so})^op}~> X) T := eq_refl.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example image_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    DirectImage InverseImage image_preimage_adjunction
  = image_preimage_galois := eq_refl.

(* 相关说明。 （已译） *)

(* Mac Lane's two inequalities, proved directly. *)
Lemma unit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)).
Proof.
  intros x Hx.
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

Lemma counit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T.
Proof.
  intros y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hx).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adj_unit_has_incl_type (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)) :=
  @unit _ _ DirectImage InverseImage image_preimage_adjunction S.

Definition adj_counit_has_incl_type
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T :=
  @counit _ _ DirectImage InverseImage image_preimage_adjunction T.

End Images.

Arguments image_monotone {X Y} f S T H.
Arguments preimage_monotone {X Y} f S T H.
Arguments image_transpose_to {X Y} f S T H.
Arguments image_transpose_from {X Y} f S T H.
Arguments image_preimage_galois {X Y} f.
Arguments DirectImage {X Y} f.
Arguments InverseImage {X Y} f.
Arguments image_preimage_adjunction {X Y} f.
Arguments unit_incl {X Y} f S.
Arguments counit_incl {X Y} f T.

(* ------------------------------------------------------------------------ *)
(** ** (E) Meets and joins *)

Section Bounds.

Universe o u.

Context {X : SetoidObject@{o o}}.

(* 相关说明。 （已译） *)
Definition subset_inter {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ i : Idx, S i x) _).
  intros x y Hxy; split; intros H i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
Defined.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition subset_union {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun i : Idx => S i x)) _).
  intros x y Hxy; split; intros Hi; destruct Hi as [i Hi]; exists i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
Defined.

Lemma subset_inter_IsGLB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsGLB (@subset_le@{o} X) S (subset_inter S).
Proof.
  split.
  - intros i x Hx; exact (Hx i).
  - intros n Hn x Hx i; exact (Hn i x Hx).
Defined.

Lemma subset_union_IsLUB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} X) S (subset_union S).
Proof.
  split.
  - intros i x Hx; exists i; exact Hx.
  - intros n Hn x Hi; destruct Hi as [i Hi]; exact (Hn i x Hi).
Defined.

(* 相关说明。 （已译） *)
Definition subset_meet (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_inter (pair_family S T).

Definition subset_join (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_union (pair_family S T).

Definition subset_top : carrier (Powerset_Prop_obj@{o} X) :=
  subset_inter (@empty_family _).

Definition subset_bot : carrier (Powerset_Prop_obj@{o} X) :=
  subset_union (@empty_family _).

Lemma subset_meet_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) S.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) true). Qed.

Lemma subset_meet_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) T.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) false). Qed.

Lemma subset_meet_greatest (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le N S → subset_le N T → subset_le N (subset_meet S T).
Proof.
  intros H1 H2.
  refine (snd (subset_inter_IsGLB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_join_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) true). Qed.

Lemma subset_join_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le T (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) false). Qed.

Lemma subset_join_least (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S N → subset_le T N → subset_le (subset_join S T) N.
Proof.
  intros H1 H2.
  refine (snd (subset_union_IsLUB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_top_greatest (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S subset_top.
Proof. intros x Hx i; destruct i. Qed.

Lemma subset_bot_least (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le subset_bot S.
Proof. intros x Hx; destruct Hx as [i _]; destruct i. Qed.

(* 相关说明。 （已译） *)
Definition Subsets_Cartesian : @Cartesian (Subsets@{o u} X) :=
  Proset_Cartesian (subset_le_preorder@{o} X)
    subset_meet subset_meet_l subset_meet_r subset_meet_greatest.

Definition Subsets_Cocartesian : @Cocartesian (Subsets@{o u} X) :=
  Proset_Cocartesian (subset_le_preorder@{o} X)
    subset_join subset_join_l subset_join_r subset_join_least.

Definition Subsets_Terminal : @Terminal (Subsets@{o u} X) :=
  Proset_Terminal (subset_le_preorder@{o} X) subset_top subset_top_greatest.

Definition Subsets_Initial : @Initial (Subsets@{o u} X) :=
  Proset_Initial (subset_le_preorder@{o} X) subset_bot subset_bot_least.

Definition Subsets_HasAllMeets : HasAllMeets (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_inter S) (subset_inter_IsGLB S).

Definition Subsets_HasAllJoins : HasAllJoins (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_union S) (subset_union_IsLUB S).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Subsets_Complete : @Complete (Subsets@{o Set} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_Cocomplete : @Cocomplete (Subsets@{o Set} X) :=
  snd (proset_Cocomplete_iff_all_joins (subset_le_preorder@{o} X))
    Subsets_HasAllJoins.

End Bounds.

(* ------------------------------------------------------------------------ *)
(** ** (F) Preservation, directly *)

Section Preservation.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* 相关说明。 （已译） *)
Theorem inverse_image_preserves_meets {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f m (T i) (fst H i)).
  - intros n Hn.
    refine (image_transpose_to f n m _).
    refine (snd H (Powerset_Prop_image@{o} f n) _).
    intro i; exact (image_transpose_from f n (T i) (Hn i)).
Qed.

(* Dually, the left-adjoint half, again directly. *)
Theorem direct_image_preserves_joins {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsLUB (@subset_le@{o} X) S m) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f m).
Proof.
  split.
  - intro i; exact (image_monotone f (S i) m (fst H i)).
  - intros n Hn.
    refine (image_transpose_from f m n _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (image_transpose_to f (S i) n (Hn i)).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem inverse_image_preserves_joins {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f (T i) m (fst H i)).
  - intros n Hn x Hx.
    assert (Hu : subset_le m (subset_union T))
      by exact (snd H (subset_union T) (fst (subset_union_IsLUB T))).
    destruct (Hu (f x) Hx) as [i Hi].
    exact (Hn i x Hi).
Qed.

End Preservation.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RAPLRoute.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition inverse_image_preserves_meets_via_RAPL {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  isalimit_IsGLB (subset_le_preorder@{o} X)
    (InverseImage f ◯ DiscreteCat_Functor (C:=Subsets Y) T) _
    (@preserves_limit _ _ _ _ _
       (right_adjoint_preserves_limit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets Y) T))
       (Proset_Limit (subset_le_preorder@{o} Y) T m H)).

(* 相关说明。 （已译） *)
Definition inverse_image_meet_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsGLB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_meets f T m H,
   inverse_image_preserves_meets_via_RAPL T m H).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition direct_image_preserves_joins_via_LAPC {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S)) :=
  isacolimit_IsLUB (subset_le_preorder@{o} Y)
    (DirectImage f ◯ DiscreteCat_Functor (C:=Subsets X) S) _
    (preserves_colimit
       (left_adjoint_preserves_colimit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets X) S))
       (Subsets_Cocomplete (DiscreteCat Idx)
          (DiscreteCat_Functor (C:=Subsets X) S))).

Definition direct_image_join_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S))
  * IsLUB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_image@{o} f (S i))
      (Powerset_Prop_image@{o} f (subset_union S)) :=
  (direct_image_preserves_joins f S (subset_union S)
     (subset_union_IsLUB S),
   direct_image_preserves_joins_via_LAPC S).

End RAPLRoute.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section MonotoneReading.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition image_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} X) _ (@subset_le@{o} Y) :=
  {| mono_map  := Powerset_Prop_image@{o} f
   ; mono_pres := image_monotone f |}.

Definition preimage_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  {| mono_map  := Powerset_Prop_preimage@{o} f
   ; mono_pres := preimage_monotone f |}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example direct_image_is_monotone_functor_obj
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) image_MonotoneFun] S
    = fobj[DirectImage f] S := eq_refl.

Example inverse_image_is_monotone_functor_obj
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) preimage_MonotoneFun] T
    = fobj[InverseImage f] T := eq_refl.

End MonotoneReading.

(* ------------------------------------------------------------------------ *)
(** ** (H) Non-vacuity *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition powerset_sng0@{o +} :
  carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) Fin.F1.

(* The unit at {1} not invertible: target f^*(f_* {1}) WHOLE
 two-element set, since 常值 map lands everything at 0. （已译） *)
Theorem unit_not_iso@{o so +} :
  subset_le
    (Powerset_Prop_preimage@{o} powerset_const0@{o so}
       (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}))
    powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (H Fin.F1 _ False _).
  - apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
    + apply Powerset_squash_intro@{o}; reflexivity.
    + reflexivity.
  - intro Heq; discriminate Heq.
Qed.

(* The counit at {1} is not invertible either: f^* {1} is EMPTY, so its
   direct image is empty, while {1} is not. *)
Theorem counit_not_iso@{o so +} :
  subset_le powerset_sng1@{o}
    (Powerset_Prop_image@{o} powerset_const0@{o so}
       (Powerset_Prop_preimage@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) _ False _).
  - apply Powerset_squash_intro@{o}; reflexivity.
  - intros [x [Hx _]]; hnf in Hx.
    refine (Hx False _); intro Heq; discriminate Heq.
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem direct_image_not_meet_preserving@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  refine (proj2 (H Fin.F1) _ False _).
  - intros [|].
    + apply Powerset_squash_intro@{o}; exists Fin.F1; split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
    + apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
  - intros [x [Hx _]].
    refine (Hx true False _); intro H0.
    refine (Hx false False _); intro H1.
    rewrite <- H0 in H1; discriminate H1.
Qed.
