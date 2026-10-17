Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   nLab: https://ncatlab.org/nlab/show/existential+quantifier
   nLab: https://ncatlab.org/nlab/show/universal+quantifier
   nLab: https://ncatlab.org/nlab/show/adjoint+triple
   nLab: https://ncatlab.org/nlab/show/Beck-Chevalley+condition
   nLab: https://ncatlab.org/nlab/show/hyperdoctrine
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection

   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (A0) General constants, and one engineering helper *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quant_refl@{o} {A : SetoidObject@{o o}} (a : carrier A) :
  @Category.Lib.Setoid.equiv _ (is_setoid A) a a.
Proof. reflexivity. Defined.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition proset_adjunction_at {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA)
  (tr : ∀ a b, RB (fobj[F] a) b → RA a (fobj[U] b))
  (tl : ∀ a b, RA a (fobj[U] b) → RB (fobj[F] a) b)
  : F ⊣ U :=
  Build_Adjunction' (F:=F) (U:=U)
    (fun a b => {| to   := {| morphism := tr a b |}
                 ; from := {| morphism := tl a b |} |}) _ _.

(* Right adjoints preserve meets, at the level of the order: Seven
   Sketches Proposition 1.111, Riehl §4.6.3's right-adjoint half. *)
Definition gal_r_preserves_glb {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → B) (m : B) (H : IsGLB RB d m) :
  IsGLB RA (fun i => gal_r G (d i)) (gal_r G m) :=
  (fun i => gal_mono_r G (fst H i),
   fun n Hn => gal_to G n m
                 (snd H (gal_l G n)
                    (fun i => gal_from G n (d i) (Hn i)))).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gal_l_preserves_lub {A B : Type}
  {RA : relation A} {RB : relation B} (G : GaloisConnection RA RB)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB RA d m) :
  IsLUB RB (fun i => gal_l G (d i)) (gal_l G m) :=
  (fun i => gal_mono_l G (fst H i),
   fun n Hn => gal_from G m n
                 (snd H (gal_r G n)
                    (fun i => gal_to G (d i) n (Hn i)))).

(* ------------------------------------------------------------------------ *)
(** ** (A) The dual image, and the right adjunction *)

(* Awodey's [f_*(U) = {b | f^{-1}(b) subseteq U}], Riehl's [f_!],
   Fong-Spivak's [f_*], Mac Lane's [P_#].  NO truncation: a [forall]
   landing in [Prop] is a [Prop] whatever it quantifies over.
   Respectfulness in [y] transports [f x ≈ y'] back to [f x ≈ y] through
   symmetry and transitivity. *)
Definition Powerset_Prop_dual@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, ∀ x : carrier X,
               @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x) _).
  intros y y' Hyy'; split; intros H x Hfx; apply H.
  - now transitivity y'.
  - transitivity y; [ exact Hfx | now symmetry ].
Defined.

Section Dual.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* Membership, on the nose.  An equality of [Prop]s, not of morphisms. *)
Example dual_mem (S : carrier (Powerset_Prop_obj@{o} X)) (y : carrier Y) :
  Powerset_Prop_dual@{o} f S y
    = (∀ x : carrier X,
         @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → S x)
  := eq_refl.

(* Riehl §4.5's [Delta_f p := p f] IS the inverse image, on the nose:
   again an equality of [Prop]s. *)
Example preimage_is_precompose (T : carrier (Powerset_Prop_obj@{o} Y))
  (x : carrier X) :
  Powerset_Prop_preimage@{o} f T x = T (f x) := eq_refl.

(* The dual image is order-preserving. *)
Definition dual_monotone (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le S T) :
  subset_le (Powerset_Prop_dual@{o} f S) (Powerset_Prop_dual@{o} f T) :=
  fun y Hy x Hfx => H x (Hy x Hfx).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition preimage_transpose_to (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le (Powerset_Prop_preimage@{o} f T) S) :
  subset_le T (Powerset_Prop_dual@{o} f S) :=
  fun y Hy x Hfx =>
    H x (proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy).

(* ... and right to left.  Evaluating the dual image at [f x] against the
   reflexivity witness is the whole argument. *)
Definition preimage_transpose_from (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le T (Powerset_Prop_dual@{o} f S)) :
  subset_le (Powerset_Prop_preimage@{o} f T) S :=
  fun x Hx => H (f x) Hx x (quant_refl (f x)).

(* THE GALOIS CONNECTION, all six fields by name. *)
Definition preimage_dual_galois :
  GaloisConnection (@subset_le@{o} Y) (@subset_le@{o} X) :=
  {| gal_l := Powerset_Prop_preimage@{o} f
   ; gal_r := Powerset_Prop_dual@{o} f
   ; gal_mono_l := preimage_monotone f
   ; gal_mono_r := dual_monotone
   ; gal_to   := preimage_transpose_to
   ; gal_from := preimage_transpose_from |}.

(* The dual-image functor: #380's [GaloisFunctor_r] applied. *)
Definition DualImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_r (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    preimage_dual_galois.

(** *** The two pinned adjunctions *)

(* #382's, under this issue's name.  A [:=] with no tactic, so "the
   existential IS the direct image" is definitional at a general [f]. *)
Definition exists_substitution_adjunction : DirectImage f ⊣ InverseImage f :=
  image_preimage_adjunction f.

(* THE HEADLINE.  Stated at #382's [InverseImage f], not at a second
   preimage functor: see the header. *)
Definition substitution_forall_adjunction : InverseImage f ⊣ DualImage :=
  proset_adjunction_at (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage preimage_transpose_to preimage_transpose_from.

(* Mac Lane's "P^*, which is the inverse image operation, has both a left
   adjoint P_* and a right adjoint P_#", packaged.  [*] is [prod]: both
   components are data. *)
Definition quantifier_triple :
  (DirectImage f ⊣ InverseImage f) * (InverseImage f ⊣ DualImage) :=
  (exists_substitution_adjunction, substitution_forall_adjunction).

(** *** Readbacks *)

Example dual_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DualImage] S = Powerset_Prop_dual@{o} f S := eq_refl.

Example exists_adj_is_image_preimage :
  exists_substitution_adjunction = image_preimage_adjunction f := eq_refl.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example dual_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (InverseImage f) DualImage substitution_forall_adjunction
  = preimage_dual_galois := eq_refl.

(** *** The unit and the counit ARE the two inclusions *)

(* Mac Lane's [X <= P_# P^* X], written directly. *)
Definition forall_unit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le T
    (Powerset_Prop_dual@{o} f (Powerset_Prop_preimage@{o} f T)) :=
  fun y Hy x Hfx => proj2 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hy.

(* Mac Lane's [P^* P_# S <= S]. *)
Definition forall_counit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_dual@{o} f S)) S :=
  fun x Hx => Hx x (quant_refl (f x)).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example adj_unit_is_forall_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) DualImage substitution_forall_adjunction T
    = forall_unit_incl T := eq_refl.

Example adj_counit_is_forall_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) DualImage substitution_forall_adjunction S
    = forall_counit_incl S := eq_refl.

(** *** (F) Seven Sketches 1.117 and Awodey 9.12, in their own words *)

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition apples_buckets_bicondition
  (T : carrier (Powerset_Prop_obj@{o} Y))
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  iffT (subset_le (Powerset_Prop_preimage@{o} f T) S)
       (subset_le T (Powerset_Prop_dual@{o} f S)) :=
  (preimage_transpose_to T S, preimage_transpose_from T S).

(* "if a bucket doesn't contain any apples at all, then vacuously all its
   apples are from A', so empty buckets count". *)
Definition dual_vacuous (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y)
  (Hy : ∀ x : carrier X,
          @Category.Lib.Setoid.equiv _ (is_setoid Y) (f x) y → False) :
  Powerset_Prop_dual@{o} f S y :=
  fun x Hfx => match Hy x Hfx with end.

(** *** (D) Awodey §9.6: what each adjoint preserves *)

(* The dual image preserves meets, directly: the second clause is the
   transpose of the family's own second clause. *)
Theorem dual_image_preserves_meets {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m).
Proof.
  split.
  - intro i; exact (dual_monotone m (S i) (fst H i)).
  - intros n Hn.
    refine (preimage_transpose_to n m _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (preimage_transpose_from n (S i) (Hn i)).
Qed.

(* The same statement read off (A0).  [gal_r preimage_dual_galois] IS the
   dual image, so the general lemma applies with no adapter. *)
Definition dual_image_preserves_meets_via_galois {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m) :=
  gal_r_preserves_glb preimage_dual_galois S m H.

(* The two routes inhabit ONE type: the pair typechecks. *)
Definition dual_image_meet_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsGLB (@subset_le@{o} X) S m) :
  IsGLB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_dual@{o} f (S i))
    (Powerset_Prop_dual@{o} f m)
  * IsGLB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_dual@{o} f (S i))
      (Powerset_Prop_dual@{o} f m) :=
  (dual_image_preserves_meets S m H,
   dual_image_preserves_meets_via_galois S m H).

(* Instance/Powerset.v proved this DIRECTLY, and the comment beside it
   says why: the adjoint route needs f^*'s right adjoint,
   which is this file's.  Here it is, as that corollary. *)
Definition inverse_image_preserves_joins_via_galois {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  gal_l_preserves_lub preimage_dual_galois T m H.

Definition inverse_image_join_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsLUB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_joins f T m H,
   inverse_image_preserves_joins_via_galois T m H).

End Dual.

Arguments dual_monotone {X Y} f S T H.
Arguments preimage_transpose_to {X Y} f T S H.
Arguments preimage_transpose_from {X Y} f T S H.
Arguments preimage_dual_galois {X Y} f.
Arguments DualImage {X Y} f.
Arguments exists_substitution_adjunction {X Y} f.
Arguments substitution_forall_adjunction {X Y} f.
Arguments quantifier_triple {X Y} f.
Arguments forall_unit_incl {X Y} f T.
Arguments forall_counit_incl {X Y} f S.
Arguments apples_buckets_bicondition {X Y} f T S.
Arguments dual_vacuous {X Y} f S y Hy.
Arguments dual_image_preserves_meets {X Y} f {Idx} S m H.

(* ------------------------------------------------------------------------ *)
(** ** (B) Mac Lane's site: the first projection U x V -> U *)

(* The product setoid.  Measured: for [U V : SetoidObject@{o o}] this is
   again a [SetoidObject@{o o}], which is what lets [Subsets] be formed
   on it. *)
Definition ProdSetoid@{o so} (U V : SetoidObject@{o o}) : SetoidObject@{o o} :=
  @product_obj Sets@{o so} Sets_Cartesian U V.

(* Mac Lane's [P : U x V -> U]. *)
Definition proj_fst@{o so} (U V : SetoidObject@{o o}) :
  ProdSetoid@{o so} U V ~{Sets@{o so}}~> U :=
  @exl Sets@{o so} Sets_Cartesian U V.

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition proj_exists@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun y : carrier V => S (x, y))) _).
  intros x x' Hxx'; split; intros Hy; destruct Hy as [y Hy]; exists y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) Hy).
Defined.

(* [P_# S = {x | forall y, y in V implies <x,y> in S}]. *)
Definition proj_forall@{o so} {U V : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  carrier (Powerset_Prop_obj@{o} U).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier U) (is_setoid U) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ y : carrier V, S (x, y)) _).
  intros x x' Hxx'; split; intros H y.
  - exact (proj1 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
  - exact (proj2 (@proper_morphism _ _ _ _ S (x, y) (x', y)
                    (Hxx', quant_refl y)) (H y)).
Defined.

(* [P^* X], which Mac Lane calls the cylinder [X x V] over the base X. *)
Definition cylinder@{o so} {U V : SetoidObject@{o o}}
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)) :=
  Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs.

Section Projection.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).

Example proj_fst_computes (x : carrier U) (y : carrier V) :
  proj_fst@{o so} U V (x, y) = x := eq_refl.

(* The cylinder over X contains exactly the pairs whose first component
   lies in X: an equality of [Prop]s, on the nose. *)
Example cylinder_mem (Xs : carrier (Powerset_Prop_obj@{o} U))
  (x : carrier U) (y : carrier V) :
  @cylinder@{o so} U V Xs (x, y) = Xs x := eq_refl.

(** *** Mac Lane's two displayed biconditionals *)

(* [S <= P^* X <=> P_* S <= X]. *)
Theorem proj_exists_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le S (@cylinder@{o so} U V Xs))
       (subset_le (@proj_exists@{o so} U V S) Xs).
Proof.
  split.
  - intros H x Hx; destruct Hx as [y Hy]; exact (H (x, y) Hy).
  - intros H z Hz; destruct z as [x y]; exact (H x (ex_intro _ y Hz)).
Qed.

(* [P^* X <= S <=> X <= P_# S]. *)
Theorem proj_forall_transpose
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  iffT (subset_le (@cylinder@{o so} U V Xs) S)
       (subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - intros H x Hx y; exact (H (x, y) Hx).
  - intros H z Hz; destruct z as [x y]; exact (H x Hz y).
Qed.

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem proj_forall_largest
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  subset_le (@cylinder@{o so} U V (@proj_forall@{o so} U V S)) S
  * (∀ Xs : carrier (Powerset_Prop_obj@{o} U),
       subset_le (@cylinder@{o so} U V Xs) S
       → subset_le Xs (@proj_forall@{o so} U V S)).
Proof.
  split.
  - exact (snd (proj_forall_transpose S (@proj_forall@{o so} U V S))
             (fun x Hx => Hx)).
  - intros Xs H; exact (fst (proj_forall_transpose S Xs) H).
Qed.

(** *** The two Galois connections at Mac Lane's own formulas *)

Definition proj_exists_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_exists@{o so} U V S) (@proj_exists@{o so} U V T) :=
  fun x Hx =>
    match Hx with ex_intro _ y Hy => ex_intro _ y (H (x, y) Hy) end.

Definition proj_forall_monotone
  (S T : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (H : subset_le S T) :
  subset_le (@proj_forall@{o so} U V S) (@proj_forall@{o so} U V T) :=
  fun x Hx y => H (x, y) (Hx y).

Definition cylinder_monotone
  (Xs Ys : carrier (Powerset_Prop_obj@{o} U)) (H : subset_le Xs Ys) :
  subset_le (@cylinder@{o so} U V Xs) (@cylinder@{o so} U V Ys) :=
  preimage_monotone (proj_fst@{o so} U V) Xs Ys H.

Definition proj_galois_exists :
  GaloisConnection (@subset_le@{o} (ProdSetoid@{o so} U V))
                   (@subset_le@{o} U) :=
  {| gal_l := @proj_exists@{o so} U V
   ; gal_r := @cylinder@{o so} U V
   ; gal_mono_l := proj_exists_monotone
   ; gal_mono_r := cylinder_monotone
   ; gal_to   := fun S Xs H => snd (proj_exists_transpose S Xs) H
   ; gal_from := fun S Xs H => fst (proj_exists_transpose S Xs) H |}.

Definition proj_galois_forall :
  GaloisConnection (@subset_le@{o} U)
                   (@subset_le@{o} (ProdSetoid@{o so} U V)) :=
  {| gal_l := @cylinder@{o so} U V
   ; gal_r := @proj_forall@{o so} U V
   ; gal_mono_l := cylinder_monotone
   ; gal_mono_r := proj_forall_monotone
   ; gal_to   := fun Xs S H => fst (proj_forall_transpose S Xs) H
   ; gal_from := fun Xs S H => snd (proj_forall_transpose S Xs) H |}.

(** *** The identifications with (A), and their exact grade *)

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem proj_exists_is_image
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_exists@{o so} U V S
    ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intro Hx; destruct Hx as [y Hy].
    apply Powerset_squash_intro@{o}; exists (x, y); split;
      [ exact Hy | reflexivity ].
  - intro H; refine (H (ex (fun y : carrier V => S (x, y))) _).
    intros Hz; destruct Hz as [z [Hz Hex]]; exists (snd z).
    refine (proj1 (@proper_morphism _ _ _ _ S z (x, snd z) _) Hz).
    exact (Hex, quant_refl (snd z)).
Qed.

(* And [P_#] is the dual image along the same projection, again at [≈]:
   [proj_forall] quantifies over [carrier V], the dual image over
   [carrier (ProdSetoid U V)]. *)
Theorem proj_forall_is_dual
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  @proj_forall@{o so} U V S
    ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S.
Proof.
  intro x; split.
  - intros H z Hz.
    exact (proj2 (@proper_morphism _ _ _ _ S z (x, snd z)
                    (Hz, quant_refl (snd z))) (H (snd z))).
  - intros H y; exact (H (x, y) (quant_refl x)).
Qed.

(* The two Galois connections' three maps agree with (A)'s.  The RECORDS
   are not compared, and no comparison of the two adjunctions is
   claimed. *)
Definition proj_maps_agree
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  (gal_l proj_galois_exists S
     ≈ Powerset_Prop_image@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_forall S
       ≈ Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S)
  * (gal_r proj_galois_exists Xs
       = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs) :=
  ((proj_exists_is_image S, proj_forall_is_dual S), eq_refl).

End Projection.

(* ------------------------------------------------------------------------ *)
(** ** (C) Beck-Chevalley for the reindexed projection *)

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cyl_reindex@{o so} {U U' : SetoidObject@{o o}}
  (V : SetoidObject@{o o}) (g : U' ~{Sets@{o so}}~> U) :
  ProdSetoid@{o so} U' V ~{Sets@{o so}}~> ProdSetoid@{o so} U V.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (ProdSetoid@{o so} U' V)) (is_setoid (ProdSetoid@{o so} U' V))
       (carrier (ProdSetoid@{o so} U V)) (is_setoid (ProdSetoid@{o so} U V))
       (λ z, (g (fst z), snd z)) _).
  intros z z' Hzz'; split.
  - exact (proper_morphism g _ _ (fst Hzz')).
  - exact (snd Hzz').
Defined.

Section BeckChevalley.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example beck_chevalley_exists_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

Example beck_chevalley_forall_mem
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V)))
  (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S) x
    = @proj_forall@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x
  := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example beck_chevalley_exists
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

Example beck_chevalley_forall
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    = @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S)
  := eq_refl.

(* The [≈] readings, for a consumer who wants the order-theoretic form. *)
Theorem beck_chevalley_exists_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    ≈ @proj_exists@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

Theorem beck_chevalley_forall_equiv
  (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))) :
  Powerset_Prop_preimage@{o} g (@proj_forall@{o so} U V S)
    ≈ @proj_forall@{o so} U' V (Powerset_Prop_preimage@{o} (cyl_reindex V g) S).
Proof. intro x; split; intro H; exact H. Qed.

End BeckChevalley.

(* ------------------------------------------------------------------------ *)
(** ** (E) Riehl 4.1.9, and Exercise 4.1.ii *)

(* A predicate on X in Riehl's sense IS an element of the power set here.
   Both readings are equalities of TYPES and of [Prop]s. *)
Example predicates_are_subsets@{o} (X : SetoidObject@{o o}) :
  carrier (Powerset_Prop_obj@{o} X)
    = SetoidMorphism@{o o o} X Powerset_Prop_truth@{o} := eq_refl.

Example pointwise_is_subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  @subset_le@{o} X S T = (∀ x : carrier X, S x → T x) := eq_refl.

(* The one-point setoid, and the unique map into it.  Named locally: both
   [SetsOne] (Construction/Elements.v, Instance/Sets/Pointed/
   Coslice.v) and [Sets_Terminal] are taken. *)
Definition quant_one@{o so} : SetoidObject@{o o} :=
  @terminal_obj Sets@{o so} Sets_Terminal.

Definition quant_bang@{o so} (X : SetoidObject@{o o}) :
  X ~{Sets@{o so}}~> quant_one@{o so} :=
  @one Sets@{o so} Sets_Terminal X.

Section Riehl.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(* Riehl's [Delta_X], [exists_X] and [forall_X], as the three functors of
   Example 4.1.8 at the unique map [X -> 1].  That instantiation IS her
   Exercise 4.1.ii. *)
Definition Delta_X : Subsets@{o u} quant_one@{o so} ⟶ Subsets@{o u} X :=
  InverseImage (quant_bang@{o so} X).

Definition exists_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DirectImage (quant_bang@{o so} X).

Definition forall_X : Subsets@{o u} X ⟶ Subsets@{o u} quant_one@{o so} :=
  DualImage (quant_bang@{o so} X).

(* [exists_X -| Delta_X -| forall_X], both legs by instantiation. *)
Definition riehl_exists_delta : exists_X ⊣ Delta_X :=
  exists_substitution_adjunction (quant_bang@{o so} X).

Definition riehl_delta_forall : Delta_X ⊣ forall_X :=
  substitution_forall_adjunction (quant_bang@{o so} X).

Definition riehl_adjoint_triple :
  (exists_X ⊣ Delta_X) * (Delta_X ⊣ forall_X) :=
  (riehl_exists_delta, riehl_delta_forall).

(* [Delta_X] is her constant functor: its value at [P] is the predicate
   constantly [P ttt].  An equality of [Prop]s, on the nose. *)
Example Delta_X_obj_mem
  (P : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) (x : carrier X) :
  fobj[Delta_X] P x = P ttt := eq_refl.

End Riehl.

(** *** The truth-value object: [Subsets 1] against [Props] *)

Section TruthValues.

Universe o so u.
Constraint o < so.

(* Evaluation at the point.  Functoriality is free: [Props] is thin. *)
Program Definition subsets_one_to_Props :
  Subsets@{o u} quant_one@{o so} ⟶ Props@{o u} := {|
  fobj := fun S => S ttt;
  fmap := fun S T (h : subset_le S T) => h ttt
|}.

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Props_to_subsets_one :
  Props@{o u} ⟶ Subsets@{o u} quant_one@{o so} := {|
  fobj := fun P =>
    @Build_SetoidMorphism@{o o o}
      (carrier quant_one@{o so}) (is_setoid quant_one@{o so})
      Prop (is_setoid Powerset_Prop_truth@{o}) (λ _, P)
      (fun _ _ _ => conj (fun p : P => p) (fun p : P => p));
  fmap := fun P Q (h : P → Q) => fun _ (p : P) => h p
|}.

(* Both round trips.  One is the identity on the nose at the level of
   [Prop]s; the other needs the point to be destructed. *)
Example Props_subsets_one_round (P : Props@{o u}) :
  fobj[subsets_one_to_Props] (fobj[Props_to_subsets_one] P) = P := eq_refl.

Theorem subsets_one_Props_round
  (S : carrier (Powerset_Prop_obj@{o} quant_one@{o so})) :
  fobj[Props_to_subsets_one] (fobj[subsets_one_to_Props] S) ≈ S.
Proof. intro x; destruct x; split; intro H; exact H. Qed.

(* Riehl's Omega, up to equivalence.  [≅[Cat]] IS equivalence in this
   library ([Cat]'s hom-setoid is [Functor_Setoid]); an isomorphism OF
   CATEGORIES is unavailable, the object types differing, and none is
   claimed. *)
Program Definition subsets_one_Props :
  @Isomorphism Cat (Subsets@{o u} quant_one@{o so}) Props@{o u} := {|
  to   := subsets_one_to_Props;
  from := Props_to_subsets_one
|}.
Next Obligation.
  unshelve eexists.
  - intro S; unshelve econstructor.
    + exact (fun x Hx => proj1 (subsets_one_Props_round S x) Hx).
    + exact (fun x Hx => proj2 (subsets_one_Props_round S x) Hx).
    + exact I.
    + exact I.
  - intros S T h; exact I.
Defined.

End TruthValues.

(* ------------------------------------------------------------------------ *)
(** ** (D) again: Awodey's two contrapositives, at a concrete witness *)

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Quantifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem dual_const0_sng0_at_1@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o}
    (Fin.FS Fin.F1).
Proof. intros x Heq; discriminate Heq. Qed.

(* ... and does NOT contain 0: the fibre over 0 is the whole set, and 1
   is not in {0}. *)
Theorem dual_const0_sng0_not_at_0@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o} Fin.F1
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(* The direct image of {1} DOES contain 0.  This is
   Instance/Sets/Powerset/Universal.v's own [powerset_direct_sng1_at_0]
   read through [Powerset_Prop_fmap_image], not a second proof. *)
Definition image_const0_sng1_at_0@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o} Fin.F1 :=
  powerset_direct_sng1_at_0@{o so}.

(* THE TWO ADJOINTS DIFFER.  At {1} the existential contains 0 and the
   universal does not: the whole point of the third leg. *)
Theorem exists_ne_forall_at_const0@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}
    ≈ Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (proj1 (H Fin.F1) image_const0_sng1_at_0@{o so}
            Fin.F1 eq_refl False _).
  intro Heq; discriminate Heq.
Qed.

(* Every element of the two-point carrier lies in {0} join {1}: the
   exhaustiveness the join witness needs, by the [Fin.caseS']/[Fin.case0]
   idiom of Structure/Limit/Product/Finite.v. *)
Lemma fin2_in_sng0_join_sng1@{o +} (i : Fin.t 2%nat) :
  subset_join powerset_sng0@{o} powerset_sng1@{o} i.
Proof.
  pattern i; apply (Fin.caseS' i).
  - exists true; apply Powerset_squash_intro@{o}; reflexivity.
  - intro j; pattern j; apply (Fin.caseS' j).
    + exists false; apply Powerset_squash_intro@{o}; reflexivity.
    + intro k; apply (Fin.case0 (fun _ => _) k).
Qed.

(* THE DUAL IMAGE DOES NOT PRESERVE JOINS.  Stated as the refutation of
   the INCLUSION, which is what the contrapositive below consumes and
   which is strictly stronger than refuting the [≈]. *)
Theorem dual_image_not_join_preserving@{o so +} :
  subset_le
    (Powerset_Prop_dual@{o} powerset_const0@{o so}
       (subset_join powerset_sng0@{o} powerset_sng1@{o}))
    (subset_join
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
       (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  assert (Hin : Powerset_Prop_dual@{o} powerset_const0@{o so}
                  (subset_join powerset_sng0@{o} powerset_sng1@{o}) Fin.F1)
    by (intros x _; exact (fin2_in_sng0_join_sng1 x)).
  destruct (H Fin.F1 Hin) as [b Hb]; destruct b.
  - refine (Hb (Fin.FS Fin.F1) eq_refl False _);
      intro Heq; discriminate Heq.
  - refine (Hb Fin.F1 eq_refl False _); intro Heq; discriminate Heq.
Qed.

Theorem dual_image_not_join_preserving_equiv@{o so +} :
  Powerset_Prop_dual@{o} powerset_const0@{o so}
      (subset_join powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_join
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_dual@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  exact (dual_image_not_join_preserving (fun x => proj1 (H x))).
Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem exists_not_right_adjoint@{o so u +} :
  (∃ L : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     L ⊣ DirectImage powerset_const0@{o so})
  → False.
Proof.
  intros [L Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               L (DirectImage powerset_const0@{o so}) Adj).
  pose (HG := gal_r_preserves_glb G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_meet powerset_sng0@{o} powerset_sng1@{o})
                (subset_inter_IsGLB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  (* The nontrivial inclusion, from the adjoint hypothesis. *)
  assert (Hge : subset_le
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))).
  { refine (snd HG _ _); intros [|].
    - exact (subset_meet_l _ _).
    - exact (subset_meet_r _ _). }
  (* ... and the trivial one, from monotonicity. *)
  assert (Hle : subset_le
                  (Powerset_Prop_image@{o} powerset_const0@{o so}
                     (subset_meet powerset_sng0@{o} powerset_sng1@{o}))
                  (subset_meet
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng0@{o})
                     (Powerset_Prop_image@{o} powerset_const0@{o so}
                        powerset_sng1@{o}))).
  { refine (subset_meet_greatest _ _ _ _ _).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_l _ _)).
    - exact (image_monotone powerset_const0@{o so} _ _
               (subset_meet_r _ _)). }
  (* Mutual inclusion IS [≈] -- Instance/Grp/Galois.v's
     [subset_le_antisym], written inline for the measured reason in the
     header. *)
  exact (direct_image_not_meet_preserving
           (fun x => conj (Hle x) (Hge x))).
Qed.

(* And dually: "as above, forall x cannot be a left adjoint, since it
   does not have this property." *)
Theorem forall_not_left_adjoint@{o so u +} :
  (∃ R : Subsets@{o u} powerset_fin2@{o} ⟶ Subsets@{o u} powerset_fin2@{o},
     DualImage powerset_const0@{o so} ⊣ R)
  → False.
Proof.
  intros [R Adj].
  pose (G := GaloisOfAdjunction (subset_le_preorder@{o} powerset_fin2@{o})
               (subset_le_preorder@{o} powerset_fin2@{o})
               (DualImage powerset_const0@{o so}) R Adj).
  pose (HG := gal_l_preserves_lub G
                (pair_family powerset_sng0@{o} powerset_sng1@{o})
                (subset_join powerset_sng0@{o} powerset_sng1@{o})
                (subset_union_IsLUB
                   (pair_family powerset_sng0@{o} powerset_sng1@{o}))).
  refine (dual_image_not_join_preserving _).
  refine (snd HG _ _); intros [|].
  - exact (subset_join_l _ _).
  - exact (subset_join_r _ _).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (G) Non-vacuity over Mac Lane's own site *)

(* Both factors are the two-element discrete setoid. *)
Definition quant_sq@{o so} : SetoidObject@{o o} :=
  ProdSetoid@{o so} powerset_fin2@{o} powerset_fin2@{o}.

Section ProjectionWitness.

Universe o so.
Constraint o < so.

(* The diagonal {(x, x)}. *)
Definition diag_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = snd z) _).
  intros z z' Hzz'; destruct Hzz' as [H1 H2]; split; intro H.
  - rewrite <- H1, <- H2; exact H.
  - rewrite H1, H2; exact H.
Defined.

(* The row {(0, y) | y}. *)
Definition row0_subset : carrier (Powerset_Prop_obj@{o} quant_sq@{o so}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier quant_sq@{o so}) (is_setoid quant_sq@{o so})
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ z, fst z = Fin.F1) _).
  intros z z' Hzz'; destruct Hzz' as [H1 _]; split; intro H.
  - rewrite <- H1; exact H.
  - rewrite H1; exact H.
Defined.

(* Mac Lane's projection of the diagonal is everything: every x pairs
   with itself. *)
Theorem proj_diag_exists_everywhere (x : Fin.t 2%nat) :
  @proj_exists@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x.
Proof. exists x; reflexivity. Qed.

(* ... while [P_#] of the diagonal is empty: no x pairs with EVERY y. *)
Theorem proj_diag_forall_nowhere (x : Fin.t 2%nat) :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} diag_subset x
  → False.
Proof.
  intro H.
  pose proof (H Fin.F1) as H0; pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  rewrite H0 in H1; discriminate H1.
Qed.

(* At a ROW, [P_#] is the singleton {0}: the row over 0 is full, the row
   over 1 is empty. *)
Theorem proj_row_forall_at_0 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    Fin.F1.
Proof. intro y; reflexivity. Qed.

Theorem proj_row_forall_not_at_1 :
  @proj_forall@{o so} powerset_fin2@{o} powerset_fin2@{o} row0_subset
    (Fin.FS Fin.F1)
  → False.
Proof. intro H; pose proof (H Fin.F1) as H0; discriminate H0. Qed.

End ProjectionWitness.
