Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.

(*
   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Instance.Grp.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(*
   nLab:      https://ncatlab.org/nlab/show/free+group
   nLab:      https://ncatlab.org/nlab/show/free+groupoid
   nLab:      https://ncatlab.org/nlab/show/free+construction
   Wikipedia: https://en.wikipedia.org/wiki/Free_group
   Wikipedia: https://en.wikipedia.org/wiki/Nielsen%E2%80%93Schreier_theorem
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Riehl, Category Theory in Context, §4.2, printed p. 139 (free ⊣
   Book: Awodey, Category Theory, §1.7 (the universal mapping property of a

   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PointQuiver (X : SetoidObject) : Quiver := {|
  nodes   := poly_unit;
  edges   := fun _ _ => carrier X;
  edgeset := fun _ _ => is_setoid X
|}.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FGWord (X : SetoidObject) : Type :=
  ttt ~{FreeGroupoid (PointQuiver X)}~> ttt.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fg_equiv (X : SetoidObject) (a b : FGWord X) : Prop :=
  inhabited (@equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b).

Lemma fg_equiv_equivalence (X : SetoidObject) : Equivalence (fg_equiv X).
Proof.
  constructor.
  - intro a; constructor; reflexivity.
  - intros a b [Hab]; constructor; now symmetry.
  - intros a b c [Hab] [Hbc]; constructor; now transitivity b.
Qed.

Definition FreeGrpSetoid (X : SetoidObject) : SetoidObject := {|
  carrier   := FGWord X;
  is_setoid := {| equiv        := fg_equiv X
                ; setoid_equiv := fg_equiv_equivalence X |}
|}.

Lemma fg_mul_respects (X : SetoidObject) :
  Proper (fg_equiv X ==> fg_equiv X ==> fg_equiv X)
    (fun a b : FGWord X => a ∘ b).
Proof.
  (* Every argument is introduced BEFORE either truncation is opened: the
     intermediate goal of a [respectful] chain is ascribed sort [Type], so an
     elimination there is refused even though the final goal is a [Prop]. *)
  intros a a' Ha b b' Hb.
  destruct Ha as [Ha], Hb as [Hb]; constructor.
  exact (@compose_respects (FreeGroupoid (PointQuiver X)) ttt ttt ttt
           a a' Ha b b' Hb).
Qed.

Definition FreeGrpObject (X : SetoidObject) : GrpObject := {|
  grp_setoid := FreeGrpSetoid X;

  grp_unit := @id (FreeGroupoid (PointQuiver X)) ttt;
  grp_mul  := fun a b => a ∘ b;
  grp_inv  := fun a => fginv a;

  grp_mul_respects := fg_mul_respects X;

  grp_mul_assoc := fun a b c =>
    inhabits (@comp_assoc_sym (FreeGroupoid (PointQuiver X))
                ttt ttt ttt ttt a b c);
  grp_mul_unit_l := fun a =>
    inhabits (@id_left (FreeGroupoid (PointQuiver X)) ttt ttt a);
  grp_mul_inv_l  := fun a => inhabits (fginv_left a);

  grp_prop :=
    @PropEquiv_of_relation _ (is_setoid (FreeGrpSetoid X)) (fg_equiv X)
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(** The multiplication IS composition and the unit IS the identity arrow,
    definitionally. *)
Example free_group_mul_is_compose (X : SetoidObject) (a b : FGWord X) :
  grp_mul (FreeGrpObject X) a b
    = @compose (FreeGroupoid (PointQuiver X)) ttt ttt ttt a b := eq_refl.

Example free_group_unit_is_id (X : SetoidObject) :
  grp_unit (FreeGrpObject X) = @id (FreeGroupoid (PointQuiver X)) ttt
  := eq_refl.

(** Inversion IS word reversal — [Lib/TList.v]'s [tlist_rev] at the sign
    swap — and it is the chosen inverse of the groupoid structure. *)
Example free_group_inv_is_reversal (X : SetoidObject) (a : FGWord X) :
  grp_inv (FreeGrpObject X) a
    = ginv (FreeGroupoid_IsGroupoid (PointQuiver X)) a := eq_refl.

(** The underlying monoid is literally [hom_monoid] of the free groupoid:
    all three data fields agree on the nose. *)
Example free_group_monoid_carrier (X : SetoidObject) :
  carrier (grp_setoid (FreeGrpObject X))
    = carrier (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_op (X : SetoidObject) :
  grp_mul (FreeGrpObject X)
    = @mon_op (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_unit (X : SetoidObject) :
  grp_unit (FreeGrpObject X)
    = @mon_unit (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* The codomain's `≈` is now the truncation, so the groupoid-level
   respectfulness is wrapped rather than reproved. *)
Definition fg_insert (X : SetoidObject)
  : X ~{Sets}~> Grp_Forget (FreeGrpObject X).
Proof.
  unshelve refine
    {| morphism :=
         @fedgemap _ _ (FreeGroupoidUnit (PointQuiver X)) ttt ttt |}.
  intros a b Hab.
  constructor.
  exact (@fedgemap_respects _ _
           (FreeGroupoidUnit (PointQuiver X)) ttt ttt a b Hab).
Defined.

Example fg_insert_is_generator (X : SetoidObject) (a : carrier X) :
  fg_insert X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition grp_deloop_monoid (H : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid H;

  mon_unit := grp_unit H;
  mon_op   := grp_mul H;

  mon_op_respects := grp_mul_respects H;

  mon_op_assoc  := fun a b c => symmetry (grp_mul_assoc H a b c);
  mon_op_unit_l := grp_mul_unit_l H;
  mon_op_unit_r := grp_mul_unit_r H
|}.

Definition grp_deloop (H : GrpObject) : Category :=
  Deloop (grp_deloop_monoid H).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_deloop_IsGroupoid (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  fun x y a =>
    @Build_IsIsomorphism (grp_deloop H) x y a (grp_inv H a)
      (grp_mul_inv_r H a) (grp_mul_inv_l H a).

(** ** Deliverable 3: the universal property of the free group *)

Section Extension.

Context (X : SetoidObject) (H : GrpObject).
Context (h : X ~{Sets}~> Grp_Forget H).

(** [h], read as a quiver homomorphism into the delooping of [H]. *)
Definition point_hom
  : QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H)) :=
  @Build_QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H))
    (fun _ => ttt)
    (fun _ _ a => h a)
    (fun _ _ => proper_morphism h).

Definition extend_functor : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H :=
  FreeGroupoidFunctor (PointQuiver X) (grp_deloop_IsGroupoid H) point_hom.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_grp_extend_map
  : SetoidMorphism (grp_setoid (FreeGrpObject X)) (grp_setoid H).
Proof using X H h.
  unshelve refine {| morphism := fun w => fmap[extend_functor] w |}.
  intros u v Huv.
  apply (@pequiv_to _ _ (grp_prop H)).
  destruct Huv as [Huv].
  apply (@pequiv_from _ _ (grp_prop H)).
  exact (@fmap_respects _ _ extend_functor ttt ttt u v Huv).
Defined.

Definition free_grp_extend : FreeGrpObject X ~{Grp}~> H :=
  @Build_GrpHom' (FreeGrpObject X) H free_grp_extend_map
    (fun a b => @fmap_comp _ _ extend_functor ttt ttt ttt a b).

(** It agrees with [h] on the generators. *)
Lemma free_grp_extend_generators (a : carrier X) :
  free_grp_extend (fg_insert X a) ≈ h a.
Proof using X H h.
  exact (FreeGroupoidFunctor_gen (PointQuiver X) (grp_deloop_IsGroupoid H)
           point_hom (x:=ttt) (y:=ttt) a).
Qed.

(** ...and it evaluates a word: the two structural clauses that pin down
    what "evaluate a word in the group" means, both instances of the
    homomorphism laws. *)
Lemma free_grp_extend_mul (u v : FGWord X) :
  free_grp_extend (grp_mul (FreeGrpObject X) u v)
    ≈ grp_mul H (free_grp_extend u) (free_grp_extend v).
Proof using X H h. exact (grp_map_mul free_grp_extend u v). Qed.

Lemma free_grp_extend_inv (u : FGWord X) :
  free_grp_extend (grp_inv (FreeGrpObject X) u)
    ≈ grp_inv H (free_grp_extend u).
Proof using X H h. exact (grp_map_inv free_grp_extend u). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition functor_of_hom (g : FreeGrpObject X ~{Grp}~> H)
  : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H.
Proof.
  unshelve eapply Build_Functor.
  - exact (fun _ => ttt).
  - intros [] [] w; exact (grp_map g w).
  (* The free group's `≈` is the truncation of the groupoid's since the PR
     "algebraic carriers are sets" (2026-09-17), so the groupoid-level
     hypothesis is wrapped on the way in. *)
  - intros [] [] u v Huv;
      exact (proper_morphism (grp_map g) u v (inhabits Huv)).
  - intros []; exact (grp_map_unit g).
  - intros [] [] [] u v; exact (grp_map_mul g u v).
Defined.

Lemma free_grp_extend_unique (g : FreeGrpObject X ~{Grp}~> H)
  (Hg : ∀ a : carrier X, g (fg_insert X a) ≈ h a) (w : FGWord X) :
  g w ≈ free_grp_extend w.
Proof using X H h.
  refine (FreeGroupoidFunctor_unique (PointQuiver X)
            (grp_deloop_IsGroupoid H) point_hom (functor_of_hom g)
            (fun _ => eq_refl) _ ttt ttt w).
  intros [] [] a; exact (Hg a).
Qed.

End Extension.

Arguments free_grp_extend {X H} h.
Arguments extend_functor {X H} h.

(** The universal property, in the shape [Theory/Universal/Arrow.v]'s
    [universal_arrow_from_UMP] consumes. *)
Theorem free_group_universal (X : SetoidObject) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X.
Proof.
  intros H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    symmetry; exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; symmetry; exact (Hg a).
Qed.

(** The free group packaged as a universal arrow.  By
    [Theory/Universal/Arrow.v] this IS an initial object of the comma
    category [=(X) ↓ Grp_Forget]. *)
Definition free_group_universal_arrow (X : Sets)
  : UniversalArrow X Grp_Forget :=
  universal_arrow_from_UMP X Grp_Forget (FreeGrpObject X) (fg_insert X)
    (free_group_universal X).

(** The same content in the direct encoding, where the universal object is
    named rather than projected out of a comma category. *)
Program Definition free_group_AUniversalArrow (X : Sets)
  : AUniversalArrow X Grp_Forget (FreeGrpObject X) := {|
  universal_arrow := fg_insert X
|}.
Next Obligation.
  intros X H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; exact (Hg a).
Qed.

(*
   本节说明伴随、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeGrp : Sets ⟶ Grp :=
  LeftAdjointFunctorFromUniversalArrows Grp_Forget free_group_universal_arrow.

Definition free_group_adjunction : FreeGrp ⊣ Grp_Forget :=
  AdjunctionFromUniversalArrows Grp_Forget free_group_universal_arrow.

(** The free functor's object part is the word group, definitionally. *)
Example FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_group_arrow_is_insert (X : Sets) :
  @arrow _ _ X Grp_Forget (free_group_universal_arrow X) = fg_insert X
  := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_group_unit (X : Sets)
  : X ~{Sets}~> Grp_Forget (FreeGrp X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_group_adjunction X.

Example free_group_unit_is_insert (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

Example free_group_unit_is_generator (X : Sets) (a : carrier X) :
  free_group_unit X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_group_counit (H : Grp)
  : FreeGrp (Grp_Forget H) ~{Grp}~> H :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_group_adjunction H.

(** On a generator the counit is the letter itself. *)
Lemma free_group_counit_generator (H : Grp) (a : carrier (Grp_Forget H)) :
  free_group_counit H (fg_insert (Grp_Forget H) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_group_adjunction H a).
Qed.

(** ...and on an arbitrary word it is the evaluation of that word in [H],
    i.e. the extension of the identity map on [H]'s carrier. *)
Theorem free_group_counit_evaluates (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w
    ≈ free_grp_extend (@id Sets (Grp_Forget H)) w.
Proof.
  apply (free_grp_extend_unique (Grp_Forget H) H (@id Sets (Grp_Forget H))
           (free_group_counit H)).
  intro a; exact (free_group_counit_generator H a).
Qed.

(** ** The triangle identities

    Both are instances of [Theory/Adjunction.v]'s derived corollaries; they
    are named here because the issue asks for them by name. *)

Corollary free_group_triangle_left (X : Sets) :
  free_group_counit (FreeGrp X) ∘ fmap[FreeGrp] (free_group_unit X)
    ≈ @id Grp (FreeGrp X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_group_adjunction X). Qed.

Corollary free_group_triangle_right (H : Grp) :
  fmap[Grp_Forget] (free_group_counit H)
    ∘ free_group_unit (Grp_Forget H)
    ≈ @id Sets (Grp_Forget H).
Proof. exact (@fmap_counit_unit _ _ _ _ free_group_adjunction H). Qed.

(** ** The free functor relabels letters

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a word has
    to be proved.  On generators it renames the letter. *)
Lemma free_group_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreeGrp] f (fg_insert X a) ≈ fg_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_group_universal_arrow X)
              (@arrow _ _ Y Grp_Forget (free_group_universal_arrow Y) ∘ f)) a).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition TwoLetters : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_to_S3
  : QuiverHomomorphism (PointQuiver TwoLetters)
      (QuiverOfCat (Deloop S3_Grp)).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (fun _ => ttt).
  - exact (fun _ _ b => if b then S3_r else S3_a).
  - intros u v b b' Hb; simpl in Hb; now rewrite Hb.
Defined.

(* A local abbreviation, purely syntactic, so that the witness proofs below
   fit on a line without disturbing any [rewrite]'s matching. *)
Local Notation FreeTwo := (FreeGroupoid (PointQuiver TwoLetters)).

Definition two_S3 : FreeTwo ⟶ Deloop S3_Grp :=
  FreeGroupoidFunctor (PointQuiver TwoLetters) deloop_S3_groupoid two_to_S3.

Theorem free_group_two_generators_nonabelian :
  grp_mul (FreeGrpObject TwoLetters)
    (fg_insert TwoLetters true) (fg_insert TwoLetters false)
  ≈ grp_mul (FreeGrpObject TwoLetters)
      (fg_insert TwoLetters false) (fg_insert TwoLetters true) → False.
Proof.
  (*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros [Hcomm].
  apply S3_not_abelian.
  assert (Hs : @equiv _ (@homset (Deloop S3_Grp) ttt ttt)
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters true)
                    (fg_insert TwoLetters false)))
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters false)
                    (fg_insert TwoLetters true))))
    by (now rewrite Hcomm).
  rewrite !fmap_comp in Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  exact Hs.
Qed.

(** The two generators are themselves distinct in the free group — the free
    group on two letters does not collapse them. *)
Theorem free_group_two_generators_distinct :
  fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False.
Proof.
  (* Same unwrapping as above, and for the same reason: the goal is [False]. *)
  intros [Hab].
  pose proof (@fmap_respects _ _ two_S3 ttt ttt _ _ Hab) as Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  discriminate.
Qed.
