Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.

Generalizable All Variables.

(** * Mac Lane's group illustration: the quotient objects of G are the
      G/N *)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+group
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Mac Lane's illustration: the quotient objects of a group *)

(* The general lemma this file needs -- two quotient objects are
   equivalent when an isomorphism of their codomains carries one epi to
   the other -- is Theory/Subobject/Quotient.v's [quot_equiv_of_cod_iso].
   It was first proved HERE during the parallel build (as
   [grp_quot_equiv_of_cod_iso], directly by [Isomorphism_Opposite
   (iso_sym i)]) and was lifted into that file at integration as a
   corollary of [quot_equiv_iff_iso]; this file now consumes it.  The
   orientation is still the trap: [SubObj_Setoid] at [C^op] asks for an
   isomorphism IN [C^op], whose [to] is a [C]-arrow the other way round,
   so the [C]-isomorphism handed in goes from the codomain of r to the
   codomain of q. *)

(* Instance/Grp/Quotient.v's [QuotientGrp N] with its projection, which
   is epic because it is the identity function on
   the carrier.  This is the whole of Mac Lane's example in one line. *)
Definition grp_quot_of_normal {G : GrpObject} (N : NormalSubgroup G) :
  @QuotObj Grp G :=
  mk_quot (quot_proj N) (quot_proj_epic N).

(* The order, in the direction the factorization preorder gives it: a
   LARGER normal subgroup gives a SMALLER (coarser) quotient object.
   The mediating arrow is the identity function, and its respectfulness
   clause is exactly the inclusion of members. *)
Lemma grp_quot_le_of_included {G : GrpObject} (N N' : NormalSubgroup G)
  (H : ∀ a : carrier G, sub_mem N a → sub_mem N' a) :
  @quot_le Grp G (grp_quot_of_normal N') (grp_quot_of_normal N).
Proof.
  unshelve eexists.
  - unshelve refine {| grp_map := {| morphism :=
      fun a : carrier (QuotientGrp N) => a : carrier (QuotientGrp N') |} |}.
    (* The quotient's `≈` is the truncation of [quot_rel] since the PR
       "algebraic carriers are sets" (2026-09-17): the inclusion is applied
       under it, [Prop] to [Prop]. *)
    + intros a b Hab.
      change (inhabited (quot_rel N a b)) in Hab.
      change (inhabited (quot_rel N' a b)).
      destruct Hab as [Hab]; exact (inhabits (H _ Hab)).
    + simpl; constructor; apply quot_rel_refl.
    + intros a b; simpl; constructor; apply quot_rel_refl.
  - intro a; simpl; constructor; apply quot_rel_refl.
Defined.

(** ** The converse, and the hypothesis it costs *)

Section Converse.

Context {G : GrpObject}.

(* In [Grp] a surjection is epic unconditionally
   (Instance/Grp/Epi.v) but the converse is not available
   constructively: [grp_epic_image_dense] gives only that no
   element can be SHOWN to miss the image, and Instance/Grp/Epi.v's
   header sets out why -- recovering a preimage from an epimorphism is
   the double-negation elimination its [GrpImageStable] names.
   So the theorem below is stated for a quotient object whose epi is
   surjective, and the [Epic]-only form is recorded separately as the
   conditional [grp_quot_is_quot_by_kernel_stable]. *)
Definition grp_quot_surjective_of_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  GrpSurjective (quot_epi q) :=
  grp_epic_is_surjective (quot_epi q) Hst (quot_is_epic q).

(* The comparison: G/ker e ≅ im e ≅ Q, the first isomorphism theorem
   (Instance/Grp/Quotient/Isomorphism.v) followed by the
   identification of the image with the codomain of a surjection. *)
Definition grp_quot_kernel_iso (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  QuotientGrp (KernelNS (quot_epi q)) ≅[Grp] quot_cod q :=
  iso_compose (surjective_image_iso (quot_epi q) Hs)
              (first_isomorphism_theorem (quot_epi q)).

(* ... and it carries the projection to the quotient epi, which is what
   makes it an equivalence OF QUOTIENT OBJECTS and not merely an
   isomorphism of codomains.  The two triangles are
   [first_isomorphism_triangle] and [image_factors]. *)
Lemma grp_quot_kernel_triangle (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  to (grp_quot_kernel_iso q Hs) ∘ quot_proj (KernelNS (quot_epi q))
    ≈ quot_epi q.
Proof.
  change (to (surjective_image_iso (quot_epi q) Hs)
            ∘ to (first_isomorphism_theorem (quot_epi q))
            ∘ quot_proj (KernelNS (quot_epi q)) ≈ quot_epi q).
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle (quot_epi q)).
  exact (image_factors (quot_epi q)).
Qed.

(* Mac Lane §V.7: the quotient objects of a group ARE the G/N.  Stated
   at ≈ on [QuotObj G], which is the strongest relation available --
   [QuotObj] inherits [SubObj]'s setoid and has no Leibniz
   antisymmetry. *)
Theorem grp_quot_is_quot_by_kernel (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (quot_equiv_of_cod_iso q
           (grp_quot_of_normal (KernelNS (quot_epi q)))
           (grp_quot_kernel_iso q Hs) (grp_quot_kernel_triangle q Hs)).
Qed.

(* The same statement with the stability hypothesis in place of
   surjectivity, so that the cost of the classical reading is visible in
   the type rather than hidden in a side condition. *)
Theorem grp_quot_is_quot_by_kernel_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (grp_quot_is_quot_by_kernel q (grp_quot_surjective_of_stable q Hst)).
Qed.

End Converse.

(** ** Non-vacuity *)

(* The correspondence is inhabited at a nondegenerate pair: A3 inside S3
   (Instance/Grp/Quotient.v) is a proper nontrivial normal subgroup
   of a nonabelian group, so [grp_quot_of_normal A3] is a quotient object
   of S3 that is neither the top nor the bottom of the order.  The two
   separations are Instance/Grp/Quotient.v's [S3_mod_A3_not_collapsed]
   and [quot_proj_A3_not_injective]; [grp_quot_S3_A3_not_collapsed]
   below is a verbatim RE-EXPORT of the first under a name that says
   what it is used for, and proves nothing new -- the constant that
   carries new content here is [grp_quot_S3_A3] itself and the order
   inhabitant [grp_quot_S3_trivial_le_A3]. *)
Definition grp_quot_S3_A3 : @QuotObj Grp S3 := grp_quot_of_normal A3.

Lemma grp_quot_S3_A3_not_collapsed :
  quot_rel A3 S3_s s3_unit → False.
Proof. exact (S3_mod_A3_not_collapsed). Qed.

(* The trivial normal subgroup sits below A3, so the identity quotient is
   above it in the factorization order -- the order lemma, inhabited. *)
Lemma grp_quot_S3_trivial_le_A3 :
  @quot_le Grp S3 (grp_quot_of_normal A3) (grp_quot_of_normal (TrivialNS S3)).
Proof. exact (grp_quot_le_of_included (TrivialNS S3) A3 trivial_in_A3). Qed.
