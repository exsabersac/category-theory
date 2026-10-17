Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Kernel.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/cokernel
 Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The trivial homomorphism computes *)

(*
   本节说明 Colimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_zero_mor_is_unit {G K : GrpObject} (a : carrier G) :
  grp_map (@zero_mor Grp Grp_Zero G K) a ≈ grp_unit K.
Proof. simpl; reflexivity. Qed.

(** ** G/N as the coequalizer of N ↪ G against the trivial map *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The cofork equation: the projection cannot tell the inclusion from the
   trivial map, because every member of N is projected to the unit. *)
Lemma quot_cofork {G : GrpObject} (N : NormalSubgroup G) :
  quot_proj N ∘ sub_incl N ≈ quot_proj N ∘ @zero_mor Grp Grp_Zero _ _.
Proof.
  intro p; simpl.
  unfold Basics.compose.
  (* The quotient's `≈` is the truncation of [quot_rel] since the PR
     "algebraic carriers are sets" (2026-09-17), so the witness is wrapped. *)
  constructor.
  apply (snd (quot_rel_unit_iff N (`1 p))).
  exact (`2 p).
Qed.

(* Descent: a homomorphism coforking the pair is exactly one that kills N,
   and [hom_theorem] then supplies the unique factorization.  Nothing here
   is a new argument. *)
Lemma quot_coeq_desc {G : GrpObject} (N : NormalSubgroup G)
  {Z : GrpObject} (h : G ~{Grp}~> Z)
  (Hh : h ∘ sub_incl N ≈ h ∘ @zero_mor Grp Grp_Zero _ _) :
  ∃! u : QuotientGrp N ~{Grp}~> Z, u ∘ quot_proj N ≈ h.
Proof.
  apply (hom_theorem_factor N h).
  intros a Ha.
  pose proof (Hh (existT _ a Ha)) as E; simpl in E.
  unfold Basics.compose in E.
  rewrite E.
  apply (grp_map_unit h).
Qed.

Definition quot_IsCoequalizer {G : GrpObject} (N : NormalSubgroup G) :
  IsCoequalizer (sub_incl N) (@zero_mor Grp Grp_Zero _ _)
                (QuotientGrp N) (quot_proj N).
Proof.
  unshelve refine {| cofork := _ |}.
  - exact (quot_cofork N).
  - exact (fun Z h Hh => quot_coeq_desc N h Hh).
Defined.

(* Awodey's colimit presentation, in the vocabulary of
   Structure/Kernel.v: the projection is the cokernel of the inclusion. *)
Definition quot_IsCokernel {G : GrpObject} (N : NormalSubgroup G) :
  @IsCokernel Grp Grp_Zero _ _ _ (sub_incl N) (quot_proj N) :=
  quot_IsCoequalizer N.

(* Consequences, applied rather than reproved. *)
Definition quot_proj_cokernel_epic {G : GrpObject} (N : NormalSubgroup G) :
  Epic (quot_proj N) := cokernel_epic (quot_IsCokernel N).

Definition quot_proj_normal_epi {G : GrpObject} (N : NormalSubgroup G) :
  normal_epi (quot_proj N) :=
  existT _ (SubgroupGrp N) (existT _ (sub_incl N) (quot_IsCokernel N)).

Definition quot_proj_regular_epi {G : GrpObject} (N : NormalSubgroup G) :
  RegularEpi (quot_proj N) := cokernel_regular_epi (quot_IsCokernel N).

(** ** Riehl Example 3.1.25: the normal closure of an image *)

(*
   本节说明 Colimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive InNormalClosure {G H : GrpObject} (f : G ~{Grp}~> H)
  : carrier H → Type :=
  | nc_gen (a : carrier G) : InNormalClosure (grp_map f a)
  | nc_unit : InNormalClosure (grp_unit H)
  | nc_mul (a b : carrier H) :
      InNormalClosure a → InNormalClosure b →
      InNormalClosure (grp_mul H a b)
  | nc_inv (a : carrier H) :
      InNormalClosure a → InNormalClosure (grp_inv H a)
  | nc_conj (t a : carrier H) :
      InNormalClosure a →
      InNormalClosure (grp_mul H (grp_mul H t a) (grp_inv H t))
  | nc_resp (a b : carrier H) :
      a ≈ b → InNormalClosure a → InNormalClosure b.

Arguments nc_gen {G H f} a.
Arguments nc_unit {G H f}.
Arguments nc_mul {G H f a b} _ _.
Arguments nc_inv {G H f a} _.
Arguments nc_conj {G H f} t {a} _.
Arguments nc_resp {G H f a b} _ _.

Program Definition NormalClosure {G H : GrpObject} (f : G ~{Grp}~> H) :
  NormalSubgroup H := {|
  ns_sub := {| sub_mem := InNormalClosure f |}
|}.
Next Obligation. intros G H f a b Hab Ha; exact (nc_resp Hab Ha). Qed.
Next Obligation. intros G H f; exact nc_unit. Qed.
Next Obligation. intros G H f a b Ha Hb; exact (nc_mul Ha Hb). Qed.
Next Obligation. intros G H f a Ha; exact (nc_inv Ha). Qed.
Next Obligation. intros G H f t a Ha; exact (nc_conj t Ha). Qed.

(* The closure contains the image. *)
Lemma normal_closure_contains_image {G H : GrpObject} (f : G ~{Grp}~> H)
  (a : carrier G) : sub_mem (NormalClosure f) (grp_map f a).
Proof. exact (nc_gen a). Qed.

(*
   本节说明 Colimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma normal_closure_least {G H : GrpObject} (f : G ~{Grp}~> H)
  (P : NormalSubgroup H)
  (Hgen : ∀ a : carrier G, sub_mem P (grp_map f a))
  (x : carrier H) : sub_mem (NormalClosure f) x → sub_mem P x.
Proof.
  intro Hx; induction Hx as
    [ a | | a b Ha IHa Hb IHb | a Ha IHa | t a Ha IHa | a b Hab Ha IHa ].
  - exact (Hgen a).
  - exact (sub_unit P).
  - exact (sub_mul P _ _ IHa IHb).
  - exact (sub_inv P _ IHa).
  - exact (ns_conj P t _ IHa).
  - exact (sub_resp P _ _ Hab IHa).
Qed.

(* A homomorphism killing the image kills the whole closure: the same
   induction, and the descent step of the cokernel below. *)
Lemma normal_closure_killed {G H Z : GrpObject} (f : G ~{Grp}~> H)
  (h : H ~{Grp}~> Z)
  (Hgen : ∀ a : carrier G, grp_map h (grp_map f a) ≈ grp_unit Z)
  (x : carrier H) :
  sub_mem (NormalClosure f) x → grp_map h x ≈ grp_unit Z.
Proof.
  exact (normal_closure_least f (KernelNS h) Hgen x).
Qed.

Lemma normal_closure_cofork {G H : GrpObject} (f : G ~{Grp}~> H) :
  quot_proj (NormalClosure f) ∘ f
    ≈ quot_proj (NormalClosure f) ∘ @zero_mor Grp Grp_Zero _ _.
Proof.
  intro a; simpl.
  unfold Basics.compose.
  (* One [constructor] for the truncation, as in [quot_cofork] above. *)
  constructor.
  apply (snd (quot_rel_unit_iff (NormalClosure f) (grp_map f a))).
  exact (nc_gen a).
Qed.

Lemma normal_closure_coeq_desc {G H : GrpObject} (f : G ~{Grp}~> H)
  {Z : GrpObject} (h : H ~{Grp}~> Z)
  (Hh : h ∘ f ≈ h ∘ @zero_mor Grp Grp_Zero _ _) :
  ∃! u : QuotientGrp (NormalClosure f) ~{Grp}~> Z,
    u ∘ quot_proj (NormalClosure f) ≈ h.
Proof.
  apply (hom_theorem_factor (NormalClosure f) h).
  apply (normal_closure_killed f h).
  intro a.
  pose proof (Hh a) as E; simpl in E.
  unfold Basics.compose in E.
  rewrite E.
  apply (grp_map_unit h).
Qed.

(* Riehl's Example 3.1.25, in full: the coequalizer of φ with the trivial
   homomorphism is H modulo the normal closure of the image of φ. *)
Definition normal_closure_IsCoequalizer {G H : GrpObject} (f : G ~{Grp}~> H) :
  IsCoequalizer f (@zero_mor Grp Grp_Zero _ _)
                (QuotientGrp (NormalClosure f)) (quot_proj (NormalClosure f)).
Proof.
  unshelve refine {| cofork := _ |}.
  - exact (normal_closure_cofork f).
  - exact (fun Z h Hh => normal_closure_coeq_desc f h Hh).
Defined.

Definition normal_closure_IsCokernel {G H : GrpObject} (f : G ~{Grp}~> H) :
  @IsCokernel Grp Grp_Zero _ _ _ f (quot_proj (NormalClosure f)) :=
  normal_closure_IsCoequalizer f.

Definition normal_closure_cokernel_epic {G H : GrpObject} (f : G ~{Grp}~> H) :
  Epic (quot_proj (NormalClosure f)) :=
  cokernel_epic (normal_closure_IsCokernel f).

(** ** The two presentations agree where they overlap *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma normal_closure_of_incl {G : GrpObject} (N : NormalSubgroup G)
  (x : carrier G) :
  sub_mem (NormalClosure (sub_incl N)) x ↔ sub_mem N x.
Proof.
  split.
  - apply (normal_closure_least (sub_incl N) N).
    intro p; exact (`2 p).
  - intro Hx.
    exact (@nc_gen _ _ (sub_incl N) (existT _ x Hx)).
Qed.

Definition quot_normal_closure_iso {G : GrpObject} (N : NormalSubgroup G) :
  QuotientGrp (NormalClosure (sub_incl N)) ≅[Grp] QuotientGrp N :=
  coequalizer_unique (sub_incl N) (@zero_mor Grp Grp_Zero _ _)
    (normal_closure_IsCoequalizer (sub_incl N)) (quot_IsCoequalizer N).

(** ** Non-vacuity at S3 *)

(* The cokernel of A3 ↪ S3 is the two-element quotient, so the cokernel
   witnesses above are not about a collapsed situation. *)
Definition S3_A3_IsCokernel :
  @IsCokernel Grp Grp_Zero _ _ _ (sub_incl A3) (quot_proj A3) :=
  quot_IsCokernel A3.

(* The hypothesis is the truncation since the PR "algebraic carriers are
   sets" (2026-09-17); the goal is [False], so it is unwrapped at no cost. *)
Theorem S3_A3_cokernel_nondegenerate :
  grp_map (quot_proj A3) S3_s ≈ grp_map (quot_proj A3) (grp_unit S3) → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
   本节说明 Colimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition S3_refl_incl : SubgroupGrp S3_refl_sub ~{Grp}~> S3 :=
  sub_incl S3_refl_sub.

Definition S3_refl_gen : carrier (SubgroupGrp S3_refl_sub) :=
  existT _ S3_s (eq_refl : fst S3_s = rot0).

Theorem S3_refl_closure_contains_rotation :
  sub_mem (NormalClosure S3_refl_incl) S3_r.
Proof.
  apply (sub_at (NormalClosure S3_refl_incl)
           (a := grp_mul S3 (grp_map S3_refl_incl S3_refl_gen)
                   (grp_mul S3
                      (grp_mul S3 S3_r (grp_map S3_refl_incl S3_refl_gen))
                      (grp_inv S3 S3_r)))).
  - vm_compute; reflexivity.
  - exact (nc_mul (nc_gen S3_refl_gen) (nc_conj S3_r (nc_gen S3_refl_gen))).
Qed.

(* And r is NOT in the subgroup, so the closure is strictly larger. *)
Theorem S3_refl_sub_lacks_rotation : sub_mem S3_refl_sub S3_r → False.
Proof. simpl; discriminate. Qed.

(*
   本节说明 Colimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_trivial_closure_not_collapsed :
  sub_mem (NormalClosure (sub_incl (TrivialNS S3))) S3_s → False.
Proof.
  intro Hs.
  pose proof (fst (normal_closure_of_incl (TrivialNS S3) S3_s) Hs) as E.
  simpl in E.
  discriminate E.
Qed.

(* Whereas the normal closure of the identity of S3 is all of S3, and that
   cokernel does collapse -- the far end of the construction's range. *)
Theorem S3_total_closure_collapses (a b : carrier S3) :
  quot_rel (NormalClosure (@id Grp S3)) a b.
Proof. exact (nc_gen (grp_mul S3 a (grp_inv S3 b))). Qed.
