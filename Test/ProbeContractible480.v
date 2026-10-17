(*
   本文件为测试：ProbeContractible480。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Contractible.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Lift.
Require Import Category.Structure.Coequalizer.Absolute.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p480_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** (b) after (a): a split fork, through Mac Lane's Lemma, and back *)

Section FromSplit.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context (S : SplitCoequalizer f g).

(* C1: the object comes back on the nose. *)
Example p480_c1_split_round_obj :
  scoeq_obj (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_obj S := eq_refl.

(* C2: so does e. *)
Example p480_c2_split_round_e :
  scoeq_e (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_e S := eq_refl.

(* C3: so does t. *)
Example p480_c3_split_round_t :
  scoeq_t (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_t S := eq_refl.

(* R1 *)
Fail Example p480_r1_split_round_s :
  scoeq_s (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    = scoeq_s S := eq_refl.

(* C4: s comes back up to ≈, by the uniqueness of the descent. *)
Definition p480_c4_split_round_s :
  scoeq_s (every_coequalizer_split S (split_coequalizer_is_coequalizer f g S))
    ≈ scoeq_s S :=
  contractible_coequalizer_split_s_unique (split_coequalizer_contractible S)
    (split_coequalizer_is_coequalizer f g S) (scoeq_s S) (scoeq_law4 S).

End FromSplit.

(* ------------------------------------------------------------------------ *)
(** ** (a) after (b): a contraction, through a coequalizer, and back *)

Section FromContractible.

Context {C : Category} {x y : C} {f g : x ~> y}.
Context (P : ContractiblePair f g) {q : C} {e : y ~> q}.
Context (E : IsCoequalizer f g q e).

(* C5: the contraction comes back on the nose. *)
Example p480_c5_contr_round_t :
  contr_t (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_t P := eq_refl.

(* C6: so does the proof of the first equation. *)
Example p480_c6_contr_round_section :
  contr_section
    (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_section P := eq_refl.

(* R2 *)
Fail Example p480_r2_contr_round_cofork :
  contr_cofork
    (split_coequalizer_contractible (contractible_coequalizer_split P E))
    = contr_cofork P := eq_refl.

End FromContractible.

(* ------------------------------------------------------------------------ *)
(** ** Restatements of the target's readbacks *)

Section Readbacks.

Context {C : Category} {x y : C} {f g : x ~> y}.

(* C7: (a)'s t is the split fork's t. *)
Example p480_c7_a_t (S : SplitCoequalizer f g) :
  contr_t (split_coequalizer_contractible S) = scoeq_t S := eq_refl.

Context {q : C} {e : y ~> q}.

(* C8: (b)'s object is the coequalizer's. *)
Example p480_c8_b_obj (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_obj (contractible_coequalizer_split P E) = q := eq_refl.

(* C9: (b)'s e is the coequalizing arrow. *)
Example p480_c9_b_e (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_e (contractible_coequalizer_split P E) = e := eq_refl.

(* C10: (b)'s s is the descent of g ∘ t. *)
Example p480_c10_b_s (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_s (contractible_coequalizer_split P E)
    = unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) := eq_refl.

(* C11: (b)'s t is the contraction. *)
Example p480_c11_b_t (P : ContractiblePair f g)
  (E : IsCoequalizer f g q e) :
  scoeq_t (contractible_coequalizer_split P E) = contr_t P := eq_refl.

(* C12: every coequalizer of a split pair is split on its own arrow. *)
Example p480_c12_every_e (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_e (every_coequalizer_split S E) = e := eq_refl.

(* C25: ... and on its own object. *)
Example p480_c25_every_obj (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_obj (every_coequalizer_split S E) = q := eq_refl.

(* C26: ... by the given split fork's t. *)
Example p480_c26_every_t (S : SplitCoequalizer f g)
  (E : IsCoequalizer f g q e) :
  scoeq_t (every_coequalizer_split S E) = scoeq_t S := eq_refl.

End Readbacks.

(* C13: a functor's image of a contraction is contracted by F t. *)
Example p480_c13_functor_t {C D : Category} (F : C ⟶ D) {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) :
  contr_t (functor_preserves_contractible F f g P) = fmap[F] (contr_t P)
  := eq_refl.

Section Idempotent.

Context {C : Category} {x : C} (i : x ~> x) (I : Idempotent i).
Context {q : C} {r : x ~> q} (E : IsCoequalizer id i q r).

(* C27: a coequalizer of (1, i) splits i itself ... *)
Example p480_c27_idem_idem :
  @split_idem C x q (coequalizer_splits_idempotent i I E) = i := eq_refl.

(* C28: ... through the coequalizer r. *)
Example p480_c28_idem_r :
  @split_idem_r C x q (coequalizer_splits_idempotent i I E) = r := eq_refl.

End Idempotent.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the targets' hom levels may lie strictly above C's *)

(* C14: absoluteness at a target hom level strictly above C's. *)
Definition p480_c14_absolute_above@{co ch xo xh + | ch < xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e :=
  contractible_coequalizer_absolute P E.

(* C15: a functor into a category whose hom level is strictly above C's. *)
Definition p480_c15_functor_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} {f g : x ~> y} (P : ContractiblePair f g) :
  ContractiblePair (fmap[F] f) (fmap[F] g) :=
  functor_preserves_contractible F f g P.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the targets, by name *)

Check @Category.Structure.Coequalizer.Contractible.ContractiblePair.
Check @Category.Structure.Coequalizer.Contractible.contr_t.
Check @Category.Structure.Coequalizer.Contractible.contr_section.
Check @Category.Structure.Coequalizer.Contractible.contr_cofork.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_contractible.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_contractible_t.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_obj.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_e.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_s.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_t.
Check @Category.Structure.Coequalizer.Contractible.contractible_coequalizer_split_s_unique.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_obj.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_e.
Check @Category.Structure.Coequalizer.Contractible.every_coequalizer_split_t.
Check @Category.Structure.Coequalizer.Contractible.split_coequalizer_iff_contractible.
Check @Category.Structure.Coequalizer.Contractible.idempotent_contractible.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent_idem.
Check @Category.Structure.Coequalizer.Contractible.coequalizer_splits_idempotent_r.
Check @Category.Structure.Coequalizer.Contractible.functor_preserves_contractible.
Check @Category.Structure.Coequalizer.Contractible.functor_preserves_contractible_t.
Check @Category.Structure.Coequalizer.Absolute.contractible_coequalizer_absolute.

(* ------------------------------------------------------------------------ *)
(** ** A reflexive pair with a coequalizer that is not contractible *)

(*
   本节说明 ProbeContractible480 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Coequalizer.

(* C16: the common section of #479's reflexive pair at Z/4 over {0, 2} is
   #479's [semidirect_refl], x ↦ ⟨x, 0⟩, 0 being the subgroup's unit. *)
Example p480_c16_z4_section (a : carrier Z4) :
  grp_map (refl_section (semidirect_reflexive Z4_two)) a
    = (a, snd (sdp_unit Z4_two)) := eq_refl.

(* C17: so Mac Lane's pair is reflexive, by #479's [semidirect_reflexive]. *)
Definition p480_c17_z4_reflexive :
  ReflexivePair (semidirect_d0 Z4_two) (semidirect_d1 Z4_two) :=
  semidirect_reflexive Z4_two.

(* C18: it has a coequalizer, the projection onto Z/4 / {0, 2} (#479). *)
Definition p480_c18_z4_coequalizer :
  IsCoequalizer (semidirect_d0 Z4_two) (semidirect_d1 Z4_two)
    (QuotientGrp Z4_two) (quot_proj Z4_two) :=
  quot_proj_IsCoequalizer Z4_two.

(* C19: and it is not contractible: by (b) its coequalizer would split,
   which #479 refutes. *)
Definition p480_c19_z4_not_contractible :
  ContractiblePair (semidirect_d0 Z4_two) (semidirect_d1 Z4_two) → False :=
  fun P => Z4_two_not_split_in_Grp
             (contractible_coequalizer_split P p480_c18_z4_coequalizer).

(* C24: C19's positive control: the pair at A₃ ◁ S₃, which #479 splits in
   Grp, is contractible, by (a). *)
Definition p480_c24_a3_contractible :
  ContractiblePair (semidirect_d0 A3) (semidirect_d1 A3) :=
  split_coequalizer_contractible S3_A3_Grp_split.

(* ------------------------------------------------------------------------ *)
(** ** A contractible pair with no coequalizer, and not reflexive *)

(* Required here, after every other command; the lines
   Instance/Presented/Cyclic.v adds to the lists above, and that
   module. *)
Require Import Category.Lib.TList.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Construction.Deloop.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Presented.Cyclic.

(* C20: in Awodey's one-object category of the idempotent s ∘ s = s,
   the pair (1, s) is contracted by 1. *)
Definition p480_c20_idem_contractible :
  @ContractiblePair IdemCat ttt ttt id (spath 1) :=
  @idempotent_contractible IdemCat ttt (spath 1)
    (@Build_Idempotent IdemCat ttt (spath 1) idem_rel).

(* C21: and it has no coequalizer: one would split s through it, with
   e ∘ s' ≈ 1 and s' ∘ e ≈ s, and the arrows are 1 and s alone. *)
Theorem p480_c21_idem_no_coequalizer (q : IdemCat) (e : ttt ~{IdemCat}~> q) :
  @IsCoequalizer IdemCat ttt ttt id (spath 1) q e → False.
Proof.
  destruct q.
  intro E.
  pose (S := @coequalizer_splits_idempotent IdemCat ttt (spath 1)
               (@Build_Idempotent IdemCat ttt (spath 1) idem_rel) ttt e E).
  pose proof (@split_idem_rs _ _ _ S) as L2.
  pose proof (@split_idem_sr _ _ _ S) as L4.
  change (e ∘ @split_idem_s _ _ _ S ≈ id) in L2.
  change (@split_idem_s _ _ _ S ∘ e ≈ spath 1) in L4.
  destruct (idem_exhaust e) as [re [Hre He]].
  destruct (idem_exhaust (@split_idem_s _ _ _ S)) as [rs [Hrs Hs]].
  rewrite He, Hs in L2.
  rewrite He, Hs in L4.
  destruct re as [|[|re]]; [ | | lia ];
  destruct rs as [|[|rs]]; [ | | lia | | | lia ];
  [ apply (rho_nf_of_spath_eq 1 1 0 1) in L4
  | apply (rho_nf_of_spath_eq 1 1 1 0) in L2
  | apply (rho_nf_of_spath_eq 1 1 1 0) in L2
  | apply (rho_nf_of_spath_eq 1 1 2 0) in L2 ];
  discriminate.
Qed.

(* C22: nor is (1, s) reflexive: a common section r would have
   s ∘ r ≈ 1, and the arrows are 1 and s alone. *)
Theorem p480_c22_idem_not_reflexive :
  @ReflexivePair IdemCat ttt ttt id (spath 1) → False.
Proof.
  intros R.
  pose proof (refl_section_f R) as Hf.
  pose proof (refl_section_g R) as Hg.
  destruct (idem_exhaust (refl_section R)) as [rr [Hrr Hr]].
  rewrite Hr in Hf, Hg.
  destruct rr as [|[|rr]]; [ | | lia ];
  [ apply (rho_nf_of_spath_eq 1 1 1 0) in Hg
  | apply (rho_nf_of_spath_eq 1 1 1 0) in Hf ];
  discriminate.
Qed.

(* C23: C21's positive control: (s, s) has a coequalizer there, 1. *)
Definition p480_c23_idem_ss_coequalizer :
  @IsCoequalizer IdemCat ttt ttt (spath 1) (spath 1) ttt id.
Proof.
  unshelve econstructor.
  - reflexivity.
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact h.
    + apply id_right.
    + intros v Hv.
      rewrite <- Hv.
      rewrite id_right.
      reflexivity.
Defined.
