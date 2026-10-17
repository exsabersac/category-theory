(* * * Coextension scalars: 右伴随 R-Mod → Ab （已译） *)

(*
 Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
 Book:      Riehl, "Category Theory in Context", Dover 2016, §4.1
 nLab:      https://ncatlab.org/nlab/show/coextension+of+scalars
 nLab:      https://ncatlab.org/nlab/show/restriction+of+scalars
 Wikipedia: https://en.wikipedia.org/wiki/Change_of_rings

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Adjunction.Additive.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section Coextension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation RG := (ring_ab R).

Definition coex_group (A : AbObject) : AbObject :=
  hom_ab Ab_AbEnriched RG A.

Example coex_group_carrier (A : AbObject) :
  carrier (cmon_setoid (coex_group A)) = (RG ~{Ab}~> A) := eq_refl.

Example coex_group_plus (A : AbObject) :
  cmon_plus (coex_group A) = @ab_hom_add RG A := eq_refl.

Example coex_group_zero (A : AbObject) :
  cmon_zero (coex_group A) = @ab_hom_zero RG A := eq_refl.

(* * ** The scalar action: translation ring 论元 （已译） *)

Program Definition coex_act (A : AbObject) (r : RS) (f : AbHom RG A) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s =>
    cmon_map f (rig_mul (ring_rig R) s r) |}
|}.
Next Obligation.
  intros A r f s s' Hs.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_respects (ring_rig R) s s' Hs r r (reflexivity r))).
Qed.
Next Obligation.
  intros A r f; simpl.
  transitivity (cmon_map f (rig_zero (ring_rig R))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_zero_l (ring_rig R) r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A r f s s'; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s' r))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_r (ring_rig R) s s' r)).
  - exact (cmon_map_plus f _ _).
Qed.

Example coex_act_at (A : AbObject) (r s : RS) (f : AbHom RG A) :
  cmon_map (coex_act A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(** ** The four module laws *)

Lemma coex_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (coex_act A).
Proof.
  intros r r' Hr f g Hfg s; simpl.
  transitivity (cmon_map f (rig_mul (ring_rig R) s r')).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_respects (ring_rig R) s s (reflexivity s) r r' Hr)).
  - exact (Hfg _).
Qed.

Lemma coex_act_distr_l (A : AbObject) (r : RS) (f g : AbHom RG A) :
  coex_act A r (cmon_plus (coex_group A) f g)
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r g).
Proof. intro s; reflexivity. Qed.

Lemma coex_act_distr_r (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r' f).
Proof.
  intro s; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s r'))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_l (ring_rig R) s r r')).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma coex_act_assoc (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_mul (ring_rig R) r r') f
    ≈ coex_act A r (coex_act A r' f).
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (symmetry (rig_mul_assoc (ring_rig R) s r r'))).
Qed.

Lemma coex_act_one (A : AbObject) (f : AbHom RG A) :
  coex_act A (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_one_r (ring_rig R) s)).
Qed.

Definition CoextObj (A : AbObject) : RModObject R := {|
  rm_ab            := coex_group A;
  rm_smul          := coex_act A;
  rm_smul_respects := coex_act_respects A;
  rm_smul_distr_l  := coex_act_distr_l A;
  rm_smul_distr_r  := coex_act_distr_r A;
  rm_smul_assoc    := coex_act_assoc A;
  rm_smul_one      := coex_act_one A
|}.

(* * ** The arrow action: postcomposition, 函子 （已译） *)

Program Definition coex_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (coex_group A) (coex_group B) := {|
  cmon_map := {| morphism := fun phi =>
    (cmon_hom_compose f phi : AbHom RG B) |}
|}.
Next Obligation.
  intros A B f phi phi' Hphi s; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hphi s)).
Qed.
Next Obligation.
  intros A B f s; simpl.
  exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f phi psi s; simpl.
  exact (cmon_map_plus f _ _).
Qed.

Example coex_map_at {A B : AbObject} (f : AbHom A B)
  (phi : AbHom RG A) (s : RS) :
  cmon_map (cmon_map (coex_map_ab f) phi) s
    = cmon_map f (cmon_map phi s) := eq_refl.

Program Definition CoextMap {A B : AbObject} (f : AbHom A B) :
  CoextObj A ~{RMod R}~> CoextObj B := {|
  rm_hom := coex_map_ab f
|}.
Next Obligation. intros A B f r phi s; reflexivity. Qed.

Program Definition Coextension : Ab ⟶ RMod R := {|
  fobj := CoextObj;
  fmap := @CoextMap
|}.
Next Obligation.
  intros A B f g Hfg phi s; simpl.
  exact (Hfg _).
Qed.
Next Obligation. intros A phi s; reflexivity. Qed.
Next Obligation. intros A B C f g phi s; reflexivity. Qed.

(** ** The two transposes *)

Program Definition coex_to_inner {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s => cmon_map g (rm_smul M s m) |}
|}.
Next Obligation.
  intros A M g m s s' Hs.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s' Hs m m (reflexivity m))).
Qed.
Next Obligation.
  intros A M g m; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_l M m)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m s s'; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s' m))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_r M s s' m)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to_ab {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : AbHom (rm_ab M) (coex_group A) := {|
  cmon_map := {| morphism := fun m => coex_to_inner g m |}
|}.
Next Obligation.
  intros A M g m m' Hm s; simpl.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s (reflexivity s) m m' Hm)).
Qed.
Next Obligation.
  intros A M g s; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_r M s)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m n s; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s n))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_l M s m n)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : M ~{RMod R}~> CoextObj A := {|
  rm_hom := coex_to_ab g
|}.
Next Obligation.
  intros A M g r m s; simpl.
  symmetry.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_assoc M s r m)).
Qed.

Program Definition coex_from {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A) : AbHom (rm_ab M) A := {|
  cmon_map := {| morphism := fun m =>
    cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) |}
|}.
Next Obligation.
  intros A M h m m' Hm.
  exact (proper_morphism (cmon_map (rm_hom h)) m m' Hm
           (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h; simpl.
  exact (cmon_map_zero (rm_hom h) (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h m n; simpl.
  exact (cmon_map_plus (rm_hom h) m n (rig_one (ring_rig R))).
Qed.

Example coex_to_at {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M)))
  (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_to g)) m) s
    = cmon_map g (rm_smul M s m) := eq_refl.

Example coex_from_at {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (coex_from h) m
    = cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) := eq_refl.

(* * ** The hom-set bijection 伴随 （已译） *)

Program Definition coex_adj_to (M : RModObject R) (A : AbObject) :
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |}
    ~{Sets}~>
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  morphism := fun g => coex_to g
|}.
Next Obligation. intros M A g g' Hg m s; exact (Hg _). Qed.

Program Definition coex_adj_from (M : RModObject R) (A : AbObject) :
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |}
    ~{Sets}~>
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |} := {|
  morphism := fun h => coex_from h
|}.
Next Obligation. intros M A h h' Hh m; exact (Hh m _). Qed.

Program Definition coex_adj (M : RModObject R) (A : AbObject) :
  @Isomorphism Sets
    {| carrier := rm_ab M ~{Ab}~> A;
       is_setoid := @homset Ab (rm_ab M) A |}
    {| carrier := M ~{RMod R}~> CoextObj A;
       is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  to   := coex_adj_to M A;
  from := coex_adj_from M A
|}.
Next Obligation.
  intros M A h m s; simpl.
  transitivity (cmon_map (coex_act A s (cmon_map (rm_hom h) m))
                  (rig_one (ring_rig R))).
  - exact (rm_map_smul h s m (rig_one (ring_rig R))).
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom h) m)) _ _
             (rig_mul_one_l (ring_rig R) s)).
Qed.
Next Obligation.
  intros M A g m; simpl.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_one M m)).
Qed.

Definition coex_adjunction : RMod_Forget_Ab R ⊣ Coextension.
Proof.
  unshelve eapply (@Build_Adjunction' Ab (RMod R) (RMod_Forget_Ab R)
                     Coextension coex_adj).
  - intros M N A f g m s; simpl.
    exact (proper_morphism (cmon_map f) _ _ (rm_map_smul g s m)).
  - intros M A B f g m s; reflexivity.
Defined.

(* 相关说明。 （已译） *)

Definition coex_unit (M : RModObject R) :
  M ~{RMod R}~> CoextObj (rm_ab M) :=
  @unit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction M.

Definition coex_counit (A : AbObject) :
  rm_ab (CoextObj A) ~{Ab}~> A :=
  @counit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction A.

(* 相关说明。 （已译） *)
Example coex_counit_is_eval_at_one (A : AbObject) (phi : AbHom RG A) :
  cmon_map (coex_counit A) phi
    = cmon_map phi (rig_one (ring_rig R)) := eq_refl.

Example coex_unit_is_smul (M : RModObject R)
  (m : carrier (cmon_setoid (rm_ab M))) (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_unit M)) m) s = rm_smul M s m
  := eq_refl.

Example coex_adj_to_is_coex_to (M : RModObject R) (A : AbObject)
  (g : rm_ab M ~{Ab}~> A) :
  to (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
        coex_adjunction M A) g = coex_to g := eq_refl.

Example coex_adj_from_is_coex_from (M : RModObject R) (A : AbObject)
  (h : M ~{RMod R}~> CoextObj A) :
  from (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
          coex_adjunction M A) h = coex_from h := eq_refl.

Example coex_fobj_is_CoextObj (A : AbObject) :
  fobj[Coextension] A = CoextObj A := eq_refl.

Example coex_fmap_is_CoextMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Coextension] f = CoextMap f := eq_refl.

Example coex_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End Coextension.

(** ** A concrete witness over ℤ *)

(** 本节：The coextension ℤ along ℤ: abelian group additive
 endomorphisms ℤ, made ℤ-module translation. （已译） *)
Definition CoextInt : RModObject Int_Ring :=
  CoextObj Int_Ring (ring_ab Int_Ring).

(** Multiplication by [n], obtained as the unit at [Int_RMod] rather
    than hand-built: [coex_unit] sends m to (s ↦ s · m). *)
Definition coex_int_mul (n : Z) :
  carrier (cmon_setoid (rm_ab CoextInt)) :=
  cmon_map (rm_hom (coex_unit Int_Ring Int_RMod)) n.

Example coex_int_mul_at (n s : Z) :
  cmon_map (coex_int_mul n) s = (s * n)%Z := eq_refl.

(** 本节：The comparison map out: evaluation at 1, counit. （已译） *)
Definition coex_int_eval :
  rm_ab CoextInt ~{Ab}~> ring_ab Int_Ring :=
  coex_counit Int_Ring (ring_ab Int_Ring).

Example coex_int_eval_computes :
  cmon_map coex_int_eval (coex_int_mul 3) = 3%Z := eq_refl.

Example coex_int_eval_zero :
  cmon_map coex_int_eval (cmon_zero (rm_ab CoextInt)) = 0%Z := eq_refl.

Example coex_int_act_computes :
  cmon_map coex_int_eval
    (rm_smul CoextInt 2%Z (coex_int_mul 3)) = 6%Z := eq_refl.

Lemma coex_int_nonzero : coex_int_mul 1 ≈ cmon_zero (rm_ab CoextInt) →
  False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

Lemma coex_int_muls_distinct : coex_int_mul 3 ≈ coex_int_mul 5 → False.
Proof.
  intro Hz.
  assert (Hev : (3%Z = 5%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(** The action is not trivial: 2 · (multiplication by 3) is not
    (multiplication by 3). *)
Lemma coex_int_act_nontrivial :
  rm_smul CoextInt 2%Z (coex_int_mul 3) ≈ coex_int_mul 3 → False.
Proof.
  intro Hz.
  assert (Hev : (6%Z = 3%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(*
   本节说明（余）端、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoexProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (g : rm_ab M ~{Ab}~> A) (h : M ~{RMod R}~> CoextObj R A).
Context (f f' : ring_ab R ~{Ab}~> A).
Context (m : carrier (cmon_setoid (rm_ab M))).
Context (r s : carrier (rig_setoid (ring_rig R))).

(* CONTROL negative 1: round trip DOES hold at ≈, 证明
 term names exact law closes gap. （已译） *)
Example coex_ctrl_from_to :
  cmon_map (coex_from R (coex_to R g)) m ≈ cmon_map g m
  := proper_morphism (cmon_map g) _ _ (rm_smul_one M m).

(* NEGATIVE 1 (CONVERSION).  [coex_from (coex_to g)] evaluates to
   g (1 · m), and 1 · − is not the identity by conversion:
   [rm_smul_one] is an abstract field of [RModObject], so neither side
   reduces and no downstream transparency would help. *)
Fail Example coex_probe_from_to_strict :
  cmon_map (coex_from R (coex_to R g)) m = cmon_map g m := eq_refl.

(* CONTROL for negative 2. *)
Example coex_ctrl_to_from :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    ≈ cmon_map (cmon_map (rm_hom h) m) s
  := iso_to_from (coex_adj R M A) h m s.

(* 相关说明。 （已译） *)
Fail Example coex_probe_to_from_strict :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    = cmon_map (cmon_map (rm_hom h) m) s := eq_refl.

(* 相关说明。 （已译） *)
Example coex_ctrl_handedness :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(*
   本节说明 Coextension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example coex_probe_handedness_swapped :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) r s) := eq_refl.

(* 相关说明。 （已译） *)
Example coex_ctrl_distr_l_pointwise :
  cmon_map (coex_act R A r (cmon_plus (coex_group R A) f f')) s
    = cmon_map (cmon_plus (coex_group R A)
                  (coex_act R A r f) (coex_act R A r f')) s := eq_refl.

(*
   本节说明 Coextension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example coex_probe_distr_l_record :
  coex_act R A r (cmon_plus (coex_group R A) f f')
    = cmon_plus (coex_group R A)
        (coex_act R A r f) (coex_act R A r f') := eq_refl.

(* 相关说明。 （已译） *)
Check (coex_counit R A : rm_ab (CoextObj R A) ~{Ab}~> A).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (coex_counit R A : CoextObj R A ~{RMod R}~> A).

(* CONTROL negative 6: 伴随 delivered. （已译） *)
Check (coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R).

(* NEGATIVE 6 (TYPING). The direction not negotiable: coextension is
 RIGHT adjoint, so forgetful 函子 sits left. （已译） *)
Fail Check (coex_adjunction R : Coextension R ⊣ RMod_Forget_Ab R).

End CoexProbeStrength.

(* 相关说明。 （已译） *)
Check (cmon_map coex_int_eval (coex_int_mul 3)).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example coex_probe_int_strict : CoextInt = Int_RMod := eq_refl.

Section CoexProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}) (Au Bu : AbObject).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (RMod Ru).
Check (ring_ab Ru).
Check (RMod_Forget_Ab Ru).
Check (hom_ab Ab_AbEnriched Au Bu).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).
Check (obj[RMod Ru]).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (AbHom (ring_ab Ru) Au).

(* 相关说明。 （已译） *)
Fail Check (ring_ab Ru : obj[Ab]).

(* NEGATIVE 10 (FORMABILITY).  Hence the scalar action. *)
Fail Check (coex_act Ru Au).

(* NEGATIVE 11 (FORMABILITY).  Hence the carrier. *)
Fail Check (coex_group Ru Au).

(*
   本节说明 Coextension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

(* NEGATIVE 13 (FORMABILITY).  Hence the functor. *)
Fail Check (Coextension Ru).

(* 相关说明。 （已译） *)
Fail Check (coex_adjunction Ru).

End CoexProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. *)
Fail Example coex_probe_instrument : (true = false) := eq_refl.
