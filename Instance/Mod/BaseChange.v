(** * Base change along ℤ → R: the free R-module on an abelian group *)

(*
 Book:      Mac Lane, ibid., §I.8, printed pp. 28–29 — the tensor
 Book:      Riehl, "Category Theory in Context", Dover 2016, §4.1
 nLab:      https://ncatlab.org/nlab/show/extension+of+scalars
 nLab:      https://ncatlab.org/nlab/show/free+module
 Wikipedia: https://en.wikipedia.org/wiki/Extension_of_scalars

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
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section ZExtension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation TT A := (AbTensor (ring_ab R) A).
Local Notation ZG A s a := (@ts_gen (ring_ab R) A s a).

(** ** The scalar action *)

Program Definition zext_bilin (A : AbObject) (r : RS) :
  Bilinear (ring_ab R) A (TT A) := {|
  bilin_map := fun s a => ts_gen (rig_mul (ring_rig R) r s) a
|}.
Next Obligation.
  intros A r s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r (reflexivity r) s s' Hs) Ha).
Qed.
Next Obligation.
  intros A r s s' a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_l (ring_rig R) r s s') (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r s') a)).
Qed.
Next Obligation.
  intros A r s a a'.
  exact (@te_bilin_r (ring_ab R) A (rig_mul (ring_rig R) r s) a a').
Qed.

Definition zext_smul (A : AbObject) (r : RS) :
  AbHom (TT A) (TT A) := tensor_ump (zext_bilin A r).

Definition zext_act (A : AbObject) (r : RS)
  (x : carrier (cmon_setoid (TT A))) : carrier (cmon_setoid (TT A)) :=
  cmon_map (zext_smul A r) x.

Example zext_act_gen (A : AbObject) (r s : RS) (a : carrier A) :
  zext_act A r (ZG A s a) = ZG A (rig_mul (ring_rig R) r s) a := eq_refl.


(** ** The four module laws, each by agreement on generators *)

Lemma zext_smul_scalar (A : AbObject) (r r' : RS) :
  r ≈ r' → ∀ x, zext_act A r x ≈ zext_act A r' x.
Proof.
  intros Hr x.
  refine (tensor_hom_ext (zext_smul A r) (zext_smul A r') _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_respects (ring_rig R) r r' Hr s s (reflexivity s))
           (reflexivity a)).
Qed.

Lemma zext_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (zext_act A).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (zext_act A r y).
  - exact (proper_morphism (cmon_map (zext_smul A r)) x y Hxy).
  - exact (zext_smul_scalar A r r' Hr y).
Qed.

Lemma zext_act_distr_r (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (TT A) (zext_act A r x) (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_add (ring_rig R) r r'))
            (ab_hom_add (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (te_trans
           (@te_gen (ring_ab R) A _ _ _ _
              (rig_distr_r (ring_rig R) r r' s) (reflexivity a))
           (@te_bilin_l (ring_ab R) A (rig_mul (ring_rig R) r s)
                        (rig_mul (ring_rig R) r' s) a)).
Qed.

Lemma zext_act_assoc (A : AbObject) (r r' : RS)
  (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_mul (ring_rig R) r r') x
    ≈ zext_act A r (zext_act A r' x).
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (zext_smul A r) (zext_smul A r')) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_assoc (ring_rig R) r r' s) (reflexivity a)).
Qed.

Lemma zext_act_one (A : AbObject) (x : carrier (cmon_setoid (TT A))) :
  zext_act A (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (tensor_hom_ext (zext_smul A (rig_one (ring_rig R)))
            (@cmon_hom_id (TT A)) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) A _ _ _ _
           (rig_mul_one_l (ring_rig R) s) (reflexivity a)).
Qed.

Definition ZExtObj (A : AbObject) : RModObject R := {|
  rm_ab            := TT A;
  rm_smul          := zext_act A;
  rm_smul_respects := zext_act_respects A;
  rm_smul_distr_l  := fun r x y => cmon_map_plus (zext_smul A r) x y;
  rm_smul_distr_r  := zext_act_distr_r A;
  rm_smul_assoc    := zext_act_assoc A;
  rm_smul_one      := zext_act_one A
|}.

(** ** The arrow action, and the functor *)

Program Definition zext_map_bilin {A B : AbObject} (f : AbHom A B) :
  Bilinear (ring_ab R) A (TT B) := {|
  bilin_map := fun s a => ZG B s (cmon_map f a)
|}.
Next Obligation.
  intros A B f s s' Hs a a' Ha.
  exact (@te_gen (ring_ab R) B _ _ _ _ Hs
           (proper_morphism (cmon_map f) a a' Ha)).
Qed.
Next Obligation.
  intros A B f s s' a.
  exact (@te_bilin_l (ring_ab R) B s s' (cmon_map f a)).
Qed.
Next Obligation.
  intros A B f s a a'.
  exact (te_trans
           (@te_gen (ring_ab R) B _ _ _ _
              (reflexivity s) (cmon_map_plus f a a'))
           (@te_bilin_r (ring_ab R) B s (cmon_map f a) (cmon_map f a'))).
Qed.

Definition zext_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (TT A) (TT B) := tensor_ump (zext_map_bilin f).

Program Definition ZExtMap {A B : AbObject} (f : AbHom A B) :
  ZExtObj A ~{RMod R}~> ZExtObj B := {|
  rm_hom := zext_map_ab f
|}.
Next Obligation.
  intros A B f r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (zext_map_ab f) (zext_smul A r))
            (cmon_hom_compose (zext_smul B r) (zext_map_ab f)) _ x).
  intros s a; reflexivity.
Qed.

Program Definition ZExt : Ab ⟶ RMod R := {|
  fobj := ZExtObj;
  fmap := @ZExtMap
|}.
Next Obligation.
  intros A B f g Hfg x.
  refine (tensor_hom_ext (zext_map_ab f) (zext_map_ab g) _ x).
  intros s a.
  exact (@te_gen (ring_ab R) B _ _ _ _ (reflexivity s) (Hfg a)).
Qed.
Next Obligation.
  intros A x.
  refine (tensor_hom_ext (zext_map_ab (@id Ab A))
            (@cmon_hom_id (TT A)) _ x).
  intros s a; reflexivity.
Qed.
Next Obligation.
  intros A B C f g x.
  refine (tensor_hom_ext (zext_map_ab (f ∘ g))
            (cmon_hom_compose (zext_map_ab f) (zext_map_ab g)) _ x).
  intros s a; reflexivity.
Qed.

(** ** The transposes *)

Lemma zext_gen_zero_r (A : AbObject) (s : RS) :
  (ZG A s (cmon_zero A) : carrier (cmon_setoid (TT A)))
    ≈ cmon_zero (TT A).
Proof.
  apply (ab_cancel_l (TT A) (ZG A s (cmon_zero A))).
  exact (te_trans
           (te_trans
              (te_sym (@te_bilin_r (ring_ab R) A s
                         (cmon_zero A) (cmon_zero A)))
              (@te_gen (ring_ab R) A _ _ _ _ (reflexivity s)
                 (cmon_plus_zero_l A (cmon_zero A))))
           (te_sym (cmon_plus_zero_r (TT A) (ZG A s (cmon_zero A))))).
Qed.

Program Definition zext_to {A : AbObject} {M : RModObject R}
  (g : ZExtObj A ~{RMod R}~> M) : A ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun a =>
    cmon_map (rm_hom g) (ZG A (rig_one (ring_rig R)) a) |}
|}.
Next Obligation.
  intros A M g a a' Ha; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@te_gen (ring_ab R) A _ _ _ _ (reflexivity _) Ha)).
Qed.
Next Obligation.
  intros A M g; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (TT A))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (zext_gen_zero_r A (rig_one (ring_rig R)))).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros A M g a b; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (TT A) (ZG A (rig_one (ring_rig R)) a)
                                    (ZG A (rig_one (ring_rig R)) b))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_bilin_r (ring_ab R) A (rig_one (ring_rig R)) a b)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition zext_lmul (M : RModObject R) (r : RS) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M r m |}
|}.
Next Obligation.
  intros M r m m' Hm.
  exact (rm_smul_respects M r r (reflexivity r) m m' Hm).
Qed.
Next Obligation. intros M r; simpl; exact (rm_smul_zero_r M r). Qed.
Next Obligation.
  intros M r m m'; simpl; exact (rm_smul_distr_l M r m m').
Qed.

Program Definition zext_from_bilin {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : Bilinear (ring_ab R) A (rm_ab M) := {|
  bilin_map := fun s a => rm_smul M s (cmon_map h a)
|}.
Next Obligation.
  intros A M h s s' Hs a a' Ha.
  exact (rm_smul_respects M s s' Hs _ _
           (proper_morphism (cmon_map h) a a' Ha)).
Qed.
Next Obligation.
  intros A M h s s' a.
  exact (rm_smul_distr_r M s s' (cmon_map h a)).
Qed.
Next Obligation.
  intros A M h s a a'.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map h a) (cmon_map h a'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus h a a')).
  - exact (rm_smul_distr_l M s (cmon_map h a) (cmon_map h a')).
Qed.

Program Definition zext_from {A : AbObject} {M : RModObject R}
  (h : A ~{Ab}~> rm_ab M) : ZExtObj A ~{RMod R}~> M := {|
  rm_hom := tensor_ump (zext_from_bilin h)
|}.
Next Obligation.
  intros A M h r x.
  refine (tensor_hom_ext
            (cmon_hom_compose (tensor_ump (zext_from_bilin h))
                              (zext_smul A r))
            (cmon_hom_compose (zext_lmul M r)
                              (tensor_ump (zext_from_bilin h))) _ x).
  intros s a.
  exact (rm_smul_assoc M r s (cmon_map h a)).
Qed.

(** ** The adjunction *)

Program Definition zext_adj_to (A : AbObject) (M : RModObject R) :
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |}
    ~{Sets}~>
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |} := {|
  morphism := fun g => zext_to g
|}.
Next Obligation. intros A M g g' Hg a; exact (Hg _). Qed.

Program Definition zext_adj_from (A : AbObject) (M : RModObject R) :
  {| carrier := A ~{Ab}~> rm_ab M;
     is_setoid := @homset Ab A (rm_ab M) |}
    ~{Sets}~>
  {| carrier := ZExtObj A ~{RMod R}~> M;
     is_setoid := @homset (RMod R) (ZExtObj A) M |} := {|
  morphism := fun h => zext_from h
|}.
Next Obligation.
  intros A M h h' Hh x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin h))
                         (tensor_ump (zext_from_bilin h')) _ x).
  intros s a.
  exact (rm_smul_respects M s s (reflexivity s) _ _ (Hh a)).
Qed.

Program Definition zext_adj (A : AbObject) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := ZExtObj A ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (ZExtObj A) M |}
    {| carrier := A ~{Ab}~> rm_ab M;
       is_setoid := @homset Ab A (rm_ab M) |} := {|
  to   := zext_adj_to A M;
  from := zext_adj_from A M
|}.
Next Obligation.
  intros A M h a.
  exact (rm_smul_one M (cmon_map h a)).
Qed.
Next Obligation.
  intros A M g x.
  refine (tensor_hom_ext (tensor_ump (zext_from_bilin (zext_to g)))
                         (rm_hom g) _ x).
  intros s a.
  transitivity (cmon_map (rm_hom g)
                  (ZG A (rig_mul (ring_rig R) s
                           (rig_one (ring_rig R))) a)).
  - symmetry.
    exact (rm_map_smul g s (ZG A (rig_one (ring_rig R)) a)).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@te_gen (ring_ab R) A _ _ _ _
                (rig_mul_one_r (ring_rig R) s) (reflexivity a))).
Qed.

Definition zext_adjunction : ZExt ⊣ RMod_Forget_Ab R.
Proof.
  unshelve eapply (@Build_Adjunction' (RMod R) Ab ZExt
                     (RMod_Forget_Ab R) zext_adj).
  - intros A B M f g a; reflexivity.
  - intros A M N f g a; reflexivity.
Defined.

(** ** Unit, counit, and the strict readings *)

Definition zext_unit (A : AbObject) :
  A ~{Ab}~> rm_ab (ZExtObj A) :=
  @unit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A.

Definition zext_counit (M : RModObject R) :
  ZExtObj (rm_ab M) ~{RMod R}~> M :=
  @counit (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction M.

(* THE REVIEWER CHECK.  The unit IS a |-> 1 (x) a, on the nose. *)
Example zext_unit_is_gen (A : AbObject) (a : carrier A) :
  cmon_map (zext_unit A) a = ZG A (rig_one (ring_rig R)) a := eq_refl.

Example zext_counit_is_smul (M : RModObject R) (s : RS)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom (zext_counit M)) (ZG (rm_ab M) s m)
    = rm_smul M s m := eq_refl.

Example zext_adj_to_is_zext_to (A : AbObject) (M : RModObject R)
  (g : ZExtObj A ~{RMod R}~> M) :
  to (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) g
    = zext_to g := eq_refl.

Example zext_adj_from_is_zext_from (A : AbObject) (M : RModObject R)
  (h : A ~{Ab}~> rm_ab M) :
  from (@adj (RMod R) Ab ZExt (RMod_Forget_Ab R) zext_adjunction A M) h
    = zext_from h := eq_refl.

Example zext_fobj_is_ZExtObj (A : AbObject) :
  fobj[ZExt] A = ZExtObj A := eq_refl.

Example zext_fmap_is_ZExtMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[ZExt] f = ZExtMap f := eq_refl.

Example zext_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End ZExtension.

(** ** A concrete witness over ℤ *)

Definition ZIntExt : RModObject Int_Ring :=
  ZExtObj Int_Ring (ring_ab Int_Ring).

Definition ZIntGen (s a : Z) : carrier (cmon_setoid (rm_ab ZIntExt)) :=
  @ts_gen (ring_ab Int_Ring) (ring_ab Int_Ring) s a.

Definition zext_int_eval : ZIntExt ~{RMod Int_Ring}~> Int_RMod :=
  zext_counit Int_Ring Int_RMod.

Example zext_int_eval_computes :
  cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4) = 12%Z := eq_refl.

Example zext_int_eval_zero :
  cmon_map (rm_hom zext_int_eval) (cmon_zero (rm_ab ZIntExt)) = 0%Z
  := eq_refl.

Example zext_int_unit_computes (a : Z) :
  cmon_map (zext_unit Int_Ring (ring_ab Int_Ring)) a = ZIntGen 1 a
  := eq_refl.

Lemma zext_int_gen_nonzero :
  ZIntGen 1 1 ≈ cmon_zero (rm_ab ZIntExt) → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_gens_distinct : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 2%Z)) by
    exact (proper_morphism (cmon_map (rm_hom zext_int_eval)) _ _ Hz).
  discriminate.
Qed.

Lemma zext_int_unit_separates : ZIntGen 1 1 ≈ ZIntGen 1 2 → False.
Proof. exact zext_int_gens_distinct. Qed.

(** ** Probes

    Every strength claim the header makes is pinned here, each negative
    beside an APPLIED positive control.  Each was stripped of its [Fail]
    and compiled alone, and its WHOLE error read: negatives 1, 2 and 4
    end in [cannot unify] (CONVERSION), negative 3 is a plain type
    mismatch with no [cannot unify] and no universe clause (TYPING), and
    negatives 5-8 end in [universe inconsistency: Cannot enforce rc = ra]
    (FORMABILITY). *)

Section ZExtProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (h : A ~{Ab}~> rm_ab M) (g : ZExtObj R A ~{RMod R}~> M).
Context (a : carrier A) (s : carrier (rig_setoid (ring_rig R))).

(* CONTROL for negative 1: the round trip DOES hold at ≈, and the proof
   term names the exact law that closes the gap. *)
Example zext_ctrl_to_from :
  cmon_map (zext_to R (zext_from R h)) a ≈ cmon_map h a
  := rm_smul_one M (cmon_map h a).

(* NEGATIVE 1 (CONVERSION).  [zext_to (zext_from h)] evaluates to
   1 · h a, and 1 · − is not the identity by conversion: [rm_smul_one]
   is an abstract field of [RModObject], so neither side reduces. *)
Fail Example zext_probe_to_from_strict :
  cmon_map (zext_to R (zext_from R h)) a = cmon_map h a := eq_refl.

(* CONTROL for negative 2. *)
Example zext_ctrl_from_to :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    ≈ cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a)
  := iso_from_to (zext_adj R A M) g _.

(* NEGATIVE 2 (CONVERSION).  The other round trip leaves an s · 1 in the
   scalar slot; [rig_mul_one_r] is what removes it, and it too is an
   abstract field. *)
Fail Example zext_probe_from_to_strict :
  cmon_map (rm_hom (zext_from R (zext_to R g)))
    (@ts_gen (ring_ab R) A s a)
    = cmon_map (rm_hom g) (@ts_gen (ring_ab R) A s a) := eq_refl.

(* CONTROL for negative 3: the unit IS an arrow of [Ab]. *)
Check (zext_unit R A : A ~{Ab}~> rm_ab (ZExtObj R A)).

(* NEGATIVE 3 (TYPING).  It is NOT an arrow of [RMod R] — [A] is an
   [AbObject] and there is no coercion into [obj[RMod R]].  This is the
   shape of the adjunction, not an accident: the unit lives downstairs. *)
Fail Check (zext_unit R A : A ~{RMod R}~> rm_ab (ZExtObj R A)).

End ZExtProbeStrength.

(* CONTROL for negative 4: the comparison map exists and computes. *)
Check (cmon_map (rm_hom zext_int_eval) (ZIntGen 3 4)).

(* NEGATIVE 4 (CONVERSION).  ℤ ⊗ ℤ is NOT ℤ on the nose — the carriers
   are [tsum] and [Z] — so [zext_int_gen_nonzero] is a statement about a
   genuinely constructed object and not about ℤ in disguise. *)
Fail Example zext_probe_int_strict : ZIntExt = Int_RMod := eq_refl.

Section ZExtProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}) (Au Bu : AbObject).
Context (fu : Au ~{Ab}~> Bu).

(* CONTROLS.  With the ring's FIRST and THIRD universes declared strictly
   apart, all of these are formable — so the identification below is
   neither the tensor's, nor the category's, nor the forgetful functor's,
   nor the abelian-group-level arrow action's, nor the extension OBJECT's.
   Each is APPLIED to [Ru], which is the argument carrying the levels. *)
Check (RMod Ru).
Check (ring_ab Ru).
Check (AbTensor (ring_ab Ru) Au).
Check (ZExtObj Ru Au).
Check (zext_act Ru Au).
Check (zext_map_ab Ru fu).
Check (RMod_Forget_Ab Ru).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).

(* CONTROLS 5, 7 and 8, WHICH USED TO BE NEGATIVES.  An earlier revision read:
   "NEGATIVE 5 (FORMABILITY).  The identification enters exactly when the
   extension is READ AS AN OBJECT of [RMod R] — not when it is built";
   "NEGATIVE 7 (FORMABILITY).  Hence the functor"; "NEGATIVE 8 (FORMABILITY).
   And hence the headline."  All three were re-measured after the PR
   "algebraic carriers are sets" (2026-09-17) and all three are now FORMABLE
   at the declared separation.  The cause is upstream: [ZExtObj] is built on
   Instance/Ab/Tensor.v's [AbTensor], whose relation [ts_eq] moved to [Prop],
   so [tensor_med_respects] no longer inducts on a [Type]-valued relation into
   a [Type]-valued goal and the identification that induction forced is gone.
   Negative 6 below still fires, which is the instrument check that the
   section still constrains anything at all.  The ring's auxiliary universe is
   also now the FIRST argument of [RingObject] rather than the third, which is
   why the binder reads `RingObject@{rc ra rb}`. *)
Check (ZExtObj Ru Au : obj[RMod Ru]).

(* NEGATIVE 6 (FORMABILITY).  The surviving donor, and it is not this file's.
   Instance/Mod.v's OWN [Ring_RMod] is rejected at these levels while the
   bare [Check (Ring_RMod Ru)] control above is accepted, so what the
   ascription to [obj[RMod Ru]] forces is inherited. *)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

Check (ZExt Ru).
Check (zext_adjunction Ru).

End ZExtProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. *)
Fail Example zext_probe_instrument : (true = false) := eq_refl.
