(*
 nLab: https://ncatlab.org/nlab/show/Mod
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_modules

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Objects *)

(** A left R-module: an abelian group together with a scalar action of the
    ring R that respects ≈, distributes on both sides, is associative
    against ring multiplication, and is unital.  Nothing about the
    underlying group is restated — [rm_ab] is a coercion. *)
Record RModObject (R : RingObject) := {
  rm_ab :> AbObject;

  rm_smul : carrier (rig_setoid (ring_rig R)) →
            carrier (cmon_setoid rm_ab) → carrier (cmon_setoid rm_ab);

  rm_smul_respects : Proper (equiv ==> equiv ==> equiv) rm_smul;

  (* r·(m + n) ≈ r·m + r·n *)
  rm_smul_distr_l : ∀ r m n,
    rm_smul r (cmon_plus rm_ab m n)
      ≈ cmon_plus rm_ab (rm_smul r m) (rm_smul r n);
  (* (r + s)·m ≈ r·m + s·m *)
  rm_smul_distr_r : ∀ r s m,
    rm_smul (rig_add (ring_rig R) r s) m
      ≈ cmon_plus rm_ab (rm_smul r m) (rm_smul s m);
  (* (r·s)·m ≈ r·(s·m) *)
  rm_smul_assoc : ∀ r s m,
    rm_smul (rig_mul (ring_rig R) r s) m ≈ rm_smul r (rm_smul s m);
  (* 1·m ≈ m *)
  rm_smul_one : ∀ m, rm_smul (rig_one (ring_rig R)) m ≈ m
}.

Arguments rm_ab {R} _.
Arguments rm_smul {R} _ _ _.
Arguments rm_smul_respects {R} _.
Arguments rm_smul_distr_l {R} _ _ _ _.
Arguments rm_smul_distr_r {R} _ _ _ _.
Arguments rm_smul_assoc {R} _ _ _ _.
Arguments rm_smul_one {R} _ _.

#[export] Existing Instance rm_smul_respects.

(** The three facts that are usually listed as axioms and are not: each
    follows from the four laws above together with Instance/Ab.v's group
    lemmas.  They are stated here once and used throughout. *)

(** 0·m ≈ 0, by cancelling [0·m] against itself. *)
Lemma rm_smul_zero_l {R : RingObject} (M : RModObject R)
  (m : carrier (cmon_setoid M)) :
  rm_smul M (rig_zero (ring_rig R)) m ≈ cmon_zero M.
Proof.
  apply (ab_cancel_l M (rm_smul M (rig_zero (ring_rig R)) m)).
  rewrite <- (rm_smul_distr_r M (rig_zero (ring_rig R))
                (rig_zero (ring_rig R)) m).
  rewrite (rig_add_zero_l (ring_rig R) (rig_zero (ring_rig R))).
  symmetry.
  apply (cmon_plus_zero_r M (rm_smul M (rig_zero (ring_rig R)) m)).
Qed.

(** r·0 ≈ 0, dually. *)
Lemma rm_smul_zero_r {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) :
  rm_smul M r (cmon_zero M) ≈ cmon_zero M.
Proof.
  apply (ab_cancel_l M (rm_smul M r (cmon_zero M))).
  rewrite <- (rm_smul_distr_l M r (cmon_zero M) (cmon_zero M)).
  rewrite (cmon_plus_zero_r M (cmon_zero M)).
  symmetry.
  apply (cmon_plus_zero_r M (rm_smul M r (cmon_zero M))).
Qed.

(** (−r)·m ≈ −(r·m): the scalar negation IS a left inverse of r·m, and
    Instance/Ab.v's [ab_neg_unique] says that is enough. *)
Lemma rm_smul_neg_l {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (cmon_setoid M)) :
  rm_smul M (ring_neg R r) m ≈ ab_neg M (rm_smul M r m).
Proof.
  apply ab_neg_unique.
  rewrite <- (rm_smul_distr_r M (ring_neg R r) r m).
  rewrite (ring_neg_l R r).
  apply rm_smul_zero_l.
Qed.

(** r·(−m) ≈ −(r·m), by the same argument on the other side. *)
Lemma rm_smul_neg_r {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (m : carrier (cmon_setoid M)) :
  rm_smul M r (ab_neg M m) ≈ ab_neg M (rm_smul M r m).
Proof.
  apply ab_neg_unique.
  rewrite <- (rm_smul_distr_l M r (ab_neg M m) m).
  rewrite (ab_neg_left M m).
  apply rm_smul_zero_r.
Qed.

(** ** Morphisms *)

(** An R-module homomorphism is a homomorphism of the underlying abelian
    groups that additionally commutes with the action.  Preservation of
    negation is NOT a field: it is Instance/Ab.v's [ab_map_neg] applied to
    [rm_hom], recorded as [rmod_map_neg] below. *)
Record RModHom {R : RingObject} (M N : RModObject R) := {
  rm_hom :> AbHom M N;

  rm_map_smul : ∀ r m,
    cmon_map rm_hom (rm_smul M r m) ≈ rm_smul N r (cmon_map rm_hom m)
}.

Arguments rm_hom {R M N} _.
Arguments rm_map_smul {R M N} _ _ _.

(** Citation, not a second proof. *)
Lemma rmod_map_neg {R : RingObject} {M N : RModObject R} (f : RModHom M N)
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom f) (ab_neg M m) ≈ ab_neg N (cmon_map (rm_hom f) m).
Proof. apply (ab_map_neg (rm_hom f)). Qed.

(** The hom-setoid is Instance/CMon.v's [CMonHom_Setoid] on the underlying
    homomorphisms, written out: two module maps are equivalent when their
    underlying setoid maps agree pointwise.  The action plays no part, so
    the equivalence proof is the one from [CMon] with the extra field
    ignored. *)
#[export]
Program Instance RModHom_Setoid {R : RingObject} {M N : RModObject R} :
  Setoid (RModHom M N) := {|
  equiv := fun f g => ∀ a, cmon_map (rm_hom f) a ≈ cmon_map (rm_hom g) a
|}.
Next Obligation.
  intros R M N.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map (rm_hom g) a).
    + apply Hfg.
    + apply Hgh.
Qed.

(** L2: the hom-setoid is propositional, pointwise into the CODOMAIN's
    [cmon_prop] (reached through [rm_ab] and [ab_cmon]).  Same shape as
    Instance/CMon.v's [CMonHom_PropEquiv]; restated because [RModHom_Setoid]
    is a setoid on [RModHom M N], a different record.

    Measured (About under Set Printing Universes):

      RModHom_PropEquiv@{u u0 u1 u2 u3 u4} :
        ∀ {R : RingObject@{u1 u2 u3}}
          {M N : RModObject@{u u0 u4 u4 u4 u1 u2 u3} R},
        PropEquiv@{u u4} RModHom_Setoid@{u u0 u1 u2 u3 u4}
      (* u2 <= u, u2 <= u0, and the bounds [RModObject] already carries *)

    -- the transport adds no constraint of its own; the six universes are
    [RModObject]'s and the ring's. *)
#[export] Instance RModHom_PropEquiv {R : RingObject} {M N : RModObject R} :
  PropEquiv (@RModHom_Setoid R M N).
Proof.
  unshelve refine
    {| pequiv := fun f g : RModHom M N =>
                   forall a : carrier (cmon_setoid M),
                     @pequiv _ _ (cmon_prop N)
                       (cmon_map (rm_hom f) a) (cmon_map (rm_hom g) a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(** The identity: the identity group homomorphism, which commutes with the
    action on the nose. *)
Program Definition rmod_hom_id {R : RingObject} {M : RModObject R} :
  RModHom M M := {|
  rm_hom := @cmon_hom_id M
|}.
Next Obligation.
  intros R M r m; simpl.
  reflexivity.
Qed.

(** Composition: the composite of the group homomorphisms; commuting with
    the action composes. *)
Program Definition rmod_hom_compose {R : RingObject} {M N P : RModObject R}
        (f : RModHom N P) (g : RModHom M N) : RModHom M P := {|
  rm_hom := cmon_hom_compose (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N P f g r m; simpl.
  unfold Basics.compose.
  rewrite (rm_map_smul g r m).
  apply (rm_map_smul f r (cmon_map (rm_hom g) m)).
Qed.

Lemma rmod_hom_compose_respects {R : RingObject} {M N P : RModObject R} :
  Proper (equiv ==> equiv ==> equiv) (@rmod_hom_compose R M N P).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(** ** The category *)

(** [RMod R] has the same shape as [Ab]: objects with more structure,
    homomorphisms respecting it, and identities, composition and the
    hom-setoid inherited unchanged from the underlying groups. *)
Program Definition RMod (R : RingObject) : Category := {|
  obj     := RModObject R;
  hom     := @RModHom R;
  homset  := fun M N => @RModHom_Setoid R M N;
  id      := fun M => @rmod_hom_id R M;
  compose := fun M N P f g => @rmod_hom_compose R M N P f g;

  compose_respects := fun M N P => @rmod_hom_compose_respects R M N P
|}.
Next Obligation. intros R x y f a; simpl; reflexivity. Qed.
Next Obligation. intros R x y f a; simpl; reflexivity. Qed.
Next Obligation. intros R x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros R x y z w f g h a; simpl; reflexivity. Qed.

(** L8: [RMod R]'s hom-setoid IS [RModHom_Setoid], so [RModHom_PropEquiv]
    supplies the whole family.  With Instance/Ab.v's [Ab_LocallyPropositional]
    this is what lets Adjunction/Additive.v's [hom_ab] and
    Construction/Enriched/Ab.v's [ehom_ab] -- which since the PR "algebraic
    carriers are sets" (2026-09-17) ask their ambient category for a [Prop]
    equality on homs -- be used at the two ambients the module and bimodule
    objects of Instance/Mod/Bimodule.v and Instance/Mod/Coextension.v actually
    take. *)
#[export] Instance RMod_LocallyPropositional (R : RingObject) :
  LocallyPropositional (RMod R).
Proof.
  constructor.
  intros M N.
  exact (@RModHom_PropEquiv R M N).
Defined.

(** The forgetful functor to [Ab], dropping the action, and the one to
    [Sets], taken directly through the underlying setoid rather than as a
    composite (the object and morphism parts agree with the composite; the
    functor-law proofs are opaque, so the two records are not the same
    term). *)
Program Definition RMod_Forget_Ab (R : RingObject) : RMod R ⟶ Ab := {|
  fobj := fun M => rm_ab M;
  fmap := fun _ _ f => rm_hom f
|}.
Next Obligation. intros R M N f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R M a; simpl; reflexivity. Qed.
Next Obligation. intros R M N P f g a; simpl; reflexivity. Qed.

Program Definition RMod_Forget (R : RingObject) : RMod R ⟶ Sets := {|
  fobj := fun M => cmon_setoid (ab_cmon (rm_ab M));
  fmap := fun _ _ f => cmon_map (rm_hom f)
|}.
Next Obligation. intros R M N f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R M a; simpl; reflexivity. Qed.
Next Obligation. intros R M N P f g a; simpl; reflexivity. Qed.

(** ** The zero module as a zero object *)

(** The one-element module: Instance/Ab.v's [Ab_trivial] with the only
    action available.  Every law holds by computation. *)
Definition RMod_trivial (R : RingObject) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab    := Ab_trivial;
    rm_smul  := fun _ _ => ttt
  |}.
  - (* rm_smul_respects *)
    intros r s Hrs x y Hxy; reflexivity.
  - (* rm_smul_distr_l *)
    intros r m n; reflexivity.
  - (* rm_smul_distr_r *)
    intros r s m; reflexivity.
  - (* rm_smul_assoc *)
    intros r s m; reflexivity.
  - (* rm_smul_one *)
    intros m; destruct m; reflexivity.
Defined.

(** Everything maps to the point, and only one map does. *)
Program Definition RMod_one {R : RingObject} (M : RModObject R) :
  M ~{RMod R}~> RMod_trivial R := {|
  rm_hom := Ab_one M
|}.
Next Obligation. intros R M r m; reflexivity. Qed.

Lemma RMod_one_unique {R : RingObject} (M : RModObject R)
  (f : M ~{RMod R}~> RMod_trivial R) : f ≈ RMod_one M.
Proof. intro a; destruct (cmon_map (rm_hom f) a); reflexivity. Qed.

Program Definition RMod_Terminal (R : RingObject) : @Terminal (RMod R) := {|
  terminal_obj := RMod_trivial R;
  one          := @RMod_one R
|}.
Next Obligation.
  intros R M f g.
  now rewrite (RMod_one_unique _ f), (RMod_one_unique _ g).
Qed.

(** Dually, the unique map out of the point sends it to zero — and the
    action has nothing to say, since r·0 ≈ 0 ([rm_smul_zero_r]). *)
Program Definition RMod_zero_hom {R : RingObject} (M : RModObject R) :
  RMod_trivial R ~{RMod R}~> M := {|
  rm_hom := Ab_zero_hom M
|}.
Next Obligation.
  intros R M r m; simpl.
  symmetry; apply rm_smul_zero_r.
Qed.

Lemma RMod_zero_hom_unique {R : RingObject} (M : RModObject R)
  (f : RMod_trivial R ~{RMod R}~> M) : f ≈ RMod_zero_hom M.
Proof.
  intro a; destruct a; simpl.
  now rewrite (cmon_map_zero (rm_hom f)).
Qed.

Program Definition RMod_Initial (R : RingObject) : @Initial (RMod R) := {|
  terminal_obj := RMod_trivial R : obj[(RMod R)^op];
  one          := @RMod_zero_hom R
|}.
Next Obligation.
  (* As at Instance/Ab.v, routed through transitivity at the
     hom-setoid level rather than by [rewrite]. *)
  intros R M f g.
  etransitivity;
    [ apply RMod_zero_hom_unique | symmetry; apply RMod_zero_hom_unique ].
Qed.

(** The same object is both, so the coincidence iso is the identity. *)
#[export] Instance RMod_Zero (R : RingObject) : ZeroObject (RMod R) :=
  @Build_ZeroObject (RMod R) (RMod_Terminal R) (RMod_Initial R) iso_id.

(** ** Mac Lane's §I.7 proposition: monic = injective, epic = surjective *)

Definition RModInjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Type :=
  ∀ x y : carrier (cmon_setoid M),
    cmon_map (rm_hom f) x ≈ cmon_map (rm_hom f) y → x ≈ y.

Definition RModSurjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Type :=
  ∀ b : carrier (cmon_setoid N), { a & cmon_map (rm_hom f) a ≈ b }.

(** *** The kernel submodule, the probe object for the monic half *)

(** Instance/Ab.v's [AbKernel] carries the group; all that is added is that
    the kernel is closed under the action, which is [rm_smul_zero_r]. *)

Section Kernel.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Lemma rmod_ker_smul_pf (r : carrier (rig_setoid (ring_rig R)))
  (p : ab_ker_carrier (rm_hom f)) :
  cmon_map (rm_hom f) (rm_smul M r (projT1 p)) ≈ cmon_zero N.
Proof.
  rewrite (rm_map_smul f r (projT1 p)).
  rewrite (projT2 p).
  apply rm_smul_zero_r.
Qed.

Definition RModKernel : RModObject R.
Proof using R M N f.
  unshelve notypeclasses refine {|
    rm_ab   := AbKernel (rm_hom f);
    rm_smul := fun r p =>
      existT _ (rm_smul M r (projT1 p)) (rmod_ker_smul_pf r p)
  |}.
  - (* rm_smul_respects *)
    intros r s Hrs p q Hpq; simpl in *.
    now rewrite Hrs, Hpq.
  - (* rm_smul_distr_l *)
    intros r p q; simpl; apply rm_smul_distr_l.
  - (* rm_smul_distr_r *)
    intros r s p; simpl; apply rm_smul_distr_r.
  - (* rm_smul_assoc *)
    intros r s p; simpl; apply rm_smul_assoc.
  - (* rm_smul_one *)
    intros p; simpl; apply rm_smul_one.
Defined.

(** The inclusion and the zero map, which [f] equalizes. *)
Program Definition rmod_kernel_incl : RModKernel ~{RMod R}~> M := {|
  rm_hom := ab_kernel_incl (rm_hom f)
|}.
Next Obligation. intros r p; simpl; reflexivity. Qed.

Program Definition rmod_kernel_zero : RModKernel ~{RMod R}~> M := {|
  rm_hom := ab_kernel_zero (rm_hom f)
|}.
Next Obligation.
  intros r p; simpl.
  symmetry; apply rm_smul_zero_r.
Qed.

End Kernel.

Arguments RModKernel {R M N} f.
Arguments rmod_kernel_incl {R M N} f.
Arguments rmod_kernel_zero {R M N} f.

(** *** Monic *)

(** Monic implies injective, by probing with the kernel submodule: [f]
    equalizes the inclusion and the zero map, so a monic collapses them,
    so every kernel element is zero — and [f x ≈ f y] puts [x − y] in the
    kernel.  The argument is Instance/Ab.v's [ab_monic_injective] with the
    kernel replaced by the kernel SUBMODULE; the note there applies here
    too, that the probe is convenient rather than necessary. *)
Lemma rmod_monic_injective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Monic f → RModInjective f.
Proof.
  intros Hm x y Hxy.
  (* Step 1: monic collapses the two maps out of the kernel. *)
  assert (Hk : ∀ p : carrier (cmon_setoid (RModKernel f)),
                 projT1 p ≈ cmon_zero M).
  { apply (@monic _ _ _ f Hm (RModKernel f)
             (rmod_kernel_incl f) (rmod_kernel_zero f)).
    intro p; simpl.
    rewrite (projT2 p).
    symmetry; apply cmon_map_zero. }
  (* Step 2: x − y lies in the kernel. *)
  assert (Hd : cmon_map (rm_hom f) (cmon_plus M x (ab_neg M y))
                 ≈ cmon_zero N).
  { rewrite cmon_map_plus, ab_map_neg, Hxy.
    apply ab_neg_right. }
  (* Step 3: so x − y is zero, hence x ≈ y. *)
  pose proof (Hk (existT _ (cmon_plus M x (ab_neg M y)) Hd)) as Hz.
  simpl in Hz.
  apply (ab_cancel_l M (ab_neg M y)).
  rewrite (cmon_plus_comm M (ab_neg M y) x) in *.
  rewrite Hz.
  now rewrite (cmon_plus_comm M (ab_neg M y) y), ab_neg_right.
Qed.

Lemma rmod_injective_monic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModInjective f → Monic f.
Proof.
  intros Hi.
  constructor; intros Z g h Hgh z.
  apply Hi.
  exact (Hgh z).
Qed.

(** Mac Lane §I.7's proposition, first half. *)
Theorem rmod_monic_iff_injective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Monic f ↔ RModInjective f.
Proof.
  split; [ apply rmod_monic_injective | apply rmod_injective_monic ].
Qed.

(** *** The quotient module N/fM, the probe object for the epic half *)

(** Instance/Ab.v's [AbQuotient] carries the group — the carrier is [N]
    itself, only the equality coarsening to "differ by something in the
    image" — and all three equivalence laws of that coarser equality are
    proved there.  What is added here is that the action DESCENDS: from
    x ≈ y + f a one gets r·x ≈ r·y + f (r·a), so the image is closed under
    the action and the coset relation is a congruence for it as well. *)

Section Quotient.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(** Fine equality implies coarse: the witness is 0. *)
Lemma rmod_coset_of_equiv (x y : carrier (cmon_setoid N)) :
  x ≈ y → ab_coset_eq (rm_hom f) x y.
Proof.
  intro H.
  exists (cmon_zero M).
  apply pequiv_from.
  rewrite cmon_map_zero, (cmon_plus_zero_r N y).
  exact H.
Qed.

Definition RModQuotient : RModObject R.
Proof using R M N f.
  unshelve notypeclasses refine {|
    rm_ab   := AbQuotient (rm_hom f);
    rm_smul := rm_smul N
  |}.
  - (* rm_smul_respects: THE module content of this construction.  The
       witness r·a is what says the image is a submodule.

       [simpl] before the elimination: the goal is an application of the
       [equiv] projection, whose ascribed sort is [Type], and since the PR
       "algebraic carriers are sets" (2026-09-17) [ab_coset_eq] is a [Prop]
       and may not be destructed into it.  Instance/Ab.v's [AbQuotient]
       records the same step. *)
    intros r s Hrs x y Hxy; simpl in Hxy |- *.
    destruct Hxy as [a Ha].
    apply pequiv_to in Ha.
    exists (rm_smul M r a).
    apply pequiv_from.
    rewrite (rm_map_smul f r a).
    rewrite <- Hrs.
    rewrite <- (rm_smul_distr_l N r y (cmon_map (rm_hom f) a)).
    now rewrite <- Ha.
  - (* rm_smul_distr_l *)
    intros r x y.
    apply rmod_coset_of_equiv, (rm_smul_distr_l N r x y).
  - (* rm_smul_distr_r *)
    intros r s x.
    apply rmod_coset_of_equiv, (rm_smul_distr_r N r s x).
  - (* rm_smul_assoc *)
    intros r s x.
    apply rmod_coset_of_equiv, (rm_smul_assoc N r s x).
  - (* rm_smul_one *)
    intros x.
    apply rmod_coset_of_equiv, (rm_smul_one N x).
Defined.

(** The projection (identity on carriers, coarser equality) and the zero
    map, which [f] equalizes. *)
Program Definition rmod_quot_proj : N ~{RMod R}~> RModQuotient := {|
  rm_hom := ab_quot_proj (rm_hom f)
|}.
Next Obligation. intros r n; simpl; apply ab_coset_refl. Qed.

Program Definition rmod_quot_zero : N ~{RMod R}~> RModQuotient := {|
  rm_hom := ab_quot_zero (rm_hom f)
|}.
Next Obligation.
  intros r n; simpl.
  apply rmod_coset_of_equiv.
  symmetry; apply rm_smul_zero_r.
Qed.

End Quotient.

Arguments RModQuotient {R M N} f.
Arguments rmod_quot_proj {R M N} f.
Arguments rmod_quot_zero {R M N} f.

(** *** Epic *)

(** Epic implies PROPOSITIONAL surjectivity: [f] equalizes the projection
    and the zero map into N/fM, so an epi collapses them, and
    [rmod_quot_proj ≈ rmod_quot_zero] says precisely that every [b] is
    congruent to zero modulo the image — which is to say that a preimage
    EXISTS.  Instance/Ab.v's [ab_epic_surjective], with the quotient group
    replaced by the quotient MODULE.

    AN EARLIER REVISION concluded the split [RModSurjective] and said the
    witness "IS the preimage, read straight back out".  Since the PR
    "algebraic carriers are sets" (2026-09-17) the coset relation is a [Prop]
    (Instance/Ab.v's [ab_coset_eq]), so the witness may not be read back out
    into a [Type]-valued goal.  Nothing is chosen and nothing is doubly
    negated; the preimage is simply no longer data.  The split notion survives
    as the hypothesis of [rmod_surjective_epic] and of every construction that
    builds a preimage directly. *)
Definition RModPropSurjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Type :=
  ∀ b : carrier (cmon_setoid N),
    (exists a : carrier (cmon_setoid M),
       @pequiv _ _ (cmon_prop N) (cmon_map (rm_hom f) a) b)%type.

Lemma rmod_surjective_prop {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective f → RModPropSurjective f.
Proof.
  intros Hs b.
  destruct (Hs b) as [a Ha].
  exists a.
  now apply pequiv_from.
Qed.

Lemma rmod_epic_surjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f → RModPropSurjective f.
Proof.
  intros He b.
  assert (Hpq : rmod_quot_proj f ≈ rmod_quot_zero f).
  { apply (@epic _ _ _ f He (RModQuotient f)
             (rmod_quot_proj f) (rmod_quot_zero f)).
    intro a; simpl.
    exists a.
    apply pequiv_from.
    rewrite cmon_plus_zero_l.
    reflexivity. }
  specialize (Hpq b); simpl in Hpq.
  destruct Hpq as [a Ha].
  apply pequiv_to in Ha.
  exists a.
  apply pequiv_from.
  rewrite cmon_plus_zero_l in Ha.
  now symmetry.
Qed.

Lemma rmod_surjective_epic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  destruct (Hs b) as [a Ha].
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(** The same implication from the propositional notion: drop into [pequiv]
    with [pequiv_to], destruct there, and come back with [pequiv_from]. *)
Lemma rmod_prop_surjective_epic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModPropSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  apply (@pequiv_to _ _ (cmon_prop Z)).
  destruct (Hs b) as [a Ha].
  apply pequiv_from.
  apply pequiv_to in Ha.
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(** Mac Lane §I.7's proposition, second half.  An earlier revision put
    [RModSurjective] on the right; see [rmod_epic_surjective]. *)
Theorem rmod_epic_iff_surjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f ↔ RModPropSurjective f.
Proof.
  split; [ apply rmod_epic_surjective | apply rmod_prop_surjective_epic ].
Qed.

(** The spellings the issue's verification snippet uses. *)
Definition rmod_monic_iff {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Monic f ↔ RModInjective f :=
  rmod_monic_iff_injective f.

Definition rmod_epic_iff {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f ↔ RModPropSurjective f :=
  rmod_epic_iff_surjective f.

(** ** The opposite ring, right modules, and bimodules *)

(** No opposite-ring construction existed in the tree, so here is the
    minimal one: multiplication flipped, EVERYTHING ELSE THE SAME TERM.
    Keeping [rig_setoid], [rig_zero], [rig_add] and [rig_one] literally
    the originals is what makes the additive laws transfer as themselves
    rather than as transported copies, and it is what
    [Ring_op_additive_agrees] below records. *)

Lemma rig_op_mul_respects (R : RigObject) :
  Proper (equiv ==> equiv ==> equiv) (fun a b => rig_mul R b a).
Proof.
  intros a b Hab c d Hcd; simpl.
  now rewrite Hab, Hcd.
Qed.

Lemma rig_op_mul_assoc (R : RigObject) : ∀ a b c,
  rig_mul R c (rig_mul R b a) ≈ rig_mul R (rig_mul R c b) a.
Proof.
  intros a b c.
  symmetry; apply rig_mul_assoc.
Qed.

Definition Rig_op (R : RigObject) : RigObject := {|
  rig_setoid       := rig_setoid R;
  rig_prop         := rig_prop R;
  rig_zero         := rig_zero R;
  rig_add          := rig_add R;
  rig_one          := rig_one R;
  rig_mul          := fun a b => rig_mul R b a;

  rig_add_respects := rig_add_respects R;
  rig_mul_respects := rig_op_mul_respects R;

  rig_add_assoc    := rig_add_assoc R;
  rig_add_comm     := rig_add_comm R;
  rig_add_zero_l   := rig_add_zero_l R;

  rig_mul_assoc    := rig_op_mul_assoc R;
  (* The two unit laws and the two distributive laws swap sides. *)
  rig_mul_one_l    := fun a => rig_mul_one_r R a;
  rig_mul_one_r    := fun a => rig_mul_one_l R a;
  rig_distr_l      := fun a b c => rig_distr_r R b c a;
  rig_distr_r      := fun a b c => rig_distr_l R c a b;
  rig_mul_zero_l   := fun a => rig_mul_zero_r R a;
  rig_mul_zero_r   := fun a => rig_mul_zero_l R a
|}.

Definition Ring_op (R : RingObject) : RingObject := {|
  ring_rig          := Rig_op (ring_rig R);
  ring_neg          := ring_neg R;
  ring_neg_respects := ring_neg_respects R;
  ring_neg_l        := ring_neg_l R
|}.

(** The additive structure of the opposite ring is the original one on the
    nose, not merely isomorphic to it. *)
Example Ring_op_additive_agrees (R : RingObject) :
  rig_setoid (ring_rig (Ring_op R)) = rig_setoid (ring_rig R) := eq_refl.
Example Ring_op_zero_agrees (R : RingObject) :
  rig_zero (ring_rig (Ring_op R)) = rig_zero (ring_rig R) := eq_refl.
Example Ring_op_add_agrees (R : RingObject) :
  rig_add (ring_rig (Ring_op R)) = rig_add (ring_rig R) := eq_refl.
Example Ring_op_one_agrees (R : RingObject) :
  rig_one (ring_rig (Ring_op R)) = rig_one (ring_rig R) := eq_refl.
Example Ring_op_neg_agrees (R : RingObject) :
  ring_neg (Ring_op R) = ring_neg R := eq_refl.

(** A RIGHT R-module is a left module over the opposite ring; that is
    taken as the definition, m ⊲ r being r ·[Ring_op R] m.  The
    definition is justified by [bimodule_right_RMod] below, which turns a
    right action written in the usual order into an object of this
    category. *)
Definition ModR (R : RingObject) : Category := RMod (Ring_op R).

(** A bimodule: a left R-module carrying a compatible right S-action.
    The compatibility law is Mac Lane's (rm)s ≈ r(ms), i.e. r(ms) up to symmetry.  This stays
    definition-level; no category of bimodules and no tensor product are
    built here. *)
Record Bimodule (R S : RingObject) := {
  bm_left :> RModObject R;

  bm_rsmul : carrier (cmon_setoid bm_left) →
             carrier (rig_setoid (ring_rig S)) →
             carrier (cmon_setoid bm_left);

  bm_rsmul_respects : Proper (equiv ==> equiv ==> equiv) bm_rsmul;

  (* (m + n)·s ≈ m·s + n·s *)
  bm_rsmul_distr_l : ∀ m n s,
    bm_rsmul (cmon_plus bm_left m n) s
      ≈ cmon_plus bm_left (bm_rsmul m s) (bm_rsmul n s);
  (* m·(s + t) ≈ m·s + m·t *)
  bm_rsmul_distr_r : ∀ m s t,
    bm_rsmul m (rig_add (ring_rig S) s t)
      ≈ cmon_plus bm_left (bm_rsmul m s) (bm_rsmul m t);
  (* m·(s·t) ≈ (m·s)·t *)
  bm_rsmul_assoc : ∀ m s t,
    bm_rsmul m (rig_mul (ring_rig S) s t) ≈ bm_rsmul (bm_rsmul m s) t;
  (* m·1 ≈ m *)
  bm_rsmul_one : ∀ m, bm_rsmul m (rig_one (ring_rig S)) ≈ m;

  (* The compatibility law: (rm)s ≈ r(ms), i.e. r(ms) up to symmetry. *)
  bm_compat : ∀ r m s,
    bm_rsmul (rm_smul bm_left r m) s ≈ rm_smul bm_left r (bm_rsmul m s)
}.

Arguments bm_left {R S} _.
Arguments bm_rsmul {R S} _ _ _.
Arguments bm_rsmul_respects {R S} _.
Arguments bm_rsmul_distr_l {R S} _ _ _ _.
Arguments bm_rsmul_distr_r {R S} _ _ _ _.
Arguments bm_rsmul_assoc {R S} _ _ _ _.
Arguments bm_rsmul_one {R S} _ _.
Arguments bm_compat {R S} _ _ _ _.

#[export] Existing Instance bm_rsmul_respects.

(** The right action of a bimodule IS a left [Ring_op S]-action: the
    associativity law reverses exactly as the opposite multiplication
    does.  This is what makes [ModR] the right definition. *)
Definition bimodule_right_RMod {R S : RingObject} (B : Bimodule R S) :
  RModObject (Ring_op S).
Proof.
  (* The constructor is named explicitly: a record literal here elaborates
     the scalar argument's type against [S] and infers the parameter to be
     [S] rather than [Ring_op S], the two being convertible. *)
  unshelve notypeclasses refine
    (@Build_RModObject (Ring_op S) (rm_ab (bm_left B))
       (fun s m => bm_rsmul B m s) _ _ _ _ _).
  - (* rm_smul_respects *)
    intros s t Hst m n Hmn; simpl.
    now rewrite Hst, Hmn.
  - (* rm_smul_distr_l *)
    intros s m n; simpl; apply bm_rsmul_distr_l.
  - (* rm_smul_distr_r *)
    intros s t m; simpl; apply bm_rsmul_distr_r.
  - (* rm_smul_assoc: (s ·op t) acts as t then s *)
    intros s t m; simpl; apply bm_rsmul_assoc.
  - (* rm_smul_one *)
    intros m; simpl; apply bm_rsmul_one.
Defined.

(** ** [RMod R] is preadditive *)

(** Pointwise addition and zero, mirroring Structure/AbCategory.v's
    [Ab_Preadditive] and reusing its [ab_hom_add]/[ab_hom_zero] for the
    group part.  The one new obligation each time is linearity: the sum of
    two linear maps is linear because the action distributes over
    addition, (f+g)(r·m) ≈ r·f m + r·g m ≈ r·((f+g) m); and the zero map
    is linear because r·0 ≈ 0. *)
Program Definition rmod_hom_add {R : RingObject} {M N : RModObject R}
        (f g : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_add (rm_hom f) (rm_hom g)
|}.
Next Obligation.
  intros R M N f g r m; simpl.
  rewrite (rm_map_smul f r m), (rm_map_smul g r m).
  symmetry; apply rm_smul_distr_l.
Qed.

Program Definition rmod_hom_zero {R : RingObject} {M N : RModObject R} :
  RModHom M N := {|
  rm_hom := ab_hom_zero
|}.
Next Obligation.
  intros R M N r m; simpl.
  symmetry; apply rm_smul_zero_r.
Qed.

#[export] Program Instance RMod_Preadditive (R : RingObject) :
  @Preadditive (RMod R) := {
  padd  := fun M N => rmod_hom_add;
  pzero := fun M N => rmod_hom_zero
}.
Next Obligation.
  intros R M N f f' Hf g g' Hg a; simpl.
  now rewrite (Hf a), (Hg a).
Qed.
Next Obligation.
  intros R M N f g h a; simpl; apply cmon_plus_assoc.
Qed.
Next Obligation.
  intros R M N f g a; simpl; apply cmon_plus_comm.
Qed.
Next Obligation.
  intros R M N f a; simpl; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R M N P h f g a; simpl.
  apply cmon_map_plus.
Qed.
Next Obligation.
  intros R M N P f g h a; simpl; reflexivity.
Qed.
Next Obligation.
  intros R M N P f a; simpl; reflexivity.
Qed.
Next Obligation.
  intros R M N P f a; simpl.
  apply cmon_map_zero.
Qed.

(** ** A concrete witness: a ring as a module over itself *)

(** Every ring is a left module over itself, with multiplication as the
    action.  Nothing is proved here: each of the four module laws IS the
    corresponding rig law, and the underlying abelian group is
    Instance/Rng.v's [ring_ab].  This is the cheapest non-vacuous witness
    available, and it is uniform in R. *)
Definition Ring_RMod (R : RingObject) : RModObject R := {|
  rm_ab            := ring_ab R;
  rm_smul          := rig_mul (ring_rig R);

  rm_smul_respects := rig_mul_respects (ring_rig R);
  rm_smul_distr_l  := rig_distr_l (ring_rig R);
  rm_smul_distr_r  := rig_distr_r (ring_rig R);
  rm_smul_assoc    := rig_mul_assoc (ring_rig R);
  rm_smul_one      := rig_mul_one_l (ring_rig R)
|}.

(** The integers as a ℤ-module.  The action computes. *)
Definition Int_RMod : RModObject Int_Ring := Ring_RMod Int_Ring.

(* The compatibility law is inhabited: every ring is an (R,R)-bimodule
   over itself — both actions the multiplication, [bm_compat] being
   exactly associativity (an audit-supplied witness). *)
Definition Ring_Bimodule (R : RingObject) : Bimodule R R.
Proof.
  unshelve notypeclasses refine
    (@Build_Bimodule R R (Ring_RMod R) (rig_mul (ring_rig R)) _ _ _ _ _ _).
  - intros a b Hab c d Hcd; now rewrite Hab, Hcd.
  - intros m n s; apply rig_distr_r.
  - intros m s t; apply rig_distr_l.
  - intros m s t; symmetry; apply rig_mul_assoc.
  - intros m; apply rig_mul_one_r.
  - intros r m s; apply rig_mul_assoc.
Defined.

Definition Int_Bimodule : Bimodule Int_Ring Int_Ring :=
  Ring_Bimodule Int_Ring.

Example int_bimodule_rsmul : bm_rsmul Int_Bimodule 5%Z 6%Z = 30%Z :=
  eq_refl.
Example int_bimodule_right_action :
  rm_smul (bimodule_right_RMod Int_Bimodule) 5%Z 6%Z = 30%Z := eq_refl.

Example int_rmod_smul : rm_smul Int_RMod 3%Z 4%Z = 12%Z := eq_refl.

Example int_rmod_distr :
  rm_smul Int_RMod 2%Z (rig_add Int_Rig 5%Z 7%Z) = 24%Z := eq_refl.

Example int_rmod_neg :
  rm_smul Int_RMod (ring_neg Int_Ring 3%Z) 4%Z = (-12)%Z := eq_refl.

(** The zero object's carrier really is the trivial group: both the
    terminal and the initial object are [RMod_trivial], by [eq_refl]. *)
Example rmod_zero_terminal_is_trivial (R : RingObject) :
  @terminal_obj (RMod R) (RMod_Terminal R) = RMod_trivial R := eq_refl.

Example rmod_zero_initial_is_trivial (R : RingObject) :
  @initial_obj (RMod R) (RMod_Initial R) = RMod_trivial R := eq_refl.

Example rmod_trivial_carrier (R : RingObject) :
  carrier (cmon_setoid (rm_ab (RMod_trivial R))) = poly_unit := eq_refl.
