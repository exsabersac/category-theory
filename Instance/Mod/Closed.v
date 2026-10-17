(** * (R-Mod, ⊗, R) is symmetric monoidal CLOSED: the tensor-hom adjunction *)

(*
 Book:      Mac Lane, ibid., §IV.6, printed p. 98 — the tensor-hom
 nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab:      https://ncatlab.org/nlab/show/closed+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

   本文件给出闭结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Monoidal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.AbCategory.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Engineering note (c): [mt_eq_Equivalence] (Instance/Mod/Tensor.v) is
   a Lemma, not an Instance, so [transitivity] and setoid [rewrite] cannot
   see it on goals that have unfolded to [mt_eq] — and the error names the
   wrong culprit when they cannot. *)
#[local] Existing Instance mt_eq_Equivalence.

(** ** The internal hom

    The module of R-linear maps V ⟶ W.  Carrier, addition, zero and
    negation are Instance/Mod.v's own hom-algebra; the ACTION is the
    pointwise (r · φ) v := r · φ v, and that is where commutativity
    lands. *)

Section InternalHom.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

(* Negation of a module homomorphism.  Instance/Mod.v supplies
   [rmod_hom_add] and [rmod_hom_zero] but no negation, and the obvious name
   [rmod_hom_neg] is taken by Instance/FdVect/DoubleDual.v — hence the
   local name. *)
Program Definition hm_neg {M N : RModObject R} (f : RModHom M N) :
  RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(* The carrier setoid: two homomorphisms agree when they agree pointwise. *)
Definition hm_setoid (V W : RModObject R) : SetoidObject := {|
  carrier   := RModHom V W;
  is_setoid := @RModHom_Setoid R V W
|}.

Program Definition hm_cmon (V W : RModObject R) : CMonObject := {|
  cmon_setoid := hm_setoid V W;
  cmon_zero   := @rmod_hom_zero R V W;
  cmon_plus   := @rmod_hom_add R V W
|}.
Next Obligation.
  intros V W f f' Hf g g' Hg v; simpl.
  now rewrite (Hf v), (Hg v).
Qed.
Next Obligation. intros V W f g h v; simpl; apply cmon_plus_assoc. Qed.
Next Obligation. intros V W f g v; simpl; apply cmon_plus_comm. Qed.
Next Obligation. intros V W f v; simpl; apply cmon_plus_zero_l. Qed.

Program Definition hm_ab (V W : RModObject R) : AbObject := {|
  ab_cmon := hm_cmon V W;
  ab_neg  := @hm_neg V W
|}.
Next Obligation.
  intros V W f g Hfg v; simpl.
  now rewrite (Hfg v).
Qed.
Next Obligation. intros V W f v; simpl; apply ab_neg_left. Qed.

(** *** The pointwise action, and the one use of commutativity

    Preservation of zero and of addition are annihilation and
    distributivity in W, and neither mentions [Rcomm] — the two lemmas
    below are what the probe section uses as controls.  The remaining
    clause, that r · φ is still LINEAR, is the one that does. *)

Lemma hm_smul_zero (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  rm_smul W r (cmon_map (rm_hom f) (cmon_zero V)) ≈ cmon_zero W.
Proof.
  rewrite (cmon_map_zero (rm_hom f)).
  apply rm_smul_zero_r.
Qed.

Lemma hm_smul_plus (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ v w, rm_smul W r (cmon_map (rm_hom f) (cmon_plus V v w))
           ≈ cmon_plus W (rm_smul W r (cmon_map (rm_hom f) v))
                         (rm_smul W r (cmon_map (rm_hom f) w)).
Proof.
  intros v w.
  rewrite (cmon_map_plus (rm_hom f) v w).
  apply rm_smul_distr_l.
Qed.

(* THE ONE USE OF COMMUTATIVITY IN THE WHOLE FILE.

   The `Proof using R Rcomm` annotation is LOAD-BEARING and is the
   instrument the header describes: Lib.v sets
   [Default Proof Using "Type"], [Rcomm] occurs in no statement here, and
   without the annotation this lemma fails at [Qed] with "The following
   section variable is used but not declared: Rcomm."  Do not remove it,
   and do not silence it with `Set Default Proof Using "All"` — that would
   destroy the measurement rather than pass it. *)
Lemma hm_smul_linear (V W : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  ∀ s v, rm_smul W r (cmon_map (rm_hom f) (rm_smul V s v))
           ≈ rm_smul W s (rm_smul W r (cmon_map (rm_hom f) v)).
Proof using R Rcomm.
  intros s v.
  rewrite (rm_map_smul f s v).
  rewrite <- (rm_smul_assoc W r s (cmon_map (rm_hom f) v)).
  rewrite (Rcomm r s).
  apply (rm_smul_assoc W s r (cmon_map (rm_hom f) v)).
Qed.

Program Definition hm_smul (V W : RModObject R)
        (r : carrier (rig_setoid (ring_rig R))) (f : RModHom V W) :
  RModHom V W := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v =>
                          rm_smul W r (cmon_map (rm_hom f) v) |};
    cmon_map_zero := hm_smul_zero V W r f;
    cmon_map_plus := hm_smul_plus V W r f
  |};
  rm_map_smul := hm_smul_linear V W r f
|}.
Next Obligation.
  intros V W r f v w Hvw; simpl.
  now rewrite Hvw.
Qed.

(** *** The internal hom module

    Every module law below is the corresponding law of W read at each
    vector; none of them needs [Rcomm] again. *)
Program Definition HomMod (V W : RModObject R) : RModObject R := {|
  rm_ab   := hm_ab V W;
  rm_smul := hm_smul V W
|}.
Next Obligation.
  intros V W r s Hrs f g Hfg v; simpl.
  now rewrite Hrs, (Hfg v).
Qed.
Next Obligation. intros V W r f g v; simpl; apply rm_smul_distr_l. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros V W r s f v; simpl; apply rm_smul_assoc. Qed.
Next Obligation. intros V W f v; simpl; apply rm_smul_one. Qed.

(* The carrier IS the hom-set, on the nose. *)
Example HomMod_carrier (V W : RModObject R) :
  carrier (cmon_setoid (HomMod V W)) = RModHom V W := eq_refl.

End InternalHom.

(** ** Currying and uncurrying

    [hm_curry] sends f : V ⊗ W ⟶ X to v ↦ (w ↦ f (v ⊗ w)); [hm_uncurry]
    factors the bilinear map (v, w) ↦ (g v) w through the tensor.  Both
    round trips are below, and both are cheap for the reason the header
    gives: [tensor_med] computes on generators. *)

Section Adjunction.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH := (HomMod R Rcomm).

Section Curry.

Context {V W X : RModObject R}.
Context (f : TensorMod V W ~{RMod R}~> X).

(* [mval] is Instance/Mod/Monoidal.v's name for the underlying function of
   a module homomorphism; it is imported, not redeclared. *)
Definition cur_fun (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid W)) : carrier (cmon_setoid X) :=
  mval f (mt_gen v w).

(* w ↦ f (v ⊗ w) is a module homomorphism W ⟶ X: each clause is one
   clause of [tensor_gen] pushed through f. *)

Lemma cur_at_zero (v : carrier (cmon_setoid V)) :
  cur_fun v (cmon_zero W) ≈ cmon_zero X.
Proof.
  unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_r tensor_gen v).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_at_plus (v : carrier (cmon_setoid V)) :
  ∀ w w', cur_fun v (cmon_plus W w w')
            ≈ cmon_plus X (cur_fun v w) (cur_fun v w').
Proof.
  intros w w'; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v w'))).
  - apply proper_morphism, (rbl_add_r tensor_gen v w w').
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_at_smul (v : carrier (cmon_setoid V)) :
  ∀ r w, cur_fun v (rm_smul W r w) ≈ rm_smul X r (cur_fun v w).
Proof.
  intros r w; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_r tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition cur_at (v : carrier (cmon_setoid V)) : RModHom W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_fun v |};
    cmon_map_zero := cur_at_zero v;
    cmon_map_plus := cur_at_plus v
  |};
  rm_map_smul := cur_at_smul v
|}.
Next Obligation.
  intros v w w' Hw; unfold cur_fun, mval; simpl.
  apply proper_morphism, (rbl_respects tensor_gen); [reflexivity | exact Hw].
Qed.

(* And v ↦ cur_at v is a module homomorphism V ⟶ IH W X: the same three
   clauses of [tensor_gen] in the OTHER variable. *)

Lemma cur_out_zero : cur_at (cmon_zero V) ≈ cmon_zero (IH W X).
Proof.
  intro w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f) (cmon_zero (TensorMod V W))).
  - apply proper_morphism, (rbl_zero_l tensor_gen w).
  - apply (cmon_map_zero (rm_hom f)).
Qed.

Lemma cur_out_plus : ∀ v v',
  cur_at (cmon_plus V v v') ≈ cmon_plus (IH W X) (cur_at v) (cur_at v').
Proof.
  intros v v' w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (TensorMod V W) (mt_gen v w) (mt_gen v' w))).
  - apply proper_morphism, (rbl_add_l tensor_gen v v' w).
  - apply (cmon_map_plus (rm_hom f)).
Qed.

Lemma cur_out_smul : ∀ r v,
  cur_at (rm_smul V r v) ≈ rm_smul (IH W X) r (cur_at v).
Proof.
  intros r v w; simpl; unfold cur_fun, mval.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (TensorMod V W) r (mt_gen v w))).
  - apply proper_morphism, (rbl_smul_l tensor_gen r v w).
  - apply (rm_map_smul f r (mt_gen v w)).
Qed.

Program Definition hm_curry : V ~{RMod R}~> IH W X := {|
  rm_hom := {|
    cmon_map      := {| morphism := cur_at |};
    cmon_map_zero := cur_out_zero;
    cmon_map_plus := cur_out_plus
  |};
  rm_map_smul := cur_out_smul
|}.
Next Obligation.
  intros v v' Hv w; simpl; unfold cur_fun, mval.
  apply proper_morphism, (rbl_respects tensor_gen); [exact Hv | reflexivity].
Qed.

End Curry.

Arguments hm_curry {V W X} f.

Section Uncurry.

Context {V W X : RModObject R}.
Context (g : V ~{RMod R}~> IH W X).

(* (v, w) ↦ (g v) w is bilinear: linearity in w is g v's own linearity,
   linearity in v is g's, read at w. *)
Program Definition uncur_bilinear : RBilinear V W X := {|
  rbl_map := fun v w => mval (mval g v) w
|}.
Next Obligation.
  intros v v' Hv w w' Hw; simpl; unfold mval.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom g) v)) w').
  - apply proper_morphism, Hw.
  - exact (proper_morphism (cmon_map (rm_hom g)) v v' Hv w').
Qed.
Next Obligation.
  intros v v' w; simpl.
  exact (cmon_map_plus (rm_hom g) v v' w).
Qed.
Next Obligation.
  intros v w w'; simpl.
  apply (cmon_map_plus (rm_hom (cmon_map (rm_hom g) v)) w w').
Qed.
Next Obligation.
  intros r v w; simpl.
  exact (rm_map_smul g r v w).
Qed.
Next Obligation.
  intros r v w; simpl.
  apply (rm_map_smul (cmon_map (rm_hom g) v) r w).
Qed.

Definition hm_uncurry : TensorMod V W ~{RMod R}~> X :=
  tensor_med uncur_bilinear.

End Uncurry.

Arguments hm_uncurry {V W X} g.

(* The uncurried map's value at a generator is φ applied to the argument,
   at LEIBNIZ equality.  This is [tensor_med]'s own `eq_refl` generator
   equation (Instance/Mod/Tensor.v) instantiated, and it is what makes
   everything below cheap. *)
Example hm_uncurry_gen {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) v w :
  mval (hm_uncurry g) (mt_gen v w) = mval (mval g v) w := eq_refl.

(* Round trip one: extensionality, then the generator computation. *)
Lemma hm_uncurry_curry {V W X : RModObject R}
  (f : TensorMod V W ~{RMod R}~> X) : hm_uncurry (hm_curry f) ≈ f.
Proof.
  refine (tensor_hom_ext (hm_uncurry (hm_curry f)) f _).
  intros v w; reflexivity.
Qed.

(* Round trip two: pointwise definitional, no extensionality needed. *)
Lemma hm_curry_uncurry {V W X : RModObject R}
  (g : V ~{RMod R}~> IH W X) : hm_curry (hm_uncurry g) ≈ g.
Proof. intros v w; reflexivity. Qed.

End Adjunction.

(** ** The bijection, evaluation, and the universal property *)

Section ExpIso.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH  := (HomMod R Rcomm).
Notation cur := (hm_curry R Rcomm).
Notation unc := (hm_uncurry R Rcomm).

Program Definition exp_to (V W X : RModObject R) :
  {| carrier := TensorMod V W ~{RMod R}~> X |}
    ~{Sets}~> {| carrier := V ~{RMod R}~> IH W X |} := {|
  morphism := @hm_curry R Rcomm V W X
|}.
Next Obligation.
  intros V W X f f' Hf v w; simpl.
  exact (Hf (mt_gen v w)).
Qed.

Program Definition exp_from (V W X : RModObject R) :
  {| carrier := V ~{RMod R}~> IH W X |}
    ~{Sets}~> {| carrier := TensorMod V W ~{RMod R}~> X |} := {|
  morphism := @hm_uncurry R Rcomm V W X
|}.
Next Obligation.
  intros V W X g g' Hg.
  refine (tensor_hom_ext (unc g) (unc g') _).
  intros v w; exact (Hg v w).
Qed.

Program Definition exp_iso_Mod (V W X : RModObject R) :
  @Isomorphism Sets
    {| carrier := TensorMod V W ~{RMod R}~> X |}
    {| carrier := V ~{RMod R}~> IH W X |} := {|
  to   := exp_to V W X;
  from := exp_from V W X
|}.
Next Obligation.
  intros V W X g; exact (hm_curry_uncurry R Rcomm g).
Qed.
Next Obligation.
  intros V W X f; exact (hm_uncurry_curry R Rcomm f).
Qed.

(** Evaluation is the uncurried identity — which is exactly what the class
    takes [eval'] to be, so [smc_eval] below is `eq_refl`. *)
Definition eval_Mod (W X : RModObject R) :
  TensorMod (IH W X) W ~{RMod R}~> X :=
  unc (@id (RMod R) (IH W X)).

Example eval_Mod_gen (W X : RModObject R)
  (phi : carrier (cmon_setoid (IH W X))) (w : carrier (cmon_setoid W)) :
  mval (eval_Mod W X) (mt_gen phi w) = mval phi w := eq_refl.

(* The beta law.  [mt_fmap] is Instance/Mod/Monoidal.v's arrow action, and
   `bimap h id` reduces to it — see [smc_bimap] below. *)
Lemma ump_beta (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X) :
  f ≈ eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext f
            (eval_Mod W X ∘ mt_fmap (cur f) (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

(* Uniqueness: evaluate the hypothesis at a generator.  Nothing else. *)
Lemma ump_uniq (V W X : RModObject R) (f : TensorMod V W ~{RMod R}~> X)
  (h : V ~{RMod R}~> IH W X) :
  f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W) → cur f ≈ h.
Proof.
  intros Hh v w.
  exact (Hh (mt_gen v w)).
Qed.

Theorem ump_exponents_Mod (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  ∃! h : V ~{RMod R}~> IH W X,
    f ≈ eval_Mod W X ∘ mt_fmap h (@id (RMod R) W).
Proof.
  exists (cur f).
  - exact (ump_beta V W X f).
  - intros h Hh; exact (ump_uniq V W X f h Hh).
Qed.

End ExpIso.

(** ** THE HEADLINE

    Every field is filled by `:=` with no tactic and no transport.  The
    underlying symmetric monoidal structure is Instance/Mod/Monoidal.v's
    [ModSymmetric] itself, not a copy; the internal hom is [HomMod]; the
    bijection is [exp_iso_Mod]; the universal property is
    [ump_exponents_Mod].  A plain [Definition] rather than an [Instance],
    for the reason the header gives. *)

Definition RMod_SymMonClosed (R : RingObject)
  (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
      rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a) :
  @SymMonClosed (RMod R) := {|
  smc_is_symmetric := ModSymmetric Rcomm;
  exponent_obj     := HomMod R Rcomm;
  exp_iso          := @exp_iso_Mod R Rcomm;
  ump_exponents'   := @ump_exponents_Mod R Rcomm
|}.

(** *** What the class returns, measured at [eq_refl]

    Seven identifications.  Three of them concern the class's DEFINED
    fields — [curry'], [uncurry'] and [eval'] have bodies rather than being
    arguments, so a consumer could have received a repackaging; these
    record that they receive this file's own constants instead.  Two more
    check the join with Instance/Mod/Monoidal.v: the tensor's object action
    and the reduction of `bimap h id` to [mt_fmap h id]. *)

Section Slot.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation SMC := (RMod_SymMonClosed R Rcomm).

Example smc_symmetric :
  @smc_is_symmetric (RMod R) SMC = ModSymmetric Rcomm := eq_refl.

Example smc_exponent (V W : RModObject R) :
  @exponent_obj (RMod R) SMC V W = HomMod R Rcomm V W := eq_refl.

Example smc_curry (V W X : RModObject R)
  (f : TensorMod V W ~{RMod R}~> X) :
  @curry' (RMod R) SMC V W X f = hm_curry R Rcomm f := eq_refl.

Example smc_uncurry (V W X : RModObject R)
  (g : V ~{RMod R}~> HomMod R Rcomm W X) :
  @uncurry' (RMod R) SMC V W X g = hm_uncurry R Rcomm g := eq_refl.

Example smc_eval (W X : RModObject R) :
  @eval' (RMod R) SMC W X = eval_Mod R Rcomm W X := eq_refl.

Example smc_tensor (V W : RModObject R) :
  fobj[@tensor (RMod R) SMC] (V, W) = TensorMod V W := eq_refl.

Example smc_bimap (V W X : RModObject R)
  (h : V ~{RMod R}~> HomMod R Rcomm W X) :
  @bimap _ _ _ (@tensor (RMod R) SMC) _ _ _ _ h (@id (RMod R) W)
    = mt_fmap h (@id (RMod R) W) := eq_refl.

End Slot.

(** ** Naturality in all three variables

    The internal hom's two arrow actions, and then the six squares.  See
    the header for why both legs are stated. *)

Section Naturality.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).

Notation IH   := (HomMod R Rcomm).
Notation cur  := (hm_curry R Rcomm).
Notation unc  := (hm_uncurry R Rcomm).

(* Postcomposition: covariant in the target. *)
Program Definition ihom_post {W X X' : RModObject R}
  (k : X ~{RMod R}~> X') : IH W X ~{RMod R}~> IH W X' := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W X X' k phi |} |}
|}.
Next Obligation.
  intros W X X' k phi psi Hphi w; simpl; unfold Basics.compose.
  apply proper_morphism, (Hphi w).
Qed.
Next Obligation.
  intros W X X' k w; simpl; unfold Basics.compose.
  apply (cmon_map_zero (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k phi psi w; simpl; unfold Basics.compose.
  apply (cmon_map_plus (rm_hom k)).
Qed.
Next Obligation.
  intros W X X' k r phi w; simpl; unfold Basics.compose.
  apply (rm_map_smul k).
Qed.

(* Precomposition: contravariant in the source.  Every clause is
   [reflexivity] — precomposition moves no structure. *)
Program Definition ihom_pre {W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) : IH W X ~{RMod R}~> IH W' X := {|
  rm_hom := {| cmon_map := {| morphism := fun phi =>
    @rmod_hom_compose R W' W X phi j |} |}
|}.
Next Obligation.
  intros W W' X j phi psi Hphi w; simpl; unfold Basics.compose.
  exact (Hphi _).
Qed.
Next Obligation. intros W W' X j w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j phi psi w; simpl; reflexivity. Qed.
Next Obligation. intros W W' X j r phi w; simpl; reflexivity. Qed.

(** *** The three FORWARD squares

    Each holds by [reflexivity]: the two sides are pointwise the same
    term.  Note that this is agreement in the hom-SETOID; the whole
    morphism records are NOT Leibniz-equal, and the probe section pins
    that. *)

(* (a) In V, contravariantly: precomposing with i ⊗ id downstairs is
       precomposing with i upstairs. *)
Theorem cur_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap i (@id (RMod R) W)) ≈ cur f ∘ i.
Proof. intros v w; reflexivity. Qed.

(* (b) In W, contravariantly: precomposing with id ⊗ j downstairs is
       postcomposing with [ihom_pre j] upstairs. *)
Theorem cur_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (f : TensorMod V W ~{RMod R}~> X) :
  cur (f ∘ mt_fmap (@id (RMod R) V) j) ≈ ihom_pre j ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(* (c) In X, covariantly: postcomposing with k downstairs is
       postcomposing with [ihom_post k] upstairs. *)
Theorem cur_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (f : TensorMod V W ~{RMod R}~> X) :
  cur (k ∘ f) ≈ ihom_post k ∘ cur f.
Proof. intros v w; reflexivity. Qed.

(** *** The three BACKWARD squares

    NOT definitional.  Both sides are recursions over [MTerm] — the
    left-hand one built from a single bilinear map, the right-hand one a
    composite — so they agree at every generator but are different terms
    at a variable tensor.  Each needs one [tensor_hom_ext] and then
    [reflexivity], and nothing else: no [tensor_factor_commutes], no
    transitivity chain. *)

Theorem unc_natural_V {V V' W X : RModObject R}
  (i : V' ~{RMod R}~> V) (g : V ~{RMod R}~> IH W X) :
  unc (g ∘ i) ≈ unc g ∘ mt_fmap i (@id (RMod R) W).
Proof.
  refine (tensor_hom_ext (unc (g ∘ i))
            (unc g ∘ mt_fmap i (@id (RMod R) W)) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_W {V W W' X : RModObject R}
  (j : W' ~{RMod R}~> W) (g : V ~{RMod R}~> IH W X) :
  unc (ihom_pre j ∘ g) ≈ unc g ∘ mt_fmap (@id (RMod R) V) j.
Proof.
  refine (tensor_hom_ext (unc (ihom_pre j ∘ g))
            (unc g ∘ mt_fmap (@id (RMod R) V) j) _).
  intros v w; reflexivity.
Qed.

Theorem unc_natural_X {V W X X' : RModObject R}
  (k : X ~{RMod R}~> X') (g : V ~{RMod R}~> IH W X) :
  unc (ihom_post k ∘ g) ≈ k ∘ unc g.
Proof.
  refine (tensor_hom_ext (unc (ihom_post k ∘ g)) (k ∘ unc g) _).
  intros v w; reflexivity.
Qed.

End Naturality.

(** ** Acceptance tests over ℤ

    ℤ is commutative (Instance/Rng.v's [Int_Ring_commutative]), so the
    whole structure is inhabited at a concrete base.  The bilinear map is
    Instance/Mod/Tensor.v's own [Int_mul_bilinear] — nothing is
    rebuilt — and every Example below closes by `eq_refl`: these are
    computations, not equational arguments. *)

Local Notation Zc := Int_Ring_commutative.
Local Notation ZIH := (HomMod Int_Ring Zc).
Local Notation zg := (@mt_gen Int_Ring Int_RMod Int_RMod).

Definition Int_Mod_SymMonClosed : @SymMonClosed (RMod Int_Ring) :=
  RMod_SymMonClosed Int_Ring Int_Ring_commutative.

(* The ℤ-linear endomorphisms of ℤ, as a ℤ-module. *)
Definition ZEnd : RModObject Int_Ring := ZIH Int_RMod Int_RMod.

(* The pointwise action COMPUTES: (3 · id) 5 = 15. *)
Example Zsmul_computes :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z = 15%Z
  := eq_refl.

(* Two elements of the internal hom that are provably distinct, so it is
   not a subsingleton and the computations above are not degenerate. *)
Example ZEnd_nontrivial :
  mval (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 1%Z
    ≈ mval (@id (RMod Int_Ring) Int_RMod) 1%Z → False.
Proof. simpl; discriminate. Qed.

Definition Zmul_tensor_hom :
  TensorMod Int_RMod Int_RMod ~{RMod Int_Ring}~> Int_RMod :=
  tensor_med Int_mul_bilinear.

(* Currying computes: cur(multiplication) at 2, applied to 3, is 6. *)
Example Zcur_computes :
  mval (mval (hm_curry Int_Ring Zc Zmul_tensor_hom) 2%Z) 3%Z = 6%Z
  := eq_refl.

(* And so does the round trip, at a generator. *)
Example Zuncur_computes :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 4%Z 5%Z) = 20%Z := eq_refl.

(* Evaluation computes, through the file's own [eval_Mod] ... *)
Example Zeval_computes :
  mval (eval_Mod Int_Ring Zc Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 15%Z := eq_refl.

(* ... and through the CLASS's [eval'], which is the same term. *)
Example Zsmc_eval :
  mval (@eval' (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod)
       (@mt_gen Int_Ring ZEnd Int_RMod
          (rm_smul ZEnd 4%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z)
    = 20%Z := eq_refl.

Example Zsmc_exp :
  @exponent_obj (RMod Int_Ring) Int_Mod_SymMonClosed Int_RMod Int_RMod
    = ZEnd := eq_refl.

(** ** Probes

    THIRTEEN negatives of THREE KINDS — two TYPING, three CONVERSION,
    eight FORMABILITY — kept lexically apart, each beside an APPLIED
    positive control, plus a scope-free instrument check.  With
    Instance/Mod/Monoidal.v's eight that is twenty-one negatives across the
    pair, in four kinds; the two instrument checks are guards and are not
    counted among them, so the two files carry twenty-three [Fail]
    commands in all.  A [Fail] that succeeds prints nothing under this
    repository's [coqc], so each negative below
    was stripped of its [Fail] and compiled alone, and its failure KIND
    read off the WHOLE error message rather than the tail: the TYPING two
    report a bare type mismatch with no `cannot unify` and no universe
    clause, the CONVERSION three end in `cannot unify`, and the
    FORMABILITY eight end in a universe inconsistency naming the levels
    the probe section declared — `Cannot enforce rc = ra because
    ra < rc` for the five that test FIRST=THIRD, and `Cannot enforce
    rb = ra because rb < ra` for the three that test FIRST=SECOND. *)

(* INSTRUMENT CHECK — scope-free, guards that [Fail] is doing anything. *)
Fail Example mod_closed_instrument : (true = false) := eq_refl.

(** *** Kind 1: TYPING *)

Section ProbeTyping.

Context (R : RingObject).
Context (V W : RModObject R).
Context (r : carrier (rig_setoid (ring_rig R))).
Context (f : RModHom V W).

(* NEGATIVE 1.  The [Default Proof Using] instrument, read from outside
   the proof: [hm_smul_linear] carries [Rcomm] as an ARGUMENT, so [V]
   lands in the commutativity slot and the application is ill-typed. *)
Fail Check (@hm_smul_linear R V W r f).

(* CONTROLS.  Its two siblings — same section, same statement shape, same
   [Program] block — do not, because their PROOFS do not use it. *)
Check (@hm_smul_zero R V W r f).
Check (@hm_smul_plus R V W r f).

End ProbeTyping.

(* NEGATIVE 2.  Engineering note: [mt_gen] at a hom-module needs explicit
   indices — the inner generator elaborates before the outer tensor is
   known, and the error blames the second argument. *)
Fail Check (mt_gen (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(* CONTROL: the annotated form. *)
Check (@mt_gen Int_Ring ZEnd Int_RMod
         (rm_smul ZEnd 3%Z (@id (RMod Int_Ring) Int_RMod)) 5%Z).

(** *** Kind 2: CONVERSION *)

(* NEGATIVE 3.  The round trip is an `≈`, not a Leibniz identity of
   morphism records: [hm_uncurry (hm_curry f)] is a [tensor_med] over
   [uncur_bilinear], while [Zmul_tensor_hom] is one over
   [Int_mul_bilinear], and the two bilinear records are different terms. *)
Fail Example probe_rt_strict :
  hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom)
    = Zmul_tensor_hom := eq_refl.

(* CONTROL: at a generator it IS a Leibniz identity, so the obstruction is
   exactly extensionality and not the generator computation. *)
Example probe_rt_gen :
  mval (hm_uncurry Int_Ring Zc (hm_curry Int_Ring Zc Zmul_tensor_hom))
       (zg 2%Z 3%Z)
    = mval Zmul_tensor_hom (zg 2%Z 3%Z) := eq_refl.

Section ProbeConversion.

Context (R : RingObject).
Context (Rcomm : ∀ a b : carrier (rig_setoid (ring_rig R)),
            rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a).
Context (V V' W X : RModObject R).
Context (i : V' ~{RMod R}~> V).
Context (g : V ~{RMod R}~> HomMod R Rcomm W X).
Context (v : carrier (cmon_setoid V')) (w : carrier (cmon_setoid W)).

(* NEGATIVE 4.  [unc_natural_V] at Leibniz strength: refuted.  This is
   what the [tensor_hom_ext] in its proof is buying. *)
Fail Example probe_unc_nat_strict :
  hm_uncurry R Rcomm (g ∘ i)
    = hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W) := eq_refl.

(* CONTROL: the same statement at a generator, at Leibniz `=`. *)
Example probe_unc_nat_gen :
  mval (hm_uncurry R Rcomm (g ∘ i)) (mt_gen v w)
    = mval (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
           (mt_gen v w) := eq_refl.

(* NEGATIVE 5.  The FORWARD square is `≈` by [reflexivity], but the two
   morphism RECORDS are still not Leibniz-equal — so "holds by
   [reflexivity]" must not be over-read as "is the same term". *)
Fail Example probe_cur_nat_strict :
  hm_curry R Rcomm (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))
    = hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i := eq_refl.

(* CONTROL: pointwise, at Leibniz `=`, which is what [cur_natural_V]'s
   [reflexivity] actually discharges. *)
Example probe_cur_nat_at :
  mval (mval (hm_curry R Rcomm
                (hm_uncurry R Rcomm g ∘ mt_fmap i (@id (RMod R) W))) v) w
    = mval (mval (hm_curry R Rcomm (hm_uncurry R Rcomm g) ∘ i) v) w
  := eq_refl.

End ProbeConversion.

(** *** Kind 3: FORMABILITY (universes)

    The header's measurement, guarded.  A library file CAN carry a
    section-local [Universes]/[Constraint] block without constraining
    itself — Instance/Fun/Group.v establishes that, and the two
    Test/Probe files that claimed otherwise are corrected there — so the
    probes live here rather than in a separate file.  All five controls
    are APPLIED, at the very levels where the five negatives are
    rejected. *)

Section ProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(* CONTROLS: formable with the ring's first and third universes declared
   strictly apart. *)
Check (RMod Ru).
Check (TensorMod V W).
Check (@tensor_gen Ru V W).
Check (HomMod Ru Rcu V W).
Check (@ihom_post Ru Rcu V W W).

(* CONTROLS 6, 7 and 8, WHICH USED TO BE NEGATIVES.  An earlier revision read:
   "NEGATIVE 6.  The DONOR.  [tensor_med] (Instance/Mod/Tensor.v) already
   identifies the ring's first and third universes, while [TensorMod] and
   [tensor_gen] above do not"; "NEGATIVE 7.  Instance/Mod/Monoidal.v's arrow
   action inherits it"; "NEGATIVE 8.  Hence this file's currying."  All three
   were re-measured after the PR "algebraic carriers are sets" (2026-09-17)
   and all three are now FORMABLE at the declared separation.  The cause is
   the move of [mt_eq] to [Prop]: [tensor_med_respects] no longer inducts on a
   [Type]-valued relation into a [Type]-valued goal but runs through [pequiv],
   and the identification the old proof forced is gone.  Negatives 9 and 10
   below still fire, which is the instrument check that the section still
   constrains anything at all. *)
Check (@tensor_med Ru V W).
Check (@mt_fmap Ru V W).
Check (@hm_curry Ru Rcu V W W).

(* NEGATIVE 9.  Instance/Mod/Monoidal.v's symmetric structure.  The ring
   is given EXPLICITLY: written `ModSymmetric Rcu` this probe is a FALSE
   GUARD — it still fails, but on an unresolved implicit (`?R`) with a
   plain type mismatch and no universe clause at all, so it would say
   nothing about the constraint.  Compare the trap
   Structure/Limit/Product/Finite.v records. *)
Fail Check (@ModSymmetric Ru Rcu).

(* NEGATIVE 10.  And therefore the headline.  Note the binder/block trap:
   `RMod_SymMonClosed@{u u0}`'s constraint block carries no equation at
   all, and only the binder `R : RingObject@{u0 u0 u0}` reveals this. *)
Fail Check (RMod_SymMonClosed Ru Rcu).

End ProbeUniverses.

(** The OTHER identification, guarded separately.

    The section above declares the ring's FIRST and THIRD universes apart
    and so tests only that equation.  This one declares the FIRST and
    SECOND apart, which is the identification the header attributes to
    Instance/Mod/Monoidal.v's [ModMonoidal] rather than to anything
    declared here.  Without this section that attribution would be
    measured and unguarded, and nothing in the build would notice an
    upstream annotation changing it. *)

Section ProbeMiddleUniverse.

Universes ra rb rc.
Constraint rb < ra.

Context (Ru : RingObject@{rc ra rb}).
Context (Rcu : ∀ a b : carrier (rig_setoid (ring_rig Ru)),
            rig_mul (ring_rig Ru) a b ≈ rig_mul (ring_rig Ru) b a).
Context (V W : RModObject Ru).

(* CONTROLS: nothing this file declares identifies the ring's first two
   universes, so all four are formable with them declared strictly apart.
   Each is APPLIED to [Ru], which is the argument carrying the levels. *)
Check (@hm_curry Ru Rcu V W W).
Check (HomMod Ru Rcu V W).
Check (@exp_iso_Mod Ru Rcu).
Check (@ump_exponents_Mod Ru Rcu).

(* NEGATIVE 11.  The donor: Instance/Mod/Monoidal.v's packaged monoidal
   structure, which identifies the first two where none of its own
   components does. *)
Fail Check (@ModMonoidal Ru Rcu).

(* NEGATIVE 12.  Inherited by the symmetric packaging. *)
Fail Check (@ModSymmetric Ru Rcu).

(* NEGATIVE 13.  And hence by the headline — whose own constraint block
   is still empty, the equation living in the binder alone. *)
Fail Check (@RMod_SymMonClosed Ru Rcu).

End ProbeMiddleUniverse.
