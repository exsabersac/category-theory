Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/quotient+module
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_module

   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The scalar action distributes over subtraction. *)
Lemma rm_smul_sub {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) (x y : carrier (cmon_setoid M)) :
  rm_smul M r (ab_sub M x y)
    ≈ ab_sub M (rm_smul M r x) (rm_smul M r y).
Proof.
  unfold ab_sub.
  rewrite rm_smul_distr_l.
  now rewrite rm_smul_neg_r.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record Submodule {R : RingObject} (M : RModObject R) := {
  smod_mem : carrier (cmon_setoid M) → Type;

  (* (1) ≈-saturation *)
  smod_resp : ∀ a b : carrier (cmon_setoid M),
    a ≈ b → smod_mem a → smod_mem b;
  (* (2) zero *)
  smod_zero : smod_mem (cmon_zero M);
  (* (3) closure under addition *)
  smod_plus : ∀ a b : carrier (cmon_setoid M),
    smod_mem a → smod_mem b → smod_mem (cmon_plus M a b);
  (* (4) closure under the scalar action *)
  smod_smul : ∀ (r : carrier (rig_setoid (ring_rig R)))
                (a : carrier (cmon_setoid M)),
    smod_mem a → smod_mem (rm_smul M r a)
}.

Arguments smod_mem {R M} _ _.
Arguments smod_resp {R M} _ _ _ _ _.
Arguments smod_zero {R M} _.
Arguments smod_plus {R M} _ _ _ _ _.
Arguments smod_smul {R M} _ _ _ _.

(* Saturation in the argument-implicit shape the proofs below want. *)
Definition smod_at {R : RingObject} {M : RModObject R} (S : Submodule M)
  {a b : carrier (cmon_setoid M)} (Hab : a ≈ b) (Ha : smod_mem S a) :
  smod_mem S b := smod_resp S a b Hab Ha.

(* THE FIFTH FIELD THAT IS NOT A FIELD: closure under negation, because
   -a is (-1)·a.  The scalar (-1) exists because R is a RING; over a rig
   this would have to be assumed. *)
Lemma smod_neg {R : RingObject} {M : RModObject R} (S : Submodule M)
  (a : carrier (cmon_setoid M)) : smod_mem S a → smod_mem S (ab_neg M a).
Proof.
  intro Ha.
  apply (smod_at S (a := rm_smul M (ring_neg R (rig_one (ring_rig R))) a)).
  - rewrite (rm_smul_neg_l M (rig_one (ring_rig R)) a).
    now rewrite (rm_smul_one M a).
  - exact (smod_smul S _ _ Ha).
Qed.

(* Closure under subtraction, the shape every proof below uses. *)
Lemma smod_sub {R : RingObject} {M : RModObject R} (S : Submodule M)
  (a b : carrier (cmon_setoid M)) :
  smod_mem S a → smod_mem S b → smod_mem S (ab_sub M a b).
Proof.
  intros Ha Hb.
  exact (smod_plus S _ _ Ha (smod_neg S _ Hb)).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma smod_conjugate_inert {R : RingObject} {M : RModObject R}
  (t a : carrier (cmon_setoid M)) :
  ab_sub M (cmon_plus M t a) t ≈ a.
Proof. apply ab_sub_add_cancel. Qed.

Theorem smod_normal {R : RingObject} {M : RModObject R} (S : Submodule M)
  (t a : carrier (cmon_setoid M)) :
  smod_mem S a → smod_mem S (ab_sub M (cmon_plus M t a) t).
Proof.
  intro Ha.
  exact (smod_at S (symmetry (smod_conjugate_inert t a)) Ha).
Qed.

(** ** The submodule as an object of [RMod R] *)

Definition smod_carrier {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Type :=
  { a : carrier (cmon_setoid M) & smod_mem S a }.

Program Definition smod_setoid {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Setoid (smod_carrier S) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R M S; equivalence; now transitivity (`1 y).
Qed.

Definition SubmoduleMod {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab :=
      {| ab_cmon :=
           {| cmon_setoid := {| carrier := smod_carrier S
                              ; is_setoid := smod_setoid S |}
            ; cmon_zero := existT _ (cmon_zero M) (smod_zero S)
            ; cmon_plus := fun p q =>
                existT _ (cmon_plus M (`1 p) (`1 q))
                  (smod_plus S _ _ (`2 p) (`2 q))
            (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
            ; cmon_prop :=
                sigma_first_PropEquiv (smod_setoid S)
                  (fun _ _ h => h) (fun _ _ h => h) (cmon_prop M) |}
       ; ab_neg := fun p =>
           existT _ (ab_neg M (`1 p)) (smod_neg S _ (`2 p)) |};
    rm_smul := fun r p =>
      existT _ (rm_smul M r (`1 p)) (smod_smul S r _ (`2 p))
  |}.
  - (* cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *; now rewrite Hp, Hq.
  - (* cmon_plus_assoc *)
    intros p q u; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros p q; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros p; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left *)
    intros p; simpl; apply ab_neg_left.
  - (* rm_smul_respects *)
    intros r s Hrs p q Hpq; simpl in *; now rewrite Hrs, Hpq.
  - (* rm_smul_distr_l *)
    intros r p q; simpl; apply rm_smul_distr_l.
  - (* rm_smul_distr_r *)
    intros r s p; simpl; apply rm_smul_distr_r.
  - (* rm_smul_assoc *)
    intros r s p; simpl; apply rm_smul_assoc.
  - (* rm_smul_one *)
    intros p; simpl; apply rm_smul_one.
Defined.

(* The inclusion of a submodule: the first projection. *)
Program Definition smod_incl {R : RingObject} {M : RModObject R}
  (S : Submodule M) : SubmoduleMod S ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun p : smod_carrier S => `1 p |} |}
|}.
Next Obligation. intros R M S p q Hpq; exact Hpq. Qed.
Next Obligation. intros R M S; simpl; reflexivity. Qed.
Next Obligation. intros R M S p q; simpl; reflexivity. Qed.
Next Obligation. intros R M S r p; simpl; reflexivity. Qed.

Lemma smod_incl_injective {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModInjective (smod_incl S).
Proof. intros p q Hpq; exact Hpq. Qed.

Lemma smod_incl_monic {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Monic (smod_incl S).
Proof. apply rmod_injective_monic, smod_incl_injective. Qed.

(** ** The quotient relation *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mquot_rel {R : RingObject} {M : RModObject R} (S : Submodule M)
  (x y : carrier (cmon_setoid M)) : Prop :=
  inhabited (smod_mem S (ab_sub M x y)).

Section QuotientRelation.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S : Submodule M).

Lemma mquot_rel_of_equiv (x y : carrier (cmon_setoid M)) :
  x ≈ y → mquot_rel S x y.
Proof.
  intro Hxy; unfold mquot_rel.
  constructor.
  apply (smod_at S (a := cmon_zero M)); [| exact (smod_zero S) ].
  rewrite <- Hxy.
  symmetry; apply ab_sub_self.
Qed.

Lemma mquot_rel_refl (x : carrier (cmon_setoid M)) : mquot_rel S x x.
Proof. apply mquot_rel_of_equiv; reflexivity. Qed.

Lemma mquot_rel_sym (x y : carrier (cmon_setoid M)) :
  mquot_rel S x y → mquot_rel S y x.
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := ab_neg M (ab_sub M x y))).
  - apply ab_sub_neg.
  - exact (smod_neg S _ K).
Qed.

Lemma mquot_rel_trans (x y z : carrier (cmon_setoid M)) :
  mquot_rel S x y → mquot_rel S y z → mquot_rel S x z.
Proof.
  unfold mquot_rel; intros [K1] [K2].
  constructor.
  apply (smod_at S (a := cmon_plus M (ab_sub M x y) (ab_sub M y z))).
  - apply ab_sub_trans.
  - exact (smod_plus S _ _ K1 K2).
Qed.

(* Addition respects the relation.  Where the group case spends
   NORMALITY ([quot_rel_mul]), this spends COMMUTATIVITY, inside
   [ab_sub_plus]. *)
Lemma mquot_rel_plus (x x' y y' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S y y' →
  mquot_rel S (cmon_plus M x y) (cmon_plus M x' y').
Proof.
  unfold mquot_rel; intros [K1] [K2].
  constructor.
  apply (smod_at S (a := cmon_plus M (ab_sub M x x') (ab_sub M y y'))).
  - apply ab_sub_plus.
  - exact (smod_plus S _ _ K1 K2).
Qed.

(* Negation respects the relation; again no normality, only
   [ab_sub_neg]. *)
Lemma mquot_rel_neg (x x' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S (ab_neg M x) (ab_neg M x').
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := ab_neg M (ab_sub M x x'))).
  - now rewrite ab_sub_neg, ab_sub_neg_neg.
  - exact (smod_neg S _ K).
Qed.

(* The scalar action respects the relation.  THIS is the one place the
   submodule's fourth field is spent, and it has no counterpart in the
   group case at all. *)
Lemma mquot_rel_smul (r : carrier (rig_setoid (ring_rig R)))
  (x x' : carrier (cmon_setoid M)) :
  mquot_rel S x x' → mquot_rel S (rm_smul M r x) (rm_smul M r x').
Proof.
  unfold mquot_rel; intros [K].
  constructor.
  apply (smod_at S (a := rm_smul M r (ab_sub M x x'))).
  - apply rm_smul_sub.
  - exact (smod_smul S _ _ K).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mquot_rel_zero_iff (x : carrier (cmon_setoid M)) :
  mquot_rel S x (cmon_zero M) ↔ inhabited (smod_mem S x).
Proof.
  split; intros [K]; unfold mquot_rel in *; constructor.
  - exact (smod_at S (ab_sub_zero_r M x) K).
  - exact (smod_at S (symmetry (ab_sub_zero_r M x)) K).
Qed.

(* The half of the biconditional that keeps its [Type]-valued hypothesis:
   nothing is truncated on the way in. *)
Lemma mquot_rel_of_mem (x : carrier (cmon_setoid M)) :
  smod_mem S x → mquot_rel S x (cmon_zero M).
Proof.
  intro K; unfold mquot_rel; constructor.
  exact (smod_at S (symmetry (ab_sub_zero_r M x)) K).
Qed.

Program Definition mquot_setoid : Setoid (carrier (cmon_setoid M)) := {|
  equiv := mquot_rel S
|}.
Next Obligation.
  constructor.
  - exact mquot_rel_refl.
  - exact mquot_rel_sym.
  - exact mquot_rel_trans.
Qed.

End QuotientRelation.

Arguments mquot_setoid {R M} S.

(** ** The quotient module and its projection *)

Definition QuotientMod {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab :=
      {| ab_cmon :=
           {| cmon_setoid := {| carrier := carrier (cmon_setoid M)
                              ; is_setoid := mquot_setoid S |}
            ; cmon_zero := cmon_zero M
            ; cmon_plus := cmon_plus M
            (* [mquot_rel] IS a [Prop] relation, so it is its own mirror. *)
            ; cmon_prop :=
                @PropEquiv_of_relation _ (mquot_setoid S) (mquot_rel S)
                  (fun _ _ h => h) (fun _ _ h => h) |}
       ; ab_neg := ab_neg M |};
    rm_smul := rm_smul M
  |}.
  - (* cmon_plus_respects *)
    intros x x' Hx y y' Hy; now apply mquot_rel_plus.
  - (* cmon_plus_assoc *)
    intros x y z; apply mquot_rel_of_equiv, cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros x y; apply mquot_rel_of_equiv, cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros x; apply mquot_rel_of_equiv, cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros x y Hxy; now apply mquot_rel_neg.
  - (* ab_neg_left *)
    intros x; apply mquot_rel_of_equiv, ab_neg_left.
  - (* rm_smul_respects *)
    intros r s Hrs x y Hxy.
    apply (mquot_rel_trans S _ (rm_smul M r y)).
    + now apply mquot_rel_smul.
    + apply mquot_rel_of_equiv; now rewrite Hrs.
  - (* rm_smul_distr_l *)
    intros r x y; apply mquot_rel_of_equiv, rm_smul_distr_l.
  - (* rm_smul_distr_r *)
    intros r s x; apply mquot_rel_of_equiv, rm_smul_distr_r.
  - (* rm_smul_assoc *)
    intros r s x; apply mquot_rel_of_equiv, rm_smul_assoc.
  - (* rm_smul_one *)
    intros x; apply mquot_rel_of_equiv, rm_smul_one.
Defined.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The projection: the identity function, read from the fine setoid into
   the coarse one. *)
Program Definition mquot_proj {R : RingObject} {M : RModObject R}
  (S : Submodule M) : M ~{RMod R}~> QuotientMod S := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid M) => x |} |}
|}.
Next Obligation. intros R M S x y Hxy; apply mquot_rel_of_equiv, Hxy. Qed.
Next Obligation. intros R M S; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S r x; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_proj_kills {R : RingObject} {M : RModObject R}
  (S : Submodule M) (x : carrier (cmon_setoid M)) :
  smod_mem S x →
  cmon_map (rm_hom (mquot_proj S)) x ≈ cmon_zero (QuotientMod S).
Proof.
  intro Hx; simpl.
  exact (mquot_rel_of_mem S x Hx).
Qed.

(* Conversely: the projection's kernel is exactly S, as a
   biconditional. *)
(* Restated in lockstep with [mquot_rel_zero_iff]: the right-hand side is the
   truncation.  [mquot_proj_kills] above keeps the [Type]-valued direction. *)
Lemma mquot_proj_kernel {R : RingObject} {M : RModObject R}
  (S : Submodule M) (x : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (mquot_proj S)) x ≈ cmon_zero (QuotientMod S)
    ↔ inhabited (smod_mem S x).
Proof. exact (mquot_rel_zero_iff S x). Qed.

Lemma mquot_proj_surjective {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RModSurjective (mquot_proj S).
Proof.
  intro x; exists x; simpl; apply mquot_rel_refl.
Qed.

Lemma mquot_proj_epic {R : RingObject} {M : RModObject R}
  (S : Submodule M) : Epic (mquot_proj S).
Proof. apply rmod_surjective_epic, mquot_proj_surjective. Qed.

(** ** The functor of homomorphisms killing S *)

Definition MKills {R : RingObject} {M : RModObject R} (S : Submodule M)
  (K : RModObject R) : Type :=
  { h : M ~{RMod R}~> K
  & ∀ a : carrier (cmon_setoid M), smod_mem S a →
      cmon_map (rm_hom h) a ≈ cmon_zero K }.

Program Definition MKills_Setoid {R : RingObject} {M : RModObject R}
  (S : Submodule M) (K : RModObject R) : Setoid (MKills S K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros R M S K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q u Hpq Hqu; now transitivity (`1 q).
Qed.

Lemma MKills_post {R : RingObject} {M : RModObject R} (S : Submodule M)
  {K K' : RModObject R} (k : K ~{RMod R}~> K') (p : MKills S K)
  (a : carrier (cmon_setoid M)) :
  smod_mem S a → cmon_map (rm_hom (k ∘ `1 p)) a ≈ cmon_zero K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (cmon_map_zero (rm_hom k)).
Qed.

Program Definition MKillsFunctor {R : RingObject} {M : RModObject R}
  (S : Submodule M) : RMod R ⟶ Sets := {|
  fobj := fun K => {| carrier := MKills S K
                    ; is_setoid := MKills_Setoid S K |};
  fmap := fun K K' k =>
    {| morphism := fun p : MKills S K =>
         existT _ (k ∘ `1 p) (MKills_post S k p) |}
|}.
Next Obligation.
  intros R M S K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros R M S K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros R M S K p a; simpl; reflexivity. Qed.
Next Obligation. intros R M S K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism *)

Section Mediator.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S : Submodule M).
Context {K : RModObject R}.
Context (p : MKills S K).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mkills_descends (x y : carrier (cmon_setoid M)) :
  mquot_rel S x y →
  cmon_map (rm_hom (`1 p)) x ≈ cmon_map (rm_hom (`1 p)) y.
Proof.
  intro Hxy.
  apply (fst (ab_sub_eq_zero_iff K _ _)).
  rewrite <- (ab_map_sub (rm_hom (`1 p)) x y).
  (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply (@pequiv_to _ _ (cmon_prop K)).
  destruct Hxy as [Hxy].
  apply pequiv_from.
  exact (`2 p _ Hxy).
Qed.

Program Definition mquot_med : QuotientMod S ~{RMod R}~> K := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S)) =>
                     cmon_map (rm_hom (`1 p)) x |} |}
|}.
Next Obligation. intros x y Hxy; exact (mkills_descends x y Hxy). Qed.
Next Obligation. simpl; apply (cmon_map_zero (rm_hom (`1 p))). Qed.
Next Obligation. intros x y; simpl; apply (cmon_map_plus (rm_hom (`1 p))). Qed.
Next Obligation. intros r x; simpl; apply (rm_map_smul (`1 p)). Qed.

(* The mediator's defining triangle holds by reflexivity, the projection
   being the identity function. *)
Lemma mquot_med_commutes : mquot_med ∘ mquot_proj S ≈ `1 p.
Proof. intro x; simpl; reflexivity. Qed.

Lemma mquot_med_unique (v : QuotientMod S ~{RMod R}~> K)
  (Hv : v ∘ mquot_proj S ≈ `1 p) : mquot_med ≈ v.
Proof. intro x; simpl; symmetry; exact (Hv x). Qed.

End Mediator.

Arguments mquot_med {R M} S {K} p.

(** ** Mac Lane §III.1 Exercise 5: ⟨A/S, p⟩ is a universal element *)

Definition mquot_elem {R : RingObject} {M : RModObject R}
  (S : Submodule M) : MKills S (QuotientMod S) :=
  existT _ (mquot_proj S) (mquot_proj_kills S).

Program Definition mquot_universal_element {R : RingObject}
  {M : RModObject R} (S : Submodule M) :
  AUniversalElement (MKillsFunctor S) (QuotientMod S) := {|
  aue_elem := mquot_elem S
|}.
Next Obligation.
  intros R M S K x.
  unshelve refine {| unique_obj := mquot_med S x |}.
  - exact (mquot_med_commutes S x).
  - intros v Hv; simpl in *.
    exact (mquot_med_unique S x v Hv).
Defined.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example mquot_universal_elem_is_proj {R : RingObject} {M : RModObject R}
  (S : Submodule M) :
  `1 (@aue_elem _ (MKillsFunctor S) (QuotientMod S)
        (mquot_universal_element S)) = mquot_proj S.
Proof. reflexivity. Qed.

Example mquot_universal_med_is_mquot_med {R : RingObject}
  {M : RModObject R} (S : Submodule M) {K : RModObject R} (x : MKills S K) :
  unique_obj (@aue_universal _ (MKillsFunctor S) (QuotientMod S)
                (mquot_universal_element S) K x)
    = mquot_med S x.
Proof. reflexivity. Qed.

(** ** The homomorphism theorem, as a biconditional *)

Theorem mod_hom_theorem {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K) :
  (∀ a : carrier (cmon_setoid M), smod_mem S a →
     cmon_map (rm_hom h) a ≈ cmon_zero K)
    ↔ (∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : M ~{RMod R}~> K =>
                         ∀ a : carrier (cmon_setoid M), smod_mem S a →
                           cmon_map (rm_hom h) a ≈ cmon_zero K) h Hkill).
    unshelve refine {| unique_obj := mquot_med S x |}.
    + exact (mquot_med_commutes S x).
    + intros v Hv.
      exact (mquot_med_unique S x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (cmon_map (rm_hom u)
                    (cmon_map (rm_hom (mquot_proj S)) a)).
    + symmetry; exact (Hu a).
    + transitivity (cmon_map (rm_hom u) (cmon_zero (QuotientMod S))).
      * apply proper_morphism.
        exact (mquot_proj_kills S a Ha).
      * exact (cmon_map_zero (rm_hom u)).
Qed.

Definition mod_hom_theorem_factor {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K)
  (Hkill : ∀ a : carrier (cmon_setoid M), smod_mem S a →
     cmon_map (rm_hom h) a ≈ cmon_zero K) :
  ∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h :=
  fst (mod_hom_theorem S h) Hkill.

Definition mod_hom_theorem_kills {R : RingObject} {M K : RModObject R}
  (S : Submodule M) (h : M ~{RMod R}~> K)
  (Hfac : ∃! u : QuotientMod S ~{RMod R}~> K, u ∘ mquot_proj S ≈ h) :
  ∀ a : carrier (cmon_setoid M), smod_mem S a →
    cmon_map (rm_hom h) a ≈ cmon_zero K :=
  snd (mod_hom_theorem S h) Hfac.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition KernelSub {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Submodule M := {|
  smod_mem := fun a : carrier (cmon_setoid M) =>
                cmon_map (rm_hom f) a ≈ cmon_zero N
|}.
Next Obligation.
  intros R M N f a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation.
  intros R M N f; simpl; apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f a b Ha Hb; simpl in *.
  rewrite (cmon_map_plus (rm_hom f)), Ha, Hb.
  apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R M N f r a Ha; simpl in *.
  rewrite (rm_map_smul f), Ha.
  apply rm_smul_zero_r.
Qed.

Example KernelSub_mem {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (a : carrier (cmon_setoid M)) :
  smod_mem (KernelSub f) a = (cmon_map (rm_hom f) a ≈ cmon_zero N).
Proof. reflexivity. Qed.

(* The submodule object of the kernel has the same carrier as
   Instance/Mod.v's [RModKernel], by convertibility. *)
Example KernelSub_carrier_is_RModKernel {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  carrier (cmon_setoid (SubmoduleMod (KernelSub f)))
    = carrier (cmon_setoid (RModKernel f)).
Proof. reflexivity. Qed.

(* The image of f, as a submodule of the codomain.  Membership carries
   the preimage as DATA (the tree's ∃ is [sigT]), so nothing is
   chosen. *)
Program Definition ImageSubmod {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Submodule N := {|
  smod_mem := fun b : carrier (cmon_setoid N) =>
                { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ b }
|}.
Next Obligation.
  intros R M N f b b' Hbb' [a Ha].
  exists a; now rewrite Ha.
Qed.
Next Obligation.
  intros R M N f; simpl.
  exists (cmon_zero M); apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f b b' [a Ha] [a' Ha'].
  exists (cmon_plus M a a').
  rewrite (cmon_map_plus (rm_hom f)).
  now rewrite Ha, Ha'.
Qed.
Next Obligation.
  intros R M N f r b [a Ha].
  exists (rm_smul M r a).
  rewrite (rm_map_smul f).
  now rewrite Ha.
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Reconcile.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Ltac recon_refl :=
  intros; simpl;
  first [ apply (mquot_rel_refl (ImageSubmod f)) | apply ab_coset_refl ].

Theorem rmod_quotient_relations_agree (x y : carrier (cmon_setoid N)) :
  ab_coset_eq (rm_hom f) x y ↔ mquot_rel (ImageSubmod f) x y.
Proof.
  (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  split.
  - intros [a Ha]; apply pequiv_to in Ha.
    unfold mquot_rel; simpl.
    constructor.
    exists a.
    rewrite Ha.
    symmetry; apply ab_sub_add_cancel.
  - intros [Hm]; simpl in Hm.
    destruct Hm as [a Ha]; simpl in Ha.
    exists a.
    apply pequiv_from.
    rewrite Ha.
    symmetry; apply ab_add_sub_cancel.
Qed.

(* The identification, in [RMod R].  Both legs are the identity on
   elements; what they transport is the witness, through the
   biconditional above. *)
Program Definition RModQuotient_is_quotient_by_image :
  RModQuotient f ≅[RMod R] QuotientMod (ImageSubmod f) := {|
  to := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (RModQuotient f)) => x |} |} |};
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod (ImageSubmod f)))
                   => x |} |} |}
|}.
Next Obligation.
  intros x y Hxy; exact (fst (rmod_quotient_relations_agree x y) Hxy).
Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation.
  intros x y Hxy; exact (snd (rmod_quotient_relations_agree x y) Hxy).
Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.
Next Obligation. recon_refl. Qed.

(* And the projections agree under it: the identification carries
   Instance/Mod.v's projection to this file's. *)
Lemma RModQuotient_proj_agrees :
  to RModQuotient_is_quotient_by_image ∘ rmod_quot_proj f
    ≈ mquot_proj (ImageSubmod f).
Proof. recon_refl. Qed.

End Reconcile.

(** ** Quotients by coextensive submodules agree *)

Program Definition mquot_congr {R : RingObject} {M : RModObject R}
  (S S' : Submodule M)
  (H1 : ∀ a : carrier (cmon_setoid M), smod_mem S a → smod_mem S' a)
  (H2 : ∀ a : carrier (cmon_setoid M), smod_mem S' a → smod_mem S a) :
  QuotientMod S ≅[RMod R] QuotientMod S' := {|
  to := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S)) => x |} |} |};
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun x : carrier (cmon_setoid (QuotientMod S')) => x |} |} |}
|}.
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  intros R M S S' H1 H2 x y Hxy; simpl in Hxy |- *.
  destruct Hxy as [Hxy]; constructor; exact (H1 _ Hxy).
Qed.
Next Obligation. intros R M S S' H1 H2; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 r x; simpl; apply mquot_rel_refl. Qed.
Next Obligation.
  intros R M S S' H1 H2 x y Hxy; simpl in Hxy |- *.
  destruct Hxy as [Hxy]; constructor; exact (H2 _ Hxy).
Qed.
Next Obligation. intros R M S S' H1 H2; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x y; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 r x; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros R M S S' H1 H2 x; simpl; apply mquot_rel_refl. Qed.

(** ** The degenerate submodules, named and separated *)

Program Definition TrivialSub {R : RingObject} (M : RModObject R) :
  Submodule M := {|
  smod_mem := fun a : carrier (cmon_setoid M) => a ≈ cmon_zero M
|}.
Next Obligation.
  intros R M a b Hab Ha; simpl in *; now rewrite <- Hab.
Qed.
Next Obligation. intros R M; simpl; reflexivity. Qed.
Next Obligation.
  intros R M a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros R M r a Ha; simpl in *.
  rewrite Ha; apply rm_smul_zero_r.
Qed.

Program Definition TotalSub {R : RingObject} (M : RModObject R) :
  Submodule M := {|
  smod_mem := fun _ : carrier (cmon_setoid M) => poly_unit
|}.
Next Obligation. intros R M a b Hab Ha; exact ttt. Qed.
Next Obligation. intros R M; exact ttt. Qed.
Next Obligation. intros R M a b Ha Hb; exact ttt. Qed.
Next Obligation. intros R M r a Ha; exact ttt. Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mquot_trivial_iff {R : RingObject} (M : RModObject R)
  (x y : carrier (cmon_setoid M)) :
  mquot_rel (TrivialSub M) x y ↔ x ≈ y.
Proof.
  split.
  - intro H.
    apply (@pequiv_to _ _ (cmon_prop M)).
    destruct H as [H].
    apply pequiv_from.
    exact (fst (ab_sub_eq_zero_iff M x y) H).
  - intro H; constructor.
    exact (snd (ab_sub_eq_zero_iff M x y) H).
Qed.

Lemma mquot_total_collapses {R : RingObject} (M : RModObject R)
  (x y : carrier (cmon_setoid M)) : mquot_rel (TotalSub M) x y.
Proof. exact (inhabits ttt). Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example int_zero_is_0 : cmon_zero Int_RMod = 0%Z := eq_refl.
Example int_plus_is_add (a b : Z) : cmon_plus Int_RMod a b = (a + b)%Z :=
  eq_refl.
Example int_neg_is_opp (a : Z) : ab_neg Int_RMod a = (- a)%Z := eq_refl.
Example int_smul_is_mul (r a : Z) : rm_smul Int_RMod r a = (r * a)%Z :=
  eq_refl.
Example int_sub_is_minus (a b : Z) : ab_sub Int_RMod a b = (a - b)%Z :=
  eq_refl.

Definition ZEvenMod (a : Z) : Type := { k : Z & a = (2 * k)%Z }.

Program Definition EvenSub : Submodule Int_RMod := {|
  smod_mem := ZEvenMod
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

(* 2ℤ is PROPER: 1 is not even. *)
Theorem EvenSub_proper : smod_mem EvenSub 1%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 2ℤ is NONTRIVIAL: it contains 2, which is not zero. *)
Theorem EvenSub_nontrivial :
  smod_mem EvenSub 2%Z
  * ((2%Z : carrier (cmon_setoid Int_RMod)) ≈ cmon_zero Int_RMod → False).
Proof.
  split.
  - exists 1%Z; reflexivity.
  - simpl; discriminate.
Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: 1 stays apart from 0 in ℤ/2ℤ. *)
Theorem Z_mod_2Z_not_collapsed : mquot_rel EvenSub 1%Z 0%Z → False.
Proof.
  intros [[k Hk]]; rewrite int_sub_is_minus in Hk; lia.
Qed.

(* But it does collapse 2 into 0, so the projection is not injective and
   the quotient is a genuine quotient rather than a relabelling of ℤ. *)
Theorem Z_mod_2Z_collapses_two :
  cmon_map (rm_hom (mquot_proj EvenSub)) 2%Z
    ≈ cmon_map (rm_hom (mquot_proj EvenSub)) 0%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem mquot_proj_EvenSub_not_injective :
  RModInjective (mquot_proj EvenSub) → False.
Proof.
  intro Hinj.
  pose proof (Hinj 2%Z 0%Z Z_mod_2Z_collapses_two) as E.
  vm_compute in E; discriminate E.
Qed.

(* The scalar action survives the quotient nondegenerately: 3·1 is
   congruent to 1 and not to 0. *)
Example Z_mod_2Z_smul_three :
  mquot_rel EvenSub (rm_smul Int_RMod 3%Z 1%Z) 1%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

Theorem Z_mod_2Z_smul_three_not_zero :
  mquot_rel EvenSub (rm_smul Int_RMod 3%Z 1%Z) 0%Z → False.
Proof.
  intros [[k Hk]].
  rewrite int_sub_is_minus, int_smul_is_mul in Hk.
  lia.
Qed.

(* The kernel of the projection is exactly 2ℤ, in both directions. *)
(* Restated up to the truncation, in lockstep with [mquot_proj_kernel]. *)
Lemma EvenSub_is_kernel_of_proj (a : Z) :
  smod_mem (KernelSub (mquot_proj EvenSub)) a ↔ inhabited (smod_mem EvenSub a).
Proof. exact (mquot_proj_kernel EvenSub a). Qed.
