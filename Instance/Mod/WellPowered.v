Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
(* Imported before Theory/Subobject.v on purpose: Adjunction/SAFT.v's
   record [SubobjectIndex] has its own [sub_dom] and [sub_mono], which
   must not shadow the subobject projections used throughout. *)
Require Import Category.Adjunction.SAFT.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Instance.Mod.Representable.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/generator
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Submodule
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_module

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* Instance/Mod/Spanning.v's round trip between submodules and
   subobjects IS a [WellPoweredAt]; nothing is added. *)
Definition RMod_WellPoweredAt_up@{a c p o x w +| c < w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c x} W :=
  {| wp_index   := Submodule W;
     wp_to      := smod_subobj;
     wp_from    := subobj_smod;
     wp_to_from := smod_subobj_image_equiv |}.

(** ** 2. [Prop]-valued submodules *)

(* 相关说明。 （已译） *)
Record PSubmodule@{a c p m0 m1 m2 m3 m4}
  {R : RingObject@{a c p}} (M : RModObject@{m0 m1 m2 m3 m4 a c p} R) := {
  psm_mem : carrier (cmon_setoid M) → Prop;
  psm_resp : ∀ a b : carrier (cmon_setoid M), a ≈ b → psm_mem a → psm_mem b;
  psm_zero : psm_mem (cmon_zero M);
  psm_plus : ∀ a b, psm_mem a → psm_mem b → psm_mem (cmon_plus M a b);
  psm_smul : ∀ (r : carrier (rig_setoid (ring_rig R))) a,
      psm_mem a → psm_mem (rm_smul M r a)
}.

Arguments psm_mem {R M} _ _.
Arguments psm_resp {R M} _ _ _ _ _.
Arguments psm_zero {R M} _.
Arguments psm_plus {R M} _ _ _ _ _.
Arguments psm_smul {R M} _ _ _ _.

(* A [Prop] submodule read as a [Submodule]: [Prop] is a [Type]. *)
Definition psm_sub@{a c p o x +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]} (P : PSubmodule M) :
  Submodule M :=
  {| smod_mem  := fun a => psm_mem P a;
     smod_resp := psm_resp P;
     smod_zero := psm_zero P;
     smod_plus := psm_plus P;
     smod_smul := psm_smul P |}.

(* 相关说明。 （已译） *)
Definition pimage@{a c p o x +}
  {R : RingObject@{a c p}} {M N : obj[RMod@{o x a p c} R]}
  (f : M ~{RMod@{o x a p c} R}~> N) : PSubmodule N.
Proof.
  unshelve refine {| psm_mem := fun b => Powerset_squash
        { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ b } |}.
  - intros a b Hab H Q k. apply H. intros [x Hx]. apply k.
    exists x. exact (Equivalence_Transitive _ _ _ Hx Hab).
  - intros Q k; apply k; exists (cmon_zero M);
      exact (cmon_map_zero (rm_hom f)).
  - intros a b Ha Hb Q k. apply Ha; intros [x Hx]. apply Hb; intros [y Hy].
    apply k. exists (cmon_plus M x y).
    rewrite (cmon_map_plus (rm_hom f)). now rewrite Hx, Hy.
  - intros r a Ha Q k. apply Ha; intros [x Hx]; apply k.
    exists (rm_smul M r x). rewrite (rm_map_smul f). now rewrite Hx.
Defined.

(* 相关说明。 （已译） *)

Section Untrunc.

Universes a c p o x.
Constraint Set < c, c < o, c < x, p <= a, c <= a, a <= o.

Context {R : RingObject@{a c p}} (U : Untruncate@{c})
        {W : obj[RMod@{o x a p c} R]} (m : @SubObj (RMod@{o x a p c} R) W).

(* 相关说明。 （已译） *)
Definition pim_fn (p : smod_carrier (psm_sub (pimage (sub_mono m)))) :
  smod_carrier (subobj_smod m) :=
  existT (fun b => smod_mem (subobj_smod m) b) (`1 p) (U _ (`2 p)).

Definition tim_fn (p : smod_carrier (subobj_smod m)) :
  smod_carrier (psm_sub (pimage (sub_mono m))) :=
  existT (fun b => smod_mem (psm_sub (pimage (sub_mono m))) b) (`1 p)
         (Powerset_squash_intro (`2 p)).

Definition pim_to_tim :
  RModHom (SubmoduleMod (psm_sub (pimage (sub_mono m))))
          (SubmoduleMod (subobj_smod m)).
Proof using R U W m.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact pim_fn.
  - intros p q H; exact H.
  - simpl; reflexivity.
  - intros a b; simpl; reflexivity.
  - intros r a; simpl; reflexivity.
Defined.

Definition tim_to_pim :
  RModHom (SubmoduleMod (subobj_smod m))
          (SubmoduleMod (psm_sub (pimage (sub_mono m)))).
Proof.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact tim_fn.
  - intros p q H; exact H.
  - simpl; reflexivity.
  - intros a b; simpl; reflexivity.
  - intros r a; simpl; reflexivity.
Defined.

Definition pim_le :
  sub_le (smod_subobj (psm_sub (pimage (sub_mono m))))
         (smod_subobj (subobj_smod m)).
Proof using R U W m. exists pim_to_tim. intro p; simpl; reflexivity. Defined.

Definition pim_ge :
  sub_le (smod_subobj (subobj_smod m))
         (smod_subobj (psm_sub (pimage (sub_mono m)))).
Proof. exists tim_to_pim. intro p; simpl; reflexivity. Defined.

Definition pim_to_from :
  smod_subobj (psm_sub (pimage (sub_mono m))) ≈ m.
Proof using R U W m.
  etransitivity.
  - apply sub_le_antisym; [exact pim_le | exact pim_ge].
  - exact (smod_subobj_image_equiv m).
Defined.

End Untrunc.

Definition RMod_WellPoweredAt_untruncate@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{c o o c x} W :=
  {| wp_index   := PSubmodule W;
     wp_to      := fun P => smod_subobj (psm_sub P);
     wp_from    := fun m => pimage (sub_mono m);
     wp_to_from := pim_to_from U |}.

Definition RMod_WellPowered_untruncate@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  WellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_WellPoweredAt_untruncate U W.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pker@{a c p o x +}
  {R : RingObject@{a c p}} {W Q : obj[RMod@{o x a p c} R]}
  (e : W ~{RMod@{o x a p c} R}~> Q) : PSubmodule W.
Proof.
  unshelve refine {| psm_mem := fun x =>
     @pequiv _ _ (cmon_prop Q) (cmon_map (rm_hom e) x) (cmon_zero Q) |}.
  - intros a b Hab Ha. apply pequiv_from.
    rewrite <- Hab. exact (pequiv_to _ _ Ha).
  - apply pequiv_from. exact (cmon_map_zero (rm_hom e)).
  - intros a b Ha Hb. apply pequiv_from.
    rewrite (cmon_map_plus (rm_hom e)).
    rewrite (pequiv_to _ _ Ha), (pequiv_to _ _ Hb). apply cmon_plus_zero_l.
  - intros r a Ha. apply pequiv_from. rewrite (rm_map_smul e).
    rewrite (pequiv_to _ _ Ha). apply rm_smul_zero_r.
Defined.

(* The quotient 对象 [Prop] submodule names: projection onto the
 quotient module, epic Instance/Mod/Quotient.v's [mquot_proj_epic]. （已译） *)
Definition pquot@{a c p o x +}
  {R : RingObject@{a c p}} {W : obj[RMod@{o x a p c} R]}
  (N : PSubmodule W) : @QuotObj (RMod@{o x a p c} R) W :=
  mk_quot (mquot_proj (psm_sub N)) (mquot_proj_epic (psm_sub N)).

(* An existential in [Prop] read as an impredicative truncation. *)
Definition squash_of_ex@{c +} {A : Type@{c}} {P : A → Prop} :
  (exists a, P a)%type → Powerset_squash@{c} { a : A & P a }.
Proof. intros [a Ha] Qp k. exact (k (existT _ a Ha)). Defined.

Section CoUntrunc.

Universes a c p o x.
Constraint Set < c, c < o, c < x, p <= a, c <= a, a <= o.

Context {R : RingObject@{a c p}} (U : Untruncate@{c})
        {W : obj[RMod@{o x a p c} R]} (u : @QuotObj (RMod@{o x a p c} R) W).

Let Q := quot_cod u.
Let e : W ~{RMod R}~> Q := quot_epi u.
Let S := psm_sub (pker e).

(* 相关说明。 （已译） *)
Definition pre_fn (q : carrier (cmon_setoid Q)) : carrier (cmon_setoid W) :=
  `1 (U _ (squash_of_ex (rmod_epic_surjective e (quot_is_epic u) q))).

Lemma pre_spec (q : carrier (cmon_setoid Q)) :
  cmon_map (rm_hom e) (pre_fn q) ≈ q.
Proof using R U W u.
  unfold pre_fn.
  destruct (U _ _) as [a Ha]; simpl. exact (pequiv_to _ _ Ha).
Qed.

(* x ~ y in W/ker e as soon as e x ≈ e y, and conversely. *)
Lemma rel_of_image (x y : carrier (cmon_setoid W)) :
  cmon_map (rm_hom e) x ≈ cmon_map (rm_hom e) y → mquot_rel S x y.
Proof using R W u.
  intro H. constructor. simpl. apply pequiv_from.
  rewrite (ab_map_sub (rm_hom e)). exact (snd (ab_sub_eq_zero_iff _ _ _) H).
Qed.

Lemma image_of_rel (x y : carrier (cmon_setoid W)) :
  mquot_rel S x y → cmon_map (rm_hom e) x ≈ cmon_map (rm_hom e) y.
Proof using R W u.
  intro H. apply pequiv_to. destruct H as [K]. apply pequiv_from.
  simpl in K. apply (pequiv_to _ _) in K.
  rewrite (ab_map_sub (rm_hom e)) in K.
  exact (fst (ab_sub_eq_zero_iff _ _ _) K).
Qed.

Definition pre_map : Q ~{RMod R}~> QuotientMod S.
Proof using R U W u.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact pre_fn.
  - intros q q' H. apply rel_of_image. now rewrite !pre_spec.
  - apply rel_of_image. rewrite pre_spec. symmetry.
    exact (cmon_map_zero (rm_hom e)).
  - intros a b. apply rel_of_image. simpl.
    rewrite (cmon_map_plus (rm_hom e)), !pre_spec. reflexivity.
  - intros r a. apply rel_of_image. simpl.
    rewrite (rm_map_smul e), !pre_spec. reflexivity.
Defined.

Definition ev_map : QuotientMod S ~{RMod R}~> Q.
Proof using R W u.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact (cmon_map (rm_hom e)).
  - intros x y H. exact (image_of_rel x y H).
  - exact (cmon_map_zero (rm_hom e)).
  - intros a b. exact (cmon_map_plus (rm_hom e) a b).
  - intros r a. exact (rm_map_smul e r a).
Defined.

Definition pre_iso : Q ≅[RMod R] QuotientMod S.
Proof using R U W u.
  unshelve econstructor.
  - exact pre_map.
  - exact ev_map.
  - intro x. apply rel_of_image. simpl. apply pre_spec.
  - intro q. simpl. apply pre_spec.
Defined.

Definition cwp_to_from : pquot (pker e) ≈ u.
Proof using R U W u.
  apply (quot_equiv_of_cod_iso (pquot (pker e)) u pre_iso).
  intro x. apply rel_of_image. simpl. apply pre_spec.
Defined.

End CoUntrunc.

Definition RMod_CoWellPoweredAt_untruncate@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{c o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index   := PSubmodule W;
     wp_to      := pquot;
     wp_from    := fun u => pker (quot_epi u);
     wp_to_from := cwp_to_from U |}.

Definition RMod_CoWellPowered_untruncate@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  CoWellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_CoWellPoweredAt_untruncate U W.

(** ** 5. R is a generator of R-Mod *)

(* 相关说明。 （已译） *)
Lemma RMod_ring_separates@{c o x +| Set < o, c < o, c < x +}
  {R : RingObject@{c c c}} :
  @IsSeparator (RMod@{o x c c c} R) (Ring_RMod R).
Proof.
  intros x y f g Hk m.
  pose proof (Hk (rmod_by_element R x m) (rig_one (ring_rig R))) as H.
  simpl in H.
  rewrite (rm_smul_one x m) in H. exact H.
Qed.

Definition RMod_Generator@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : Generator (RMod@{o x c c c} R) :=
  @Generator_of_separator (RMod R) (Ring_RMod R) RMod_ring_separates.

Definition RModop_Cogenerator@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : Cogenerator ((RMod@{o x c c c} R)^op) :=
  cog_of_gen (RMod_Generator R).

(* 相关说明。 （已译） *)

(*
   本节说明同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RMod_CoWellPoweredAt_up@{a c p o x w +| c < w, a <= w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W.
Proof.
  unshelve refine {|
    wp_index := { Q : RModObject@{c a c c c a c p} R
                & { e : W ~{RMod@{o x a p c} R}~> Q & RModPropSurjective e } };
    wp_to := fun i => @mk_quot (RMod@{o x a p c} R) W (`1 i) (`1 (`2 i))
                        (rmod_prop_surjective_epic _ (`2 (`2 i)));
    wp_from := fun u => existT _ (quot_cod u)
                 (existT _ (quot_epi u)
                    (rmod_epic_surjective _ (quot_is_epic u))) |}.
  intro u. exists iso_id. simpl. cat.
Defined.

(* The family, in [CoWellPowered]'s shape but one universe up, which
   [CoWellPowered]'s own [w <= h] rules out. *)
Definition RMod_CoWellPowered_up@{a c p o x w +| c < w, a <= w +}
  {R : RingObject@{a c p}} :
  ∀ W : obj[RMod@{o x a p c} R],
    @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  fun W => RMod_CoWellPoweredAt_up W.
