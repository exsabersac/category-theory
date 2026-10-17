Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab:      https://ncatlab.org/nlab/show/solution+set+condition
 nLab:      https://ncatlab.org/nlab/show/subobject
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition smod_subobj {R : RingObject} {W : RModObject R} (S : Submodule W) :
  @SubObj (RMod R) W :=
  @Build_SubObj (RMod R) W (SubmoduleMod S) (smod_incl S) (smod_incl_monic S).

Example smod_subobj_dom {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_dom (smod_subobj S) = SubmoduleMod S := eq_refl.

Example smod_subobj_mono {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_mono (smod_subobj S) = smod_incl S := eq_refl.

Definition subobj_smod {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : Submodule W := ImageSubmod (sub_mono m).

Example subobj_smod_mem {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) (b : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod m) b
    = { a : carrier (cmon_setoid (sub_dom m))
      & cmon_map (rm_hom (sub_mono m)) a ≈ b } := eq_refl.

(* The witness carried by a member of an image submodule. *)
Lemma rmod_image_witness {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (p : smod_carrier (ImageSubmod f)) :
  cmon_map (rm_hom f) (`1 (`2 p)) ≈ `1 p.
Proof. exact (`2 (`2 p)). Qed.

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_image_retract {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  SubmoduleMod (ImageSubmod f) ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (ImageSubmod f) => `1 (`2 p) |} |}
|}.
Next Obligation.
  intros R M N f Hm p q Hpq.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q); exact Hpq.
Qed.
Next Obligation.
  intros R M N f Hm; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f (cmon_zero (SubmoduleMod (ImageSubmod f)))).
  simpl; symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hm p q; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (cmon_plus (SubmoduleMod (ImageSubmod f)) p q)).
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q).
  simpl; reflexivity.
Qed.
Next Obligation.
  intros R M N f Hm r p; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (rm_smul (SubmoduleMod (ImageSubmod f)) r p)).
  rewrite (rm_map_smul f).
  rewrite (rmod_image_witness f p).
  simpl; reflexivity.
Qed.

Lemma rmod_image_retract_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  @compose (RMod R) _ _ _ f (rmod_image_retract f Hm)
    ≈ smod_incl (ImageSubmod f).
Proof. intro p; exact (rmod_image_witness f p). Qed.

(* 相关说明。 （已译） *)
Definition smod_subobj_image_le {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le (smod_subobj (subobj_smod m)) m.
Proof.
  exact (existT _ (rmod_image_retract (sub_mono m) (sub_is_monic m))
                  (rmod_image_retract_commutes (sub_mono m)
                     (sub_is_monic m))).
Defined.

Definition smod_subobj_image_ge {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le m (smod_subobj (subobj_smod m)).
Proof.
  exact (existT _ (mod_image_cores (sub_mono m))
                  (mod_image_factors (sub_mono m))).
Defined.

(* Mac Lane V.7 Definition 1's "these categorical subobjects agree with
   the element-defined ones in R-Mod", one half: every subobject of a
   module IS its image submodule, at `≈` on [SubObj W]. *)
Theorem smod_subobj_image_equiv {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : smod_subobj (subobj_smod m) ≈ m.
Proof.
  apply sub_le_antisym.
  - exact (smod_subobj_image_le m).
  - exact (smod_subobj_image_ge m).
Defined.

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition smod_round_to {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a → smod_mem S a.
Proof.
  intros [p Hp]; exact (smod_at S Hp (`2 p)).
Defined.

Definition smod_round_from {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem S a → smod_mem (subobj_smod (smod_subobj S)) a.
Proof.
  intro Ha.
  unshelve eexists.
  - exact (existT _ a Ha).
  - simpl; reflexivity.
Defined.

Theorem smod_round_iff {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a ↔ smod_mem S a.
Proof.
  split; [ exact (smod_round_to S a) | exact (smod_round_from S a) ].
Defined.

(* 相关说明。 （已译） *)

Section Generated.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (P : carrier (cmon_setoid M) → Type).

(* FIVE constructors, not four: [mgen_zero] cannot be dropped (P may be
   empty) and [mgen_resp] is required because [smod_resp] is a FIELD of
   [Submodule].  Closure under negation is DERIVED -- [smod_neg]
   (Instance/Mod/Quotient.v) gets it from (−1)·a -- so there is no
   [mgen_neg]. *)
Inductive MGen : carrier (cmon_setoid M) → Type :=
  | mgen_base : ∀ a, P a → MGen a
  | mgen_resp : ∀ a b, a ≈ b → MGen a → MGen b
  | mgen_zero : MGen (cmon_zero M)
  | mgen_plus : ∀ a b, MGen a → MGen b → MGen (cmon_plus M a b)
  | mgen_smul : ∀ (r : carrier (rig_setoid (ring_rig R))) a,
      MGen a → MGen (rm_smul M r a).

Definition SubGenMod : Submodule M :=
  @Build_Submodule R M MGen mgen_resp mgen_zero mgen_plus mgen_smul.

Definition mgen_incl (a : carrier (cmon_setoid M)) (Ha : P a) :
  smod_mem SubGenMod a := mgen_base a Ha.

(* Leastness, in the [Fixpoint] idiom of Instance/Variety/Spanning.v:
   one case per constructor, no tactic. *)
Fixpoint mgen_least (S : Submodule M) (HS : ∀ a, P a → smod_mem S a)
  (a : carrier (cmon_setoid M)) (D : MGen a) {struct D} : smod_mem S a :=
  match D in MGen a' return smod_mem S a' with
  | mgen_base a Ha      => HS a Ha
  | mgen_resp a b H D'  => smod_resp S a b H (mgen_least S HS a D')
  | mgen_zero           => smod_zero S
  | mgen_plus a b D1 D2 =>
      smod_plus S a b (mgen_least S HS a D1) (mgen_least S HS b D2)
  | mgen_smul r a D'    => smod_smul S r a (mgen_least S HS a D')
  end.

End Generated.

(* 相关说明。 （已译） *)
Program Definition mgen_sub_include {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  SubmoduleMod (SubGenMod P) ~{RMod R}~> SubmoduleMod S := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (SubGenMod P) =>
      existT _ (`1 p) (mgen_least P S HS (`1 p) (`2 p)) |} |}
|}.
Next Obligation. intros R M P S HS p q Hpq; exact Hpq. Qed.
Next Obligation. intros R M P S HS; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS p q; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS r p; simpl; reflexivity. Qed.

Theorem mgen_sub_le_least {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  sub_le (smod_subobj (SubGenMod P)) (smod_subobj S).
Proof.
  exists (mgen_sub_include P S HS).
  intro p; simpl; reflexivity.
Defined.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition rbl_image {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) (x : carrier (cmon_setoid W)) : Type :=
  { v : carrier (cmon_setoid V) &
    { w : carrier (cmon_setoid V') & rbl_map β v w ≈ x } }.

(* 相关说明。 （已译） *)
Definition RBilinearSpanning {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) : Type :=
  ∀ x : carrier (cmon_setoid W), MGen (rbl_image β) x.

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_split {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  N ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun b : carrier (cmon_setoid N) => `1 (Hs b) |} |}
|}.
Next Obligation.
  intros R M N f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros R M N f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero N))).
  symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (`2 (Hs (cmon_plus N a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.
Next Obligation.
  intros R M N f Hi Hs r a; simpl.
  apply Hi.
  rewrite (rm_map_smul f).
  rewrite (`2 (Hs (rm_smul N r a))), (`2 (Hs a)).
  reflexivity.
Qed.

Lemma rmod_split_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  @compose (RMod R) _ _ _ f (rmod_split f Hi Hs) ≈ @id (RMod R) N.
Proof. intro b; exact (`2 (Hs b)). Qed.

Section SpanningEquivalence.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(* The restriction of β to a submodule it factors through, as a datum. *)
Definition rbl_restrict_image (m : @SubObj (RMod R) W)
  (β' : RBilinear V V' (sub_dom m))
  (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                 ≈ rbl_map β v w)
  (a : carrier (cmon_setoid W)) (Ha : rbl_image β a) :
  smod_mem (subobj_smod m) a.
Proof.
  destruct Ha as [v [w Hvw]].
  exists (rbl_map β' v w).
  rewrite (Hβ v w); exact Hvw.
Defined.

(* → : elementwise spanning implies Mac Lane's categorical form. *)
Theorem rbilinear_spanning_to_spanning (H : RBilinearSpanning β) :
  Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  intros m [k Hk].
  (* 相关说明。 （已译） *)
  pose (β' := k ttt).
  assert (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                        ≈ rbl_map β v w) by exact (Hk ttt).
  (* 相关说明。 （已译） *)
  assert (Hs : RModSurjective (sub_mono m)).
  { intro x.
    exact (mgen_least (rbl_image β) (subobj_smod m)
             (rbl_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : RModInjective (sub_mono m)) by
    exact (rmod_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (rmod_split (sub_mono m) Hi Hs).
  exact (rmod_split_commutes (sub_mono m) Hi Hs).
Defined.

(* 相关说明。 （已译） *)
Program Definition rbl_gen_corestrict :
  RBilinear V V' (SubmoduleMod (SubGenMod (rbl_image β))) := {|
  rbl_map := fun v w =>
    existT _ (rbl_map β v w)
      (mgen_base (rbl_image β) (rbl_map β v w)
         (existT _ v (existT _ w (reflexivity _))))
|}.
Next Obligation. intros v v' Hv w w' Hw; simpl; now rewrite Hv, Hw. Qed.
Next Obligation. intros v v' w; simpl; apply rbl_add_l. Qed.
Next Obligation. intros v w w'; simpl; apply rbl_add_r. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_l. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_r. Qed.

(* ← : Mac Lane's categorical form implies elementwise spanning. *)
Theorem spanning_to_rbilinear_spanning
  (H : Spanning (Bilin V V') (global_element (X := Bilin V V' W) β)) :
  RBilinearSpanning β.
Proof.
  assert (Hfac : SubFactorsThrough (Bilin V V')
                   (global_element (X := Bilin V V' W) β)
                   (smod_subobj (SubGenMod (rbl_image β)))).
  { exists (global_element (X := Bilin V V' (SubmoduleMod
                                   (SubGenMod (rbl_image β))))
              rbl_gen_corestrict).
    intros u v w; simpl; reflexivity. }
  destruct (H _ Hfac) as [j Hj].
  intro x.
  exact (mgen_resp (rbl_image β) _ _ (Hj x)
           (`2 (cmon_map (rm_hom j) x))).
Defined.

Theorem rbilinear_spanning_iff :
  RBilinearSpanning β
    ↔ Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  split.
  - exact rbilinear_spanning_to_spanning.
  - exact spanning_to_rbilinear_spanning.
Defined.

End SpanningEquivalence.

(* 相关说明。 （已译） *)

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem tensor_gen_spanning {R : RingObject} (V V' : RModObject R) :
  RBilinearSpanning (@tensor_gen R V V').
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (@tensor_gen R V V')) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (@tensor_gen R V V'))).
  - exact (mgen_plus (rbl_image (@tensor_gen R V V')) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (@tensor_gen R V V'))) _ IHt).
  - exact (mgen_smul (rbl_image (@tensor_gen R V V')) _ _ IHt).
Defined.

Theorem tensor_gen_spanning_categorical {R : RingObject}
  (V V' : RModObject R) :
  Spanning (Bilin V V')
    (global_element (X := Bilin V V' (TensorMod V V')) (@tensor_gen R V V')).
Proof.
  exact (rbilinear_spanning_to_spanning (@tensor_gen R V V')
           (tensor_gen_spanning V V')).
Defined.

(** ** 5. Wide pullbacks in [RMod R] *)

Section WidePullbackMod.

Context {R : RingObject}.
Context {I : Type}.
Context {A : I → RModObject R}.
Context {z : RModObject R}.
Context (g : ∀ i : I, A i ~{RMod R}~> z).

(* 相关说明。 （已译） *)
Definition wpull_mem (f : carrier (cmon_setoid (ProdMod A))) : Type :=
  ∀ i j : I,
    cmon_map (rm_hom (g i)) (f i) ≈ cmon_map (rm_hom (g j)) (f j).

Definition WPullSub : Submodule (ProdMod A).
Proof using A I R g z.
  unshelve refine (@Build_Submodule R (ProdMod A) wpull_mem _ _ _ _).
  - intros a b Hab Ha i j.
    rewrite <- (Hab i), <- (Hab j); exact (Ha i j).
  - intros i j.
    rewrite (cmon_map_zero (rm_hom (g i))).
    rewrite (cmon_map_zero (rm_hom (g j))).
    reflexivity.
  - intros a b Ha Hb i j.
    rewrite (cmon_map_plus (rm_hom (g i)) (a i) (b i)).
    rewrite (cmon_map_plus (rm_hom (g j)) (a j) (b j)).
    rewrite (Ha i j), (Hb i j); reflexivity.
  - intros r a Ha i j.
    rewrite (rm_map_smul (g i) r (a i)), (rm_map_smul (g j) r (a j)).
    rewrite (Ha i j); reflexivity.
Defined.

Definition WPullMod : RModObject R := SubmoduleMod WPullSub.

Definition wpull_mod_proj (i : I) : WPullMod ~{RMod R}~> A i :=
  @compose (RMod R) _ _ _ (prod_proj A i) (smod_incl WPullSub).

Lemma wpull_mod_commutes (i j : I) :
  @compose (RMod R) _ _ _ (g i) (wpull_mod_proj i)
    ≈ @compose (RMod R) _ _ _ (g j) (wpull_mod_proj j).
Proof. intro p; exact (`2 p i j). Qed.

Program Definition wpull_mod_tuple {Q : RModObject R}
  (q : ∀ i : I, Q ~{RMod R}~> A i)
  (Hq : ∀ i j : I, @compose (RMod R) _ _ _ (g i) (q i)
                     ≈ @compose (RMod R) _ _ _ (g j) (q j)) :
  Q ~{RMod R}~> WPullMod := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun x : carrier (cmon_setoid Q) =>
      existT _ (fun i => cmon_map (rm_hom (q i)) x)
               (fun i j => Hq i j x) |} |}
|}.
Next Obligation.
  intros Q q Hq x y Hxy i; simpl.
  exact (proper_morphism (cmon_map (rm_hom (q i))) x y Hxy).
Qed.
Next Obligation.
  intros Q q Hq i; exact (cmon_map_zero (rm_hom (q i))).
Qed.
Next Obligation.
  intros Q q Hq x y i; exact (cmon_map_plus (rm_hom (q i)) x y).
Qed.
Next Obligation.
  intros Q q Hq r x i; exact (rm_map_smul (q i) r x).
Qed.

Definition RMod_WidePullback : WidePullback g.
Proof using A I R g z.
  unshelve refine (@Build_WidePullback (RMod R) I A z g
                     WPullMod wpull_mod_proj _ _).
  - exact wpull_mod_commutes.
  - intros Q q Hq.
    unshelve refine {| unique_obj := wpull_mod_tuple q Hq |}.
    + intros i x; reflexivity.
    + intros v Hv x i; symmetry; exact (Hv i x).
Defined.

End WidePullbackMod.

#[export] Instance RMod_HasWidePullbacks (R : RingObject) :
  HasWidePullbacks (RMod R) :=
  @Build_HasWidePullbacks (RMod R) (@RMod_WidePullback R).

(* 相关说明。 （已译） *)

Section BilinWidePullbacks.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtAFamily.

Context {I : Type}.
Context {B : I → RModObject R}.
Context {zz : RModObject R}.
Context (g : ∀ i : I, B i ~{RMod R}~> zz).
Context {P : RModObject R}.
Context {p : ∀ i : I, P ~{RMod R}~> B i}.
Context (HP : IsWidePullback g P p).

(* 相关说明。 （已译） *)
Lemma wpull_elem_unique (x y : carrier (cmon_setoid P))
  (H : ∀ i, cmon_map (rm_hom (p i)) x ≈ cmon_map (rm_hom (p i)) y) : x ≈ y.
Proof using B HP I P R g p zz.
  assert (Hd : ∀ i, @compose (RMod R) _ _ _ (p i) (rmod_by_element R P x)
                      ≈ @compose (RMod R) _ _ _ (p i) (rmod_by_element R P y)).
  { intros i r; simpl.
    rewrite (rm_map_smul (p i) r x), (rm_map_smul (p i) r y).
    now rewrite (H i). }
  pose proof (wide_pullback_jointly_monic HP
                (rmod_by_element R P x) (rmod_by_element R P y) Hd
                (rig_one (ring_rig R))) as Hone.
  simpl in Hone.
  rewrite (rm_smul_one P x), (rm_smul_one P y) in Hone.
  exact Hone.
Qed.

Lemma wpull_elem_maps_agree (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  ∀ i j : I,
    @compose (RMod R) _ _ _ (g i) (rmod_by_element R (B i) (b i))
      ≈ @compose (RMod R) _ _ _ (g j) (rmod_by_element R (B j) (b j)).
Proof using B I R g zz.
  intros i j r; simpl.
  rewrite (rm_map_smul (g i) r (b i)), (rm_map_smul (g j) r (b j)).
  now rewrite (Hb i j).
Qed.

(* 相关说明。 （已译） *)
Definition wpull_elem (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  carrier (cmon_setoid P) :=
  cmon_map (rm_hom (unique_obj
     (wpull_ump HP (fun i => rmod_by_element R (B i) (b i))
        (wpull_elem_maps_agree b Hb))))
    (rig_one (ring_rig R)).

Lemma wpull_elem_proj (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) (i : I) :
  cmon_map (rm_hom (p i)) (wpull_elem b Hb) ≈ b i.
Proof using B HP I P R g p zz.
  unfold wpull_elem.
  transitivity (cmon_map (rm_hom (rmod_by_element R (B i) (b i)))
                  (rig_one (ring_rig R))).
  - exact (unique_property
             (wpull_ump HP (fun k => rmod_by_element R (B k) (b k))
                (wpull_elem_maps_agree b Hb)) i (rig_one (ring_rig R))).
  - simpl; apply rm_smul_one.
Qed.

(* A compatible family bilinear maps 进入 [B i] IS bilinear map
 进入 apex -- elementwise content preservation. （已译） *)
Program Definition wpull_bilin_med
  (β : ∀ i : I, RBilinear V V' (B i))
  (Hβ : ∀ (i j : I) (v : carrier (cmon_setoid V))
          (w : carrier (cmon_setoid V')),
          cmon_map (rm_hom (g i)) (rbl_map (β i) v w)
            ≈ cmon_map (rm_hom (g j)) (rbl_map (β j) v w)) :
  RBilinear V V' P := {|
  rbl_map := fun v w =>
    wpull_elem (fun i => rbl_map (β i) v w) (fun i j => Hβ i j v w)
|}.
Next Obligation.
  intros β Hβ v v' Hv w w' Hw.
  apply wpull_elem_unique; intro i.
  rewrite !wpull_elem_proj.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros β Hβ v v' w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros β Hβ v w w'.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_r.
Qed.

End AtAFamily.

Theorem Bilin_PreservesWidePullbacks : PreservesWidePullbacks (Bilin V V').
Proof using R V V'.
  intros I B zz g Hm P p HP.
  unshelve refine (@Build_IsWidePullback Sets I _ _ _ _ _ _ _).
  - (* 相关说明。 （已译） *)
    intros i j β v w.
    exact (wpull_commutes HP i j (rbl_map β v w)).
  - (* the universal property *)
    intros Q q Hq.
    unshelve refine {| unique_obj := {| morphism := fun x : carrier Q =>
      wpull_bilin_med g HP (fun i => q i x)
        (fun i j v w => Hq i j x v w) |} |}.
    + (* the mediator respects [≈] on Q *)
      intros x y Hxy v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite !(wpull_elem_proj g HP).
      exact (proper_morphism (q i) x y Hxy v w).
    + (* it lifts every leg *)
      intros i x v w.
      exact (wpull_elem_proj g HP (fun k => rbl_map (q k x) v w)
               (fun k l => Hq k l x v w) i).
    + (* and is the only one *)
      intros u Hu x v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite (wpull_elem_proj g HP).
      symmetry; exact (Hu i x v w).
Qed.

End BilinWidePullbacks.

(* 相关说明。 （已译） *)

Section TensorSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context `{HWP : @HasWidePullbacks (RMod R)}.

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_solution_set (X : Sets) : SolutionSet (Bilin V V') X :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') X.

Definition tensor_esols : ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V') (tensor_solution_set SetsOne).

(* The index, 对象 elements survive both repackagings on
 nose. （已译） *)
Example tensor_esol_index :
  esol_index tensor_esols = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols i = `1 i := eq_refl.

Example tensor_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols i = `1 (`2 i) ttt := eq_refl.

End TensorSolutionSet.

(* 相关说明。 （已译） *)

Section AbGenerated.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive ABGen : carrier (cmon_setoid A) → Type :=
  | abgen_base : ∀ a, P a → ABGen a
  | abgen_resp : ∀ a b, a ≈ b → ABGen a → ABGen b
  | abgen_zero : ABGen (cmon_zero A)
  | abgen_plus : ∀ a b, ABGen a → ABGen b → ABGen (cmon_plus A a b)
  | abgen_neg  : ∀ a, ABGen a → ABGen (ab_neg A a).

(* Leastness, against a bare closed predicate rather than against a
   record: Instance/Ab/DirectedColimit.v's [AbSubgroup] is the
   in-tree record, but its own generated notion [InGen] is
   generated by a finite LIST, so nothing there is reused and that file
   is deliberately not [Require]d here. *)
Fixpoint abgen_least (Q : carrier (cmon_setoid A) → Type)
  (Hresp : ∀ a b, a ≈ b → Q a → Q b)
  (Hzero : Q (cmon_zero A))
  (Hplus : ∀ a b, Q a → Q b → Q (cmon_plus A a b))
  (Hneg : ∀ a, Q a → Q (ab_neg A a))
  (HP : ∀ a, P a → Q a)
  (a : carrier (cmon_setoid A)) (D : ABGen a) {struct D} : Q a :=
  match D in ABGen a' return Q a' with
  | abgen_base a Ha     => HP a Ha
  | abgen_resp a b H D' =>
      Hresp a b H (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  | abgen_zero          => Hzero
  | abgen_plus a b D1 D2 =>
      Hplus a b (abgen_least Q Hresp Hzero Hplus Hneg HP a D1)
                (abgen_least Q Hresp Hzero Hplus Hneg HP b D2)
  | abgen_neg a D'      =>
      Hneg a (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  end.

End AbGenerated.

Section BalancedSpanning.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Definition bal_image {A : AbObject} (β : BalBiadditive N M A)
  (x : carrier (cmon_setoid A)) : Type :=
  { n : carrier (cmon_setoid (rm_ab N)) &
    { m : carrier (cmon_setoid (rm_ab M)) & bal_map β n m ≈ x } }.

Definition BalSpanning {A : AbObject} (β : BalBiadditive N M A) : Type :=
  ∀ x : carrier (cmon_setoid A), ABGen (bal_image β) x.

(* Mac Lane's Exercise 3, second clause: "A ⊗_R B is spanned, as an
   abelian group, by the elements a ⊗ b."  Four cases, by induction on
   [bsum]; the [bs_neg] case needs [abgen_neg] because an abelian group
   carries no scalar to derive it from. *)
Theorem bal_gen_spanning : BalSpanning (@bal_gen X N M).
Proof using M N X.
  intro s; induction s as [n m| |s1 IH1 s2 IH2|s IH].
  - refine (abgen_base (bal_image (@bal_gen X N M)) _ _).
    exists n, m; reflexivity.
  - exact (abgen_zero (bal_image (@bal_gen X N M))).
  - exact (abgen_plus (bal_image (@bal_gen X N M)) _ _ IH1 IH2).
  - exact (abgen_neg (bal_image (@bal_gen X N M)) _ IH).
Qed.

End BalancedSpanning.

(* 相关说明。 （已译） *)

Section BalBaseChange.

Context {T R : RingObject}.
Context (phi : T ~{Rng}~> R).
Context (N : RModObject (Ring_op R)).
Context (M : RModObject R).

(*
   本节说明 Spanning 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bal_right_T : RModObject (Ring_op T) :=
  RestrictObj (RigHom_op phi) N.

Definition bal_left_T : RModObject T := RestrictObj phi M.

(* 相关说明。 （已译） *)
Definition bal_change_bil :
  BalBiadditive bal_right_T bal_left_T (@BalTensor R N M).
Proof using M N R T phi.
  unshelve refine (@Build_BalBiadditive T bal_right_T bal_left_T
                     (@BalTensor R N M) (@bs_gen R N M) _ _ _ _).
  - intros n n' Hn m m' Hm; exact (@be_gen R N M n n' m m' Hn Hm).
  - intros n n' m; exact (@be_add_l R N M n n' m).
  - intros n m m'; exact (@be_add_r R N M n m m').
  - intros t n m; exact (@be_balance R N M (rig_map phi t) n m).
Defined.

(* The comparison homomorphism A ⊗_T B → A ⊗_R B. *)
Definition bal_change :
  @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M :=
  bal_med bal_change_bil.

(* Generators go to generators, on the nose. *)
Example bal_change_gen (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_change (@bs_gen T bal_right_T bal_left_T n m)
    = @bs_gen R N M n m := eq_refl.

(* Mac Lane's "examine 关系": comparison SURJECTIVE --
 A ⊗_R B quotient A ⊗_T B -- induction formal sums
 target. （已译） *)
Theorem bal_change_surjective : AbSurjective bal_change.
Proof using M N R T phi.
  intro t; induction t as [n m| |t1 IH1 t2 IH2|t IH].
  - exists (@bs_gen T bal_right_T bal_left_T n m); reflexivity.
  - exists (@bs_zero T bal_right_T bal_left_T); reflexivity.
  - destruct IH1 as [s1 H1]; destruct IH2 as [s2 H2].
    exists (@bs_plus T bal_right_T bal_left_T s1 s2).
    exact (be_plus H1 H2).
  - destruct IH as [s H].
    exists (@bs_neg T bal_right_T bal_left_T s).
    exact (be_neg H).
Qed.

(* 相关说明。 （已译） *)
Theorem bal_change_is_med
  (f : @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M)
  (Hf : ∀ (n : carrier (cmon_setoid (rm_ab N)))
          (m : carrier (cmon_setoid (rm_ab M))),
          cmon_map f (@bs_gen T bal_right_T bal_left_T n m)
            ≈ @bs_gen R N M n m) :
  f ≈ bal_change.
Proof using M N R T phi. exact (bal_med_unique bal_change_bil f Hf). Qed.

End BalBaseChange.
