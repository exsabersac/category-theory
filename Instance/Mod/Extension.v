Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/extension+of+scalars
 nLab:      https://ncatlab.org/nlab/show/restriction+of+scalars
 Wikipedia: https://en.wikipedia.org/wiki/Extension_of_scalars
 Book: Riehl, Category Theory in Context, Dover 2016, Sec. 4.1,

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The 假设: image phi central S （已译） *)

Definition CentralImage {R S : RingObject} (phi : R ~{Rng}~> S) : Type :=
  ∀ (r : carrier (rig_setoid (ring_rig R)))
    (s : carrier (rig_setoid (ring_rig S))),
    rig_mul (ring_rig S) (rig_map phi r) s
      ≈ rig_mul (ring_rig S) s (rig_map phi r).

Lemma central_of_commutative {R S : RingObject} (phi : R ~{Rng}~> S)
  (Hcomm : ∀ a b : carrier (rig_setoid (ring_rig S)),
      rig_mul (ring_rig S) a b ≈ rig_mul (ring_rig S) b a) :
  CentralImage phi.
Proof. intros r s; apply Hcomm. Qed.

Section ExtensionOfScalars.

Context {R S : RingObject}.
Context (phi : R ~{Rng}~> S).

(** S as a left R-module along phi. *)
Definition ExtBase : RModObject R := RestrictObj phi (Ring_RMod S).

Example ExtBase_smul (r : carrier (rig_setoid (ring_rig R)))
  (x : carrier (rig_setoid (ring_rig S))) :
  rm_smul ExtBase r x = rig_mul (ring_rig S) (rig_map phi r) x := eq_refl.

(*
   本节说明 Extension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ExtBimodule : Bimodule S R := {|
  bm_left  := Ring_RMod S;
  bm_rsmul := fun s r => rig_mul (ring_rig S) s (rig_map phi r)
|}.
Next Obligation.
  intros s s' Hs r r' Hr; simpl.
  now rewrite Hs, Hr.
Qed.
Next Obligation. intros s t r; simpl; apply (rig_distr_r (ring_rig S)). Qed.
Next Obligation.
  intros s r r'; simpl.
  rewrite (rig_map_add phi r r').
  apply (rig_distr_l (ring_rig S)).
Qed.
Next Obligation.
  intros s r r'; simpl.
  rewrite (rig_map_mul phi r r').
  symmetry; apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros s; simpl.
  rewrite (rig_map_one phi).
  apply (rig_mul_one_r (ring_rig S)).
Qed.
Next Obligation. intros r s t; simpl; apply (rig_mul_assoc (ring_rig S)). Qed.

(*
   本节说明等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem ext_actions_agree_iff :
  (∀ (r : carrier (rig_setoid (ring_rig R)))
     (s : carrier (rig_setoid (ring_rig S))),
      bm_rsmul ExtBimodule s r ≈ rm_smul ExtBase r s) ↔ CentralImage phi.
Proof.
  split.
  - intros H r s; symmetry; exact (H r s).
  - intros H r s; symmetry; exact (H r s).
Qed.

Context (Hc : CentralImage phi).

Section OneModule.

Context (M : RMod R).

(** 本节：The elementary tensor x (x) m, two module arguments named
 so [mt_gen]'s implicit arguments determined. （已译） *)
Definition ext_gen (x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M))
  : carrier (cmon_setoid (TensorMod ExtBase M)) := @mt_gen R ExtBase M x m.

(** The scaling bilinear map. *)
Program Definition ext_scale (s : carrier (rig_setoid (ring_rig S)))
  : RBilinear ExtBase M (TensorMod ExtBase M) := {|
  rbl_map := fun x m => mt_gen (rig_mul (ring_rig S) s x) m
|}.
Next Obligation.
  intros s x x' Hx m m' Hm; simpl.
  apply mte_gen; [ | exact Hm ].
  now rewrite Hx.
Qed.
Next Obligation.
  intros s x y m; simpl.
  refine (mte_trans _ (mte_add_l _ _ _)).
  apply mte_gen; [ | reflexivity ].
  apply (rig_distr_l (ring_rig S)).
Qed.
Next Obligation.
  intros s x m n; simpl.
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros s r x m; simpl.
  refine (mte_trans _ (mte_sym (mte_act_l r _ m))).
  apply mte_gen; [ | reflexivity ].
  (* s * (phi r * x) = phi r * (s * x): ONLY use 中心性
 construction S-action. （已译） *)
  rewrite <- (rig_mul_assoc (ring_rig S) s (rig_map phi r) x).
  rewrite <- (Hc r s).
  apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros s r x m; simpl.
  exact (mte_sym (mte_act_r r _ m)).
Qed.

Definition ext_act (s : carrier (rig_setoid (ring_rig S)))
  : TensorMod ExtBase M ~{RMod R}~> TensorMod ExtBase M :=
  tensor_med (ext_scale s).

Definition ext_smul (s : carrier (rig_setoid (ring_rig S)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M)))
  : carrier (cmon_setoid (TensorMod ExtBase M)) :=
  tensor_med_fun (ext_scale s) t.

Example ext_smul_is_act (s : carrier (rig_setoid (ring_rig S)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  ext_smul s t = cmon_map (rm_hom (ext_act s)) t := eq_refl.

Example ext_smul_gen (s x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M)) :
  ext_smul s (ext_gen x m) = ext_gen (rig_mul (ring_rig S) s x) m := eq_refl.

(** Respectfulness action SCALAR 论元 one clause
 not free: it [tensor_hom_ext] between two mediators. （已译） *)
Lemma ext_smul_scalar (s s' : carrier (rig_setoid (ring_rig S)))
  (Hs : s ≈ s') (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  ext_smul s t ≈ ext_smul s' t.
Proof.
  refine (tensor_hom_ext (ext_act s) (ext_act s') _ t).
  intros x m; simpl.
  apply mte_gen; [ now rewrite Hs | reflexivity ].
Qed.

Lemma ext_smul_respects : Proper (equiv ==> equiv ==> equiv) ext_smul.
Proof.
  intros s s' Hs t t' Ht.
  transitivity (ext_smul s t').
  - exact (tensor_med_respects (ext_scale s) t t' Ht).
  - exact (ext_smul_scalar s s' Hs t').
Qed.

(** 本节：The extension scalars: same abelian group tensor
 product over R, S acting left-hand factor. （已译） *)
Program Definition ExtendObj : RModObject S := {|
  rm_ab   := rm_ab (TensorMod ExtBase M);
  rm_smul := ext_smul
|}.
Next Obligation. exact ext_smul_respects. Qed.
Next Obligation. intros s t u; reflexivity. Qed.
Next Obligation.
  intros s s' t.
  refine (tensor_hom_ext (ext_act (rig_add (ring_rig S) s s'))
            (rmod_hom_add (ext_act s) (ext_act s')) _ t).
  intros x m; simpl.
  refine (mte_trans _ (mte_add_l _ _ _)).
  apply mte_gen; [ | reflexivity ].
  apply (rig_distr_r (ring_rig S)).
Qed.
Next Obligation.
  intros s s' t.
  refine (tensor_hom_ext (ext_act (rig_mul (ring_rig S) s s'))
            (rmod_hom_compose (ext_act s) (ext_act s')) _ t).
  intros x m; simpl.
  apply mte_gen; [ | reflexivity ].
  apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros t.
  refine (tensor_hom_ext (ext_act (rig_one (ring_rig S)))
            (@rmod_hom_id R (TensorMod ExtBase M)) _ t).
  intros x m; simpl.
  apply mte_gen; [ | reflexivity ].
  apply (rig_mul_one_l (ring_rig S)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma extend_restrict_action (r : carrier (rig_setoid (ring_rig R)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  rm_smul (TensorMod ExtBase M) r t ≈ ext_smul (rig_map phi r) t.
Proof.
  revert r.
  induction t as [ x m | | t1 IH1 t2 IH2 | t1 IH1 | r' t1 IH1 ]; intro r.
  - exact (mte_act_l r x m).
  - exact (rm_smul_zero_r (TensorMod ExtBase M) r).
  - transitivity (cmon_plus (TensorMod ExtBase M)
                    (rm_smul (TensorMod ExtBase M) r t1)
                    (rm_smul (TensorMod ExtBase M) r t2)).
    + apply rm_smul_distr_l.
    + exact (cmon_plus_respects (TensorMod ExtBase M) _ _ (IH1 r) _ _ (IH2 r)).
  - transitivity (ab_neg (TensorMod ExtBase M)
                    (rm_smul (TensorMod ExtBase M) r t1)).
    + apply rm_smul_neg_r.
    + exact (ab_neg_respects (TensorMod ExtBase M) _ _ (IH1 r)).
  - rewrite (rm_map_smul (ext_act (rig_map phi r)) r' t1).
    rewrite <- (IH1 r).
    rewrite <- !(rm_smul_assoc (TensorMod ExtBase M)).
    transitivity (ext_smul (rig_map phi (rig_mul (ring_rig R) r r')) t1);
      [ apply IH1 | ].
    transitivity (ext_smul (rig_map phi (rig_mul (ring_rig R) r' r)) t1).
    + apply ext_smul_scalar.
      rewrite !(rig_map_mul phi).
      apply Hc.
    + symmetry; apply IH1.
Qed.

(** ** The unit: m goes to 1 (x) m *)

Program Definition extend_unit
  : M ~{RMod R}~> RestrictObj phi ExtendObj := {|
  rm_hom := {| cmon_map :=
                 {| morphism := fun m => ext_gen (rig_one (ring_rig S)) m |} |}
|}.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.

Example extend_unit_computes (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom extend_unit) m = ext_gen (rig_one (ring_rig S)) m := eq_refl.

(** 本节：Every elementary tensor unit scaled: x (x) m = x . (1 (x) m).
 This what makes unit generate, it used three times
 below. （已译） *)
Lemma ext_gen_scale (x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M)) :
  ext_gen x m ≈ ext_smul x (ext_gen (rig_one (ring_rig S)) m).
Proof.
  apply mte_gen; [ symmetry; apply (rig_mul_one_r (ring_rig S))
                 | reflexivity ].
Qed.

(** The 恒等 elements, read map tensor's own
 R-module structure restriction S-module structure. Its
 one obligation IS [extend_restrict_action]. （已译） *)
Program Definition ext_restrict_id
  : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi ExtendObj := {|
  rm_hom := {| cmon_map := {| morphism := fun t => t |} |}
|}.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.

(** ** The universal property *)

Section Mediator.

Context (N : RModObject S).
Context (g : M ~{RMod R}~> RestrictObj phi N).

(** (x, m) |-> x . g m, R-bilinear 进入 restriction N. Only the
 last clause needs 中心性; R-action FIRST variable
 passes through phi nothing spent. （已译） *)
Program Definition ext_bil : RBilinear ExtBase M (RestrictObj phi N) := {|
  rbl_map := fun x m => rm_smul N x (cmon_map (rm_hom g) m)
|}.
Next Obligation.
  intros x x' Hx m m' Hm; simpl.
  now rewrite Hx, Hm.
Qed.
Next Obligation.
  intros x y m; simpl.
  apply (rm_smul_distr_r N).
Qed.
Next Obligation.
  intros x m n; simpl.
  rewrite (cmon_map_plus (rm_hom g) m n).
  apply (rm_smul_distr_l N).
Qed.
Next Obligation.
  intros r x m; simpl.
  apply (rm_smul_assoc N).
Qed.
Next Obligation.
  intros r x m; simpl.
  rewrite (rm_map_smul g r m); simpl.
  rewrite <- !(rm_smul_assoc N).
  apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ].
Qed.

Definition ext_med_R : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi N :=
  tensor_med ext_bil.

(** Left multiplication s, map restricted R-modules: the
 third place 中心性 spent. （已译） *)
Program Definition ext_lmul (s : carrier (rig_setoid (ring_rig S)))
  : RestrictObj phi N ~{RMod R}~> RestrictObj phi N := {|
  rm_hom := {| cmon_map := {| morphism := fun y => rm_smul N s y |} |}
|}.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.

(** The factorization, as a map of S-modules. *)
Program Definition extend_med : ExtendObj ~{RMod S}~> N := {|
  rm_hom := rm_hom ext_med_R
|}.
Next Obligation.
  intros s t.
  refine (tensor_hom_ext (rmod_hom_compose ext_med_R (ext_act s))
            (rmod_hom_compose (ext_lmul s) ext_med_R) _ t).
  intros x m; simpl.
  apply (rm_smul_assoc N).
Qed.

Lemma extend_med_commutes (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom extend_med) (ext_gen (rig_one (ring_rig S)) m)
    ≈ cmon_map (rm_hom g) m.
Proof. exact (rm_smul_one N (cmon_map (rm_hom g) m)). Qed.

(** 本节：An S-linear map out extension IS R-linear map out the
 tensor product, [extend_restrict_action]. （已译） *)
Program Definition ext_forget (h : ExtendObj ~{RMod S}~> N)
  : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi N := {|
  rm_hom := rm_hom h
|}.
Next Obligation.
  intros h r t.
  rewrite (extend_restrict_action r t).
  exact (rm_map_smul h (rig_map phi r) t).
Qed.

Lemma extend_med_unique (h : ExtendObj ~{RMod S}~> N)
  (Hh : ∀ m, cmon_map (rm_hom h) (ext_gen (rig_one (ring_rig S)) m)
               ≈ cmon_map (rm_hom g) m)
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  cmon_map (rm_hom h) t ≈ cmon_map (rm_hom extend_med) t.
Proof.
  refine (tensor_hom_ext (ext_forget h) ext_med_R _ t).
  intros x m; simpl.
  transitivity (rm_smul N x
                  (cmon_map (rm_hom h) (ext_gen (rig_one (ring_rig S)) m))).
  - rewrite <- (rm_map_smul h x (ext_gen (rig_one (ring_rig S)) m)).
    apply proper_morphism, ext_gen_scale.
  - now rewrite (Hh m).
Qed.

End Mediator.

Theorem extend_universal (N : RModObject S)
  (g : M ~{RMod R}~> Restrict phi N) :
  ∃! h : ExtendObj ~{RMod S}~> N,
    g ≈ fmap[Restrict phi] h ∘ extend_unit.
Proof.
  unshelve eexists.
  - exact (extend_med N g).
  - intro m; simpl; symmetry; exact (extend_med_commutes N g m).
  - intros h Hh t; simpl.
    symmetry.
    apply (extend_med_unique N g h).
    intro m; symmetry; exact (Hh m).
Qed.

Definition extend_universal_arrow : UniversalArrow M (Restrict phi) :=
  universal_arrow_from_UMP M (Restrict phi) ExtendObj extend_unit
    extend_universal.

End OneModule.

(* * ** The 函子 伴随 （已译） *)

Definition ExtendScalars : RMod R ⟶ RMod S :=
  LeftAdjointFunctorFromUniversalArrows (Restrict phi) extend_universal_arrow.

Definition extend_restrict_adjunction : ExtendScalars ⊣ Restrict phi :=
  AdjunctionFromUniversalArrows (Restrict phi) extend_universal_arrow.

(* 相关说明。 （已译） *)

(** The 函子 produced 伴随 plumbing IS [ExtendObj] on
 对象, nose. （已译） *)
Example ExtendScalars_obj (M : RMod R) :
  fobj[ExtendScalars] M = ExtendObj M := eq_refl.

Example extend_arrow_is_unit (M : RMod R) :
  @arrow _ _ M (Restrict phi) (extend_universal_arrow M) = extend_unit M
  := eq_refl.

Definition extend_adj_unit (M : RMod R)
  : M ~{RMod R}~> Restrict phi (ExtendScalars M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ extend_restrict_adjunction M.

Example extend_adj_unit_computes (M : RMod R) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (extend_adj_unit M)) m
    = ext_gen M (rig_one (ring_rig S)) m := eq_refl.

Example extend_med_gen (M : RMod R) (N : RModObject S)
  (g : M ~{RMod R}~> RestrictObj phi N)
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (extend_med M N g)) (ext_gen M x m)
    = rm_smul N x (cmon_map (rm_hom g) m) := eq_refl.

(** 本节：The counit does NOT compute: it [unique_obj] [Qed]-opaque
 [ump_universal_arrows]. What holds agreement up [≈]. （已译） *)
Definition extend_adj_counit (N : RMod S)
  : ExtendScalars (Restrict phi N) ~{RMod S}~> N :=
  @Category.Theory.Adjunction.counit _ _ _ _ extend_restrict_adjunction N.

Lemma extend_counit_unit (N : RMod S) (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit N))
    (ext_gen (Restrict phi N) (rig_one (ring_rig S)) m) ≈ m.
Proof.
  exact (@to_adj_counit _ _ _ _ extend_restrict_adjunction N m).
Qed.

Lemma extend_counit_gen (N : RMod S)
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit N))
    (ext_gen (Restrict phi N) x m) ≈ rm_smul N x m.
Proof.
  rewrite (ext_gen_scale (Restrict phi N) x m).
  rewrite (rm_map_smul (extend_adj_counit N) x
             (ext_gen (Restrict phi N) (rig_one (ring_rig S)) m)).
  now rewrite (extend_counit_unit N m).
Qed.

(** The arrow action relabels right-hand factor. It defined by
 universal factorization, not formula, so 这是 定理. （已译） *)
Lemma extend_fmap_gen {M M' : RMod R} (u : M ~{RMod R}~> M')
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (fmap[ExtendScalars] u)) (ext_gen M x m)
    ≈ ext_gen M' x (cmon_map (rm_hom u) m).
Proof.
  rewrite (ext_gen_scale M x m).
  rewrite (rm_map_smul (fmap[ExtendScalars] u) x
             (ext_gen M (rig_one (ring_rig S)) m)).
  rewrite <- (unique_property
                (ump_universal_arrows (extend_universal_arrow M)
                   (@arrow _ _ M' (Restrict phi)
                      (extend_universal_arrow M') ∘ u)) m).
  symmetry; apply ext_gen_scale.
Qed.

(*
   本节说明 Extension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ext_ring_hom
  : Ring_RMod R ~{RMod R}~> RestrictObj phi (Ring_RMod S) := {|
  rm_hom := {| cmon_map := {| morphism := rig_map phi |} |}
|}.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.

Definition extend_ring_to
  : ExtendObj (Ring_RMod R) ~{RMod S}~> Ring_RMod S :=
  extend_med (Ring_RMod R) (Ring_RMod S) ext_ring_hom.

Program Definition extend_ring_from
  : Ring_RMod S ~{RMod S}~> ExtendObj (Ring_RMod R) := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun s => ext_gen (Ring_RMod R) s (rig_one (ring_rig R)) |} |}
|}.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.

Program Definition extend_ring_iso
  : @Isomorphism (RMod S) (ExtendObj (Ring_RMod R)) (Ring_RMod S) := {|
  to   := extend_ring_to;
  from := extend_ring_from
|}.
Next Obligation.
  intro s; simpl.
  rewrite (rig_map_one phi); apply (rig_mul_one_r (ring_rig S)).
Qed.

Next Obligation.
  intro t.
  refine (tensor_hom_ext
            (ext_forget (Ring_RMod R) (ExtendObj (Ring_RMod R))
               (rmod_hom_compose extend_ring_from extend_ring_to))
            (ext_restrict_id (Ring_RMod R)) _ t).
  intros x r; simpl.
  refine (mte_trans (@mte_gen R ExtBase (Ring_RMod R) _ _ _ _
                       (symmetry (Hc r x)) (reflexivity _)) _).
  refine (mte_trans (@tensor_balanced R ExtBase (Ring_RMod R) r x
                       (rig_one (ring_rig R))) _).
  exact (@mte_gen R ExtBase (Ring_RMod R) _ _ _ _
           (reflexivity x) (rig_mul_one_r (ring_rig R) r)).
Qed.

(** Non-degeneracy, by mapping OUT: no induction over [mt_eq] could give
    a negative.  If S is not the zero ring then 1 (x) 1 is not 0. *)
Lemma extend_gen_nonzero
  (Hnz : rig_one (ring_rig S) ≈ rig_zero (ring_rig S) → False) :
  ext_gen (Ring_RMod R) (rig_one (ring_rig S)) (rig_one (ring_rig R))
    ≈ cmon_zero (ExtendObj (Ring_RMod R)) → False.
Proof.
  intro He.
  apply Hnz.
  pose proof (proper_morphism (cmon_map (rm_hom extend_ring_to)) _ _ He)
    as Hz.
  simpl in Hz.
  rewrite <- Hz.
  rewrite (rig_map_one phi).
  symmetry; apply (rig_mul_one_r (ring_rig S)).
Qed.

End ExtensionOfScalars.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Fail Definition ext_probe_instrument : true = false := eq_refl.

(*
   本节说明 Extension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example ext_probe_action_strict {R S : RingObject}
  (phi : R ~{Rng}~> S) (Hc : CentralImage phi) (M : RMod R)
  (r : carrier (rig_setoid (ring_rig R)))
  (t : carrier (cmon_setoid (TensorMod (ExtBase phi) M))) :
  rm_smul (TensorMod (ExtBase phi) M) r t
    = rm_smul (RestrictObj phi (ExtendObj phi Hc M)) r t := eq_refl.

(* The counit does not compute: it is [unique_obj] of the [Qed]-opaque
   [ump_universal_arrows], so nothing reduces through it.  Compare the
   UNIT, which does compute — [extend_adj_unit_computes] above. *)
Fail Example ext_probe_counit_strict {R S : RingObject}
  (phi : R ~{Rng}~> S) (Hc : CentralImage phi) (N : RMod S)
  (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit phi Hc N))
    (ext_gen phi (Restrict phi N) (rig_one (ring_rig S)) m) = m := eq_refl.

(*
   本节说明 Extension 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.QArith.QArith.

Lemma Q_central : CentralImage ZtoQ.
Proof.
  apply central_of_commutative.
  intros a b; simpl; apply Qmult_comm.
Qed.

Lemma Q_one_neq_zero :
  rig_one (ring_rig Q_Ring) ≈ rig_zero (ring_rig Q_Ring) → False.
Proof. intro H; vm_compute in H; discriminate. Qed.

Definition QZ_extend : RModObject Q_Ring :=
  ExtendObj ZtoQ Q_central (Ring_RMod Int_Ring).

Example QZ_is_ExtendScalars :
  fobj[ExtendScalars ZtoQ Q_central] (Ring_RMod Int_Ring) = QZ_extend
  := eq_refl.

(** Q (x)_Z Z is Q, as an isomorphism of Q-modules. *)
Definition QZ_iso
  : @Isomorphism (RMod Q_Ring) QZ_extend (Ring_RMod Q_Ring) :=
  extend_ring_iso ZtoQ Q_central.

(** The factorization COMPUTES: (1/2) (x) 3 goes to 3/2. *)
Example QZ_med_computes :
  cmon_map (rm_hom (extend_ring_to ZtoQ Q_central))
    (ext_gen ZtoQ (Ring_RMod Int_Ring) (1 # 2) 3%Z) = (3 # 2)%Q := eq_refl.

(** The quotient does not collapse, unit does not collapse: both
 proved 映射 OUT Q, since no induction over the
 quotienting 关系 could produce negative. （已译） *)
Lemma QZ_gen_nonzero :
  ext_gen ZtoQ (Ring_RMod Int_Ring)
    (rig_one (ring_rig Q_Ring)) (rig_one (ring_rig Int_Ring))
    ≈ cmon_zero QZ_extend → False.
Proof. exact (extend_gen_nonzero ZtoQ Q_central Q_one_neq_zero). Qed.

Lemma QZ_unit_separates :
  cmon_map (rm_hom (extend_unit ZtoQ Q_central (Ring_RMod Int_Ring))) 1%Z
    ≈ cmon_map (rm_hom (extend_unit ZtoQ Q_central (Ring_RMod Int_Ring))) 2%Z
    → False.
Proof.
  intro He.
  pose proof (proper_morphism
                (cmon_map (rm_hom (extend_ring_to ZtoQ Q_central))) _ _ He)
    as Hq.
  vm_compute in Hq; discriminate.
Qed.
