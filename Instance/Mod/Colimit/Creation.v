(** * U : R-Mod ⟶ Ab creates every colimit: Riehl's Corollary 5.6.10 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Ab.ModFunctor.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/monadic+functor
 nLab: https://ncatlab.org/nlab/show/Mod

   本文件给出余极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Joint epimorphicity of a colimiting cocone *)

(* Two maps out of the nadir that agree after every insertion are ≈: both
   mediate the cocone i ↦ v ∘ ι_i. *)

Lemma mcol_ext@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  {W : obj[Ab@{o c}]} (u v : vertex_obj[N] ~{Ab@{o c}}~> W)
  (H : ∀ (i : J) (m : carrier (rm_ab (K i))),
         cmon_map u (cmon_map (cone_leg N i) m)
           ≈ cmon_map v (cmon_map (cone_leg N i) m)) :
  u ≈ v.
Proof.
  unshelve eset (P := @Build_Cone (J^op) (Ab@{o c}^op)
    ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) W
    (@Build_ACone (J^op) (Ab@{o c}^op) W _
       (fun i => v ∘[Ab@{o c}] cone_leg N i) _)).
  - intros x y f m; simpl.
    exact (proper_morphism (cmon_map v) _ _
             (cone_leg_coh@{j c o c c c} N f m)).
  - transitivity (unique_obj (HN P)).
    + symmetry. apply (uniqueness (HN P)).
      intros i m. exact (H i m).
    + apply (uniqueness (HN P)).
      intros i m. reflexivity.
Qed.

(** ** The created action on the nadir *)

(* For a fixed r, i ↦ ι_i ∘ (r ·) is a cocone in Ab; its mediator is the
   action. *)

Definition mcol_smul_cone@{a c p o x j} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (r : carrier (rig_setoid (ring_rig R))) :
  Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) (Ab@{o c}^op)
       ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) vertex_obj[N]
       (@Build_ACone (J^op) (Ab@{o c}^op) vertex_obj[N]
          ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op)
          (fun i => cone_leg N i ∘[Ab@{o c}] module_act (K i) r) _)).
  intros x y f m; simpl.
  transitivity (cmon_map (cone_leg N x)
                  (cmon_map (rm_hom (fmap[K] f)) (rm_smul (K y) r m))).
  - apply (proper_morphism (cmon_map (cone_leg N x))).
    symmetry. exact (rm_map_smul (fmap[K] f) r m).
  - exact (cone_leg_coh@{j c o c c c} N f (rm_smul (K y) r m)).
Defined.

Definition mcol_smul_map@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N] :=
  unique_obj (HN (mcol_smul_cone N r)).

Lemma mcol_smul_triangle@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (i : J) (m : carrier (rm_ab (K i))) :
  cmon_map (mcol_smul_map N HN r) (cmon_map (cone_leg N i) m)
    ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m).
Proof. exact (unique_property (HN (mcol_smul_cone N r)) i m). Qed.

Definition mcol_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) : carrier (@vertex_obj _ _ _ N) :=
  cmon_map (mcol_smul_map N HN r) b.

Lemma mcol_smul_respects@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  Proper (equiv ==> equiv ==> equiv) (mcol_smul N HN).
Proof.
  intros r r' Hr b b' Hb. unfold mcol_smul.
  rewrite (proper_morphism (cmon_map (mcol_smul_map N HN r)) _ _ Hb).
  apply (mcol_ext N HN (mcol_smul_map N HN r) (mcol_smul_map N HN r')).
  intros i m.
  rewrite !mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  exact (rm_smul_respects (K i) r r' Hr m m (reflexivity _)).
Qed.

Lemma mcol_smul_distr_l@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b b' : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN r (cmon_plus vertex_obj[N] b b')
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN r b').
Proof. exact (cmon_map_plus (mcol_smul_map N HN r) b b'). Qed.

Lemma mcol_smul_distr_r@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_add (ring_rig R) r s) b
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_add (ring_rig R) r s))
            (ab_hom_add (mcol_smul_map N HN r) (mcol_smul_map N HN s))
            _ b).
  intros i m.
  etransitivity; [ exact (mcol_smul_triangle N HN _ i m) | ].
  etransitivity;
    [ exact (proper_morphism (cmon_map (cone_leg N i)) _ _
               (rm_smul_distr_r (K i) r s m)) | ].
  etransitivity; [ exact (cmon_map_plus (cone_leg N i) _ _) | ].
  exact (cmon_plus_respects _ _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m))
           _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN s i m))).
Qed.

Lemma mcol_smul_assoc@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_mul (ring_rig R) r s) b
    ≈ mcol_smul N HN r (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_mul (ring_rig R) r s))
            (mcol_smul_map N HN r ∘[Ab@{o c}] mcol_smul_map N HN s) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  rewrite (mcol_smul_triangle N HN s i m).
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_assoc.
Qed.

Lemma mcol_smul_one@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_one (ring_rig R)) b ≈ b.
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_one (ring_rig R)))
            (@id Ab@{o c} vertex_obj[N]) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_one.
Qed.

(** ** The created module and cocone *)

Definition ColimMod@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : obj[RMod@{o x a p c} R] :=
  @Build_RModObject R vertex_obj[N] (mcol_smul N HN)
    (mcol_smul_respects N HN) (mcol_smul_distr_l N HN)
    (mcol_smul_distr_r N HN) (mcol_smul_assoc N HN) (mcol_smul_one N HN).

Definition mcol_hom@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  K i ~{RMod@{o x a p c} R}~> ColimMod N HN :=
  @Build_RModHom R (K i) (ColimMod N HN) (cone_leg N i)
    (fun r m => Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m)).

Definition mcol_cone@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : Cone (K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) ((RMod@{o x a p c} R)^op) (K^op) (ColimMod N HN)
       (@Build_ACone (J^op) ((RMod@{o x a p c} R)^op) (ColimMod N HN)
          (K^op) (mcol_hom N HN) _)).
  intros x y f m. exact (cone_leg_coh@{j c o c c c} N f m).
Defined.

(** ** Reflection, and the created cocone is colimiting *)

(* A cocone of modules whose underlying cocone is colimiting in Ab is
   colimiting; the mediator is the Ab one, R-linear by [mcol_ext]. *)

Definition mcol_reflect@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M)) :
  IsLimitCone@{l l0 j c o} M.
Proof.
  intros P.
  pose (m := unique_obj
               (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))).
  assert (Hm : ∀ (i : J) (a : carrier (rm_ab (K i))),
             cmon_map m (cmon_map (rm_hom (cone_leg M i)) a)
               ≈ cmon_map (rm_hom (cone_leg P i)) a).
  { intros i a.
    exact (unique_property
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P)) i a). }
  unshelve refine (@Build_Unique _ _ _ (@Build_RModHom R _ _ m _) _ _).
  - intros r b.
    refine (mcol_ext (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M) HM
              (m ∘[Ab@{o c}] module_act vertex_obj[M] r)
              (module_act vertex_obj[P] r ∘[Ab@{o c}] m) _ b).
    intros i a; simpl.
    transitivity (cmon_map m (cmon_map (rm_hom (cone_leg M i))
                                (rm_smul (K i) r a))).
    + apply (proper_morphism (cmon_map m)).
      symmetry. exact (rm_map_smul (cone_leg M i) r a).
    + rewrite Hm.
      rewrite (rm_map_smul (cone_leg P i) r a).
      apply rm_smul_respects; [ reflexivity | ].
      symmetry. exact (Hm i a).
  - intros i a. exact (Hm i a).
  - intros v Hv b.
    exact (uniqueness
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
             (rm_hom v) Hv b).
Defined.

Definition mcol_strict_lift@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  StrictLift (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N :=
  @Build_StrictLift _ _ _ (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N
    (mcol_cone N HN) eq_refl (fun i m => reflexivity _).

(** ** Riehl's Corollary 5.6.10 *)

Definition RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  StrictlyCreatesColimit@{l x l l l0 j o c o} K
    (RMod_Forget_Ab@{x o o a p c} R) :=
  @Build_StrictlyCreatesLimit (J^op) ((RMod@{o x a p c} R)^op)
    (Ab@{o c}^op) (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op)
    (fun N HN => mcol_strict_lift N HN)
    (fun N HN => mcol_reflect (mcol_cone N HN) HN)
    (fun M HM => mcol_reflect M HM).

Definition RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  CreatesColimit@{l x l l l0 j o c o} K (RMod_Forget_Ab@{x o o a p c} R) :=
  StrictlyCreatesLimit_CreatesLimit
    (RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0} K).

Definition RMod_Forget_Ab_creates_colimits@{a c p o x t l l0 s}
  (R : RingObject@{a c p}) :
  CreatesAllColimits@{t l x l l l0 s o c o}
    (RMod_Forget_Ab@{x o o a p c} R) :=
  fun J K => RMod_Forget_Ab_CreatesColimit@{a c p o x s l l0} K.

(** ** Readbacks: the lift is on the nose *)

Example mcol_over_obj@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  rm_ab (ColimMod N HN) = vertex_obj[N] := eq_refl.

Example mcol_over_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  rm_hom (mcol_hom N HN i) = cone_leg N i := eq_refl.

Example mcol_smul_is_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  rm_smul (ColimMod N HN) r
  = cmon_map (unique_obj (HN (mcol_smul_cone N r))) := eq_refl.

Example mcol_lift_apex@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  rm_ab (vertex_obj[creates_colimit_lift
           (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L])
  = vertex_obj[L] := eq_refl.

Example mcol_lift_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) (i : J) :
  rm_hom (cone_leg (@limit_cone _ _ _
            (creates_colimit_lift
               (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L)) i)
  = cone_leg (@limit_cone _ _ _ L) i := eq_refl.

(* The whole lifted module IS [ColimMod] of the given colimit, read in the
   opposite category. *)
Example mcol_lift_module@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  vertex_obj[creates_colimit_lift
     (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L]
  = ColimMod (cone_op_comp (@limit_cone _ _ _ L))
      (islimitcone_op_comp (limit_limitcone L)) := eq_refl.

(* The reflected mediator computes: its group map IS the Ab mediator of
   the underlying cocones. *)
Example mcol_reflect_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M))
  (P : Cone (K^op)) :
  rm_hom (unique_obj (mcol_reflect M HM P))
  = unique_obj (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
  := eq_refl.

(** ** Uniqueness of the created action *)

(* Any family of Ab endomorphisms making every insertion R-linear is ≈ the
   created action. *)

Lemma mcol_smul_unique@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (s : carrier (rig_setoid (ring_rig R)) →
       vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N])
  (Hs : ∀ (i : J) r (m : carrier (rm_ab (K i))),
     cmon_map (s r) (cmon_map (cone_leg N i) m)
       ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m))
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  cmon_map (s r) b ≈ mcol_smul N HN r b.
Proof.
  refine (mcol_ext N HN (s r) (mcol_smul_map N HN r) _ b).
  intros i m. rewrite Hs. symmetry. apply mcol_smul_triangle.
Qed.

(** ** A witness: every diagram over a shape with a terminal object *)

(* Structure/Limit/Initial.v's [terminal_Colimit] is a colimit in Ab of
   U ◯ K; the lift has group U (K 1) and action K(!)(r · m). *)

Definition rmod_terminal_colimit@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  Colimit K :=
  creates_colimit_lift (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K)
    (terminal_Colimit@{j c o c l0 l} T (RMod_Forget_Ab@{x o o a p c} R ◯ K)).

Example rmod_terminal_group@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  rm_ab (vertex_obj[@limit_cone _ _ _
           (rmod_terminal_colimit@{a c p o x j l l0} T K)])
  = rm_ab (K (@terminal_obj J T)) := eq_refl.

Example rmod_terminal_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  = cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
      (rm_smul (K (@terminal_obj J T)) r m) := eq_refl.

Lemma rmod_terminal_smul_own@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  ≈ rm_smul (K (@terminal_obj J T)) r m.
Proof.
  change (cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
            (rm_smul (K (@terminal_obj J T)) r m)
          ≈ rm_smul (K (@terminal_obj J T)) r m).
  etransitivity.
  - exact (@fmap_respects _ _ K _ _ (@one J T (@terminal_obj J T)) id
             (one_unique _ _) (rm_smul (K (@terminal_obj J T)) r m)).
  - exact (@fmap_id _ _ K _ (rm_smul (K (@terminal_obj J T)) r m)).
Qed.
