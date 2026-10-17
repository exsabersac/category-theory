Require Import Coq.Lists.List.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Adjunction.Continuity.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Closed.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Import ListNotations.

Section DualNoRightAdjoint.

Context (F : FieldObject).

Notation Vct := (Vct_F F).

(** ** The line, its countable power and the coordinate functionals *)

Definition VctLine : Vct := Ring_RMod (field_ring F).

Definition PowLine : Vct := ProdMod (fun _ : nat => VctLine).

Definition vct_coord (n : nat) : PowLine ~{Vct}~> VctLine :=
  prod_proj (fun _ : nat => VctLine) n.

Notation DP := (DualMod F PowLine).

(* The zero homomorphism between two vector spaces. *)
Program Definition vct_zero_hom (M N : Vct) : M ~{Vct}~> N := {|
  rm_hom := {| cmon_map := {| morphism := fun _ => cmon_zero N |} |}
|}.
Next Obligation. intros M N a b _; reflexivity. Qed.
Next Obligation. intros M N; reflexivity. Qed.
Next Obligation. intros M N a b; simpl; symmetry; apply cmon_plus_zero_l. Qed.
Next Obligation. intros M N r m; simpl; symmetry; apply rm_smul_zero_r. Qed.

(** ** The span of the coordinate functionals inside the dual of the power *)

(* A finite formal combination of coordinate functionals, evaluated. *)
Fixpoint span_sum (p : list (nat * carrier (cmon_setoid VctLine)))
  : carrier (cmon_setoid DP) :=
  match p with
  | nil => cmon_zero DP
  | (n, c) :: q => cmon_plus DP (rm_smul DP c (vct_coord n)) (span_sum q)
  end.

Lemma span_sum_app (p q : list (nat * carrier (cmon_setoid VctLine))) :
  span_sum (p ++ q) ≈ cmon_plus DP (span_sum p) (span_sum q).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - symmetry; apply rig_add_zero_l.
  - rewrite IH; symmetry; apply rig_add_assoc.
Qed.

Lemma span_sum_scale (r : carrier (cmon_setoid VctLine))
  (p : list (nat * carrier (cmon_setoid VctLine))) :
  rm_smul DP r (span_sum p)
    ≈ span_sum
        (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
             p).
Proof.
  intro v.
  induction p as [|[n c] p IH]; simpl.
  - apply rig_mul_zero_r.
  - rewrite rig_distr_l, IH.
    apply rig_add_respects; [| reflexivity].
    symmetry; apply rig_mul_assoc.
Qed.

(* The submodule of [DP] spanned by the coordinates: the functionals that
   ARE finite linear combinations of coordinate projections. *)
Program Definition SpanCoords : Submodule DP := {|
  smod_mem := fun phi => { p : list (nat * carrier (cmon_setoid VctLine))
                         & phi ≈ span_sum p }
|}.
Next Obligation.
  intros a b Hab [p Hp]; exists p; now rewrite <- Hab.
Qed.
Next Obligation. exists nil; simpl; reflexivity. Qed.
Next Obligation.
  intros a b [p Hp] [q Hq]; exists (p ++ q).
  rewrite span_sum_app, Hp, Hq; reflexivity.
Qed.
Next Obligation.
  intros r a [p Hp].
  exists (map (fun nc => (fst nc, rig_mul (ring_rig (field_ring F)) r (snd nc)))
              p).
  rewrite Hp; apply span_sum_scale.
Qed.

(* Every functional of the form [ψ ∘ coord n] lies in the span — the one
   place field commutativity is spent. *)
Lemma dual_coord_in_span (n : nat)
  (psi : carrier (cmon_setoid (DualMod F VctLine))) :
  smod_mem SpanCoords (cmon_map (rm_hom (fmap[Dual F] (vct_coord n))) psi).
Proof.
  exists [(n, cmon_map (rm_hom psi) (rig_one (ring_rig (field_ring F))))].
  intro v; simpl.
  rewrite rig_add_zero_r.
  transitivity (cmon_map (rm_hom psi)
                  (rm_smul VctLine (v n) (rig_one (ring_rig (field_ring F))))).
  - apply (proper_morphism (cmon_map (rm_hom psi))).
    simpl; symmetry; apply rig_mul_one_r.
  - rewrite (rm_map_smul psi (v n)).
    apply field_comm.
Qed.

(** ** The concrete colimit: the countable power, as a cocone in Vct^op *)

Definition LineDiagram : DiscreteCat nat ⟶ Vct^op :=
  DiscreteCat_Functor' (fun _ : nat => VctLine : obj[Vct^op]).

(* A family of maps out of an apex in Vct is a cocone over [LineDiagram]
   in [Vct^op]; the coherence over a discrete shape is [fmap_id]. *)
Definition op_discrete_cone (c : Vct) (pi : ∀ n : nat, c ~{Vct}~> VctLine) :
  Cocone LineDiagram.
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) ((Vct^op)^op)
                     (LineDiagram^op) c
                     (@Build_ACone ((DiscreteCat nat)^op) ((Vct^op)^op) c
                        (LineDiagram^op) pi _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

Definition PowCocone : Cocone LineDiagram := op_discrete_cone PowLine vct_coord.

(* The power is the colimit of the constant diagram in [Vct^op]: the
   product's universal property, read backwards. *)
Lemma PowCocone_IsColimitCocone : IsColimitCocone PowCocone.
Proof.
  intro M.
  unshelve refine {| unique_obj := _ |}.
  - exact (prod_tuple (fun _ : nat => VctLine)
             (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)).
  - intros n z; reflexivity.
  - intros u Hu z n; symmetry; apply (Hu n z).
Defined.

(** ** The obstruction hypothesis, in Mac Lane's own words *)

(* Some functional on [F^ℕ] is NOT a finite linear combination of the
   coordinate projections.  Classically true (Erdős–Kaplansky); not
   provable in ZF + DC, hence a hypothesis — see the header. *)
Definition CoordSpanProper : Type :=
  { phi : carrier (cmon_setoid DP) & smod_mem SpanCoords phi → False }.

(** ** The refutation *)

Definition SpanQuot : Vct := QuotientMod SpanCoords.

Definition span_quot : Dual F PowLine ~{Vct}~> SpanQuot :=
  mquot_proj SpanCoords.

(* The competing cocone under the image diagram: the quotient by the span,
   with the composite legs. *)
Definition ZeroCocone : Cocone (Dual F ◯ LineDiagram).
Proof.
  unshelve refine (@Build_Cone ((DiscreteCat nat)^op) (Vct^op)
                     ((Dual F ◯ LineDiagram)^op) SpanQuot
                     (@Build_ACone ((DiscreteCat nat)^op) (Vct^op) SpanQuot
                        ((Dual F ◯ LineDiagram)^op)
                        (fun n => span_quot ∘ fmap[Dual F] (vct_coord n)) _)).
  intros x y e; destruct e.
  change (@eq_refl nat y) with (@id ((DiscreteCat nat)^op) y).
  rewrite fmap_id.
  apply id_left.
Defined.

(* If [Dual F] preserved the colimit, the image cocone would be colimiting,
   and two mediators to [ZeroCocone] — the quotient map and the zero map —
   would coincide; then every functional lies in the span. *)
Theorem dual_not_PreservesColimitCocone (H : CoordSpanProper) :
  PreservesColimitCocone LineDiagram (Dual F) → False.
Proof.
  intro P.
  destruct H as [phi Hphi].
  pose proof (P PowCocone PowCocone_IsColimitCocone) as HC.
  destruct (HC ZeroCocone) as [w Hw Huniq].
  assert (Hq : w ≈ span_quot) by (apply Huniq; intros n psi; reflexivity).
  assert (Hz : w ≈ vct_zero_hom (Dual F PowLine) SpanQuot).
  { apply Huniq; intros n psi.
    symmetry.
    exact (mquot_proj_kills SpanCoords _ (dual_coord_in_span n psi)). }
  (* [mquot_proj_kernel]'s right-hand side is the [inhabited] truncation of
     membership since the PR "algebraic carriers are sets" (2026-09-17), so
     the witness is opened here rather than applied directly.  The goal is
     [False], a [Prop], so the elimination is allowed and nothing is lost. *)
  unshelve refine
    (match fst (mquot_proj_kernel SpanCoords phi) _ with
     | inhabits Hm => Hphi Hm
     end).
  transitivity (cmon_map (rm_hom w) phi).
  - symmetry; exact (Hq phi).
  - exact (Hz phi).
Qed.

(* Mac Lane §V.5 Exercise 2: a right adjoint of [Dual F] would make it a
   left adjoint, hence carry the colimit above to a colimit. *)
Definition dual_functor_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : Dual F ⊣ Rt) : False :=
  dual_not_PreservesColimitCocone H
    (left_adjoint_PreservesColimitCocone A LineDiagram).

(* The corollary: [Dual F] is not the left adjoint of its opposite. *)
Definition dual_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : Dual F ⊣ Opposite_Functor (Dual F)) : False :=
  dual_functor_no_right_adjoint H (Opposite_Functor (Dual F)) A.

(** ** The unconditional positive half: [Dual F] is adjoint to itself on the
       right, so it is continuous *)

(* The remaining obligations (respectfulness, the two round trips, the four
   naturality squares) are closed by the tree's default tactic. *)
#[local] Obligation Tactic := cat_simpl.

(* The transpose [a ~> D x ↦ x ~> D a]: [D f ∘ η x]. *)
Definition vct_transpose {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  x ~{Vct}~> Dual F a :=
  fmap[Dual F] f ∘ eta F x.

Lemma vct_transpose_invol {a x : Vct} (f : a ~{Vct}~> Dual F x) :
  vct_transpose (vct_transpose f) ≈ f.
Proof. intros v w; simpl; reflexivity. Qed.

Program Definition vct_transpose_morphism (a x : Vct) :
  @SetoidMorphism _ (@homset Vct a (Dual F x))
                  _ (@homset Vct x (Dual F a)) := {|
  morphism := @vct_transpose a x
|}.

Program Definition vct_aor (a x : Vct) :
  @Isomorphism Sets
    {| carrier := @hom Vct a (Dual F x);
       is_setoid := @homset Vct a (Dual F x) |}
    {| carrier := @hom Vct x (Dual F a);
       is_setoid := @homset Vct x (Dual F a) |} := {|
  to   := vct_transpose_morphism a x;
  from := vct_transpose_morphism x a
|}.

Program Definition dual_vct_AdjointOnTheRight :
  @AdjointOnTheRight Vct Vct (Dual F) (Dual F) := {|
  aor := vct_aor
|}.

Definition dual_vct_Adjunction : Opposite_Functor (Dual F) ⊣ Dual F :=
  Adjunction_of_AdjointOnTheRight dual_vct_AdjointOnTheRight.

(* Mac Lane's contrast: as a right adjoint, [Dual F] carries every colimit
   of Vct to a limit; the exercise is about the other direction. *)
Definition dual_vct_Continuous : ContinuousFunctor (Dual F) :=
  right_adjoint_Continuous dual_vct_Adjunction.

(** ** The functor the issue names: StarAutonomous.v's [dual] at the line *)

(* Instance/Mod/Closed.v's [RMod_SymMonClosed] makes Vct symmetric
   monoidal closed, and Structure/Monoidal/StarAutonomous.v's [dual],
   read at the line, is the dual-object functor #359 proves self-adjoint on
   the right.  Its objects are the internal homs [HomMod x VctLine], whose
   carriers and operations coincide with [DualMod]'s on the nose; only the
   packed records differ (probe N1, N5). *)
Definition VctSMC : @SymMonClosed Vct :=
  RMod_SymMonClosed (field_ring F) (field_comm F).

Definition VctDual359 : Vct^op ⟶ Vct := @dual Vct VctSMC VctLine.

(* The identity on functionals, as a module homomorphism each way. *)
Definition to359 (x : Vct) : Dual F x ~{Vct}~> VctDual359 x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (Dual F x) (VctDual359 x)
       (@Build_CMonHom (ab_cmon (Dual F x)) (ab_cmon (VctDual359 x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Definition from359 (x : Vct) : VctDual359 x ~{Vct}~> Dual F x.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (VctDual359 x) (Dual F x)
       (@Build_CMonHom (ab_cmon (VctDual359 x)) (ab_cmon (Dual F x))
          (@Build_SetoidMorphism _ _ _ _ (fun g => g) _) _ _) _).
  - intros g g' Hg; exact Hg.
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

Program Definition iso359 (x : Vct) : Dual F x ≅[Vct] VctDual359 x := {|
  to := to359 x; from := from359 x
|}.

(* [dual]'s arrow action is the closed transpose of evaluation; by the
   uniqueness clause of the exponential's universal property it is
   precomposition, checked on the tensor's generators. *)
Lemma dual359_fmap_pre {x y : Vct} (f : y ~{Vct}~> x) :
  fmap[VctDual359] (f : x ~{Vct^op}~> y)
    ≈ to359 y ∘ fmap[Dual F] f ∘ from359 x.
Proof.
  apply (@dcur_uniq Vct VctSMC).
  refine (tensor_hom_ext _ _ _).
  intros g w; reflexivity.
Qed.

(* The natural isomorphism [Dual F ≈ VctDual359], in [Fun]'s [≈]. *)
Definition dual_iso359 : Dual F ≈ VctDual359.
Proof.
  exists (fun x : Vct^op => iso359 x).
  intros x y f.
  rewrite (dual359_fmap_pre f).
  intros g v; simpl; reflexivity.
Defined.

(* Mac Lane §V.5 Exercise 2 for the functor the issue names, by transport
   of the adjunction along the isomorphism (Theory/Adjunction.v's
   [adjunction_along_left_iso], #431). *)
Definition dual359_no_right_adjoint (H : CoordSpanProper)
  (Rt : Vct ⟶ Vct^op) (A : VctDual359 ⊣ Rt) : False :=
  dual_functor_no_right_adjoint H Rt (adjunction_along_left_iso dual_iso359 A).

Definition dual359_not_left_adjoint_of_op (H : CoordSpanProper)
  (A : VctDual359 ⊣ Opposite_Functor VctDual359) : False :=
  dual359_no_right_adjoint H (Opposite_Functor VctDual359) A.

(** ** Readbacks *)

Example vct_coord_component (n : nat) (v : carrier (cmon_setoid PowLine)) :
  cmon_map (rm_hom (vct_coord n)) v = v n := eq_refl.

Example pow_line_carrier :
  carrier (cmon_setoid PowLine) = (nat → carrier (cmon_setoid VctLine))
  := eq_refl.

Example vct_transpose_component {a x : Vct} (f : a ~{Vct}~> Dual F x)
  (v : carrier (cmon_setoid x)) (w : carrier (cmon_setoid a)) :
  cmon_map (rm_hom (cmon_map (rm_hom (vct_transpose f)) v)) w
    = cmon_map (rm_hom (cmon_map (rm_hom f) w)) v := eq_refl.

(* The isomorphism's components are the identity on functionals; this is
   what keeps [dual_iso359] transparent. *)
Example iso359_to_component (x : Vct) (g : carrier (cmon_setoid (Dual F x))) :
  cmon_map (rm_hom (to (projT1 dual_iso359 x))) g = g := eq_refl.

(* The colimit mediator computes: at a vector [z] of the competing apex it
   is the family of that cocone's legs at [z].  This is what keeps
   [PowCocone_IsColimitCocone] transparent. *)
Example pow_cocone_mediator_component (M : Cocone LineDiagram)
  (z : carrier (cmon_setoid (vertex_obj[M] : Vct))) (n : nat) :
  cmon_map (rm_hom (unique_obj (PowCocone_IsColimitCocone M))) z n
    = cmon_map (rm_hom (@vertex_map _ _ _ _ (@coneFrom _ _ _ M) n)) z
  := eq_refl.

End DualNoRightAdjoint.
