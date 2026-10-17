Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.Limit.

Generalizable All Variables.

(** * The free group functor, read through the adjoint functor theorem *)

(*
 nLab: https://ncatlab.org/nlab/show/free+group

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** [Prop] congruences on the free group's carrier: a solution set AT
       the carrier universe *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeGrpCongruence.

Context (X : SetoidObject).

Record IsGrpCongruence (Rq : FGWord X → FGWord X → Prop) : Prop := {
  gc_refl  : ∀ w, Rq w w;
  gc_sym   : ∀ u v, Rq u v → Rq v u;
  gc_trans : ∀ u v w, Rq u v → Rq v w → Rq u w;
  gc_gen   : ∀ u v, @equiv _ (is_setoid (FreeGrpSetoid X)) u v → Rq u v;
  gc_mul   : ∀ u u' v v', Rq u u' → Rq v v' →
               Rq (grp_mul (FreeGrpObject X) u v)
                  (grp_mul (FreeGrpObject X) u' v');
  gc_inv   : ∀ u v, Rq u v →
               Rq (grp_inv (FreeGrpObject X) u) (grp_inv (FreeGrpObject X) v)
}.

Definition FGCongIdx : Type :=
  { Rq : FGWord X → FGWord X → Prop & IsGrpCongruence Rq }.

(* NAMED, or [PropEquiv_of_relation] picks the ambient setoid by resolution
   and both implications are refused. *)
Definition QGrp_Setoid (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : Setoid (FGWord X) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := gc_refl  Rq H
        ; Equivalence_Symmetric  := gc_sym   Rq H
        ; Equivalence_Transitive := gc_trans Rq H |} |}.

(*
   本节说明 FreeAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QGrp (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : GrpObject :=
  {| grp_setoid := {| carrier := FGWord X ; is_setoid := QGrp_Setoid Rq H |};
     grp_unit := grp_unit (FreeGrpObject X);
     grp_mul  := grp_mul (FreeGrpObject X);
     grp_inv  := grp_inv (FreeGrpObject X);
     grp_mul_respects := fun _ _ Hu _ _ Hv => gc_mul Rq H _ _ _ _ Hu Hv;
     grp_mul_assoc := fun a b c =>
       gc_gen Rq H _ _ (grp_mul_assoc (FreeGrpObject X) a b c);
     grp_mul_unit_l := fun a =>
       gc_gen Rq H _ _ (grp_mul_unit_l (FreeGrpObject X) a);
     grp_mul_inv_l := fun a =>
       gc_gen Rq H _ _ (grp_mul_inv_l (FreeGrpObject X) a);
     grp_prop := @PropEquiv_of_relation _ (QGrp_Setoid Rq H) Rq
                   (fun _ _ h => h) (fun _ _ h => h)
  |}.

(* The insertion of generators into the quotient.  Written as a TACTIC
   proof: the record field expects `≈`, which is [Rq] only after delta. *)
Definition QGrp_insert (Rq : FGWord X → FGWord X → Prop)
  (H : IsGrpCongruence Rq) : X ~{Sets}~> Grp_Forget (QGrp Rq H).
Proof.
  unshelve refine {| morphism := fun a => fg_insert X a |}.
  intros a b Hab.
  exact (gc_gen Rq H _ _ (proper_morphism (fg_insert X) a b Hab)).
Defined.

End FreeGrpCongruence.

Arguments IsGrpCongruence {X} Rq.
Arguments QGrp_Setoid {X} Rq H.
Arguments QGrp {X} Rq H.
Arguments QGrp_insert {X} Rq H.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeGrpKernel.

Context (X : SetoidObject).
Context (G : GrpObject).
Context (h : X ~{Sets}~> Grp_Forget G).

Definition fg_ev (w : FGWord X) : carrier (grp_setoid G) :=
  grp_map (free_grp_extend h) w.

Definition fg_ker : FGWord X → FGWord X → Prop :=
  fun u v => @pequiv _ _ (grp_prop G) (fg_ev u) (fg_ev v).

Lemma fg_ker_is_cong : IsGrpCongruence fg_ker.
Proof.
  unfold fg_ker, fg_ev.
  constructor.
  - intro w; apply (@pequiv_from _ _ (grp_prop G)); reflexivity.
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)); symmetry;
      exact (@pequiv_to _ _ (grp_prop G) _ _ Huv).
  - intros u v w H1 H2; apply (@pequiv_from _ _ (grp_prop G)).
    transitivity (grp_map (free_grp_extend h) v);
      [ exact (@pequiv_to _ _ (grp_prop G) _ _ H1)
      | exact (@pequiv_to _ _ (grp_prop G) _ _ H2) ].
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)).
    exact (proper_morphism (grp_map (free_grp_extend h)) u v Huv).
  - intros u u' v v' H1 H2; apply (@pequiv_from _ _ (grp_prop G)).
    rewrite (grp_map_mul (free_grp_extend h) u v).
    rewrite (grp_map_mul (free_grp_extend h) u' v').
    exact (grp_mul_respects G _ _ (@pequiv_to _ _ (grp_prop G) _ _ H1)
                              _ _ (@pequiv_to _ _ (grp_prop G) _ _ H2)).
  - intros u v Huv; apply (@pequiv_from _ _ (grp_prop G)).
    rewrite (grp_map_inv (free_grp_extend h) u).
    rewrite (grp_map_inv (free_grp_extend h) v).
    exact (grp_inv_respects_law G _ _ (@pequiv_to _ _ (grp_prop G) _ _ Huv)).
Qed.

Definition fg_ker_idx : FGCongIdx X := existT _ fg_ker fg_ker_is_cong.

(*
   本节说明 FreeAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fg_ker_med : QGrp fg_ker fg_ker_is_cong ~{Grp}~> G.
Proof.
  unshelve refine (@Build_GrpHom' (QGrp fg_ker fg_ker_is_cong) G
                     {| morphism := fg_ev |} _).
  - intros u v Huv; exact (@pequiv_to _ _ (grp_prop G) _ _ Huv).
  - intros u v; exact (grp_map_mul (free_grp_extend h) u v).
Defined.

End FreeGrpKernel.

Arguments fg_ev {X G} h w.
Arguments fg_ker {X G} h.
Arguments fg_ker_is_cong {X G} h.
Arguments fg_ker_idx {X G} h.
Arguments fg_ker_med {X G} h.

(** ** The solution set, and the application *)

(* NAMED so that both record fields elaborate [QGrp] at ONE universe
   instance; written inline they mint two. *)
Definition QGrpOf {X : Sets} (i : FGCongIdx X) : obj[Grp] :=
  QGrp (`1 i) (`2 i).

Definition QGrpInsertOf {X : Sets} (i : FGCongIdx X)
  : X ~{Sets}~> Grp_Forget (QGrpOf i) := QGrp_insert (`1 i) (`2 i).

(* THE NON-CIRCULAR SOLUTION SET.  The covering of an [h : X ~> U c] is its
   own kernel congruence, and the covering equation is
   [free_grp_extend_generators] on the nose. *)
Definition Grp_Forget_solution_set_prop (X : Sets) : SolutionSet Grp_Forget X.
Proof.
  unshelve refine (@Build_SolutionSet Grp Sets Grp_Forget X
                     (FGCongIdx X) QGrpOf QGrpInsertOf _).
  intros c h.
  exists (fg_ker_idx h), (fg_ker_med h).
  intro a; simpl.
  exact (free_grp_extend_generators X c h a).
Defined.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grp_Forget_solution_set_from_adjunction (X : Sets) :
  SolutionSet Grp_Forget X :=
  solution_set_of_adjunction free_group_adjunction X.

(* UNCONDITIONAL and non-circular since this PR.  The statement is
   unchanged; only the fourth argument moved. *)
Definition free_group_via_GAFT : ∃ F : Sets ⟶ Grp, F ⊣ Grp_Forget :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous)
       Grp_Forget_solution_set_prop.

(* The circular reading of the same application, kept under a name that
   says so.  Its type is the type [free_group_via_GAFT] always had, which
   is why nothing downstream had to change. *)
Definition free_group_via_GAFT_from_adjunction :
  ∃ F : Sets ⟶ Grp, F ⊣ Grp_Forget :=
  GAFT Grp_Forget Grp_Complete
       (Continuous_PreservesImageLimit Grp_Forget_continuous)
       Grp_Forget_solution_set_from_adjunction.

(*
   本节说明 FreeAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_group_via_GAFT_agrees : `1 free_group_via_GAFT ≈ FreeGrp :=
  left_adjoint_iso Grp_Forget _ FreeGrp (`2 free_group_via_GAFT)
                   free_group_adjunction.

(** ** Riehl §5.1: the induced monad on Sets *)

Definition free_group_monad : @Monad Sets (Grp_Forget ◯ FreeGrp) :=
  Adjunction_Induced_Monad free_group_adjunction.

(*
   本节说明伴随、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_group_monad_ret (X : Sets) :
  @ret Sets (Grp_Forget ◯ FreeGrp) free_group_monad X = free_group_unit X
  := eq_refl.

Example free_group_monad_join (X : Sets) :
  @join Sets (Grp_Forget ◯ FreeGrp) free_group_monad X
    = fmap[Grp_Forget] (free_group_counit (FreeGrp X))
  := eq_refl.

(* ...and Riehl's description of the underlying endofunctor — a set goes to
   the words in its letters and their formal inverses — is the carrier of
   [(U ◯ F) X], on the nose. *)
Example free_group_monad_carrier (X : Sets) :
  carrier ((Grp_Forget ◯ FreeGrp) X) = FGWord X := eq_refl.

(*
   本节说明伴随、单子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_group_monad_via_GAFT :
  @Monad Sets (Grp_Forget ◯ `1 free_group_via_GAFT) :=
  Adjunction_Induced_Monad (`2 free_group_via_GAFT).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation SetOne := unit_setoid_object.

Notation grp_adj G :=
  (@adj Grp Sets FreeGrp Grp_Forget free_group_adjunction SetOne G).

(* The two directions are lifted out of the record literal: inside
   [{| to := … |}] the names [to] and [from] resolve to the fields being
   defined, not to [Isomorphism]'s projections. *)

Program Definition grp_repr_const (G : Grp) (a : carrier (Grp_Forget G)) :
  SetOne ~{Sets}~> Grp_Forget G := {| morphism := fun _ => a |}.

Definition grp_repr_to (G : Grp) (f : FreeGrp SetOne ~{Grp}~> G) :
  carrier (Grp_Forget G) := to (grp_adj G) f ttt.

Definition grp_repr_from (G : Grp) (a : carrier (Grp_Forget G)) :
  FreeGrp SetOne ~{Grp}~> G := from (grp_adj G) (grp_repr_const G a).

(*
   本节说明 FreeAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma grp_repr_to_natural {x y : Grp} (f : x ~{Grp}~> y)
  (h : FreeGrp SetOne ~{Grp}~> x) :
  grp_repr_to y (f ∘ h) ≈ f (grp_repr_to x h).
Proof.
  exact (@to_adj_nat_r Grp Sets FreeGrp Grp_Forget free_group_adjunction
                       SetOne x y f h ttt).
Qed.

Lemma grp_repr_from_natural {x y : Grp} (f : x ~{Grp}~> y)
  (a : carrier (Grp_Forget x)) (w : carrier (Grp_Forget (FreeGrp SetOne))) :
  grp_repr_from y (f a) w ≈ f (grp_repr_from x a w).
Proof.
  unfold grp_repr_from.
  transitivity (from (grp_adj y) (fmap[Grp_Forget] f ∘ grp_repr_const x a) w).
  - exact (proper_morphism (from (grp_adj y))
             (grp_repr_const y (f a))
             (fmap[Grp_Forget] f ∘ grp_repr_const x a)
             (fun _ => reflexivity _) w).
  - exact (@from_adj_nat_r Grp Sets FreeGrp Grp_Forget free_group_adjunction
                           SetOne x y f (grp_repr_const x a) w).
Qed.

Program Definition Grp_Forget_Representable : Representable Grp_Forget := {|
  repr_obj := FreeGrp SetOne;
  represented :=
    {| to   := {| transform := fun G => {| morphism := grp_repr_to G |} |}
     ; from := {| transform := fun G => {| morphism := grp_repr_from G |} |} |}
|}.
Next Obligation. symmetry; exact (grp_repr_to_natural f x0). Qed.
Next Obligation. exact (grp_repr_to_natural f x0). Qed.
Next Obligation.
  exact (proper_morphism (from (grp_adj G))
           (grp_repr_const G x) (grp_repr_const G y) (fun _ => H) a).
Qed.
Next Obligation. symmetry; exact (grp_repr_from_natural f x0 a). Qed.
Next Obligation. exact (grp_repr_from_natural f x0 a). Qed.
(* The two isomorphism laws are the adjunction's own, read at [ttt].  In
   [Sets] an equation between morphisms is pointwise, so each is the
   corresponding [iso_?_from] applied to a point. *)
Next Obligation. exact (iso_to_from (grp_adj x) (grp_repr_const x x0) ttt). Qed.
Next Obligation.
  unfold grp_repr_from, grp_repr_to.
  transitivity (from (grp_adj x) (to (grp_adj x) x0) a).
  - refine (proper_morphism (from (grp_adj x))
              (grp_repr_const x (to (grp_adj x) x0 ttt))
              (to (grp_adj x) x0) _ a).
    intro u; destruct u; reflexivity.
  - exact (iso_from_to (grp_adj x) x0 a).
Qed.

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation grp_adj_at X H :=
  (@adj Grp Sets FreeGrp Grp_Forget free_group_adjunction X H).

(* The transpose of [g] agrees with [g] at the unit.  This is
   [to_adj_unit] composed with [iso_to_from], read pointwise. *)
Lemma free_group_transpose_at_unit {X : Sets} (H : Grp)
      (g : X ~{Sets}~> Grp_Forget H) (a : carrier X) :
  g a ≈ fmap[Grp_Forget] (from (grp_adj_at X H) g) (free_group_unit X a).
Proof.
  transitivity (to (grp_adj_at X H) (from (grp_adj_at X H) g) a).
  - symmetry; exact (iso_to_from (grp_adj_at X H) g a).
  - exact (@to_adj_unit Grp Sets FreeGrp Grp_Forget free_group_adjunction
             X H (from (grp_adj_at X H) g) a).
Qed.

(** Any embedding of [X] into a group's underlying set forces the unit to
    be injective. *)
Theorem free_group_unit_injective_of_embedding {X : Sets} (H : Grp)
        (g : X ~{Sets}~> Grp_Forget H)
        (Hg : ∀ a b : carrier X, g a ≈ g b → a ≈ b)
        (a b : carrier X) :
  free_group_unit X a ≈ free_group_unit X b → a ≈ b.
Proof.
  intro Heq.
  apply Hg.
  transitivity (fmap[Grp_Forget] (from (grp_adj_at X H) g)
                  (free_group_unit X a)).
  { exact (free_group_transpose_at_unit H g a). }
  transitivity (fmap[Grp_Forget] (from (grp_adj_at X H) g)
                  (free_group_unit X b)).
  { exact (proper_morphism (fmap[Grp_Forget] (from (grp_adj_at X H) g))
             (free_group_unit X a) (free_group_unit X b) Heq). }
  symmetry; exact (free_group_transpose_at_unit H g b).
Qed.

(* A decision procedure for a [Sets] object's own [≈].  Stated as a
   [Type]-valued sum rather than [sumbool]: [≈] is a [crelation], so it does
   not fit in [Prop]. *)
Definition SetoidDecidable (X : Sets) : Type :=
  ∀ a b : carrier X, (a ≈ b) + ((a ≈ b) → False).

(* The characteristic map of [a], the separating map of Mac Lane's
   argument.  This is the step that needs [dec]: without it there is no
   function at all, respectfulness aside. *)
Program Definition grp_chi {X : Sets} (dec : SetoidDecidable X)
        (a : carrier X) : X ~{Sets}~> Grp_Forget Z2 := {|
  morphism := fun x => if dec x a then true else false
|}.
Next Obligation.
  proper.
  (* Name the premise by its shape: since #450 made [Z2]'s setoid
     universe-polymorphic the goal reads [Proper (equiv ==> eq)] and
     [proper] no longer calls the premise [H]. *)
  match goal with Hxy : @equiv _ _ _ _ |- _ => rename Hxy into H end.
  destruct (dec x a) as [e1|n1], (dec y a) as [e2|n2]; auto.
  - now destruct (n2 (transitivity (symmetry H) e1)).
  - now destruct (n1 (transitivity H e2)).
Qed.

(** Mac Lane's separation argument, with the decision procedure it needs
    made explicit.  Distinct generators stay distinct in the free group. *)
Theorem free_group_unit_injective_dec {X : Sets} (dec : SetoidDecidable X)
        (a b : carrier X) :
  free_group_unit X a ≈ free_group_unit X b → a ≈ b.
Proof.
  intro Heq.
  destruct (dec a b) as [Hab|Hab]; [exact Hab|].
  (* The two sides disagree at [grp_chi dec a], which the transpose
     forbids. *)
  assert (Hchi : grp_chi dec a a ≈ grp_chi dec a b).
  { transitivity (fmap[Grp_Forget]
                    (from (grp_adj_at X Z2) (grp_chi dec a))
                    (free_group_unit X a)).
    { exact (free_group_transpose_at_unit Z2 (grp_chi dec a) a). }
    transitivity (fmap[Grp_Forget]
                    (from (grp_adj_at X Z2) (grp_chi dec a))
                    (free_group_unit X b)).
    { exact (proper_morphism
               (fmap[Grp_Forget] (from (grp_adj_at X Z2) (grp_chi dec a)))
               (free_group_unit X a) (free_group_unit X b) Heq). }
    symmetry; exact (free_group_transpose_at_unit Z2 (grp_chi dec a) b). }
  simpl in Hchi.
  destruct (dec a a) as [_|Haa]; [| now destruct (Haa (reflexivity a))].
  destruct (dec b a) as [Hba|_]; [| discriminate Hchi].
  now destruct (Hab (symmetry Hba)).
Qed.

(*
   本节说明 FreeAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition TwoLetters_dec : SetoidDecidable TwoLetters :=
  fun a b => match Bool.bool_dec a b with
             | left e  => inl e
             | right n => inr n
             end.

Corollary free_group_two_letters_distinct :
  free_group_unit TwoLetters true ≈ free_group_unit TwoLetters false → False.
Proof.
  intro Heq.
  exact (Bool.diff_true_false
           (free_group_unit_injective_dec TwoLetters_dec true false Heq)).
Qed.
