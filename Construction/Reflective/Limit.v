Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Limits in a full reflective subcategory *)

(*
   Book: Riehl, "Category Theory in Context", Dover 2016, §4.6,
   Book: Riehl, ibid., §5.6, Corollary 5.6.6, printed p. 211, read from

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ReflectiveLimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

(* The reflection adjunction, under a short name.  Deliberately NOT an
   [Instance]: the transpose notations below name it explicitly. *)

Definition reflective_incl_adj : reflector R ⊣ I := reflective_adj R.

Notation "⌊ f ⌋" := (to   (@adj _ _ _ _ reflective_incl_adj _ _) f).
Notation "⌈ f ⌉" := (from (@adj _ _ _ _ reflective_incl_adj _ _) f).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition reflective_Incl_Full : Functor.Full I :=
  Full_Implies_Full_Functor C S (reflective_full R).

(* Injectivity of the forward transpose.  [adj_to_inj]
   (Adjunction/Additive.v) is the same fact, in a module outside this
   file's closure. *)

Lemma reflective_to_adj_inj {x : C} {y : Sub C S}
  (f g : reflector R x ~{Sub C S}~> y) : ⌊f⌋ ≈ ⌊g⌋ → f ≈ g.
Proof.
  intro Hfg.
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ f).
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ g).
  now apply (@from_adj_respects _ _ _ _ reflective_incl_adj).
Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** The lift *)

(* A cone over the diagram read in C, transposed across the reflection.
   Its apex is the reflector applied to the apex downstairs. *)

Definition reflective_lift (N : Cone (I ◯ K)) : Cone K :=
  rapl_transposed_cone reflective_incl_adj K N.

Example reflective_lift_apex (N : Cone (I ◯ K)) :
  vertex_obj[reflective_lift N] = reflector R vertex_obj[N] := eq_refl.

Example reflective_lift_leg (N : Cone (I ◯ K)) (x : J) :
  cone_leg (reflective_lift N) x = ⌈ cone_leg N x ⌉ := eq_refl.

(** ** The comparison isomorphism *)

Section Compare.

Context (N : Cone (I ◯ K)).
Context (HN : IsLimitCone N).

(* The mediator of the image of the lift through the limiting cone N. *)

Definition reflective_compare :
  I (reflector R vertex_obj[N]) ~{C}~> vertex_obj[N] :=
  unique_obj (HN (FCone I (reflective_lift N))).

Lemma reflective_compare_leg (x : J) :
  cone_leg N x ∘ reflective_compare ≈ fmap[I] ⌈ cone_leg N x ⌉.
Proof.
  exact (unique_property (HN (FCone I (reflective_lift N))) x).
Qed.

(* One inverse law, by the uniqueness clause of the limit N. *)

Lemma reflective_compare_unit :
  reflective_compare
    ∘ @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ≈ id[vertex_obj[N]].
Proof.
  pose proof (uniqueness (HN N)) as Hu.
  transitivity (unique_obj (HN N)).
  - symmetry.
    apply Hu.
    intro x.
    rewrite comp_assoc.
    rewrite reflective_compare_leg.
    rewrite <- (@to_adj_unit _ _ _ _ reflective_incl_adj _ _
                  (⌈ cone_leg N x ⌉)).
    apply (@from_adj_comp_law _ _ _ _ reflective_incl_adj).
  - apply Hu.
    intro x.
    apply id_right.
Qed.

(* The other inverse law, by fullness.  This is the one place fullness
   is spent BY HAND; the reflection lemma below spends it too, by handing
   it to [ff_reflect_ump]. *)

Lemma reflective_unit_compare :
  @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ∘ reflective_compare
    ≈ id[I (reflector R vertex_obj[N])].
Proof.
  pose (g := @prefmap _ _ I reflective_Incl_Full
               (reflector R vertex_obj[N]) (reflector R vertex_obj[N])
               (@unit _ _ (reflector R) I reflective_incl_adj
                  vertex_obj[N] ∘ reflective_compare)).
  assert (Hg : fmap[I] g
                 ≈ @unit _ _ (reflector R) I reflective_incl_adj
                     vertex_obj[N] ∘ reflective_compare)
    by exact (@fmap_sur _ _ I reflective_Incl_Full _ _ _).
  assert (Hid : g ≈ id).
  { apply reflective_to_adj_inj.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ g).
    rewrite Hg.
    rewrite <- comp_assoc.
    rewrite reflective_compare_unit.
    rewrite id_right.
    symmetry.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ id).
    rewrite fmap_id.
    now rewrite id_left. }
  rewrite <- Hg, Hid.
  apply fmap_id.
Qed.

Definition reflective_cone_iso :
  ConeIso (FCone I (reflective_lift N)) N :=
  ({| to          := reflective_compare
    ; from        := @unit _ _ (reflector R) I reflective_incl_adj
                       vertex_obj[N]
    ; iso_to_from := reflective_compare_unit
    ; iso_from_to := reflective_unit_compare |}
   ; reflective_compare_leg).

Example reflective_cone_iso_to :
  to `1 reflective_cone_iso = reflective_compare := eq_refl.

Example reflective_cone_iso_from :
  from `1 reflective_cone_iso
    = @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
  := eq_refl.

End Compare.

(** ** Reflection *)

(*
   本节说明函子、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition reflective_ReflectsLimitCone : ReflectsLimitCone K I :=
  fun M H =>
    @ff_ReflectsLimitCone (Sub C S) C I reflective_Incl_Full
      (Incl_Faithful C S) J K M H.

(** ** Riehl 4.6.14(i) / 5.6.6, at one diagram *)

(* Note that the lift ignores the limiting hypothesis: it is defined for
   every cone downstairs. *)

Definition reflective_CreatesLimit : CreatesLimit K I :=
  {| creates_lift      := fun N _ => reflective_lift N
   ; creates_lift_over := fun N HN => reflective_cone_iso N HN
   ; creates_reflect   := reflective_ReflectsLimitCone |}.

(** ** Mac Lane §IV.3 Exercise 7 *)

Definition reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K :=
  creates_limit_lift reflective_CreatesLimit L.

Example reflective_inherits_limits_cone (L : Limit (Incl C S ◯ K)) :
  @limit_cone _ _ _ (reflective_inherits_limits L)
    = reflective_lift (@limit_cone _ _ _ L) := eq_refl.

Example reflective_inherits_limits_apex (L : Limit (Incl C S ◯ K)) :
  vertex_obj[@limit_cone _ _ _ (reflective_inherits_limits L)]
    = reflector R vertex_obj[@limit_cone _ _ _ L] := eq_refl.

(** ** The inclusion preserves limits, with no completeness hypothesis *)

Definition reflective_Incl_PreservesLimitCone : PreservesLimitCone K I :=
  right_adjoint_PreservesLimitCone reflective_incl_adj K.

(* The creation route and the right-adjoint route to the same statement
   agree on mediators up to [≈], by uniqueness of the mediator, and are
   not convertible (pinned in the probe). *)

Lemma reflective_two_routes_agree (L : Limit (I ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (I ◯ K)) :
  unique_obj (creation_preserves_limit reflective_CreatesLimit L M HM P)
    ≈ unique_obj (reflective_Incl_PreservesLimitCone M HM P).
Proof using All.
  apply (uniqueness
           (creation_preserves_limit reflective_CreatesLimit L M HM P)).
  exact (unique_property (reflective_Incl_PreservesLimitCone M HM P)).
Qed.

End Shape.

(** ** The quantified forms, and Riehl's "in particular" *)

Definition reflective_CreatesLimitsOfShape (J : Category) :
  CreatesLimitsOfShape J I := fun K => reflective_CreatesLimit K.

Definition reflective_CreatesAllLimits : CreatesAllLimits I :=
  fun J K => reflective_CreatesLimit K.

Definition reflective_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete I HC reflective_CreatesAllLimits.

Definition reflective_Incl_continuous (HC : @Complete C) :
  ∀ (J : Category) (K : J ⟶ Sub C S), PreservesLimitCone K I :=
  creates_limits_continuous I HC reflective_CreatesAllLimits.

End ReflectiveLimits.
