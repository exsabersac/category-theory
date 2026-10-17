Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.

Generalizable All Variables.

(*
   本文件给出余极限相关等价/构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ReflectiveColimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

Definition radj : reflector R ⊣ I := reflective_adj R.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition rc_unit_hom (x : Sub C S) : x ~{Sub C S}~> reflector R (I x).
Proof.
  exists (@Category.Theory.Adjunction.unit (Sub C S) C (reflector R) I radj
            (I x)).
  apply (reflective_full R).
Defined.

Lemma rc_iso_to_from (x : Sub C S) :
  @counit (Sub C S) C (reflector R) I radj x ∘ rc_unit_hom x ≈ id.
Proof. apply (@fmap_counit_unit (Sub C S) C (reflector R) I radj x). Qed.

Lemma rc_iso_from_to (x : Sub C S) :
  rc_unit_hom x ∘ @counit (Sub C S) C (reflector R) I radj x ≈ id.
Proof.
  rewrite <- (counit_naturality radj).
  apply (@counit_fmap_unit (Sub C S) C (reflector R) I radj (I x)).
Qed.

Definition rc_counit_iso (x : Sub C S) : reflector R (I x) ≅[Sub C S] x :=
  {| to := @counit (Sub C S) C (reflector R) I radj x
   ; from := rc_unit_hom x
   ; iso_to_from := rc_iso_to_from x
   ; iso_from_to := rc_iso_from_to x |}.

Lemma rc_to (x : Sub C S) :
  to (rc_counit_iso x) ≈ @counit (Sub C S) C (reflector R) I radj x.
Proof. reflexivity. Qed.

Lemma rc_from (x : Sub C S) : from (rc_counit_iso x) ≈ rc_unit_hom x.
Proof. reflexivity. Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** The diagram isomorphism [reflector ◯ (I ◯ K) ≈ K]

    The counit isomorphism at each [K x], with its naturality square: the
    one triangle identity each way and [counit_naturality]. *)

Definition reflective_diagram_iso : (reflector R ◯ (I ◯ K)) ≈ K.
Proof.
  exists (fun x => rc_counit_iso (K x)).
  intros x y f.
  rewrite <- comp_assoc.
  rewrite (rc_to (K x)).
  rewrite <- (counit_naturality radj (fmap[K] f)).
  rewrite comp_assoc.
  rewrite (rc_from (K y)).
  rewrite (rc_iso_from_to (K y)).
  now rewrite id_left.
Defined.

(*
   本节说明伴随、（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition reflective_colimit (L : Colimit (I ◯ K)) : Colimit K :=
  isalimit_to_limit
    (isacolimit_transport reflective_diagram_iso
       (lapc_is_acolimit radj L)).

Example reflective_colimit_apex (L : Colimit (I ◯ K)) :
  colimit_apex (reflective_colimit L) = reflector R (colimit_apex L)
  := eq_refl.

(* The injections: the reflector applied to the ambient injections, after
   the inverse counit — the formula the issue asks for, on the nose. *)
Example reflective_colimit_inj (L : Colimit (I ◯ K)) (x : J) :
  colimit_inj (colimit_is_acolimit (reflective_colimit L)) x
    = fmap[reflector R] (colimit_inj (colimit_is_acolimit L) x)
        ∘ rc_unit_hom (K x) := eq_refl.

(** ** The cocone-level form *)

Definition reflective_lift_cocone (N : Cocone (I ◯ K)) : Cocone K :=
  cocone_transport reflective_diagram_iso (FCocone (reflector R) N).

Example reflective_lift_cocone_apex (N : Cocone (I ◯ K)) :
  vertex_obj[reflective_lift_cocone N] = reflector R vertex_obj[N]
  := eq_refl.

Example reflective_lift_cocone_inj (N : Cocone (I ◯ K)) (x : J) :
  cocone_inj (reflective_lift_cocone N) x
    = fmap[reflector R] (cocone_inj N x) ∘ rc_unit_hom (K x) := eq_refl.

Definition reflective_colimit_cocone (N : Cocone (I ◯ K))
  (HN : IsColimitCocone N) : IsColimitCocone (reflective_lift_cocone N) :=
  isalimit_limitcone
    (isacolimit_transport reflective_diagram_iso
       (colimitcocone_isacolimit
          (left_adjoint_PreservesColimitCocone radj (I ◯ K) N HN))).

End Shape.

(** ** Mac Lane §V.5 Exercise 3 *)

Definition reflective_Cocomplete (HC : @Cocomplete C) : @Cocomplete (Sub C S) :=
  fun J K => reflective_colimit K (HC J (I ◯ K)).

(* The issue's name for the same constant. *)
Definition reflective_subcategory_cocomplete :
  @Cocomplete C → @Cocomplete (Sub C S) := reflective_Cocomplete.

(* The reflector is cocontinuous, with no hypothesis at all. *)
Definition reflective_reflector_Cocontinuous :
  CocontinuousFunctor (reflector R) := left_adjoint_Cocontinuous radj.

(** ** A hypothesis-free witness

    Over any shape with a terminal object the ambient colimit exists in
    ANY category (Structure/Limit/Initial.v's [terminal_Colimit]), so the
    reflected colimit needs no cocompleteness hypothesis. *)

Definition reflective_terminal_shape_colimit {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) : Colimit K :=
  reflective_colimit K (@terminal_Colimit J C T (I ◯ K)).

Example reflective_terminal_shape_apex {J : Category} (T : @Terminal J)
  (K : J ⟶ Sub C S) :
  colimit_apex (reflective_terminal_shape_colimit T K)
    = reflector R (I (K (@terminal_obj J T))) := eq_refl.

End ReflectiveColimits.
