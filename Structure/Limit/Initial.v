Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.

Generalizable All Variables.

(* * * Limits over shape 始对象, computed evaluation （已译） *)

(*
   nLab:        https://ncatlab.org/nlab/show/final+functor
   nLab:        https://ncatlab.org/nlab/show/limit

   本文件给出始对象结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The limit diagram over shape 始对象 （已译） *)

Section LimitFromInitial.

Context {J C : Category}.
Context (I : @Initial J).
Context (F : J ⟶ C).

(* The leg at x image 唯一箭头 ¡ : 0 ~> x. （已译） *)

Definition initial_leg (x : J) : F (@initial_obj J I) ~{C}~> F x :=
  fmap[F] (@zero J I x).

(* Cone coherence is uniqueness of arrows out of 0, pushed through F. *)

Lemma initial_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ initial_leg x ≈ initial_leg y.
Proof.
  unfold initial_leg.
  rewrite <- fmap_comp.
  apply fmap_respects.
  apply (@zero_unique J I).
Qed.

Definition initial_acone : ACone (F (@initial_obj J I)) F :=
  {| vertex_map     := initial_leg
   ; cone_coherence := @initial_leg_coherence |}.

Definition initial_cone : Cone F :=
  {| vertex_obj := F (@initial_obj J I)
   ; coneFrom   := initial_acone |}.

(* The leg AT 始对象 恒等 — up `≈`; see the
 header's STRENGTHS paragraph measured rejection at `eq_refl`. （已译） *)

Lemma initial_leg_id : initial_leg (@initial_obj J I) ≈ id.
Proof.
  unfold initial_leg.
  rewrite (@zero_unique J I _ (@zero J I (@initial_obj J I)) id).
  apply fmap_id.
Qed.

(* 相关说明。 （已译） *)

Definition initial_med (N : Cone F) :
  vertex_obj[N] ~{C}~> F (@initial_obj J I) :=
  cone_leg N (@initial_obj J I).

Lemma initial_med_commutes (N : Cone F) (x : J) :
  initial_leg x ∘ initial_med N ≈ cone_leg N x.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _ (@zero J I x)).
Qed.

(* Uniqueness: evaluate factorization condition at 0, where leg is
 `≈ id`. This whole content 普遍性质. （已译） *)

Lemma initial_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{C}~> F (@initial_obj J I)) :
  (∀ x : J, initial_leg x ∘ v ≈ cone_leg N x) → initial_med N ≈ v.
Proof.
  intro Hv.
  rewrite <- (Hv (@initial_obj J I)).
  rewrite initial_leg_id.
  now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)

Definition initial_IsLimitCone : IsLimitCone initial_cone :=
  fun N =>
    {| unique_obj      := initial_med N
     ; unique_property := initial_med_commutes N
     ; uniqueness      := initial_med_unique N |}.

Definition initial_IsALimit : IsALimit F (F (@initial_obj J I)) :=
  limitcone_isalimit initial_IsLimitCone.

Definition initial_Limit : Limit F :=
  limitcone_limit initial_cone initial_IsLimitCone.

(* Strictness, measured. *)

Example initial_leg_strict (x : J) :
  limit_leg initial_IsALimit x = fmap[F] (@zero J I x) := eq_refl.

Example initial_apex_strict :
  @vertex_obj _ _ _ initial_cone = F (@initial_obj J I) := eq_refl.

Example initial_med_strict (N : Cone F) :
  limit_med initial_IsALimit N = cone_leg N (@initial_obj J I) := eq_refl.

Example initial_Limit_strict :
  @limit_cone _ _ _ initial_Limit = initial_cone := eq_refl.

(* * *** The evaluation cone 终对象 [Cones F] （已译） *)

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition initial_Cones_Terminal : @Terminal (Cones F) := {|
  terminal_obj := initial_cone;
  one          := fun N => (initial_med N; initial_med_commutes N)
|}.
Next Obligation.
  rewrite <- (initial_med_unique x f X0).
  now rewrite <- (initial_med_unique x g X).
Qed.

Example initial_Cones_strict :
  @limit_cone _ _ _ (@Limit_Cones J C F initial_Cones_Terminal)
    = initial_cone := eq_refl.

(** *** The honest biconditional *)

(*
   本节说明（余）极限、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem limiting_iff_initial_leg_iso (N : Cone F) :
  IsLimitCone N ↔ IsIsomorphism (cone_leg N (@initial_obj J I)).
Proof.
  split.
  - intro HN.
    unshelve refine
      {| two_sided_inverse := unique_obj (HN initial_cone) |}.
    + rewrite (unique_property (HN initial_cone) (@initial_obj J I)).
      exact initial_leg_id.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN initial_cone) x).
        exact (initial_med_commutes N x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - intro Hiso.
    unshelve refine (limitcone_transport _ initial_IsLimitCone).
    unshelve eexists.
    + unshelve refine {| to   := two_sided_inverse
                       ; from := cone_leg N (@initial_obj J I) |}.
      * apply is_left_inverse.
      * apply is_right_inverse.
    + intro x; simpl.
      rewrite <- (initial_med_commutes N x).
      rewrite <- comp_assoc.
      rewrite is_right_inverse.
      now rewrite id_right.
Qed.

End LimitFromInitial.

(* * ** Reading invertibility back opposite 范畴 （已译） *)

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OpIso.

Context {C : Category}.

Definition iso_of_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h H)
    (@is_left_inverse (C^op) a b h H)
    (@is_right_inverse (C^op) a b h H).

Definition iso_to_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h H)
    (@is_left_inverse C b a h H)
    (@is_right_inverse C b a h H).

End OpIso.

(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ColimitFromTerminal.

Context {J C : Category}.
Context (T : @Terminal J).
Context (F : J ⟶ C).

(* The injection at x image 唯一箭头 ! : x ~> 1. （已译） *)

Definition terminal_inj (x : J) : F x ~{C}~> F (@terminal_obj J T) :=
  fmap[F] (@one J T x).

Definition terminal_cocone : Cocone F :=
  @initial_cone (J^op) (C^op) T (F^op).

Definition terminal_IsColimitCocone : IsColimitCocone terminal_cocone :=
  @initial_IsLimitCone (J^op) (C^op) T (F^op).

Definition terminal_IsAColimit : IsAColimit F (F (@terminal_obj J T)) :=
  @initial_IsALimit (J^op) (C^op) T (F^op).

Definition terminal_Colimit : Colimit F :=
  @initial_Limit (J^op) (C^op) T (F^op).

(* The mediator out colimit competing cocone that
 cocone's own injection at 终对象. （已译） *)

Definition terminal_med (N : Cocone F) :
  F (@terminal_obj J T) ~{C}~> vertex_obj[N] :=
  cocone_inj N (@terminal_obj J T).

Lemma terminal_med_commutes (N : Cocone F) (x : J) :
  terminal_med N ∘ terminal_inj x ≈ cocone_inj N x.
Proof. exact (colimit_med_commutes terminal_IsAColimit N x). Qed.

Lemma terminal_med_unique (N : Cocone F)
  (v : F (@terminal_obj J T) ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ terminal_inj x ≈ cocone_inj N x) → terminal_med N ≈ v.
Proof. intro Hv. exact (colimit_med_unique terminal_IsAColimit N v Hv). Qed.

Lemma terminal_inj_id : terminal_inj (@terminal_obj J T) ≈ id.
Proof. exact (@initial_leg_id (J^op) (C^op) T (F^op)). Qed.

(* Strictness of the covariant accessors, measured. *)

Example terminal_cocone_strict (x : J) :
  cocone_inj terminal_cocone x = terminal_inj x := eq_refl.

Example terminal_inj_strict (x : J) :
  colimit_inj terminal_IsAColimit x = terminal_inj x := eq_refl.

Example terminal_med_strict (N : Cocone F) :
  colimit_med terminal_IsAColimit N = terminal_med N := eq_refl.

Example terminal_apex_strict :
  colimit_apex terminal_Colimit = F (@terminal_obj J T) := eq_refl.

(*
   本节说明 Initial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition colimiting_iff_terminal_inj_iso (N : Cocone F) :
  IsColimitCocone N ↔ IsIsomorphism (cocone_inj N (@terminal_obj J T)) :=
  (fun H => iso_of_op _
     (fst (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N) H),
   fun H => snd (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N)
     (iso_to_op _ H)).

End ColimitFromTerminal.

(* 相关说明。 （已译） *)

(* `_1` has 始对象 — unique 对象 — instance did
 not exist: Instance/One.v's [Cat_Terminal] says `_1` terminal in
 Cat, different statement (see header). （已译） *)

Program Definition One_Initial : @Initial _1 := {|
  terminal_obj := ttt;
  one          := fun _ => ttt
|}.
Next Obligation. now destruct f, g. Qed.

(* The limit diagram shape 1 value at point. This is
 section-1 定理 instantiated, not second construction. （已译） *)

Definition point_cone {C : Category} (F : _1 ⟶ C) : Cone F :=
  @initial_cone _1 C One_Initial F.

Definition point_IsALimit {C : Category} (F : _1 ⟶ C) :
  IsALimit F (F ttt) := @initial_IsALimit _1 C One_Initial F.

Definition point_Limit {C : Category} (F : _1 ⟶ C) : Limit F :=
  @initial_Limit _1 C One_Initial F.

(* The cross-check exercise asks for: same cone TERMINAL
 OBJECT 范畴 cones, [Limit] that
 Instance/Cones/Limit.v reads off it very cone built above. （已译） *)

Definition point_Cones_Terminal {C : Category} (F : _1 ⟶ C) :
  @Terminal (Cones F) := @initial_Cones_Terminal _1 C One_Initial F.

Example point_Cones_strict {C : Category} (F : _1 ⟶ C) :
  @limit_cone _ _ _ (@Limit_Cones _1 C F (point_Cones_Terminal F))
    = point_cone F := eq_refl.

(** *** A computing witness in Sets *)

(*
   本节说明 Initial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition bool_set : obj[Sets] :=
  {| carrier := bool ; is_setoid := {| equiv := eq |} |}.

Program Definition elt_acone (b : bool) :
  ACone (@terminal_obj Sets Sets_Terminal) (=(bool_set)) := {|
  vertex_map := fun _ => {| morphism := fun _ => b |}
|}.

Definition elt_cone (b : bool) : Cone (=(bool_set)) :=
  {| vertex_obj := @terminal_obj Sets Sets_Terminal
   ; coneFrom   := elt_acone b |}.

Example point_Sets_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ (point_Limit (=(bool_set))))
    = bool_set := eq_refl.

(* 相关说明。 （已译） *)

Example point_Sets_med (b : bool) :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone b) ttt = b := eq_refl.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example point_Sets_separates :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone true) ttt
    <> limit_med (point_IsALimit (=(bool_set))) (elt_cone false) ttt.
Proof. discriminate. Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition ord_top (n : nat) : Ord_obj (S n) := ord_at n le_t_n.

Definition ord_bot (n : nat) : Ord_obj (S n) :=
  ord_at 0 (le_t_SS (le_t_zero n)).

Lemma ord_top_neq_bot (n : nat) : ord_top (S n) <> ord_bot (S n).
Proof. intro H; discriminate (f_equal ord_val H). Qed.

(* 相关说明。 （已译） *)

Program Definition Ordinal_Succ_Terminal (n : nat) :
  @Terminal (Ordinal (S n)) := {|
  terminal_obj := ord_top n;
  one          := fun x => le_t_SS_inv (ord_bound x)
|}.
Next Obligation. apply le_t_irr. Qed.

(* 相关说明。 （已译） *)

Definition ordinal_succ_IsAColimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : IsAColimit G (G (ord_top n)) :=
  @terminal_IsAColimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

Definition ordinal_succ_Colimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : Colimit G :=
  @terminal_Colimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ordinal_omega_apex (n : nat) :
  colimit_apex (ordinal_succ_Colimit (Ord_Omega (S n))) = n := eq_refl.

Example ordinal_omega_bot (n : nat) :
  Ord_Omega (S n) (ord_bot n) = 0%nat := eq_refl.

Lemma ordinal_omega_nonconstant (n : nat) :
  Ord_Omega (S (S n)) (ord_bot (S n))
    <> Ord_Omega (S (S n)) (ord_top (S n)).
Proof. discriminate. Qed.

(* * *** Why ω itself outside colimit half 定理 （已译） *)

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Omega_Initial : @Initial Omega := {|
  terminal_obj := 0%nat;
  one          := fun x => le_t_zero x
|}.
Next Obligation. apply le_t_irr. Qed.

Theorem Omega_no_Terminal : @Terminal Omega → False.
Proof.
  intro T.
  exact (le_t_no_desc (@one Omega T (S (@terminal_obj Omega T)))).
Qed.
