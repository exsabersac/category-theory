Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Connected.Components.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.One.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Adjunction.FullFaithful.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/connected+category
    nLab: https://ncatlab.org/nlab/show/diagonal+functor
    nLab: https://ncatlab.org/nlab/show/colimit
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/adjoint+functor
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,

   本文件给出连通性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(* * * (A) The counit at 常值 diagram invertible （已译） *)

Section ConnectedCounit.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* The counit colim ⊣ Δ read at 常值 diagram c. （已译） *)

Definition diagonal_counit (c : C) : colim_obj L Δ[J](c) ~{C}~> c :=
  @counit C ([J, C]) (ColimitFunctor L) (@Diagonal C J)
          (Colimit_Diagonal_Adjunction L) c.

Example diagonal_counit_strict (c : C) :
  diagonal_counit c = colim_transpose_from L (id{[J, C]}) := eq_refl.

(* Every triangle counit 恒等: transposition takes
 恒等 transformation, whose components [fmap[Δ] id]. （已译） *)

Lemma diagonal_counit_commutes (c : C) (j : J) :
  diagonal_counit c ∘ colim_inj L Δ[J](c) j ≈ id.
Proof.
  unfold diagonal_counit.
  rewrite (colim_transpose_from_commutes L (id{[J, C]}) j).
  simpl; reflexivity.
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma colim_const_inj_agree (c : C) (x y : J) :
  colim_inj L Δ[J](c) x ≈ colim_inj L Δ[J](c) y.
Proof using K.
  apply (@leg_zigzag J C c (colim_obj L Δ[J](c))
           (fun j => colim_inj L Δ[J](c) j)).
  - intros p q f; simpl.
    rewrite <- (colim_inj_coherence L Δ[J](c) f); simpl.
    now rewrite id_right.
  - exact (cn_zigzag K x y).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition diagonal_counit_inverse (c : C) :
  c ~{C}~> colim_obj L Δ[J](c) := colim_inj L Δ[J](c) (cn_obj K).

Program Definition diagonal_counit_iso (c : C) :
  IsIsomorphism (diagonal_counit c) := {|
  two_sided_inverse := diagonal_counit_inverse c
|}.
Next Obligation.
  apply (diagonal_counit_commutes c (cn_obj K)).
Qed.
Next Obligation.
  apply (colim_med_eq L
           (@Cocone_of J C Δ[J](c) (colim_obj L Δ[J](c))
              (fun j => colim_inj L Δ[J](c) j)
              (fun x y f => colim_inj_coherence L Δ[J](c) f)));
    intro j; simpl.
  - unfold diagonal_counit_inverse.
    rewrite <- comp_assoc, (diagonal_counit_commutes c j), id_right.
    apply colim_const_inj_agree.
  - apply id_left.
Qed.

Definition diagonal_counit_Isomorphism (c : C) :
  colim_obj L Δ[J](c) ≅ c := {|
  to := diagonal_counit c;
  from := diagonal_counit_inverse c;
  iso_to_from := diagonal_counit_iso_obligation_1 c;
  iso_from_to := diagonal_counit_iso_obligation_2 c
|}.

Example diagonal_counit_Isomorphism_to (c : C) :
  to (diagonal_counit_Isomorphism c) = diagonal_counit c := eq_refl.

End ConnectedCounit.

(*
   本节说明（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CounitNaturality.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).

Lemma colim_delta_nat {x y : C} (f : x ~{C}~> y) :
  diagonal_counit L y ∘ Colim_map L (fmap[@Diagonal C J] f)
    ≈ f ∘ diagonal_counit L x.
Proof.
  apply (colim_med_eq L
           (@Cocone_of J C Δ[J](x) y (fun _ : J => f)
              (fun p q g => id_right f)));
    intro j; simpl.
  - rewrite <- comp_assoc,
      (Colim_map_commutes L (fmap[@Diagonal C J] f) j).
    rewrite comp_assoc, (diagonal_counit_commutes L y j); simpl.
    now rewrite id_left.
  - rewrite <- comp_assoc, (diagonal_counit_commutes L x j).
    now rewrite id_right.
Qed.

End CounitNaturality.

Section ConnectedNatIso.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* [ColimitFunctor L ◯ Δ ≈ Id[C]] as functors: a natural isomorphism,
   which is what [≈] means at [Functor_Setoid]. *)

Definition colim_diagonal_iso_Id :
  @equiv _ (@Functor_Setoid C C) (ColimitFunctor L ◯ @Diagonal C J)
         Id[C].
Proof using K.
  exists (fun c => diagonal_counit_Isomorphism L K c).
  intros x y f; simpl.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- (colim_delta_nat L f).
  rewrite comp_assoc.
  rewrite (iso_from_to (diagonal_counit_Isomorphism L K y)).
  now rewrite id_left.
Defined.

(* 相关说明。 （已译） *)

Example colim_diagonal_iso_Id_component (c : C) :
  `1 colim_diagonal_iso_Id c = diagonal_counit_Isomorphism L K c
  := eq_refl.

End ConnectedNatIso.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ConnectedFFI.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).

(* Injectivity 对象 needs OBJECT shape: 对象
 action 常值 函子 at 对象 IS 常值. （已译） *)

Definition Diagonal_InjectiveOnObjects :
  InjectiveOnObjects (@Diagonal C J) :=
  fun c c' H => f_equal (fun F : [J, C] => fobj[F] (cn_obj K)) H.

Definition diagonal_FFI : LeftAdjointFFInjective (@Diagonal C J) := {|
  ffi_left := ColimitFunctor L;
  ffi_adj := Colimit_Diagonal_Adjunction L;
  ffi_full := Diagonal_Full K;
  ffi_faithful := Diagonal_Faithful (cn_obj K);
  ffi_injective := Diagonal_InjectiveOnObjects
|}.

Definition diagonal_RI : ReflectiveIsoPresentation (@Diagonal C J) :=
  ffi_implies_ri diagonal_FFI.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition diagonal_fully_faithful_of_counit :
  (Full (@Diagonal C J) * Faithful (@Diagonal C J))%type :=
  snd (@right_adjoint_fully_faithful_iff_counit_iso
         C ([J, C]) (ColimitFunctor L) (@Diagonal C J)
         (Colimit_Diagonal_Adjunction L))
      (fun c => diagonal_counit_iso L K c).

End ConnectedFFI.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ConstantColimits (J C : Category) : Type := {
  cc_colim : HasColimitsOfShape J C;
  cc_obj (c : C) : colim_obj cc_colim Δ[J](c) = c;
  cc_inj (c : C) (j : J) :
    colim_inj cc_colim Δ[J](c) j ≈ id_cast (eq_sym (cc_obj c))
}.

Arguments cc_colim {J C} _.
Arguments cc_obj {J C} _ _.
Arguments cc_inj {J C} _ _ _.

Section ConstantChoice.

Context {J C : Category}.
Context (j0 : J).
Context (P : ConstantColimits J C).

(* The counit clause record does not state derived the
 injection clause at ANY single 对象 shape -- so step
 needs point J no zig-zag. （已译） *)

Lemma constant_colimits_counit (c : C) :
  diagonal_counit (cc_colim P) c ≈ id_cast (cc_obj P c).
Proof using P j0.
  rewrite <- (id_left (id_cast (cc_obj P c))).
  rewrite <- (diagonal_counit_commutes (cc_colim P) c j0).
  rewrite <- comp_assoc, (cc_inj P c j0).
  now rewrite id_cast_inv_l, id_right.
Qed.

Definition colimit_is_lali_of_diagonal :
  LeftAdjointLeftInverse (@Diagonal C J) := {|
  lali_left := ColimitFunctor (cc_colim P);
  lali_adj := Colimit_Diagonal_Adjunction (cc_colim P);
  lali_obj := cc_obj P;
  lali_counit := constant_colimits_counit
|}.

Example lali_left_strict :
  lali_left colimit_is_lali_of_diagonal = ColimitFunctor (cc_colim P)
  := eq_refl.

Example lali_obj_strict (c : C) :
  lali_obj colimit_is_lali_of_diagonal c = cc_obj P c := eq_refl.

(* Clause (a) now feeds exercise 4's cycle, all of it consumed. *)

Definition colimit_lali_ffi : LeftAdjointFFInjective (@Diagonal C J) :=
  lali_implies_ffi colimit_is_lali_of_diagonal.

Definition colimit_lali_ri : ReflectiveIsoPresentation (@Diagonal C J) :=
  lali_implies_ri colimit_is_lali_of_diagonal.

(* The comparison at STRICT 函子 equality, section (A)'s
 natural 同构 cannot reach. The coherence square is
 [colim_delta_nat] read through derived counit clause. （已译） *)

Definition colim_diagonal_strict_Id :
  @equiv _ (@Functor_StrictEq_Setoid C C)
         (ColimitFunctor (cc_colim P) ◯ @Diagonal C J) Id[C].
Proof using P j0.
  apply (strict_equiv_of_id_cast_nat
           (ColimitFunctor (cc_colim P) ◯ @Diagonal C J) Id[C]
           (fun c => cc_obj P c)).
  intros x y f; simpl.
  rewrite <- (constant_colimits_counit x).
  rewrite <- (constant_colimits_counit y).
  apply colim_delta_nat.
Defined.

(* Load-bearing same reason: 对象-equality family the
 strict comparison IS record's own. （已译） *)

Example colim_diagonal_strict_Id_obj (c : C) :
  `1 colim_diagonal_strict_Id c = cc_obj P c := eq_refl.

End ConstantChoice.

(* ------------------------------------------------------------------ *)
(* * * (D) The 假设 inhabited: shapes 终对象 （已译） *)

Section TerminalShape.

Context {J C : Category}.
Context (T : @Terminal J).

Definition terminal_colimits : HasColimitsOfShape J C :=
  fun F => @terminal_Colimit J C T F.

Example terminal_colimit_obj_strict (c : C) :
  colim_obj terminal_colimits Δ[J](c) = c := eq_refl.

Example terminal_colimit_inj_strict (c : C) (j : J) :
  colim_inj terminal_colimits Δ[J](c) j = id[c] := eq_refl.

Definition terminal_ConstantColimits : ConstantColimits J C := {|
  cc_colim := terminal_colimits;
  cc_obj := fun c => eq_refl;
  cc_inj := fun c j => reflexivity _
|}.

Definition terminal_lali_of_diagonal :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal (@terminal_obj J T)
    terminal_ConstantColimits.

(* And such shape satisfies exercise's own 假设. （已译） *)

Definition terminal_shape_connected : ConnectedNonempty J :=
  terminal_ConnectedNonempty T.

End TerminalShape.

(* * ** Evaluation at 对象 shape （已译） *)

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition EvalAt@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (j : J) : [J, C] ⟶ C := {|
  fobj := fun F => F j;
  fmap := fun _ _ t => transform[t] j
|}.

Example EvalAt_retracts@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (j : J) (c : C) :
  fobj[@EvalAt J C j] Δ[J](c) = c := eq_refl.

(*
   本节说明函子、（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example colimit_is_EvalAt@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} (T : @Terminal J) (F : [J, C]) :
  fobj[ColimitFunctor (@terminal_colimits J C T)] F
    = fobj[@EvalAt J C (@terminal_obj J T)] F := eq_refl.

(** ** Concrete witnesses *)

(* [Ordinal (S n)] has 终对象, so it carries choice for
 every ambient 范畴; at [n := 1] shape not degenerate. （已译） *)

Definition ordinal_ConstantColimits (n : nat) (C : Category) :
  ConstantColimits (Ordinal (S n)) C :=
  @terminal_ConstantColimits (Ordinal (S n)) C (Ordinal_Succ_Terminal n).

Definition ordinal_lali (n : nat) (C : Category) :
  LeftAdjointLeftInverse (@Diagonal C (Ordinal (S n))) :=
  @terminal_lali_of_diagonal (Ordinal (S n)) C (Ordinal_Succ_Terminal n).

Theorem ordinal_two_not_degenerate :
  ord_top 1 <> ord_bot 1.
Proof. exact (ord_top_neq_bot 0). Qed.

(* 相关说明。 （已译） *)

Definition two_ConstantColimits (C : Category) : ConstantColimits _2 C :=
  @terminal_ConstantColimits _2 C Two_Terminal.

Definition two_lali (C : Category) :
  LeftAdjointLeftInverse (@Diagonal C _2) :=
  @terminal_lali_of_diagonal _2 C Two_Terminal.

(* ------------------------------------------------------------------ *)
(* * * (E) Evaluation at NON-终对象 not 左伴随 （已译） *)

(* The diagram over walking arrow carrying empty type the
 booleans. Built Theory/Shapes.v's [Walk], so no 函子 laws
 discharged here. （已译） *)

Definition TwoGap : _2 ⟶ Coq :=
  @Walk Coq (Empty_set : Coq) (bool : Coq)
        (fun z => match z return bool with end).

Example TwoGap_X : fobj[TwoGap] TwoX = Empty_set := eq_refl.
Example TwoGap_Y : fobj[TwoGap] TwoY = bool := eq_refl.

(* [_2] connected inhabited, so refutes candidate at a
 shape meeting every 假设 exercise. （已译） *)

Theorem eval_not_left_adjoint :
  @EvalAt _2 Coq TwoX ⊣ @Diagonal Coq _2 → False.
Proof.
  intro A.
  pose proof (left_adjoint_iso (@Diagonal Coq _2) (@EvalAt _2 Coq TwoX)
                (ColimitFunctor (@terminal_colimits _2 Coq Two_Terminal))
                A
                (Colimit_Diagonal_Adjunction
                   (@terminal_colimits _2 Coq Two_Terminal))) as E.
  destruct E as [iso _].
  destruct (from (iso TwoGap) true).
Qed.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ConnectedUnit.

Context {J C : Category}.
Context (H : HasLimitsOfShape J C).
Context (K : ConnectedNonempty J).

Definition diagonal_limit_unit (c : C) : c ~{C}~> lim_obj H Δ[J](c) :=
  @unit ([J, C]) C (@Diagonal C J) (LimitFunctor H)
        (Diagonal_Limit_Adjunction H) c.

Lemma diagonal_unit_commutes (c : C) (j : J) :
  lim_leg H Δ[J](c) j ∘ diagonal_limit_unit c ≈ id.
Proof.
  unfold diagonal_limit_unit.
  rewrite (lim_transpose_to_commutes H (id{[J, C]}) j).
  simpl; reflexivity.
Qed.

Lemma lim_const_leg_agree (c : C) (x y : J) :
  lim_leg H Δ[J](c) x ≈ lim_leg H Δ[J](c) y.
Proof using K.
  apply (@leg_zigzag J C (lim_obj H Δ[J](c)) c
           (fun j => lim_leg H Δ[J](c) j)).
  - intros p q f; simpl.
    rewrite <- (lim_leg_coherence H Δ[J](c) f); simpl.
    now rewrite id_left.
  - exact (cn_zigzag K x y).
Qed.

Program Definition diagonal_unit_limit_iso (c : C) :
  IsIsomorphism (diagonal_limit_unit c) := {|
  two_sided_inverse := lim_leg H Δ[J](c) (cn_obj K)
|}.
Next Obligation.
  apply (lim_med_eq H
           {| vertex_obj := lim_obj H Δ[J](c)
            ; coneFrom :=
                {| vertex_map := fun j => lim_leg H Δ[J](c) j
                 ; cone_coherence := fun x y f =>
                     lim_leg_coherence H Δ[J](c) f |} |});
    intro j; simpl.
  - rewrite comp_assoc, (diagonal_unit_commutes c j), id_left.
    apply lim_const_leg_agree.
  - apply id_right.
Qed.
Next Obligation.
  apply (diagonal_unit_commutes c (cn_obj K)).
Qed.

End ConnectedUnit.

(*
   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ConstantLimits (J C : Category) : Type := {
  cl_limit : HasLimitsOfShape J C;
  cl_obj (c : C) : lim_obj cl_limit Δ[J](c) = c;
  cl_leg (c : C) (j : J) :
    lim_leg cl_limit Δ[J](c) j ≈ id_cast (cl_obj c)
}.

Arguments cl_limit {J C} _.
Arguments cl_obj {J C} _ _.
Arguments cl_leg {J C} _ _ _.

Section ConstantLimitChoice.

Context {J C : Category}.
Context (j0 : J).
Context (Q : ConstantLimits J C).

Lemma constant_limits_unit (c : C) :
  diagonal_limit_unit (cl_limit Q) c ≈ id_cast (eq_sym (cl_obj Q c)).
Proof using Q j0.
  rewrite <- (id_right (id_cast (eq_sym (cl_obj Q c)))).
  rewrite <- (diagonal_unit_commutes (cl_limit Q) c j0).
  rewrite comp_assoc, (cl_leg Q c j0).
  now rewrite id_cast_inv_l, id_left.
Qed.

Definition diagonal_is_lari_of_limit :
  LeftAdjointRightInverse (LimitFunctor (cl_limit Q)) := {|
  lari_left := @Diagonal C J;
  lari_adj := Diagonal_Limit_Adjunction (cl_limit Q);
  lari_obj := cl_obj Q;
  lari_unit := constant_limits_unit
|}.

Example lari_left_strict :
  lari_left diagonal_is_lari_of_limit = @Diagonal C J := eq_refl.

Example lari_obj_strict (c : C) :
  lari_obj diagonal_is_lari_of_limit c = cl_obj Q c := eq_refl.

End ConstantLimitChoice.

(* Inhabited whenever SHAPE has 始对象 -- 镜像 of
 section (D), such shape connected. （已译） *)

Section InitialShape.

Context {J C : Category}.
Context (I : @Initial J).

Definition initial_limits : HasLimitsOfShape J C :=
  fun F => @initial_Limit J C I F.

Example initial_limit_obj_strict (c : C) :
  lim_obj initial_limits Δ[J](c) = c := eq_refl.

Example initial_limit_leg_strict (c : C) (j : J) :
  lim_leg initial_limits Δ[J](c) j = id[c] := eq_refl.

Definition initial_ConstantLimits : ConstantLimits J C := {|
  cl_limit := initial_limits;
  cl_obj := fun c => eq_refl;
  cl_leg := fun c j => reflexivity _
|}.

Definition initial_lari_of_limit :
  LeftAdjointRightInverse (LimitFunctor initial_limits) :=
  diagonal_is_lari_of_limit (@initial_obj J I) initial_ConstantLimits.

End InitialShape.

(* 相关说明。 （已译） *)

Definition one_ConstantLimits (C : Category) : ConstantLimits _1 C :=
  @initial_ConstantLimits _1 C One_Initial.

Definition omega_ConstantLimits (C : Category) :
  ConstantLimits Omega C :=
  @initial_ConstantLimits Omega C Omega_Initial.

Definition omega_lari (C : Category) :
  LeftAdjointRightInverse
    (LimitFunctor (@initial_limits Omega C Omega_Initial)) :=
  @initial_lari_of_limit Omega C Omega_Initial.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* Every statement below ARBITRARY choice colimits over the
 two-对象 discrete shape, so none them turns colimits
 were chosen. （已译） *)

Theorem two_discrete_counit_not_iso
  (L : HasColimitsOfShape Two_Discrete Coq) :
  (∀ c : Coq, IsIsomorphism (diagonal_counit L c)) → False.
Proof.
  intro Hiso.
  apply Diagonal_Two_Discrete_not_Full.
  exact (fst (snd (@right_adjoint_fully_faithful_iff_counit_iso
                     Coq ([Two_Discrete, Coq]) (ColimitFunctor L)
                     (@Diagonal Coq Two_Discrete)
                     (Colimit_Diagonal_Adjunction L)) Hiso)).
Qed.

Theorem two_discrete_no_ffi :
  LeftAdjointFFInjective (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro B.
  exact (Diagonal_Two_Discrete_not_Full (ffi_full B)).
Qed.

Theorem two_discrete_no_lali :
  LeftAdjointLeftInverse (@Diagonal Coq Two_Discrete) → False.
Proof.
  intro P.
  exact (two_discrete_no_ffi (lali_implies_ffi P)).
Qed.

Theorem two_discrete_no_constant_colimits :
  ConstantColimits Two_Discrete Coq → False.
Proof.
  intro P.
  exact (two_discrete_no_lali
           (colimit_is_lali_of_diagonal (TwoDX : Two_Discrete) P)).
Qed.

(* And shape inhabited, so what goes connectedness not
 point: [TwoDX] above genuine 对象 it. （已译） *)

Theorem two_discrete_objects_distinct : (TwoDX : Two_Discrete) = TwoDY
  → False.
Proof. discriminate. Qed.
