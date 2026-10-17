Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Closed.
Require Import Category.Instance.Two.

Open Scope category_scope.

Generalizable All Variables.

(** * Probe for issue #718 -- exponentials of presheaves *)

(*
   本文件为测试：ProbePresheafExp718。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

(* A deliberately absent name.  If this were to succeed, the refutation
   commands below would be measuring nothing. *)
Fail Check probe718_this_name_does_not_exist.

(* ------------------------------------------------------------------ *)
(** ** Guard controls -- every constant a negative names, named outside *)

Check @PshExp.
Check @PshExp_obj.
Check @PshExp_fmap.
Check @to_exp.
Check @to_exp_inner.
Check @from_exp.
Check @from_to_exp.
Check @to_from_exp.
Check @presheaf_exp_iso.
Check @to_exp_natural_X.
Check @from_exp_natural_X.
Check @Functor_Category_Closed.
Check @Functor_Category_Closed_cov.
Check @presheaf_terminal.
Check @presheaf_terminal_is_donor.
Check @exp_obj_is_display85.
Check @exponent_obj_is_PshExp.
Check @curry_is_to_exp.
Check @uncurry_is_from_exp.
Check @eval_is_at_identity.
Check @one_exp_iso.
Check @one_exp_to.
Check @one_exp_from.
Check @Psh2_Cart.
Check @Psh2_Closed.
Check @pq_point_distinct_unconditional.
Check @awodey_pointwise_not_exponential_unconditional.
Check @objectwise_candidate.
Check @PresheafP.
Check @PresheafQ.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Sets_Terminal.
Check @Curried_CoHom.
Check @Yoneda_Lemma.
Check @yoneda_natural_pre.
Check @YoNatPre.
Check @Closed.
Check @exponent_obj.
Check @exp_iso.
Check @curry'.
Check @uncurry'.
Check @eval'.
Check @first.
Check @split.
Check @product_obj.
Check @Fun.
Check @Opposite.
Check @Functor.
Check @Sets.
Check @Terminal.
Check @_2.
Check @_1.

(* ------------------------------------------------------------------ *)
(** ** Positive controls the file's claims rest on *)

(* The instance is found by typeclass resolution, at an arbitrary C. *)
Definition probe718_resolves (C : Category) : @Closed ([C^op, Sets]) _ := _.

(* And so is the terminal object of the same category. *)
Definition probe718_resolves_terminal (C : Category) :
  @Terminal ([C^op, Sets]) := _.

(* Awodey display (8.5), restated from OUTSIDE the target so that a
   rename in the target breaks this file. *)
Example probe718_display85 {C : Category} (P Q : C^op ⟶ Sets) (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]](
        @product_obj _ (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
          (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's data, read back from outside. *)
Example probe718_exponent {C : Category} (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

Example probe718_terminal (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(* Riehl's covariant reading is the same constant at the opposite
   category, on the nose. *)
Example probe718_cov (C : Category) :
  Functor_Category_Closed_cov C = Functor_Category_Closed (C^op) := eq_refl.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section FirstReduces.
Context {C : Category}.
Context (P : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).
Context (c c' : C) (h : c ~{C^op}~> c') (d : C^op).
Context (hp : fobj[@product_obj _ PshCart (Curried_CoHom C c') P] d).

Example probe718_first_snd :
  snd (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp) = snd hp
  := eq_refl.

Example probe718_first_fst :
  fst (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp)
    = op h ∘ fst hp
  := eq_refl.
End FirstReduces.

(* The two identifications that hold at [≈] and not at [eq_refl], stated
   from outside as the controls for negatives 5 and 6. *)
Example probe718_eval_weak {C : Category} (P Q : C^op ⟶ Sets) (c : C)
  (gy : fobj[@product_obj _
               (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
               (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy)
  := eval_is_at_identity P Q c gy.

(* The unconditional corollary of Instance/Fun/Closed.v, exercised from
   outside: the hypothesis that file's section F is stated over is now
   discharged by this issue's instance. *)
Check (awodey_pointwise_not_exponential_unconditional
         : @Isomorphism Sets
             ((@exponent_obj _ Psh2_Cart Psh2_Closed PresheafP PresheafQ) TwoY)
             objectwise_candidate -> False).
Check pq_point_distinct_unconditional.

(* ------------------------------------------------------------------ *)
(** ** The clone of the instance written WITHOUT universe binders *)

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition probe718_closed_unannotated (C : Category) :
  @Closed ([C^op, Sets])
    (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(* ------------------------------------------------------------------ *)
(** ** (1) The smallness bound: C's objects at or below Sets' carriers *)

Section SmallC.
Universes coB chB oB soB.
Constraint oB < soB.
Constraint coB <= oB.
Context (Csm : Category@{coB chB chB}).
Context (Ps Qs : Csm^op ⟶ Sets@{oB soB}).

(* CONTROL: with C's objects bounded by [Sets]' carrier universe, the
   display-(8.5) object IS an object of that same [Sets], and so are the
   functor, the isomorphism and the instance. *)
Check ([[[Csm^op, Sets@{oB soB}]]](Ps, Qs) : obj[Sets@{oB soB}]).
Check (PshExp Ps Qs).
Check (Functor_Category_Closed Csm).
End SmallC.

Section BigC.
Universes coA chA oA soA.
Constraint oA < soA.
Constraint oA < coA.
Context (Cbig : Category@{coA chA chA}).
Context (Xb Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check ([Cbig^op, Sets@{oA soA}]).
Check (presheaf_terminal Cbig : @Terminal ([Cbig^op, Sets@{oA soA}])).
Check (PshExp Pb Qb).

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check ([[[Cbig^op, Sets@{oA soA}]]](Pb, Qb) : obj[Sets@{oA soA}]).

(*
   本节说明 ProbePresheafExp718 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (PshExp Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (presheaf_exp_iso Xb Pb Qb).

(* NEGATIVE 1d (FORMABILITY).  And so, therefore, is the headline.  This
   is Awodey's "for any small category C", as a measurement. *)
Fail Check (Functor_Category_Closed Cbig).
End BigC.

(* ------------------------------------------------------------------ *)
(** ** (2)-(3) Hom = proof in the binder is the donors' doing *)

Section HomBelowProof.
Universes coC chC cpC oC soC.
Constraint chC < cpC.
Constraint oC < soC.
Context (Cu : Category@{coC chC cpC}).

(* CONTROLS accepted at levels where hom and proof are DECLARED APART:
   the hom type, an identity, and the bare functor type into [Sets].  So
   [Functor] is NOT a donor of [ch = cp]. *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (@Functor Cu Sets@{oC soC}).

(* NEGATIVE 2 (FORMABILITY).  [Opposite] forces [ch = cp] on its own; the
   stripped error ends "Cannot enforce cpC = chC because chC < cpC". *)
Fail Check (Cu^op).

(* NEGATIVE 3 (FORMABILITY).  So does [Fun], with NO [^op] anywhere in
   the command -- two INDEPENDENT donors, same error shape. *)
Fail Check ([Cu, Sets@{oC soC}]).
End HomBelowProof.

(* ------------------------------------------------------------------ *)
(** ** (4) The route, and the load-bearing annotation *)

Section Route.
Universes coD oD soD.
Constraint oD < soD.
Constraint coD < oD.
Context (Cr : Category@{coD oD oD}).
Context (Pr Qr Xr : Cr^op ⟶ Sets@{oD soD}).

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check ([Cr^op, Sets@{oD soD}]).
Check (@YoNatPre Cr).
Check ([[[Cr^op, Sets@{oD soD}]]](Pr, Qr) : obj[Sets@{oD soD}]).
Check (PshExp Pr Qr).
Check (presheaf_exp_iso Xr Pr Qr).
Check (Functor_Category_Closed Cr).
Check (Functor_Category_Closed_cov Cr).

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@Yoneda_Lemma Cr Pr).
Fail Check (yoneda_natural_pre Cr).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (probe718_closed_unannotated Cr).
End Route.

(* ------------------------------------------------------------------ *)
(** ** (5)-(6) The two conversion boundaries *)

Section Conv.
Context {C : Category}.
Context (P Q : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* CONTROLS: the two spellings of Awodey's [y h × 1_P] both elaborate,
   and at the SAME type -- so the refusal below is about conversion and
   not about formability. *)
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
           (@id ([C^op,Sets]) P)).

(*
   本节说明 ProbePresheafExp718 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe718_first_is_split (c c' : C) (h : c ~{C^op}~> c') :
  @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)
    = @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
        (@id ([C^op,Sets]) P)
  := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe718_eval_strict (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    = (fst gy) c (id[c], snd gy)
  := eq_refl.
End Conv.

(* ------------------------------------------------------------------ *)
(** ** (7)-(9) Three typing boundaries *)

Section Typing.
Context {C : Category}.
Context (P Q X : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* CONTROL: the exponential IS a presheaf. *)
Check (PshExp P Q : C^op ⟶ Sets).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe718_psh_covariant : C ⟶ Sets := PshExp P Q.

(* CONTROL: [exponent_obj y z] is z^y, so [PshExp P Q] is Q^P and the
   transposition names P as the factor and Q as the target. *)
Check (presheaf_exp_iso X P Q
         : @Isomorphism Sets
             ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
             ([[[C^op, Sets]]]( X, PshExp P Q ))).

(* NEGATIVE 8 (TYPING).  The two arguments of [PshExp] are not
   interchangeable: ascribing the same isomorphism with [PshExp Q P] on
   the right is a plain has-type mismatch. *)
Fail Definition probe718_swapped :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp Q P ))
  := presheaf_exp_iso X P Q.

(*
   本节说明 ProbePresheafExp718 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe718_objectwise : C^op ⟶ Sets :=
  fun c => @exponent_obj Sets Sets_Cartesian Sets_Closed
             (fobj[P] c) (fobj[Q] c).
End Typing.
