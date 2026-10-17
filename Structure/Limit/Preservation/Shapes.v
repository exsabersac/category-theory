Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Roof.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
   本文件给出形状/往返相关引理（对象上的 [=] 往返等）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition PreservesProductCones {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (A : Type) (K : DiscreteCat A ⟶ C), PreservesLimitCone K F.

Definition Continuous_PreservesProductCones {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesProductCones F :=
  fun A K => H (DiscreteCat A) K.

(** ** Finite shapes *)

(*
   本节说明（余）极限、拉回/推出、topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record FiniteShape (J : Category) : Type := {
  fs_objs : list (obj[J]);
  fs_objs_all : ∀ x : obj[J], List.In x fs_objs;
  fs_homs : ∀ x y : obj[J], list (x ~{J}~> y);
  fs_homs_all : ∀ (x y : obj[J]) (f : x ~{J}~> y),
    { g : x ~{J}~> y & prod (List.In g (fs_homs x y)) (g ≈ f) }
}.

Arguments fs_objs {J} _.
Arguments fs_objs_all {J} _ _.
Arguments fs_homs {J} _ _ _.
Arguments fs_homs_all {J} _ _ _ _.

Definition PreservesFiniteLimitCones {C D : Category} (F : C ⟶ D) : Type :=
  PreservesLimitConesOver FiniteShape F.

Definition Continuous_PreservesFiniteLimitCones {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesFiniteLimitCones F :=
  Continuous_PreservesLimitConesOver H.

Definition PreservesFiniteLimitCones_OfShape {C D : Category} {F : C ⟶ D}
  (H : PreservesFiniteLimitCones F) {J : Category} (HJ : FiniteShape J) :
  PreservesLimitConesOfShape J F := H J HJ.

(** ** The predicate is inhabited *)

(* The global obligation tactic preprocesses these goals unpredictably;
   take manual control (precedent: Functor/Structure/Monoidal/Id.v). *)
#[local] Obligation Tactic := idtac.

Program Definition FiniteShape_0 : FiniteShape _0 := {|
  fs_objs := nil; fs_homs := fun _ _ => nil |}.
Next Obligation. intros x; destruct x. Qed.
Next Obligation. intros x; destruct x. Qed.

Program Definition FiniteShape_Two_Discrete : FiniteShape Two_Discrete := {|
  fs_objs := TwoDX :: TwoDY :: nil;
  fs_homs := fun x y =>
    match x, y return list (x ~{Two_Discrete}~> y) with
    | TwoDX, TwoDX => TwoDIdX :: nil
    | TwoDY, TwoDY => TwoDIdY :: nil
    | _, _ => nil
    end |}.
Next Obligation. intros x; destruct x; simpl; auto. Qed.
Next Obligation.
  intros x y f; destruct x, y.
  - exists TwoDIdX; split;
      [ simpl; auto | symmetry; exact (TwoDHom_inv _ _ f) ].
  - exact (False_rect _ (TwoDHom_X_Y_absurd f)).
  - exact (False_rect _ (TwoDHom_Y_X_absurd f)).
  - exists TwoDIdY; split;
      [ simpl; auto | symmetry; exact (TwoDHom_inv _ _ f) ].
Qed.

Program Definition FiniteShape_Roof : FiniteShape Roof := {|
  fs_objs := RNeg :: RZero :: RPos :: nil;
  fs_homs := fun x y =>
    match x, y return list (x ~{Roof}~> y) with
    | RNeg,  RNeg  => IdNeg   :: nil
    | RZero, RNeg  => ZeroNeg :: nil
    | RZero, RZero => IdZero  :: nil
    | RZero, RPos  => ZeroPos :: nil
    | RPos,  RPos  => IdPos   :: nil
    | _, _ => nil
    end |}.
Next Obligation. intros x; destruct x; simpl; auto. Qed.
Next Obligation.
  intros x y f; destruct x, y.
  - exists IdNeg; split; [ simpl; auto | constructor ].
  - exact (False_rect _ (RNeg_RZero_absurd f)).
  - exact (False_rect _ (RNeg_RPos_absurd f)).
  - exists ZeroNeg; split; [ simpl; auto | constructor ].
  - exists IdZero; split; [ simpl; auto | constructor ].
  - exists ZeroPos; split; [ simpl; auto | constructor ].
  - exact (False_rect _ (RPos_RNeg_absurd f)).
  - exact (False_rect _ (RPos_RZero_absurd f)).
  - exists IdPos; split; [ simpl; auto | constructor ].
Qed.
