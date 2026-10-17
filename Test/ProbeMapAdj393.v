Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Map.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(*
   本文件为测试：ProbeMapAdj393。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check: a name that is in no file of the tree *)

Fail Check map_of_adjunctions_no_such_constant_anywhere.

(** ** Section A: controls *)

Section Controls.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context (S : @AdjSquares C D F U C' D' F' U').
Context (M : MapOfAdjunctions A A').
Context (x : D) (a : C) (k : F x ~> a).

Check @AdjSquares.
Check @MapOfAdjunctions.
Check @SquaresHom.
Check @SquaresUnit.
Check @SquaresCounit.
Check @sq_K.
Check @sq_L.
Check @sq_left.
Check @sq_left_nat.
Check @sq_right.
Check @sq_right_nat.
Check @sq_unit_eq.
Check @sq_counit_eq.
Check @map_hom.
Check @map_squares.
Check @map_K.
Check @map_L.
Check @squares_unit_fused.
Check @squares_counit_fused.
Check @squares_hom_is_generic.
Check @strict_hom_is_weak_hom.
Check @map_adj_hom_is_conjugate.
Check @MapOfAdjunctions_id.
Check @MapOfAdjunctions_compose.
Check @MapAdjHom.
Check @WeakSquaresHom.
Check @WeakAdjSquares.
Check @adj.
Check @to.
Check @from.
Check @unit.
Check @counit.
Check @fmap.
Check @transform.
Check @Id.
Check @Isomorphism.
Check @Functor.
Check @Adjunction.
Check @id_cast.
Check @Conjugate.
Check @Functor_StrictEq_Setoid.
Check @strict_equiv_of_id_cast_nat.

(* The hom-set condition WITH the cast, which negative 1 removes. *)
Definition p393_control_cast :=
  to (@adj _ _ _ _ A' _ _) (fmap[sq_K S] k ∘ id_cast (eq_sym (sq_left S x))).

(* The fused Mac Lane spelling, which negative 2 asks for at [eq_refl]. *)
Definition p393_control_fused := squares_unit_fused A A' S.

(* The composite of the identity map with M, which negative 3 asks to be M. *)
Definition p393_control_compose :=
  MapOfAdjunctions_compose A A A' (MapOfAdjunctions_id A) M.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition p393_strict_left
  : @equiv _ (@Functor_StrictEq_Setoid D C') (sq_K S ◯ F) (F' ◯ sq_L S)
  := strict_equiv_of_id_cast_nat (sq_K S ◯ F) (F' ◯ sq_L S)
       (sq_left S) (sq_left_nat S).

Definition p393_strict_right
  : @equiv _ (@Functor_StrictEq_Setoid C D') (sq_L S ◯ U) (U' ◯ sq_K S)
  := strict_equiv_of_id_cast_nat (sq_L S ◯ U) (U' ◯ sq_K S)
       (sq_right S) (sq_right_nat S).

(*
   本节说明 ProbeMapAdj393 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (to (@adj _ _ _ _ A' _ _) (fmap[sq_K S] k)).

(*
   本节说明 ProbeMapAdj393 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p393_unit_fused_strict :
  SquaresUnit A A' S
    = (∀ y : D, id_cast (sq_unit_eq S y) ∘ fmap[sq_L S] (@unit _ _ _ _ A y)
                  ≈ @unit _ _ _ _ A' (sq_L S y)) := eq_refl.

(*
   本节说明 ProbeMapAdj393 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition p393_unit_law :
  MapOfAdjunctions_compose A A A' (MapOfAdjunctions_id A) M = M := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Conjugate A A').

End Controls.

(*
   本节说明 ProbeMapAdj393 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Residue.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F2 : D ⟶ C} {U2 : C ⟶ D} (A2 : F2 ⊣ U2).
Context (sigma : F2 ⟹ F) (tau : U ⟹ U2).

Check (Conjugate A A2 sigma tau).
Check (fun x : D => transform[sigma] x).
Check (fun a : C => transform[tau] a).

Fail Check (MapAdjHom A A2 Id[C] Id[D]
              (fun x : D => transform[sigma] x)
              (fun a : C => transform[tau] a)).

End Residue.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Formability.

Universes ao ah ap bo.
Constraint ah < ap.

Context (Cu : Category@{ao ah ap}) (Du : Category@{bo ah ap}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du).

(* Controls at the declared levels. *)
Check Cu.
Check Du.
Check Fu.
Check Uu.
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check (fun x y : Cu => @Isomorphism Cu x y).
Check (fun (x y : Cu) (f g : x ~> y) => f ≈ g).

(* Negative 6: the record itself. *)
Fail Check (@AdjSquares Cu Du Fu Uu Cu Du Fu Uu).

(* Negative 7: [id_cast] alone, with no adjunction in the command. *)
Fail Check (fun (x y : Cu) (e : x = y) => @id_cast Cu x y e).

(* Negative 8: [Adjunction] alone, with no [id_cast] in the command; the
   control [Check Fu] above shows [Functor] is not what is refused. *)
Fail Check (Fu ⊣ Uu).

End Formability.
