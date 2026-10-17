Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Limit.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.One.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeArrowLimit412。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check probe412_no_such_constant.

(** ** Guards *)

Check @comma_lift_cone.
Check @comma_lift_arrow.
Check @comma_proj_CreatesLimit.
Check @comma_proj.
Check @comma_proj1.
Check @comma_proj2.
Check @Comma.
Check @FCone.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @Snd.
Check @Fst.
Check @Compose.
Check @PreservesLimitCone.
Check @IsLimitCone.
Check @Id_PreservesLimitCone.
Check @Arrow_Complete.

(* 相关说明。 （已译） *)

Section Records.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)) (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(* 相关说明。 （已译） *)
Example probe412_ctrl_apex (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  vertex_obj[FCone comma_proj (comma_lift_cone K HT N HN)] = vertex_obj[N]
  := eq_refl.

Example probe412_ctrl_leg (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  cone_leg (FCone comma_proj (comma_lift_cone K HT N HN)) j = cone_leg N j
  := eq_refl.

(* N1: CONVERSION — the whole record is not. *)
Fail Example probe412_n1 (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  FCone comma_proj (comma_lift_cone K HT N HN) = N := eq_refl.

(* Controls: the two codomain-diagram functors agree on both actions. *)
Example probe412_ctrl_fobj :
  fobj[Snd ◯ (comma_proj ◯ K)] = fobj[comma_proj2 ◯ K] := eq_refl.

Example probe412_ctrl_fmap :
  @fmap _ _ (Snd ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj2 ◯ K) := eq_refl.

(* N2: CONVERSION — not as records. *)
Fail Example probe412_n2 : Snd ◯ (comma_proj ◯ K) = comma_proj2 ◯ K := eq_refl.

(* Controls DOMAIN side, target's NOT DELIVERED paragraph
 cites: two domain-diagram 函子 agree both actions. （已译） *)
Example probe412_ctrl_fobj1 :
  fobj[Fst ◯ (comma_proj ◯ K)] = fobj[comma_proj1 ◯ K] := eq_refl.

Example probe412_ctrl_fmap1 :
  @fmap _ _ (Fst ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj1 ◯ K) := eq_refl.

End Records.

(* * ** N3: 假设 codomain side （已译） *)

Section Handedness.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).
Context (HS : PreservesLimitCone (comma_proj1 ◯ K) S).

(* Control. *)
Check (comma_proj_CreatesLimit K HT).

(* N3: TYPING. *)
Fail Check (comma_proj_CreatesLimit K HS).

End Handedness.

(* 相关说明。 （已译） *)

Section UniverseBoundary.

Universes jo jh ao ah co ch.
Constraint jh < ah.

Context (Ju : Category@{jo jh jh}).
Context (Au : Category@{ao ah ah}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Au ⟶ Cu).
Context (K : Ju ⟶ (Su ↓ Tu)).

(* Controls. *)
Check (Su ↓ Tu).
Check K.
Check (@Cone Ju (Su ↓ Tu) K).

(* N4: UNIVERSE — the donor. *)
Fail Check (comma_proj ◯ K).

(* Inherited: fires at the shape argument [Ju], [Cannot enforce jh = ah]. *)
Fail Check (@comma_proj_CreatesLimit Au Au Cu Su Tu Ju K).

End UniverseBoundary.

(* The comma 范畴 itself keeps two factors' hom levels apart. （已译） *)

Section CommaApart.

Universes ao ah bo bh co ch.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}) (Bu : Category@{bo bh bh}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Bu ⟶ Cu).

Check (Su ↓ Tu).

End CommaApart.

(* No [Set] pin on the arrow-category statements. *)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).

Check (@Arrow Cu).
Check (@Arrow_Complete Cu).

End AboveSet.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition NegK : _1 ⟶ @Arrow Coq := {|
  fobj := fun _ => ((bool, bool); negb);
  fmap := fun _ _ _ => ((id, id); _)
|}.

Definition NegN : Cone (comma_proj ◯ NegK) :=
  @initial_cone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition NegHN : IsLimitCone NegN :=
  @initial_IsLimitCone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition neg_created :=
  comma_lift_arrow NegK (Id_PreservesLimitCone _) NegN NegHN.

Example neg_created_is_negb : neg_created = negb := eq_refl.
Example neg_created_true : neg_created true = false := eq_refl.
Example neg_created_false : neg_created false = true := eq_refl.

Example neg_lift_apex :
  (`1 vertex_obj[comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN])
    = (bool, bool) := eq_refl.

Example neg_lift_leg :
  (`1 (cone_leg (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN)
         ttt))
    = (id, id) := eq_refl.

(* The created cone limiting, through general 定理. （已译） *)
Definition neg_lift_limiting :
  IsLimitCone (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN) :=
  creates_limiting (arrow_proj_creates_limits NegK) NegN NegHN.
