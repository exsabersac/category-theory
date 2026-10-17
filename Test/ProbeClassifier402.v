Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeClassifier402。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Instrument check *)

(* 相关说明。 （已译） *)
Fail Check probe402_no_such_constant.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Check @classifier_classifies.
Check @char_reindex.
Check @Sub_classifier_natural.
Check @Sub_Representable.
Check @SubObj.
Check @SubobjectClassifier.
Check @Sets_Terminal.
Check @Sets_HasPullbacks.
Check @HasPullbacks.
Check @PropSetoid.
Check @Powerset_Omega.
Check @Powerset_squash.
Check @powerset_squash_prop_inert.
Check @BoolSetoid.
Check @SetoidObject.
Check @Sets.
Check @char_setoid.
Check @SetoidMorphism_Lift.
Check @Sets_Classifier.
Check @Sets_Classifier_dec.
Check @Sets_Classifier_IEM.
Check @sets_squash_mor.
Check @bridge_record_equiv.
Check @bridge_pointwise.
Check @classifier_of_small.
Check @small_of_IEM.
Check @DecImage_of_IEM.
Check @iem_routes_omega.
Check @iem_routes_char.
Check @iem_routes_truth.
Check @Untruncate.
Check @IEM.
Check @DecImage.
Check @char.
Check @Ω.
Check @truth.
Check @Monic.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section NotAtSets.
Universes o so.
Constraint o < so.
Context (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}).

(* CONTROL: [char_reindex] IS accepted at very [Sets], very
 classifier. So two refusals below about own statements,
 not about classifier 范畴. （已译） *)
Check (fun (x y : SetoidObject@{o o}) (f : y ~{Sets@{o so}}~> x)
           (s : @SubObj Sets@{o so} x) =>
  @char_reindex Sets@{o so} Sets_Terminal@{so o} Sets_HasPullbacks@{so o}
    HS x y f s).

(* NEGATIVE 1 (FORMABILITY).  The classification theorem builds a
   [SetoidObject] whose carrier is [SubObj x], which forces objects ≤
   homs; [Sets@{o so} : Category@{so o o}] has o < so.  Stripped:
     universe inconsistency: Cannot enforce so = _ because _ <= _ < so *)
Fail Check (@classifier_classifies Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

(* NEGATIVE 2 (FORMABILITY).  Awodey's naturality clause, same wall, same
   error shape. *)
Fail Check (@Sub_classifier_natural Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

(* NEGATIVE 3 (FORMABILITY). [Sub_Representable] built that
 同构, so it inherits refusal. （已译） *)
Fail Check (@Sub_Representable Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o} HS).

End NotAtSets.

Section CarrierWall.
Universes o so.
Constraint o < so.

(* CONTROL: a hom-setoid IS an object of [Sets] at these very levels. *)
Check (fun (a b : SetoidObject@{o o}) =>
  ({| carrier := a ~{Sets@{o so}}~> b |} : obj[Sets@{o so}])).

(* NEGATIVE 4 (FORMABILITY).  [SubObj x] is a [Type@{so}], so no setoid on
   it is an object of [Sets@{o so}].  Stripped:
     universe inconsistency: Cannot enforce _ = o because o < so <= _ *)
Fail Check (fun (x : SetoidObject@{o o}) =>
  ({| carrier := @SubObj Sets@{o so} x |} : obj[Sets@{o so}])).

(* CONTROLS: two truth 对象 file actually uses ARE 对象 of
 [Sets] at one level. （已译） *)
Check (Powerset_Omega@{o} : obj[Sets@{o so}]).
Check (BoolSetoid@{o} : obj[Sets@{o so}]).

(* NEGATIVE 5 (FORMABILITY).  Instance/Sets/Classifier.v's truth-value
   setoid is not.  Stripped:
     universe inconsistency: Cannot enforce so = o because o < so *)
Fail Check (PropSetoid@{o so} : obj[Sets@{o so}]).

End CarrierWall.

Section SquashWall.
Universes o.

(* CONTROL: over [Prop] impredicative truncation inert, so it CAN
 eliminated -- what makes [Untruncate] extra 假设
 not restatement goal. （已译） *)
Check (fun (P : Prop) => proj1 (powerset_squash_prop_inert@{o} P)).

(* NEGATIVE 6 (FORMABILITY).  The naive elimination at a [Type@{o}]
   instantiates the impredicative quantifier outside [Prop].  Stripped:
     universe inconsistency: Cannot enforce o <= Prop
   This refusal is exactly what [Untruncate] buys. *)
Fail Check (fun (P : Type@{o}) (h : Powerset_squash@{o} P) =>
              h P (fun p => p)).

End SquashWall.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ClassArity.
Universes o so.
Constraint o < so.

(* CONTROL: two-论元 form, what target inhabits. （已译） *)
Check (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}).

(*
   本节说明 ProbeClassifier402 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
              Sets_HasPullbacks@{so o}).

End ClassArity.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Grades.
Universes o so sso.
Constraint o < so.
Constraint so < sso.

(* 相关说明。 （已译） *)
Check (fun (U : Untruncate@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
           (b : carrier x) => @bridge_pointwise@{o so} U u x m M b).
Check (fun (U : Untruncate@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m) =>
         @bridge_record_equiv@{o so sso} U u x m M).

(*
   本节说明 ProbeClassifier402 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example bridge_record@{o' so' sso'} (U : Untruncate@{o'})
  {u x : SetoidObject@{o' o'}} (m : u ~{Sets@{o' so'}}~> x)
  (M : @Monic Sets@{o' so'} u x m) :
  SetoidMorphism_Lift@{o' so'}
    (@char Sets@{o' so'} Sets_Terminal@{so' o'}
       (Sets_Classifier@{o' so'} U) u x m M)
    = sets_squash_mor@{o' so' sso'}
        ∘[Sets@{so' sso'}] char_setoid@{o' so'} m := eq_refl.

(* 相关说明。 （已译） *)
Check (fun (E : IEM@{o}) => @iem_routes_omega@{o so} E).
Check (fun (E : IEM@{o}) (u x : SetoidObject@{o o})
           (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
           (b : carrier x) => @iem_routes_char@{o so} E u x m M b).
Check (fun (E : IEM@{o}) => @iem_routes_truth@{o so} E).

(*
   本节说明 ProbeClassifier402 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example iem_routes@{o' so'} (E : IEM@{o'}) :
  classifier_of_small@{o' so'} (small_of_IEM@{o'} E)
    = Sets_Classifier_dec@{o' so'} (DecImage_of_IEM@{o' so'} E) := eq_refl.

End Grades.
