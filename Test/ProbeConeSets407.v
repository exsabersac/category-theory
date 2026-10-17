Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeConeSets407。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Guard block: every 常值 refutations name, named outside them （已译） *)

Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_limit_compatible.
Check @cone_apex.
Check @cone_leg_at.
Check @cone_set_IsALimit.
Check @cone_set_Limit.
Check @cone_set_med.
Check @ConeSet_Complete.
Check @discrete_limit.
Check @discrete_iprod_iso.
Check @Sets_iprod_proj.
Check @iprod_proj.
Check @DiscreteCat.
Check @DiscreteCat_Functor.
Check @IsALimit.
Check @Cone.
Check @ACone.
Check @cone_apex_iso.
Check @cone_transpose.
Check @cone_untranspose.
Check @ConeSet_Natural_Iso.
Check @ConeSet_Representable.
Check @ConeSet_HasLimitsOfShape.
Check @ConeSet_Diagonal_Limit_Adjunction.
Check @Sets_Diagonal_Limit_Adjunction.
Check @Sets_HasLimitsOfShape.
Check @Cone_Natural_Transform.
Check @adj.
Check @Isomorphism.
Check @sets_eq_obj.
Check @sets_eq_incl.
Check @sets_IsEqualizer.
Check @concrete_vs_existing.
Check @existing_IsEqualizer.
Check @Sets_HasEqualizers.
Check @APair.
Check @karoubi_IsEqualizer.
Check @sets_split_obj.
Check @tuple_obj.
Check @tuple_compat.
Check @tuple_iso.
Check @tuple_proj.
Check @FunctorOfDiagram.
Check @Diagram.
Check @Quiver.
Check @Srestr.
Check @pres_iso.
Check @PresentedQuiver.
Check @PathRel.
Check @global_elements_natural.
Check @SetoidObject.
Check @fst.
Check @snd.
Check @from.
Check @to.

(** ** Instrument check *)

(* 相关说明。 （已译） *)
Fail Check @coneset_probe_instrument_absent.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Fail Example neg_apex_strict {D : Category} (F : D ⟶ Sets) :
  Sets_limit_obj F = cone_apex F := eq_refl.

(* * ** (2) There no [≈] grade 对象 -- RESOLUTION （已译） *)

(* Objects [Sets] carry no setoid. Whole error:
 The following term contains unresolved implicit arguments ...
 ?Setoid: Cannot infer implicit parameter Setoid equiv whose
 type is "Setoid SetoidObject" (no type class 实例 found).
 A [Check] here is ACCEPTED (open evar), so this is [Definition].（已译） *)
Fail Definition neg_apex_equiv {D : Category} (F : D ⟶ Sets) : Type :=
  (Sets_limit_obj F ≈ cone_apex F).

(* 相关说明。 （已译） *)

(* [∘] in [Sets] rebuilds a [SetoidMorphism] record.  The [≈] form is
   [discrete_iprod_iso_leg], which holds. *)
Fail Example neg_discrete_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
  = iprod_proj f (discrete_limit f) a := eq_refl.

(* * ** (4) Which limit oracle 伴随 fed -- TYPING （已译） *)

(*
   本节说明 ProbeConeSets407 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition neg_wrong_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (Sets_Diagonal_Limit_Adjunction J) X F.

Definition ctrl_right_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetPin.

Universes io co ch cp.
Constraint Set < ch.
Context (A : Type@{io}).
Context (C : Category@{co ch cp}).
Context (f : A → obj[C]).

(* Controls, all accepted at these very levels. *)
Check (DiscreteCat@{io ch cp} A).
Check (DiscreteCat_Functor f).
Check (Cone (DiscreteCat_Functor f)).
Check (@ACone (DiscreteCat A) C).

(* Former donor 1: [DiscreteCat_Functor] used to pin its own SOURCE at
   [DiscreteCat@{_ Set Set}], with the error tail
     (universe inconsistency: Cannot enforce Set = ch).
   Annotated, it reaches these levels.（标题）（已译） *)
Check (DiscreteCat_Functor f : DiscreteCat@{io ch cp} A ⟶ C).

(* Former donor 2: [IsALimit] identifies shape's hom-and-证明
 universes ambient 范畴's. It still does; what it no
 longer transmits [Set]. （已译） *)
Check (IsALimit (DiscreteCat_Functor f)).

End SetPin.

(* 相关说明。 （已译） *)

(*
   本节说明 ProbeConeSets407 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_adj_to_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  = cone_transpose F X p := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Fail Example neg_adj_from_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (h : X ~{Sets}~> cone_apex F) :
  fst (Cone_Natural_Transform F X)
      (from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h)
  = cone_untranspose F X h := eq_refl.

(* 相关说明。 （已译） *)

(* The existing [HasEqualizers Sets] apex compatible-family setoid
 over walking parallel pair. The bridge [concrete_vs_existing],
 同构 nothing stronger. （已译） *)
Fail Example neg_awodey_strict {X Y : SetoidObject} (f g : X ~{Sets}~> Y) :
  sets_eq_obj f g = Sets_limit_obj (APair f g) := eq_refl.

(* * ** (10) The tuple form 同构, not equality -- CONVERSION （已译） *)

(* 相关说明。 （已译） *)
Fail Example neg_tuple_strict {G : Quiver} (D : Diagram G Sets) :
  Sets_limit_obj (FunctorOfDiagram D) = tuple_obj D := eq_refl.

(* * ** (11) Presentation-independence, at 对象 level -- CONVERSION （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example neg_pres_strict (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_obj S = Sets_limit_obj (Srestr G R S) := eq_refl.

(* 相关说明。 （已译） *)

Example ctrl_pres_carrier (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_carrier S = Sets_limit_carrier (Srestr G R S) := eq_refl.

Example ctrl_apex_is_conepresheaf {D : Category} (F : D ⟶ Sets) :
  carrier (cone_apex F)
  = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F := eq_refl.

Example ctrl_iso_to_is_med {D : Category} (F : D ⟶ Sets) :
  to (cone_apex_iso F)
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.
