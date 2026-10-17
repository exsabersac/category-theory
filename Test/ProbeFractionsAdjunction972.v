Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Construction.Fractions.Weak.
Require Import Category.Construction.Fractions.Adjunction.
Require Import Category.Construction.Groupoid.Core.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(*
   本文件为测试：ProbeFractionsAdjunction972。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Positive controls *)

(* The objects of the localization ARE the objects of the source, and the
   projection is the identity on them -- the two conversions the weak
   uniqueness argument rests on. *)

Example P1 (C : Category) : @obj (Fractions C) = @obj C := eq_refl.

Example P2 (C : Category) (x : C) : fobj[FractionsProj C] x = x := eq_refl.

(* The generated left adjoint's object map is the category of fractions on
   the nose. *)

Example P3 (C : Cat) : fobj[FractionsF] C = frac_grpd C := eq_refl.

(* The two adjunctions in the directions that ARE proved, and the triple. *)

Example P4 : Adjunction FractionsF Grpd_Incl := Fractions_Incl_Adjunction.

Example P5 : Adjunction Grpd_Incl Core := Incl_Core_Adjunction.

Example P6 : AdjointTriple FractionsF Grpd_Incl Core := riehl_4_1_15.

(* The unit is the projection up to `≈`; N9 is the same statement at
   [eq_refl] and is refused. *)

Example P7 (C : Cat) :
  @equiv _ (@Functor_Setoid C (Fractions C))
    (@unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C)
    (FractionsProj C)
  := Fractions_unit_is_proj C.

(** ** Negatives, at an abstract source, target and functor *)

Section Negatives.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

(* Both universal properties exist at their own strength; only the transfers
   are refused. *)

Example P8 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C))
  := Fractions_UMP_weak Dg F.

Example P9 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C))
  := Fractions_UMP_groupoid Dg F.

(* N1 *)
Fail Definition N1 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C)) :=
  Fractions_UMP_weak Dg F.

(* N2 *)
Fail Definition N2 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  Fractions_UMP_groupoid Dg F.

(* N3 *)
Fail Definition N3 (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D) L L' :=
  Fractions_proj_epic_weak L L' E.

(* N10 *)
Fail Definition N10 (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (FractionsLift F (fun x y f => Dg (F x) (F y) (fmap[F] f))) L :=
  FractionsLift_unique F (fun x y f => Dg (F x) (F y) (fmap[F] f)) L E.

(* N11 *)
Fail Definition N11 (G H : C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) G H) :
  @equiv _ (@Functor_StrictEq_Setoid C D) G H :=
  strict_equiv_implies_fun_equiv G H E.

End Negatives.

(** ** Negatives about the adjunction itself *)

(* N4 *)
Fail Definition N4 (C : Cat) : UniversalArrow C Grpd_Incl :=
  universal_arrow_from_UMP C Grpd_Incl (frac_grpd C) (FractionsProj C)
    (fun d' f => Fractions_UMP_groupoid (`2 d') f).

(* N5 *)
Fail Definition N5 : Adjunction Core Grpd_Incl := Incl_Core_Adjunction.

(* N6 *)
Fail Definition N6 : Adjunction Grpd_Incl FractionsF := Fractions_Incl_Adjunction.

(* N7 *)
Fail Definition N7 : AdjointTriple Core Grpd_Incl FractionsF :=
  {| triple_left  := Fractions_Incl_Adjunction;
     triple_right := Incl_Core_Adjunction |}.

(* N8 *)
Fail Example N8 (C D : Cat) (F : C ~{Cat}~> D) :
  `1 (fmap[FractionsF] F) = FractionsMap F := eq_refl.

(* N9 *)
Fail Example N9 (C : Cat) :
  @unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C
    = FractionsProj C := eq_refl.
