Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Quotient.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Strict.

(*
   本文件为测试：ProbeStrict377。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Generalizable All Variables.

(** ** Instrument check *)

(* 相关说明。 （已译） *)
Fail Check probe377_no_such_constant_anywhere.

(* * ** Controls: every 常值 negatives name, named outside guard （已译） *)

Check @unit.
Check @counit.
Check @id_cast.
Check @id_cast_iso.
Check @iso_id.
Check @eso_iso.
Check @LeftAdjointRightInverse.
Check @lari_left.
Check @lari_adj.
Check @lari_obj.
Check @lari_unit.
Check @surjective_ESO.
Check @SurjectiveOnObjects.
Check @SurjectiveOnObjects_Id.
Check @ff_surjective_left.
Check @ff_surj_eq.
Check @ff_surj_adj.
Check @ff_surj_eso.
Check @ff_surj_eso_adjoint_equivalence.
Check @ff_surjective_adjoint_equivalence.
Check @ff_surjective_counit_iso.
Check @ff_eso_inverse.
Check @adj_equivalence.
Check @Adjunction.
Check IndT.
Check indiscrete_LARI.
Check Indiscrete.
Check @Erase.
Check erase_pt.

(* * ** TYPING negatives: two 恒等 readings not statable （已译） *)

Section UnitAndCounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context (P : LeftAdjointRightInverse S).
Context (c : C).

(* Control: delivered form "unit 恒等", against the
 恒等 TRANSPORTED along 对象 equation. （已译） *)
Check (@unit A C (lari_left P) S (lari_adj P) c
         ≈ id_cast (eq_sym (lari_obj P c))).

(* 相关说明。 （已译） *)
Check (@unit A C (lari_left P) S (lari_adj P) c).
Check (@id C c).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@unit A C (lari_left P) S (lari_adj P) c ≈ @id C c).

End UnitAndCounitTyping.

Section CounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (a : A).

(* Control: counit well-formed, 同构 -- is
 strength Mac Lane's epsilon actually has. （已译） *)
Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a).
Check (ff_surjective_counit_iso surj a).
Check (@id A a).

(* NEGATIVE 2 (TYPING). The counit runs
 [ff_surjective_left (S a) ~> a], chosen preimage [S a] need
 not [a]: exercise gives 同构, not 恒等. （已译） *)
Fail Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a
            ≈ @id A a).

End CounitTyping.

(* Control: counit delivered adjoint 等价 at the
 non-degenerate witness well-formed, 同构. （已译） *)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false).

Check (@adj_equiv_counit_iso _1 (Indiscrete bool) IndT
         (Erase (Indiscrete bool)) indiscrete_adjoint_equivalence false).

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
       ≈ @id (Indiscrete bool) false).

(* 相关说明。 （已译） *)
Example p377_indiscrete_counit_is_id :
  @counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
    (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
  ≈ @id (Indiscrete bool) false.
Proof. cbn; reflexivity. Qed.

(** ** CONVERSION negatives *)

Section StrictReadbacks.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (c : C).

(* Control: residue exhibited at Leibniz equality -- unit IS
 [fmap[S] id] composed transported 恒等. （已译） *)
Check (ff_surj_unit_residue surj c).

(* Control: the [≈] form does hold. *)
Check (ff_surj_unit_is surj c).

(* NEGATIVE 3 (CONVERSION).  [unit] is [⌊id⌋], so it carries an
   [fmap[S] id] that conversion cannot remove at an abstract [S]. *)
Fail Example p377_n3 :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(* 相关说明。 （已译） *)
Check (ff_surj_eso_inverse_obj surj c).
Check (ff_surj_eso_inverse_strict surj).

(* NEGATIVE 4 (CONVERSION). The whole 函子 RECORDS not
 Leibniz-equal: three law fields rebuilt. （已译） *)
Fail Example p377_n4 :
  @ff_eso_inverse A C S _ _ (ff_surj_eso surj) = ff_surjective_left surj
  := eq_refl.

(* Control: 伴随 extracted delivered adjoint
 等价 IS directly built one. （已译） *)
Check (ff_surj_equiv_adj surj).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p377_n5 :
  @adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)
    = ff_surj_adj surj := eq_refl.

(*
   本节说明 ProbeStrict377 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p377_n6 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(* 相关说明。 （已译） *)
Definition p377_route_control :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; rewrite fmap_id, id_left; reflexivity).

(*
   本节说明函子、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p377_n7 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; reflexivity).

End StrictReadbacks.

(* Controls: at [eq_refl] witness both legs repackaged
 同构 [id] nose. （已译） *)
Check @surjective_ESO_refl_to.
Check @surjective_ESO_refl_from.

(* NEGATIVE 8 (CONVERSION). The whole 同构 RECORD nevertheless
 not [iso_id]: two inverse-law fields different proofs. （已译） *)
Fail Example p377_n8 {C : Category} (c : C) :
  @eso_iso C C Id[C] (surjective_ESO (@SurjectiveOnObjects_Id C)) c
    = @iso_id C c := eq_refl.

(** ** FORMABILITY negatives *)

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomLevelBoundary.

Universes uo uh vo vh.
Constraint uh < vh.

Context (Au : Category@{uo uh uh}).
Context (Xu : Category@{vo vh vh}).

(* Controls: both 范畴 formable at these declared levels, a
 函子 DIRECTION bound permits elaborates. （已译） *)
Check Au.
Check Xu.
Check (Au ⟶ Xu).

(* 相关说明。 （已译） *)
Fail Check (Xu ⟶ Au).

(* NEGATIVE 10 (FORMABILITY). Hence neither does record, whose
 [lari_left] field 函子 other way. （已译） *)
Fail Check (∀ S : Au ⟶ Xu, LeftAdjointRightInverse S).

End HomLevelBoundary.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomProofBoundary.

Universes wo wh wp.
Constraint wh < wp.

Context (Bu : Category@{wo wh wp}).

(* Controls: 范畴, homs, 函子 it all formable
 hom declared strictly below 证明. （已译） *)
Check Bu.
Check (∀ x y : Bu, x ~{Bu}~> y).
Check (Bu ⟶ Bu).

(* NEGATIVE 11 (FORMABILITY).  The adjunction is not. *)
Fail Check (∀ F G : Bu ⟶ Bu, F ⊣ G).

(* NEGATIVE 12 (FORMABILITY).  Nor, therefore, is the record. *)
Fail Check (∀ S : Bu ⟶ Bu, LeftAdjointRightInverse S).

End HomProofBoundary.
