Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Instance.Grp.QuotObj.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Regular.
Require Import Category.Instance.FinSet.Subobject.
Require Import Category.Instance.FinSet.QuotObj.

Generalizable All Variables.

(*
   本文件为测试：ProbeQuotObjWitnesses446。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check quot_obj_446_no_such_constant.

(** ** Positive controls: every constant the negatives name *)

Check @QuotObj.
Check @SubObj.
Check @SetoidObject.
Check @Sets.
Check @Isomorphism.
Check @to.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_is_epic.
Check @mk_quot.
Check @quot_meet.
Check @sub_meet.
Check @Sets_HasPushouts.
Check @NatDiscrete.
Check @Sets_Q_parity.
Check @Sets_Q_mod3.
Check @Sets_Q_total.
Check @Sets_quot_epi_surjective.
Check @Sets_quot_of_surjection.
Check @SetsQuotient_QuotObj.
Check @Sets_coimage.
Check @Sets_CoimageOf.
Check @Sets_HasCoimages.
Check @Sets_quot_meet_parity_mod3.
Check @grp_quot_of_normal.
Check @grp_quot_is_quot_by_kernel.
Check @grp_quot_le_of_included.
Check @finset_quot_epi_surjective.
Check @finset_quot_of_surjection.
Check @finset_coimage.
Check @FinSet_CoimageOf.
Check @FinSet_HasCoimages.
Check @finset_merge01.
Check @finset_merge12.
Check @finset_q01.
Check @finset_q12.
Check @finset_q_meet.
Check @fin4_0.
Check @fin4_2.
Check @fin4_3.

(** ** Positive controls for the computing readbacks themselves *)

(* The pushout of "identify {0,1}" and "identify {1,2}" over the
   four-element set has TWO classes, by [eq_refl]. *)
Example p446_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

Example p446_meet_merges :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example p446_coimage_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(** ** N1 -- the meet has two classes and not three (CONVERSION) *)

(* Guards [finset_quot_meet_two].  A probe against the right number
   alone would pass for a construction that did not reduce at all; this
   one pins that the number is computed and is 2. *)
Fail Example p446_n1 : quot_cod finset_q_meet = 3%nat := eq_refl.

(** ** N2 -- the meet does not collapse everything (CONVERSION) *)

(* Guards [finset_quot_meet_separates_0_3] at the strongest reading: 0
   and 3 are not identified even up to conversion. *)
Fail Example p446_n2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 := eq_refl.

(** ** N3 -- a coimage is smaller than the codomain it is read in
       (CONVERSION) *)

(* Guards [finset_coimage_merge01_three]: the coimage of a 4 ↠ 3 map is
   3 and not 4, so the construction is not silently the domain. *)
Fail Example p446_n3 :
  quot_cod (finset_coimage finset_merge01) = 4%nat := eq_refl.

Section SetsBoundaries.

Universe o so.
Constraint o < so.

(** ** N4 -- the quotient-object meet is an ≈ and NOT a Leibniz equality
       (CONVERSION) *)

(*
   本节说明子对象、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p446_n4 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 = Sets_Q_total := eq_refl.

(** ** N5 -- a quotient object of C is not a subobject of C (CONVERSION) *)

(* [@QuotObj (C^op) x = @SubObj C x] holds by [eq_refl], C^op^op being C
   on the nose.  Dropping the [^op] must NOT: that is the whole content
   of the definition. *)
Fail Example p446_n5 (X : SetoidObject@{o o}) :
  @QuotObj Sets@{o so} X = @SubObj Sets@{o so} X := eq_refl.

(** ** N6 -- the covariant reading of the setoid is a LEMMA, not a
       conversion (CONVERSION) *)

(*
   本节说明同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p446_n6 (X : SetoidObject@{o o})
  (q r : @QuotObj Sets@{o so} X) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

End SetsBoundaries.
