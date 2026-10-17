Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(* * * A universal element 始对象 范畴 elements （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/category+of+elements

   本文件给出泛元素相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ElementsInitial.

Context {D : Category}.
Context (H : D ⟶ Sets).

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* 相关说明。 （已译） *)
Definition Elements_Initial {r : D} (U : AUniversalElement H r)
  : @Initial (Elements H).
Proof.
  unshelve eapply (@Build_Terminal ((Elements H)^op)).
  - exact ((r; @aue_elem D H r U) : Elements H).
  - intros [d elt].
    exists (unique_obj (aue_universal d elt)).
    exact (unique_property (aue_universal d elt)).
  - intros [d elt] [f Hf] [g Hg]; simpl in *.
    transitivity (unique_obj (aue_universal d elt)).
    + symmetry; exact (uniqueness (aue_universal d elt) f Hf).
    + exact (uniqueness (aue_universal d elt) g Hg).
Defined.

(* 相关说明。 （已译） *)
Lemma Elements_zero_is_med {r : D} (U : AUniversalElement H r) (d : D) (x : H d) :
  `1 (@zero (Elements H) (Elements_Initial U) ((d; x) : Elements H))
    = unique_obj (aue_universal d x).
Proof. reflexivity. Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AUniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : AUniversalElement H (`1 (@initial_obj (Elements H) I)).
Proof.
  unshelve econstructor.
  - exact (`2 (@initial_obj (Elements H) I)).
  - intros d x.
    unshelve eexists (`1 (@zero (Elements H) I ((d; x) : Elements H))).
    + exact (`2 (@zero (Elements H) I ((d; x) : Elements H))).
    + intros v Hv.
      exact (@zero_unique (Elements H) I ((d; x) : Elements H)
               (@zero (Elements H) I ((d; x) : Elements H)) (v; Hv)).
Defined.

Definition UniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_Elements_Initial I).

(* 相关说明。 （已译） *)
Corollary Elements_Initial_obj {r : D} (U : AUniversalElement H r) :
  `1 (@initial_obj (Elements H) (Elements_Initial U)) = r.
Proof. reflexivity. Qed.

Corollary Elements_Initial_elem {r : D} (U : AUniversalElement H r) :
  `2 (@initial_obj (Elements H) (Elements_Initial U)) = @aue_elem D H r U.
Proof. reflexivity. Qed.

Corollary aue_of_Elements_Initial_elem (I : @Initial (Elements H)) :
  @aue_elem D H _ (AUniversalElement_of_Elements_Initial I)
    = `2 (@initial_obj (Elements H) I).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Corollary Elements_Initial_round {r : D} (U : AUniversalElement H r) :
  @aue_elem D H _
    (AUniversalElement_of_Elements_Initial (Elements_Initial U))
    = @aue_elem D H r U.
Proof. reflexivity. Qed.

End ElementsInitial.
