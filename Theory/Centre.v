Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * 范畴的中心 *)

(* nLab:      https://ncatlab.org/nlab/show/center+of+a+category
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument

   范畴的中心 (center) 收集与一切态射交换的自同态（或相关的自然变换数据）。本文件在
   setoid 设定下给出中心对象/幺半群结构，并与 Eckmann–Hilton 论证的零元阴影相联系
   （见 Theory/EckmannHilton.v）。文内其它长注释后续可续译。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/center+of+a+category
   Paper: Eckmann, Hilton, "Group-like structures in general categories I",

   本节说明自然变换、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The centre setoid 幺半群 （已译） *)

Section Centre.

Context {C : Category}.

(*
   本节说明自然变换、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition centre_setoid : SetoidObject := {|
  carrier   := @hom ([C, C]) Id[C] Id[C];
  is_setoid := @homset ([C, C]) Id[C] Id[C]
|}.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition centre_monoid : MonObject := hom_monoid ([C, C]) Id[C].

(* 相关说明。 （已译） *)

Example centre_monoid_setoid : mon_setoid centre_monoid = centre_setoid
  := eq_refl.

Example centre_monoid_carrier :
  carrier centre_monoid = (Id[C] ⟹ Id[C]) := eq_refl.

Example centre_monoid_unit :
  @mon_unit centre_monoid = @nat_id C C Id[C] := eq_refl.

Example centre_monoid_op :
  @mon_op centre_monoid = @nat_compose C C Id[C] Id[C] Id[C] := eq_refl.

(* * ** Commutativity, directly 自然性 （已译） *)

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma centre_commutes_at (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[α] x ∘ transform[β] x ≈ transform[β] x ∘ transform[α] x.
Proof.
  symmetry.
  exact (naturality[α] x x (transform[β] x)).
Qed.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem centre_commutative (α β : Id[C] ⟹ Id[C]) :
  nat_compose α β ≈[Fun] nat_compose β α.
Proof.
  intro x.
  exact (centre_commutes_at α β x).
Qed.

(* The same statement read through 幺半群 packaging, so consumer
 holding [centre_monoid] can quote commutativity 幺半群's own
 vocabulary. （已译） *)
Corollary centre_monoid_commutative (α β : carrier centre_monoid) :
  mon_op α β ≈ mon_op β α.
Proof. exact (centre_commutative α β). Qed.

End Centre.

(** ** The Eckmann–Hilton packaging *)

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CentreEH.

Context {C : Category}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition centre_vcomp (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose α β.

Definition centre_vcomp_op (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose β α.

(* 相关说明。 （已译） *)

Example centre_vcomp_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp α β] x = transform[α] x ∘ transform[β] x := eq_refl.

Example centre_vcomp_op_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[β] x ∘ transform[α] x
  := eq_refl.

(* * *** The second operation IS horizontal 复合, componentwise （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example centre_hcompose_is_vcomp (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[nat_hcompose α β] x = transform[nat_compose α β] x := eq_refl.

Example centre_vcomp_op_is_hcompose (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[nat_hcompose β α] x := eq_refl.

(* Both whiskerings against 恒等 函子 恒等 on
 components, other half same observation. （已译） *)

Example centre_whisker_left (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[Id[C] ⊳ α] x = transform[α] x := eq_refl.

Example centre_whisker_right (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[α ⊲ Id[C]] x = transform[α] x := eq_refl.

(* 相关说明。 （已译） *)

(* Respectfulness: both operations [nat_compose] up 论元 order,
 so both [nat_compose_respects] (the second two arguments
 exchanged). （已译） *)

Definition centre_vcomp_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp.
Proof. repeat intro; now apply nat_compose_respects. Qed.

Definition centre_vcomp_op_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp_op.
Proof. repeat intro; now apply nat_compose_respects. Qed.

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition centre_vcomp_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp nat_id α ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

Definition centre_vcomp_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp α nat_id ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op nat_id α ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op α nat_id ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma centre_interchange (a b c d : Id[C] ⟹ Id[C]) :
  centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
    ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d).
Proof.
  intro x.
  simpl.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity].
  exact (centre_commutes_at a d x).
Qed.

(** *** Commutativity via [eh_comm] *)

(* All seven hypotheses discharged, abstract 论元 applied. The
 conclusion [centre_commutative] again, reached long way. （已译） *)
Theorem centre_commutative_EH (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp β α.
Proof.
  exact (eh_comm centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary centre_EH_ops (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp_op α β.
Proof.
  exact (eh_ops centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary centre_EH_units : (nat_id : Id[C] ⟹ Id[C]) ≈[Fun] nat_id.
Proof.
  exact (eh_units centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem centre_interchange_forces_commutative
  (inter : ∀ a b c d : Id[C] ⟹ Id[C],
      centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
        ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d))
  (α δ : Id[C] ⟹ Id[C]) :
  centre_vcomp α δ ≈[Fun] centre_vcomp δ α.
Proof.
  (*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  specialize (inter α nat_id nat_id δ).
  intro x.
  specialize (inter x).
  simpl in *.
  rewrite !id_left, !id_right in inter.
  exact inter.
Qed.

End CentreEH.

(** ** The centre of Sets is trivial *)

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition centre_Sets_point@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) :
  ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) ~{Sets@{o so}}~> X := {|
  morphism := fun _ => x
|}.

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example centre_Sets_point_computes@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) (u : poly_unit@{o}) : centre_Sets_point x u = x := eq_refl.

(* Pointwise form: every centre element of `Sets` acts as the identity on
   every point of every setoid. *)
Theorem centre_Sets_trivial@{o so} (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}])
  (X : obj[Sets@{o so}]) (x : carrier X) : transform[α] X x ≈ x.
Proof.
  symmetry.
  exact (naturality[α] ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) X
           (centre_Sets_point x) ttt).
Qed.

(* Packaged form: every centre element `Sets` IS 恒等
 transformation, hom-setoid `[Sets, Sets]`. （已译） *)
Corollary centre_Sets_trivial_nat@{o so}
  (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Sets_trivial.
Qed.

(* Hence centre `Sets` singleton: it trivial 幺半群. （已译） *)
Corollary centre_Sets_subsingleton@{o so}
  (α β : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] β.
Proof.
  transitivity (@nat_id Sets@{o so} Sets@{o so} Id[Sets@{o so}]).
  - apply centre_Sets_trivial_nat.
  - symmetry; apply centre_Sets_trivial_nat.
Qed.

(** ** The centre of Coq is trivial *)

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem centre_Coq_trivial (α : Id[Coq] ⟹ Id[Coq])
  (X : obj[Coq]) (x : X) : transform[α] X x = x.
Proof.
  symmetry.
  exact (naturality[α] poly_unit X (fun _ => x) ttt).
Qed.

Corollary centre_Coq_trivial_nat (α : Id[Coq] ⟹ Id[Coq]) :
  α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Coq_trivial.
Qed.
