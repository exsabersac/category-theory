(*
   本文件为测试：ProbeSetsQuotient。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Quotient.Partition.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Sets.Coequalizer.Interconnect.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Section YonedaAtSets.

Context (H : Sets ⟶ Sets).
Context (r : Sets).
Context (U : AUniversalElement H r).

(** 本节：Positive control: Yoneda-FREE route builds representation
 at [Sets], [Instance/Sets/Quotient.v] uses exactly it. （已译） *)
Check (ue_representation H r U).
Check (AUniversalElement_of_repr H r).

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (universal_element_yoneda H r).

Fail Check (universal_element_representation H r).

End YonedaAtSets.

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section YonedaSmall.

Universe u.

Context (D : Category@{u u u}).
Context (K : D ⟶ Sets).
Context (d : D).

Check (universal_element_yoneda K d).

End YonedaSmall.

(* * ** (2) The untruncated class 对象 （已译） *)

(** Positive control: the [Prop]-valued part-carrier, at a PINNED [Sets]
    universe instance. *)
Definition probe_parts_prop@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Prop.

(** Positive control: the [Type]-valued one exists a level up. *)
Definition probe_parts_type_up@{o o'} (A : SetoidObject@{o o}) : Type@{o'} :=
  carrier A -> Type@{o}.

(*
   本节说明 ProbeSetsQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_parts_type_same@{o} (A : SetoidObject@{o o}) : Type@{o} :=
  carrier A -> Type@{o}.

(** ... [Prop]-valued 关系 really usable quotient's
 `≈` at pinned instance, what [prop_rel_squash_stable]
 rests on. （已译） *)
Definition probe_prop_quotient@{o so} (A : obj[Sets@{o so}])
  (Rp : carrier A -> carrier A -> Prop) (HRp : Equivalence Rp) :
  obj[Sets@{o so}] :=
  {| carrier := carrier A ;
     is_setoid := {| equiv := Rp ; setoid_equiv := HRp |} |}.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_intersection_type@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Type@{o} :=
  forall R : crelation@{o o} (carrier A), Equivalence R -> R a b.

(* * Positive control: the [Prop]-valued intersection DOES fit, [Prop]
    being impredicative -- which is why Awodey's phrasing is available
    classically and the inductive generation is what replaces it here.（标题）（已译） *)
Definition probe_intersection_prop@{o} (A : SetoidObject@{o o})
  (a b : carrier A) : Prop :=
  forall R : carrier A -> carrier A -> Prop,
    (forall x, R x x) -> R a b.

(* 相关说明。 （已译） *)

(** 本节：Positive control: quotienting setoid's OWN `≈` returns the
 record, [eq_refl]. （已译） *)
Definition probe_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A := eq_refl.

(*
   本节说明 ProbeSetsQuotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_diagonal_eq :
  SetsCoeq bool_false_map bool_false_map = BoolSet := eq_refl.

(** ... while fact header actually claims -- two
 relations agree -- 定理, tree. （已译） *)
Check (@coeq_rel_diagonal UnitSet BoolSet bool_false_map).

(* 相关说明。 （已译） *)

(** 本节：Positive controls: carrier did not move, two ports ARE
 identified coequalizer. （已译） *)
Definition probe_interconnect_carrier : carrier Interconnect = ic_port := eq_refl.

Check port_P0_P1_merged.

(** 本节：Negative: they nevertheless distinct ports. (With [Fail]
 stripped reports "cannot unify "IcP0" "IcP1"".) （已译） *)
Fail Definition probe_ports_eq : IcP0 = IcP1 := eq_refl.

(** ... coequalizer does not identify everything: 这是 the
 映射-out 论元, tree. （已译） *)
Check port_P0_P3_apart.
