Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Grp.Generator.
Require Import Category.Instance.Ab.Generator.

Generalizable All Variables.

(*
   本文件为测试：ProbeGeneratorWitnesses447。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check generator_witness_447_no_such_constant.

(** ** Positive controls *)

Check @IsSeparator.
Check @Generator.
Check @gen_index.
Check @gen_obj.
Check @Generator_of_separator.
Check @separator_iso.
Check @IsSeparator_of_Separator.
Check @Sets_Separator.
Check @Sets_unit_separates.
Check @Sets_terminal_separates.
Check @Sets_terminal_separates_by_transport.
Check @Sets_terminal_separates_from_Concrete.
Check @Sets_Generator.
Check @Sets_terminal_Generator.
Check @Sets_terminal_unit_iso.
Check @Sets_empty_not_separates.
Check @Sets_empty_not_separates_pick.
Check @Grp_free_one_separates.
Check @Grp_Generator.
Check @Ab_free_one_separates.
Check @Ab_Generator.
Check @FreeGrpObject.
Check @FreeAbObject.
Check @ab_int.
Check @unit_setoid_object.
Check @Unit_Setoid.
Check @Sets_Terminal.
Check @Sets_Initial.
Check @terminal_obj.

(** ** Readbacks that HOLD *)

(* The Generator packages are the expected one-object families, on the
   nose. *)
Example p447w_g1 : gen_index Sets_Generator = unit := eq_refl.
Example p447w_g2 : gen_obj Sets_Generator tt = unit_setoid_object := eq_refl.
Example p447w_g3 :
  gen_obj Sets_terminal_Generator tt = @terminal_obj Sets Sets_Terminal
  := eq_refl.

(* The terminal object's setoid field IS Instance/Sets.v's [Unit_Setoid];
   the singleton's is Lib/Setoid.v's [unit_setoid] -- which is why N1
   below is refused. *)
Example p447w_t1 : @terminal_obj Sets Sets_Terminal
  = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl.

(* The initial object's carrier is [False], on the nose. *)
Example p447w_empty : carrier (@terminal_obj (Sets^op) Sets_Initial) = False
  := eq_refl.

(* Control for N4: the free abelian group on one generator IS what the
   theorem is about. *)
Definition p447w_ab : @IsSeparator Ab (FreeAbObject unit_setoid_object) :=
  Ab_free_one_separates.

(** ** Negatives *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n1 : @terminal_obj Sets Sets_Terminal = unit_setoid_object
  := eq_refl.

(* N2 -- CONVERSION.  Separation is at ≈, not at Leibniz =:
   "cannot unify "f ∘ k = g ∘ k" and "f ∘ k ≈ g ∘ k"". *)
Fail Definition n2 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : unit_setoid_object ~{Sets}~> X, f ∘ k = g ∘ k) -> f = g
  := Sets_unit_separates.

(*
   本节说明 ProbeGeneratorWitnesses447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n3 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : Y ~{Sets}~> unit_setoid_object, k ∘ f ≈ k ∘ g) -> f ≈ g
  := Sets_unit_separates.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n4 : @IsSeparator Ab ab_int := Ab_free_one_separates.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n5 : @IsSeparator Sets (@terminal_obj Sets Sets_Terminal)
  := Sets_unit_separates.
