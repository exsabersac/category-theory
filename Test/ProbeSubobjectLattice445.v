Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Subobject.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   本文件为测试：ProbeSubobjectLattice445。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check sub_lattice_no_such_constant.

(* * ** Positive controls: every 常值 negatives depend on （已译） *)

Check @sub_meet.
Check @sub_meet_comm.
Check @sub_meet_is_glb.
Check @sub_wide_intersection.
Check @sub_wide_intersection_IsIntersection.
Check @sub_join.
Check @sub_join_via.
Check @sub_join_via_bot.
Check @sub_join_bot.
Check @sub_bot.
Check @sub_top.
Check @sub_pair.
Check @sub_compose.
Check @sub_reindex.
Check @ImageOf.
Check @ImageOf_of_OFS.
Check @OFS.
Check @MorphismClass.
Check @MonoClass.
Check @EpiClass.
Check @WidePullback.
Check @IsWidePullback.
Check @IsPullback.
Check @binary_wide_pullback.
Check @two_legs.
Check @terminal_obj.
Check @Sets_Terminal.
Check @Sets_HasImages.
Check @Sets_HasWidePullbacks.
Check @Sets_wpull_obj.
Check @fs_union.
Check @fs_pos.
Check @pos_obj.
Check @fs_union_is_positives.
Check @fs_inter_is_empty.
Check @FinSet_HasImages.
Check @ex11_u.
Check @ex11_v.

(* 相关说明。 （已译） *)

Section Readbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
   本节说明函子、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p445_meet_is_compose_reindex (u v : SubObj x) :
  sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v) := eq_refl.

End Readbacks.

(* 相关说明。 （已译） *)
Example p445_union_four : sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.
Example p445_meet_one : sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.
Example p445_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(** ** Negatives *)

Section NoPullbacks.

Context {C : Category}.
Context {x : C}.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n1 (u v : SubObj x) : SubObj x := sub_meet u v.

(*
   本节说明拉回/推出、子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n3 (S : Empty_set → SubObj x)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x :=
  sub_wide_intersection S _ W.

End NoPullbacks.

Section WithPullbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
   本节说明拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n2 (u v : SubObj x) : sub_meet u v = sub_meet v u :=
  sub_meet_comm u v.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n5 (u v : SubObj x) (P : C)
  (q1 : P ~> sub_dom u) (q2 : P ~> sub_dom v)
  (HP : IsPullback (sub_mono u) (sub_mono v) P q1 q2) :
  IsWidePullback (fun b => sub_mono (sub_pair u v b)) P (two_legs q1 q2) :=
  binary_wide_pullback HP.

End WithPullbacks.

Section NoImages.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(*
   本节说明 ProbeSubobjectLattice445 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n4 (u v : SubObj x) : SubObj x := sub_join u v.

End NoImages.

Section WrongClass.

Context {C : Category}.
Context {E : MorphismClass C}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n6 (O : OFS E (@EpiClass C)) {y z : C} (f : y ~> z) :
  ImageOf f := ImageOf_of_OFS O f.

End WrongClass.

Section NoStrictness.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(*
   本节说明子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n7 : SubObj x := @sub_bot C I x _.

End NoStrictness.

(*
   本节说明 ProbeSubobjectLattice445 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n8 : sub_dom (sub_join ex11_u ex11_v) = 5%nat := eq_refl.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n9 : sub_dom (sub_meet ex11_u ex11_v) = 2%nat := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n10 : sub_dom fs_union = pos_obj := eq_refl.

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n11 :
  Sets_wpull_obj (I:=False) (A:=fun i => match i with end)
    (z:=@terminal_obj Sets Sets_Terminal) (fun i => match i with end)
  = @terminal_obj Sets Sets_Terminal := eq_refl.
