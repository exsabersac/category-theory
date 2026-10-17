(*
   本文件为测试：ProbeWideParallel。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Local Open Scope category_scope.

(* 相关说明。 （已译） *)

(** Positive control: the isomorphism itself, at both strengths. *)
Check (WideParallel_bool_Parallel :
         @Isomorphism StrictCat (WideParallel bool) Parallel).
Check (WideParallel_bool_Parallel_Cat :
         @Isomorphism Cat (WideParallel bool) Parallel).

(*
   本节说明 ProbeWideParallel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

(** 本节：Negative: two [Category] records not Leibniz-equal. (With
 [Fail] stripped: cannot unify [WideParallel bool] with
 [Parallel].) （已译） *)
Fail Definition wide_bool_is_Parallel :
  WideParallel bool = Parallel := eq_refl.

(** 本节：Negative: nor hom-families convertible at [ParX], [ParY] —
 [bool] against [∃ b : bool, ParHom b ParX ParY]. (With [Fail]
 stripped: cannot unify two types.) （已译） *)
Fail Definition wide_bool_hom_is_Parallel_hom :
  (ParX ~{WideParallel bool}~> ParY) = (ParX ~{Parallel}~> ParY) := eq_refl.

(* * ** (2) The diagram comparison up strict 函子 equality （已译） *)

Section DiagramComparison.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes dco dch.
Constraint Set < dco.
Constraint Set < dch.

Context (C : Category@{dco dch dch}).
Context (x y : C).
Context (f g : x ~{C}~> y).

(** 本节：Positive control: comparison IS proved, [eq_refl]
 identification arrow action it rests on. （已译） *)
Check (AWide_bool_APair f g).

Definition probe_awide_true_is_f :
  fmap[AWide (fun b : bool => if b then f else g)]
    (true : ParX ~{WideParallel bool}~> ParY) = f := eq_refl.

(** Negative: two 函子 not Leibniz-equal. (With [Fail]
 stripped: cannot unify two [Functor] records.) （已译） *)
Fail Definition awide_bool_is_APair :
  AWide (fun b : bool => if b then f else g) = APair f g ◯ Par_of_Wide
  := eq_refl.

End DiagramComparison.

(* 相关说明。 （已译） *)

(** 本节：Positive control: index universe declared strictly BELOW the
 target's hom universe, diagram both round trips build. （已译） *)
Section SmallIndex.

Universes si so sh sp.
Constraint si < sh.
Constraint sh <= sp.

Context (C : Category@{so sh sp}).
Context (I : Type@{si}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).
Context (i0 : I).

Check (AWide fs : WideParallel I ⟶ C).
Check (is_wide_equalizer_limit fs i0).
Check (is_wide_coequalizer_colimit fs i0).

End SmallIndex.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section BigIndex.

Universes bi bo bh bp.
Constraint bh < bi.
Constraint bh <= bp.

Context (C : Category@{bo bh bp}).
Context (I : Type@{bi}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).

Fail Check (AWide fs : WideParallel I ⟶ C).

End BigIndex.

(*
   本节说明 ProbeWideParallel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (wide_round_trip_needs_point :
         (∀ (q : _2) (e : q ~{_2}~> TwoY),
            IsWideEqualizer two_empty_family q e
            → IsALimit (AWide two_empty_family) q) → False).
Check (wide_coround_trip_needs_point :
         (∀ (q : _2) (e : TwoX ~{_2}~> q),
            IsWideCoequalizer two_empty_family q e
            → IsAColimit (AWide two_empty_family) q) → False).

(*
   本节说明 ProbeWideParallel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
