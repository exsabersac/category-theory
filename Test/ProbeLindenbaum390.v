Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Theory.Lindenbaum.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeLindenbaum390。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check probe390_no_such_constant_anywhere.

(* * ** Controls: every 常值 negatives name, outside any [Fail] （已译） *)

Check @Sent.
Check @s_var.
Check @s_top.
Check @s_and.
Check @s_imp.
Check @Theo.
Check @Entails.
Check @ent_refl.
Check @ent_cut.
Check @ent_ax.
Check @ent_top.
Check @ent_pair.
Check @ent_fst.
Check @ent_snd.
Check @ent_curry.
Check @ent_eval.
Check @entails_PreOrder.
Check @Lind.
Check @lind_thin.
Check @lind_any_Faithful.
Check @Lind_Terminal.
Check @Lind_Cartesian.
Check @lind_uncurry.
Check @Lind_Closed.
Check @sdenote.
Check @ent_soundness.
Check @LindSound.
Check @LindSound_Faithful.
Check @entails_weaken.
Check @LindWeaken.
Check @sv.
Check @T_empty.
Check @T_mp.
Check @T_all.
Check @not_entails_empty.
Check @entails_mp.
Check @empty_sub_mp.
Check @empty_sub_all.
Check @weaken_not_Full.
Check @no_full_functor_empty_to_all.
Check @no_equivalence_empty_to_all.
Check @sound_not_Full.
Check @sound_misses_False.
Check @sound_not_EssentiallySurjective.

(* Donor constants named by the negatives. *)
Check @Proset.
Check @Category.
Check @terminal_obj.
Check @product_obj.
Check @exponent_obj.
Check @eval.
Check @Thin.
Check @Full.
Check @EssentiallySurjective.
Check @EquivalenceOfCategories.
Check @Props.
Check @Relation_Definitions.relation.
Check @RelationClasses.PreOrder.

(* * ** N1, N2: hom = 证明 identification, donor （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseProbe.

Universe lo lh lp.
Constraint lh < lp.

Context (Vu : Type@{lo}) (Tu : Theo@{lo lp} Vu).

(* Controls: 范畴, 对象 hom all elaborate here. （已译） *)
Check (Lind Tu : Category@{lo lh lh}).
Check (obj[Lind Tu]).
Check (fun p q : Sent@{lo} Vu => p ~{Lind Tu}~> q).

(* N1 (FORMABILITY): "Cannot enforce lh = lp because lh < lp". *)
Fail Check (Lind Tu : Category@{lo lh lp}).

Context (Au : Type@{lo}) (Ru : Relation_Definitions.relation Au)
        (Pu : RelationClasses.PreOrder Ru).

(* 相关说明。 （已译） *)
Check (Proset Pu : Category@{lo lh lh}).

(*
   本节说明 ProbeLindenbaum390 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Proset Pu : Category@{lo lh lp}).

End UniverseProbe.

(* 相关说明。 （已译） *)

(* The target's design note says Type-valued entailment would not fit
 [Proset], whose 关系 论元 stdlib [relation A]. Here is
 Type-valued one, rejection. （已译） *)

Inductive TEnt {V : Type} (T : Theo V) : Sent V -> Sent V -> Type :=
  | tent_refl p : TEnt p p
  | tent_cut p q r : TEnt p q -> TEnt q r -> TEnt p r.

(* Controls: Prop-valued one IS stdlib 关系, the
 Type-valued one does elaborate family. （已译） *)
Check (Entails T_empty : Relation_Definitions.relation (Sent bool)).
Check (TEnt T_empty).

(*
   本节说明 ProbeLindenbaum390 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe390_tent_relation :
  Relation_Definitions.relation (Sent bool) := TEnt T_empty.

(** ** N4, N5: two typing rejections *)

Section TypingProbe.

Context {V : Type} (T : Theo V) (p q r : Sent V).

(* Control: product 对象 right structure supplied. （已译） *)
Check (@product_obj (Lind T) (Lind_Cartesian T) p q).

(*
   本节说明笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@product_obj (Lind T) (Lind_Terminal T) p q).

End TypingProbe.

(* Control: the derivation exists at its own theory. *)
Check (entails_mp : Entails T_mp (sv true) (sv false)).

(* N5 (TYPING): derivation at [T_mp] not one at [T_empty]. The
 theory INDEX hom-type, so 这是 type mismatch and
 not unification report. （已译） *)
Fail Check (entails_mp : Entails T_empty (sv true) (sv false)).

(* 相关说明。 （已译） *)

(* Control: each category is convertible with itself. *)
Definition probe390_lind_self : Lind T_empty = Lind T_empty := eq_refl.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe390_two_theories :
  Lind T_empty = Lind T_mp := eq_refl.

Section OrientationProbe.

Context {V : Type} (T : Theo V) (p q : Sent V).

(* Control: Mac Lane's q ^ p IS "p implies q". *)
Definition probe390_exp_orientation :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition probe390_exp_flipped :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp q p := eq_refl.

(* Control: [eval] IS [lind_uncurry] at 恒等 derivation, it
 ≈-equal evaluation RULE, since 范畴 thin. （已译） *)
Definition probe390_eval_unfold :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = lind_uncurry (ent_refl T (s_imp p q)) := eq_refl.

Definition probe390_eval_equiv :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    ≈ ent_eval T p q := lind_thin T _ _ _ _.

(* 相关说明。 （已译） *)
Fail Definition probe390_eval_strict :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = ent_eval T p q := eq_refl.

End OrientationProbe.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example probe390_weaken_reduces (p : Sent bool) :
  entails_weaken empty_sub_mp (ent_refl T_empty p) = ent_refl T_mp p
  := eq_refl.

Example probe390_weaken_fmap (p q : Sent bool) (f : Entails T_empty p q) :
  fmap[LindWeaken empty_sub_mp] f = entails_weaken empty_sub_mp f
  := eq_refl.

(* 相关说明。 （已译） *)

(* Product is conjunction, terminal is truth, exponential is
   implication — at Leibniz equality of objects. *)
Example probe390_structure {V} (T : Theo V) (p q : Sent V) :
  (@terminal_obj (Lind T) (Lind_Terminal T) = s_top)
  * (@product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q)
  * (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
       = s_imp p q)
  := (eq_refl, eq_refl, eq_refl).

(* The 范畴 thin, so transpose unique free. （已译） *)
Example probe390_thin {V} (T : Theo V) : Thin (Lind T) := lind_thin T.

(* Two axiom sets, two 范畴: derivable one side, refuted on
 other, no full 函子 between them. （已译） *)
Example probe390_derivable : Entails T_mp (sv true) (sv false) :=
  entails_mp.

Example probe390_underivable :
  Entails T_empty (sv true) (sv false) -> False := not_entails_empty.

Example probe390_not_full :
  Full (LindWeaken empty_sub_mp) -> False := weaken_not_Full.

Example probe390_no_equiv (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False := no_equivalence_empty_to_all F.

(* The comparison Props: 函子 preserving 1, × ^ the
 nose, faithful, but neither full nor 本质满射. （已译） *)
Example probe390_sound_functor : Lind T_empty ⟶ Props :=
  LindSound T_empty val_true val_true_empty.

Example probe390_sound_faithful : Faithful (LindSound T_empty val_true
  val_true_empty) := LindSound_Faithful T_empty val_true val_true_empty.

Example probe390_sound_not_full :
  Full (LindSound T_empty val_true val_true_empty) -> False :=
  sound_not_Full.

Example probe390_sound_not_eso :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False := sound_not_EssentiallySurjective.
