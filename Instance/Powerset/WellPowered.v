Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(** * The intersection theorem at the powerset lattice of a setoid *)

(*
 nLab:      https://ncatlab.org/nlab/show/power+set
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Subsets_Complete_free@{o u +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o u} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_WellPowered@{o u t | o <= u, u < t +}
  (X : SetoidObject@{o o}) : WellPowered@{o u u u t} (Subsets@{o u} X) :=
  trivial_small _.

(* The consequence at [Subsets X], for a [Prop]-class of subobjects. *)
Definition Subsets_has_intersections@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) (P : SubObj S → Prop)
  (HP : ∀ m m' : SubObj S, m ≈ m' → P m → P m') :
  { w : SubObj S &
    IsIntersection (fun k : { m : SubObj S & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections_prop
    (Subsets_WellPowered X) (Subsets_Complete_free X) S P HP.

(* The class of all subobjects. *)
Definition Subsets_intersection_all@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) :
  { w : SubObj S & IsIntersection (fun m : SubObj S => m) w } :=
  wellpowered_complete_intersection_all
    (Subsets_WellPowered X) (Subsets_Complete_free X) S.

(* The empty subset, as a subobject of the full one.  Every arrow of
   [Subsets X] is monic, the category being thin. *)
Definition subsets_sub_bot@{o u +} (X : SetoidObject@{o o}) :
  @SubObj (Subsets@{o u} X) subset_top :=
  {| sub_dom := (subset_bot : obj[Subsets@{o u} X]);
     sub_mono := (subset_bot_least subset_top
                    : subset_bot ~{Subsets@{o u} X}~> subset_top);
     sub_is_monic := @Build_Monic (Subsets@{o u} X) _ _
                       (subset_bot_least subset_top) (fun _ _ _ _ => I) |}.

(* Non-degeneracy: at a pointed [X], the intersection of all subobjects of
   the full subset lies below [subsets_sub_bot], so it is not the top. *)
Lemma Subsets_intersection_all_not_top@{o u +} (X : SetoidObject@{o o})
  (x : carrier X) :
  `1 (Subsets_intersection_all X (subset_top : obj[Subsets@{o u} X]))
    ≈ sub_top → False.
Proof.
  intros [iso _].
  destruct (inter_le _ _
              (`2 (Subsets_intersection_all X
                     (subset_top : obj[Subsets@{o u} X])))
              (subsets_sub_bot X)) as [k _].
  destruct (k x (from iso x (fun i => match i with end))) as [i _].
  destruct i.
Qed.
