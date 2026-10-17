Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(* * * The special initial-对象 定理 at two generic 范畴 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/well-powered+category

   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Definition Subsets_Cogenerator_empty@{o u +} (X : SetoidObject@{o o}) :
  Cogenerator (Subsets@{o u} X) :=
  @Build_Cogenerator (Subsets@{o u} X) Empty_set
    (fun e => match e with end) (fun _ _ _ _ _ => I).

Definition Subsets_Cogenerator_bot@{o u +} (X : SetoidObject@{o o}) :
  Cogenerator (Subsets@{o u} X) :=
  @Build_Cogenerator (Subsets@{o u} X) unit
    (fun _ => (subset_bot : obj[Subsets@{o u} X])) (fun _ _ _ _ _ => I).

Definition Subsets_special_initial@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @Initial (Subsets@{o u} X) :=
  special_initial_object_wellpowered (Subsets_WellPowered@{o u t} X)
    (Subsets_Complete_free X : @Complete@{so so u o} (Subsets@{o u} X)) G.

Example Subsets_special_initial_obj@{o u t so d +|
    o <= u, u < t, u <= so, u < d +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @initial_obj _ (Subsets_special_initial X G)
    = Subobject.sub_dom
        (complete_intersection
           (Subsets_Complete_free X : @Complete@{so so u o} (Subsets@{o u} X))
           (wp_class_family
              (Subsets_WellPowered@{o u t} X
                 (cogen_prod@{so d so o u}
                    (Subsets_Complete_free X
                     : @Complete@{so so u o} (Subsets@{o u} X)) G))
              (fun _ => True))) :=
  eq_refl.

Definition Subsets_special_initial_empty@{o u t +| o <= u, u < t +}
  (X : SetoidObject@{o o}) : @Initial (Subsets@{o u} X) :=
  Subsets_special_initial X (Subsets_Cogenerator_empty X).

Definition Subsets_special_initial_bot@{o u t +| o <= u, u < t +}
  (X : SetoidObject@{o o}) : @Initial (Subsets@{o u} X) :=
  Subsets_special_initial X (Subsets_Cogenerator_bot X).

Definition Subsets_special_vs_bot@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X)) :
  @initial_obj _ (Subsets_special_initial X G)
    ≅ @initial_obj _ (Subsets_Initial (X:=X)) :=
  initial_unique _ _.

Lemma Subsets_special_initial_is_empty@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X))
  (x : carrier X) :
  (@initial_obj _ (Subsets_special_initial X G)
     : carrier (Powerset_Prop_obj X)) x → False.
Proof.
  intro Hx.
  destruct (to (Subsets_special_vs_bot X G) x Hx) as [i _]; destruct i.
Qed.

Lemma Subsets_special_initial_not_top@{o u t so +| o <= u, u < t, u <= so +}
  (X : SetoidObject@{o o}) (G : Cogenerator@{so o u} (Subsets@{o u} X))
  (x : carrier X) :
  ((subset_top : obj[Subsets@{o u} X])
     ~{Subsets@{o u} X}~> @initial_obj _ (Subsets_special_initial X G))
  → False.
Proof.
  intro k.
  exact (Subsets_special_initial_is_empty X G x
           (k x (fun i => match i with end))).
Qed.

(* * ** An indiscrete 范畴 types （已译） *)

Definition Indiscrete_Cogenerator_empty@{o h +} (A : Type@{o}) :
  Cogenerator (Indiscrete@{o h h} A) :=
  @Build_Cogenerator (Indiscrete@{o h h} A) Empty_set
    (fun e => match e with end)
    (fun x y f g _ => match f, g with tt, tt => eq_refl end).

Definition Indiscrete_types_special_initial@{j o t +| j < o, j < t +} :
  @Initial (Indiscrete@{o j j} Type@{j}) :=
  special_initial_object_wellpowered
    (Indiscrete_WellPowered@{o j Set o t} Type@{j})
    (Indiscrete_Complete@{j j j o} (Datatypes.unit : Type@{j}))
    (Indiscrete_Cogenerator_empty Type@{j}).

Example Indiscrete_types_special_initial_obj@{j o t +| j < o, j < t +} :
  @initial_obj (Indiscrete@{o j j} Type@{j}) Indiscrete_types_special_initial
    = (Datatypes.unit : Type@{j}) :=
  eq_refl.
