Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.

Generalizable All Variables.

(* * * The currying 伴随 [Sets], where counit computes （已译） *)

(*
 Book: Riehl, "Category Theory in Context", Dover 2016; §2.1

   本文件给出伴随实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* The counit currying 伴随 at [Sets], named type
 ascribed so applications it elaborate without further hints. （已译） *)
Definition Sets_counit (S y : Sets) : (y ^ S) × S ~{Sets}~> y :=
  @counit _ _ _ _ (Curry_Adjunction S) y.

(* It is evaluation, as the general theory already says. *)
Lemma Sets_counit_eval (S y : Sets) : Sets_counit S y ≈ eval.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma Sets_counit_apply (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) ≈ h s.
Proof. reflexivity. Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_counit_apply_eq
  (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) = h s.
Proof. reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_curry_apply
  (S x y : Sets) (f : x × S ~{Sets}~> y) (a : carrier x) (s : carrier S) :
  f (a, s) ≈ curry f a s.
Proof. reflexivity. Qed.

Lemma Sets_uncurry_apply
  (S x y : Sets) (g : x ~{Sets}~> y ^ S) (p : carrier (x × S)) :
  g (fst p) (snd p) ≈ uncurry g p.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition NatSet : Sets := {|
  carrier   := nat;
  is_setoid := {| equiv := fun n m : nat => n = m |}
|}.

(* Addition, as a morphism NatSet × NatSet ~> NatSet of [Sets]: a genuinely
   non-identity, non-projection arrow. *)
Program Definition plus_map : NatSet × NatSet ~{Sets}~> NatSet := {|
  morphism := fun p => (fst p + snd p)%nat
|}.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example curry_plus_compute : curry plus_map 2%nat 3%nat = 5%nat.
Proof. reflexivity. Qed.

(* The counit 所消耗 transpose again: it applies curry plus_map 2, that
 (m ↦ 2 + m), 3. Again equality elements [nat]. （已译） *)
Example counit_plus_compute :
  Sets_counit NatSet NatSet (curry plus_map 2%nat, 3%nat) = 5%nat.
Proof. reflexivity. Qed.

(* The round trip hom-set bijection concrete arrow. Here the
 comparison IS between 态射 [Sets], so it stated ≈. （已译） *)
Example uncurry_curry_plus : uncurry (curry plus_map) ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.

(* The same round trip taken through 伴随's own transposes, using
 general law ⌈⌊f⌋⌉ ≈ f Theory/Adjunction.v. （已译） *)
Example adj_roundtrip_plus :
  from (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet)
       (to (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet) plus_map)
    ≈ plus_map.
Proof.
  exact (@to_adj_comp_law _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet
                          plus_map).
Qed.

(* And 普遍性质 elementary form: evaluation after the
 transpose recovers original arrow. （已译） *)
Example eval_curry_plus :
  eval ∘ first (curry plus_map) ≈ plus_map.
Proof. exact (ump_exponents plus_map). Qed.

(* 相关说明。 （已译） *)
Example curry_plus_not_constant :
  (curry plus_map 2%nat ≈ curry plus_map 0%nat) -> False.
Proof.
  intros HA.
  specialize (HA 0%nat).
  simpl in HA.
  discriminate.
Qed.

(* 相关说明。 （已译） *)

(* The functor Hom(− × A, B) : Sets^op ⟶ Sets ... *)
Definition Sets_Curry_Presheaf (A B : Sets) : Sets^op ⟶ Sets :=
  Curry_Presheaf A B.

(* ... is represented by B^A, the setoid of ≈-respecting maps A → B. *)
Definition Sets_Curry_Representable (A B : Sets) :
  Representable (Sets_Curry_Presheaf A B) := Curry_Representable A B.

(* On concrete witness: representation carries transpose of
 addition back addition itself, ≈ between 态射 [Sets]. （已译） *)
Example Sets_repr_plus :
  transform (to (Curry_Representation NatSet NatSet)) NatSet (curry plus_map)
    ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sets_prod_preserves_colimits (X : Sets) :
  PreservesAllColimits (Prod_Functor X) :=
  @left_adjoint_preserves_colimits _ _ _ _ (Curry_Adjunction X).

(* And same 推论 over arbitrary 笛卡尔闭 范畴, since
 伴随 was established there. （已译） *)
Definition CCC_prod_preserves_colimits
  {C : Category} `{@Cartesian C} `{@Closed C _} (S : C) :
  PreservesAllColimits (Prod_Functor S) :=
  @left_adjoint_preserves_colimits _ _ _ _ (Curry_Adjunction S).
