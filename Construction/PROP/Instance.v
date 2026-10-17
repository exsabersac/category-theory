Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.Quotient.

From Coq Require Import Arith.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreePROP.

Context (S : Signature).

Open Scope nat_scope.

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreePROP : PROP := {|
  prop_cat       := FreeCat S;
  prop_strict    := FreeCat_Strict S;
  prop_symmetric := FreeCat_Symmetric S;

  (* 相关说明。 （已译） *)
  prop_monoidal_coherence := eq_refl;

  (* 相关说明。 （已译） *)
  prop_of_nat := fun n : nat => n;

  (* [I] of [FreeCat_Monoidal S] is the literal [0]. *)
  prop_unit_zero := eq_refl;

  (* [fobj (FreeCat_Tensor S) (m, n)] reduces to [m + n]. *)
  prop_tensor_plus := fun m n => eq_refl
|}.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Instance FreeCat_HomEqProp : HomEqProp (FreeCat S) :=
  Build_HomEqProp (FreeCat S)
    (fun m n : nat => @TermEq S m n)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(** Objects of [FreeCat S] are [nat], whose equality is decidable. *)

#[export] Instance FreeCat_ObjDecEq : ObjDecEq (FreeCat S) := Nat.eq_dec.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、（余）极限、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example FreePROP_coherence_is_refl :
  @prop_monoidal_coherence FreePROP = eq_refl := eq_refl.

(** The 对象 correspondence 恒等 [nat]. （已译） *)
Example FreePROP_of_nat_id (n : nat) :
  @prop_of_nat FreePROP n = n := eq_refl.

(** The monoidal unit literal 对象 [0]. （已译） *)
Example FreePROP_I :
  @I _ (@strict_is_monoidal _ (@prop_strict FreePROP)) = 0%nat := eq_refl.

(** Tensor-on-对象 literally addition, [eq_refl] 证明. （已译） *)
Example FreePROP_tensor_plus_is_refl (m n : nat) :
  @prop_tensor_plus FreePROP m n = eq_refl := eq_refl.

(** [PROP.v]'s successor decomposition [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧] applies to
    [FreePROP]; whichever [Monoidal] path its statement was elaborated
    through, conversion closes the gap here, because both paths project
    the one shared record. *)
Example FreePROP_of_nat_S_smoke (n : nat) :
  @prop_of_nat FreePROP (Datatypes.S n)
  = ((@prop_of_nat FreePROP 1)
       ⨂[@strict_is_monoidal _ (@prop_strict FreePROP)]
     (@prop_of_nat FreePROP n))%object :=
  prop_of_nat_S FreePROP n.

End FreePROP.

Arguments FreePROP S : assert.
