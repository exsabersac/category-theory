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

(** * The free PROP, bundled: the library's first inhabited [PROP] *)

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

  (* [strict_is_monoidal (FreeCat_Strict S)] and
     [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]
     both reduce to the literal term [FreeCat_Monoidal S]. *)
  prop_monoidal_coherence := eq_refl;

  (* Objects of [FreeCat S] are literally the naturals. *)
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

(** ** Machine-checked sanity

    Each [Example] holds by [eq_refl], witnessing that the
    corresponding field of [FreePROP] is definitional. *)

(*
   本节说明幺半结构、（余）极限、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example FreePROP_coherence_is_refl :
  @prop_monoidal_coherence FreePROP = eq_refl := eq_refl.

(** The object correspondence is the identity on [nat]. *)
Example FreePROP_of_nat_id (n : nat) :
  @prop_of_nat FreePROP n = n := eq_refl.

(** The monoidal unit is the literal object [0]. *)
Example FreePROP_I :
  @I _ (@strict_is_monoidal _ (@prop_strict FreePROP)) = 0%nat := eq_refl.

(** Tensor-on-objects is literally addition, with [eq_refl] proof. *)
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
