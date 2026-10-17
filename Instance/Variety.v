Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(* * * The 范畴 algebras variety （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/algebraic+theory
 Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Variety 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Variety.

Context (S : UA.OpSignature).
Context (E : UA.EqSignature S).

(* 相关说明。 （已译） *)

(*
   本节说明 Variety 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition satisfies (A : UA.OpAlgebra S) : Type :=
  ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.carrier A),
    UA.lhs e args = UA.rhs e args.

Definition Variety_sub : Subcategory (@UA.Algs S) :=
  @Build_Subcategory (@UA.Algs S)
    satisfies
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Variety : Category := Sub (@UA.Algs S) Variety_sub.

(* Full: every homomorphism between algebras satisfy laws a
 态射 variety. （已译） *)
Definition Variety_Full : Full (@UA.Algs S) Variety_sub :=
  fun _ _ _ _ _ => I.

Definition Variety_Incl : Variety ⟶ @UA.Algs S := Incl (@UA.Algs S) Variety_sub.

Definition Variety_Incl_Faithful : Functor.Faithful Variety_Incl :=
  Incl_Faithful (@UA.Algs S) Variety_sub.

(* The 含入 FULL 函子, not merely full subcategory:
 Construction/Subcategory.v already turns one 进入 other, and
 audit pointed out costs one line. （已译） *)
Definition Variety_Incl_Full : Functor.Full Variety_Incl :=
  Full_Implies_Full_Functor (@UA.Algs S) Variety_sub Variety_Full.

(* 相关说明。 （已译） *)

Definition Variety_pack (A : UA.Algebra S E) : Variety :=
  (UA.alg S E A; UA.equations S E A).

Definition Variety_unpack (x : Variety) : UA.Algebra S E :=
  {| UA.alg := `1 x ; UA.equations := `2 x |}.

(* Propositional [=] packed OBJECT data — sanctioned case; no
 态射 equality asserted. （已译） *)

Lemma Variety_unpack_pack (A : UA.Algebra S E) :
  Variety_unpack (Variety_pack A) = A.
Proof. destruct A; reflexivity. Qed.

Lemma Variety_pack_unpack (x : Variety) :
  Variety_pack (Variety_unpack x) = x.
Proof. destruct x; reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Variety_Forget : Variety ⟶ Sets := {|
  fobj := fun A => {| carrier   := UA.carrier (`1 A)
                    ; is_setoid := eq_Setoid (UA.carrier (`1 A)) |};
  fmap := fun _ _ f => {| morphism := UA.map (`1 f) |}
|}.

Lemma Variety_Forget_Faithful : Functor.Faithful Variety_Forget.
Proof. construct; simpl in *; auto. Qed.

End Variety.

(*
   本节说明 Variety 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments satisfies {_} _ _.
Arguments Variety_sub {_} _.
Arguments Variety {_} _.
Arguments Variety_Full {_} _.
Arguments Variety_Incl {_} _.
Arguments Variety_Incl_Faithful {_} _.
Arguments Variety_pack {_ _} _.
Arguments Variety_unpack {_ _} _.
Arguments Variety_unpack_pack {_ _} _.
Arguments Variety_pack_unpack {_ _} _.
Arguments Variety_Forget {_} _.
Arguments Variety_Forget_Faithful {_} _.

(*
   本节说明 Variety 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition GroupVariety : Category := Variety UA.GroupEq.

(* ℤ/2 under exclusive or, witness Instance/Comp.v already builds,
 OBJECT 范畴 rather than inhabitant type. （已译） *)
Definition GroupVariety_Bool : GroupVariety := Variety_pack UA.Bool.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive magma_op : Set := magma_mul.

Definition MagmaOp : UA.OpSignature :=
  {| UA.operation := magma_op ; UA.arity := fun _ => UA.binary |}.

Inductive comm_eq : Set := comm_law.

Definition comm_swap (i : UA.binary) : UA.binary :=
  match i with UA.Fst => UA.Snd | UA.Snd => UA.Fst end.

Definition CommEq : UA.EqSignature MagmaOp.
Proof.
  refine {| UA.eq       := comm_eq
          ; UA.eq_arity := fun _ => UA.binary
          ; UA.lhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul args
          ; UA.rhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul (fun i => args (comm_swap i))
         |}.
  - intros A B f [] args; exact (UA.op_commute A B f magma_mul args).
  - intros A B f [] args;
      exact (UA.op_commute A B f magma_mul (fun i => args (comm_swap i))).
Defined.

Definition CommMagmaVariety : Category := Variety CommEq.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive invinv_eq : Set := invinv.

Definition InvInvEq : UA.EqSignature UA.GroupOp.
Proof.
  refine {| UA.eq       := invinv_eq
          ; UA.eq_arity := fun _ => UA.unary
          ; UA.lhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             UA.inv' (UA.inv' (args UA.Only))
          ; UA.rhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             args UA.Only
         |}.
  - intros A B f [] args.
    unfold UA.inv'.
    rewrite UA.op_commute.
    apply (f_equal (fun z => UA.op B UA.inv (fun _ : UA.unary => z))).
    exact (UA.op_commute A B f UA.inv (fun _ => args UA.Only)).
  - intros A B f [] args; reflexivity.
Defined.

Definition InvInvVariety : Category := Variety InvInvEq.

(*
   本节说明Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
