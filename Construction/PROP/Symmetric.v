Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Braided.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeSymmetric.

Context (S : Signature).

Open Scope nat_scope.

(*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_braid_invol (x y : nat) :
  TermEq S (T_comp (T_braid y x) (T_braid x y)) (T_id (x + y)).
Proof.
  apply TE_braid_invol.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition FreeCat_Symmetric : @SymmetricMonoidal (FreeCat S) := {|
  symmetric_is_braided := FreeCat_Braided S;
  braid_invol := fun x y => free_braid_invol x y
|}.

End FreeSymmetric.

Arguments FreeCat_Symmetric S : assert.
