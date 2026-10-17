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

(** * The symmetric monoidal structure on the free PROP *)

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

(** ** Braid involution

    The [braid_invol] field of [SymmetricMonoidal] at [x y]: the
    composite [σ_{y,x} ⊙ σ_{x,y} : x + y ⇒ x + y] is the identity.
    This is the primitive constructor [TE_braid_invol] applied at
    [m := x], [n := y]. *)

Lemma free_braid_invol (x y : nat) :
  TermEq S (T_comp (T_braid y x) (T_braid x y)) (T_id (x + y)).
Proof.
  apply TE_braid_invol.
Qed.

(** ** THE SymmetricMonoidal record on [FreeCat S]

    [symmetric_is_braided] names the ONE braided record
    [FreeCat_Braided S] (hence, through it, the ONE shared [Monoidal]
    record [FreeCat_Monoidal S]); the involution proof is the
    standalone lemma above.  Every field is explicit, so no Program
    obligations are generated. *)

Program Definition FreeCat_Symmetric : @SymmetricMonoidal (FreeCat S) := {|
  symmetric_is_braided := FreeCat_Braided S;
  braid_invol := fun x y => free_braid_invol x y
|}.

End FreeSymmetric.

Arguments FreeCat_Symmetric S : assert.
