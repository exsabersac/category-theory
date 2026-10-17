Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/free+group

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The element of a group as a map out of the singleton *)

(* The constant map at [x], read into [Sets] through [Grp_Forget].  This
   is the transpose across the free/forgetful adjunction of the
   homomorphism that picks out [x].  Built by [refine] rather than as a
   [Program Definition] because under the universe annotation the
   respectfulness obligation is not discharged before the constant is
   registered, and the next proof's reference to it is then rejected with
   "The variable grp_point was not found in the current environment".
   It must also stay TRANSPARENT: closed with [Qed] instead, the
   separation proof stops at the [assert] of the generator equation,
   whose [exact (free_grp_extend_generators …)] is refused because the
   hypothesis has frozen as
   [f (grp_mul G (grp_unit G) (grp_point x ttt)) ≈ …] with nothing left
   to reduce (an earlier revision of this sentence placed the stop at the
   final [exact], which is never reached; measured on a full copy). *)
Definition grp_point@{o so+} {G : Grp@{so o}} (x : carrier G) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Grp_Forget G.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation *)

Lemma Grp_free_one_separates@{o so+} :
  @IsSeparator Grp@{so o} (FreeGrpObject unit_setoid_object@{o o}).
Proof.
  intros G K f g Hk x.
  pose (e := @free_grp_extend unit_setoid_object@{o o} G (grp_point x)).
  pose proof (Hk e (fg_insert unit_setoid_object@{o o} ttt)) as E.
  simpl in E.
  assert (Ex : e (fg_insert unit_setoid_object@{o o} ttt) ≈ x)
    by exact (free_grp_extend_generators unit_setoid_object@{o o} G
                (grp_point x) ttt).
  rewrite <- (proper_morphism (grp_map f) _ _ Ex).
  rewrite <- (proper_morphism (grp_map g) _ _ Ex).
  exact E.
Qed.

(* Awodey's example as a one-object generating family. *)
Definition Grp_Generator@{o so+} : Generator Grp@{so o} :=
  @Generator_of_separator Grp@{so o}
    (FreeGrpObject unit_setoid_object@{o o}) Grp_free_one_separates.
