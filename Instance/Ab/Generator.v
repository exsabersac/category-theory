Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/free+abelian+group

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The element of an abelian group as a map out of the singleton *)

(* The constant map at [x], read into [Sets] through [Ab_Forget].  Built
   by [refine] for the same reason as Instance/Grp/Generator.v's
   [grp_point]: under the universe annotation the [Program] form does not
   register the constant before the obligation is met.  It must stay
   TRANSPARENT: closed with [Qed] the separation proof is refused with
   "The term "Hk (free_ab_extend (ab_point x)) (fa_gen ttt)" has type
   "(f ∘ free_ab_extend (ab_point x)) (fa_gen ttt) ≈ …" while it is
   expected to have type "f x ≈ g x"", a CONVERSION refusal. *)
Definition ab_point@{o so+} {A : Ab@{so o}} (x : carrier (cmon_setoid A)) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Ab_Forget A.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation *)

Lemma Ab_free_one_separates@{o so+} :
  @IsSeparator Ab@{so o} (FreeAbObject unit_setoid_object@{o o}).
Proof.
  intros A B f g Hk x.
  exact (Hk (@free_ab_extend unit_setoid_object@{o o} A (ab_point x))
           (@fa_gen unit_setoid_object@{o o} ttt)).
Qed.

(* Mac Lane's second example as a one-object generating family. *)
Definition Ab_Generator@{o so+} : Generator Ab@{so o} :=
  @Generator_of_separator Ab@{so o}
    (FreeAbObject unit_setoid_object@{o o}) Ab_free_one_separates.
