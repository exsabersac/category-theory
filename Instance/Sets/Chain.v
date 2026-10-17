Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Cocomplete.

Generalizable All Variables.

(** * The ω-chain colimit in [Sets] *)

(*
 nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/Direct_limit

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsOmegaColimit.

Context (G : Omega ⟶ Sets).

(** ** The colimit, as an instance of the general witness *)

Definition Sets_Omega_Colimit : Colimit G := Sets_Cocomplete Omega G.

(** ** What the apex and the legs are, by conversion *)

Example Sets_omega_carrier :
  carrier (Sets_colim_obj G) = { n : nat & carrier (G n) }.
Proof. reflexivity. Qed.

Example Sets_omega_inj_at (n : nat) (x : G n) :
  Sets_colim_inj G n x = existT _ n x.
Proof. reflexivity. Qed.

Example Sets_omega_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ Sets_Omega_Colimit) = Sets_colim_obj G.
Proof. reflexivity. Qed.

(** ** Agreeing at a common later stage suffices *)

Lemma omega_colim_of_stage (m n k : nat)
  (p : m ~{Omega}~> k) (q : n ~{Omega}~> k) (x : G m) (y : G n) :
  fmap[G] p x ≈ fmap[G] q y ->
  @equiv _ (Sets_colim_obj G) (existT _ m x) (existT _ n y).
Proof.
  intros H.
  apply (@cr_trans _ G _ (existT _ k (fmap[G] p x))).
  - exact (@cr_glue _ G m k p x).
  - apply (@cr_trans _ G _ (existT _ k (fmap[G] q y))).
    + exact (@cr_point _ G k (fmap[G] p x) (fmap[G] q y) H).
    + exact (@cr_sym _ G _ _ (@cr_glue _ G n k q y)).
Qed.

(* The one-sided special case a reader of "the colimit is the union" wants
   first: an element and its image one step along are already identified. *)
Corollary omega_colim_step (n : nat) (x : G n) :
  @equiv _ (Sets_colim_obj G) (existT _ n x)
    (existT _ (S n) (fmap[G] (omega_step n) x)).
Proof. exact (@cr_glue _ G n (S n) (omega_step n) x). Qed.

End SetsOmegaColimit.

(** ** The initial-algebra chain of an endofunctor of [Sets] *)

Definition Sets_Chain_Colimit (F : Sets ⟶ Sets) : Colimit (Chain F) :=
  Sets_Cocomplete Omega (Chain F).

(* Its apex is the sum of the chain's stages, by conversion. *)
Example Sets_chain_carrier (F : Sets ⟶ Sets) :
  carrier (Sets_colim_obj (Chain F)) = { n : nat & carrier (chain_obj F n) }.
Proof. reflexivity. Qed.

(** * Non-vacuity: the quotient merges something the coproduct keeps apart *)

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OmegaMergeWitness.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition OmegaPoints : Omega ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.

Definition omega_point (n : nat) : carrier (OmegaPoints n) := ttt.

(* MERGED in the colimit: stage 0 and stage 1 are identified, by the glue
   along the generating step [0 ~> 1]. *)
Theorem omega_stages_merged :
  @equiv _ (Sets_colim_obj OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)).
Proof. exact (omega_colim_step OmegaPoints 0%nat (omega_point 0)). Qed.

(*
   本节说明 Chain 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem omega_stages_apart_in_coproduct :
  @equiv _ (Sets_colim_sum OmegaPoints)
    (existT _ 0%nat (omega_point 0)) (existT _ 1%nat (omega_point 1)) -> False.
Proof. intros [e _]; discriminate e. Qed.

End OmegaMergeWitness.
