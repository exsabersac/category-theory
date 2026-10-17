Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(** * The General Adjoint Functor Theorem, run at [Sets] *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The three premises *)

(* [Id] is a right adjoint -- to itself, by [adj_id] -- so the general bridge
   of Construction/Comma/Limit.v supplies its cone-level preservation. *)
Definition Sets_Id_PreservesImageLimit : @PreservesImageLimit Sets Sets Id :=
  right_adjoint_PreservesImageLimit (@adj_id Sets).

(*
   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_Id_SolutionSet (d : Sets) : SolutionSet (@Id Sets) d.
Proof.
  unshelve refine (@Build_SolutionSet Sets Sets (@Id Sets) d
                     poly_unit
                     (fun _ : poly_unit => d)
                     (fun _ : poly_unit => @id Sets d)
                     _).
  intros c h.
  exists ttt.
  exists h.
  exact (id_right h).
Defined.

(** ** The application *)

(*
   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GAFT_at_Sets_Id : { F : Sets ⟶ Sets & F ⊣ Id } :=
  GAFT (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_SolutionSet.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GAFT_at_Sets_Id_is_Id : projT1 GAFT_at_Sets_Id ≈ @Id Sets :=
  left_adjoint_iso (@Id Sets) (projT1 GAFT_at_Sets_Id) (@Id Sets)
    (projT2 GAFT_at_Sets_Id) (@adj_id Sets).

(** ** By-product: equalizers in [Sets] *)

(* Read off completeness by [Complete_HasEqualizers]; NOT the first and not
   the only inhabitant -- see the note below.  Kept a [Definition]. *)
Definition Sets_HasEqualizers : HasEqualizers Sets :=
  Complete_HasEqualizers Sets_Complete.

(*
   本节说明伴随、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The characterization at [Sets], and that its reverse half is the
       application already here *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition GAFT_iff_at_Sets_Id :
  { F : Sets ⟶ Sets & F ⊣ Id }
    ↔ (@PreservesImageLimit Sets Sets Id * (∀ d : Sets, SolutionSet (@Id Sets) d))
  := GAFT_iff (@Id Sets) Sets_Complete.

Definition Sets_Id_has_left : { F : Sets ⟶ Sets & F ⊣ Id } :=
  snd GAFT_iff_at_Sets_Id (Sets_Id_PreservesImageLimit, Sets_Id_SolutionSet).

Definition Sets_Id_has_left_is_GAFT_at_Sets_Id :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

(* The manufactured family at [Id], and its agreement with the hand-built
   one at each of the three data fields. *)

Definition Sets_Id_SolutionSet_of_adjunction (d : Sets) : SolutionSet (@Id Sets) d :=
  solution_set_of_adjunction (@adj_id Sets) d.

Definition Sets_Id_sols_index (d : Sets) :
  sol_index (Sets_Id_SolutionSet_of_adjunction d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Definition Sets_Id_sols_obj (d : Sets) (i : poly_unit) :
  sol_obj (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_obj (Sets_Id_SolutionSet d) i := eq_refl.

Definition Sets_Id_sols_arr (d : Sets) (i : poly_unit) :
  sol_arr (Sets_Id_SolutionSet_of_adjunction d) i
    = sol_arr (Sets_Id_SolutionSet d) i := eq_refl.
