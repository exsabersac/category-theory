(*
   本文件为测试：ProbeFunnyPoly。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Monoidal.

(** A rigid member level [v], with outer levels [i] (StrictCat's objects) and
    [j] strictly above it, as StrictCat's universe constraints require. *)
Monomorphic Universe i j v.
Monomorphic Constraint v < i.
Monomorphic Constraint v < j.

(** ** Positive control: everything up to the unitors is fine at level [v].

    The partial application supplies the carrier, the unit object and the
    tensor, so the failures below are not caused by [StrictCat], [_1] or
    [FunnyTensor] at member level [v]. *)
Definition probe_tensor_ok :=
  @Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor.

(** ** The reproduction: the unitor field is where [Set] is enforced.

    Error: The term "Funny_unit_left@{_ v}" has type "1 □ x ≅ x"
    while it is expected to have type "fobj[FunnyTensor@{..}] (1, x) ≅ x"
    (universe inconsistency: Cannot enforce Set = v). *)
Fail Check (@Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor
              (fun x : Category@{v v v} => @Funny_unit_left x)).

(** ** The compiled instance is pinned: it does not transport to level [v].

    Error: The term "Funny_Monoidal" has type "Monoidal@{i Set}"
    while it is expected to have type "Monoidal@{i v}"
    (universe inconsistency: Cannot enforce Set = v). *)
Fail Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i v j v v}).

(** ** Positive control: [Funny_Monoidal] is a well-formed [Monoidal] at its
    own universe level.  This pins the two [Fail]s above to the specific
    [Set = v] universe conflict rather than to a malformed term or a renamed
    identifier: the instance exists and type-checks, it simply does not
    transport up to level [v].  Without this control a [Fail] would pass on
    any error at all. *)
Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i Set j Set Set}).
