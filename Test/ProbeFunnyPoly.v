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

(** A rigid member level [v], outer levels [i] (StrictCat's 对象) and
 [j] strictly above it, StrictCat's universe constraints require. （已译） *)
Monomorphic Universe i j v.
Monomorphic Constraint v < i.
Monomorphic Constraint v < j.

(*
   本节说明 ProbeFunnyPoly 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_tensor_ok :=
  @Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor.

(* 相关说明。 （已译） *)
Fail Check (@Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor
              (fun x : Category@{v v v} => @Funny_unit_left x)).

(* 相关说明。 （已译） *)
Fail Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i v j v v}).

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i Set j Set Set}).
