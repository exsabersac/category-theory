Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Constant.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/global+element
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   本文件给出函子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT T}.
Context `{@Constant D DT T}.

Class ConstantFunctor := {
  unmap_one : F 1 ~{D}~> 1;     (* unit comparison: F of C's `1` into D's `1` *)

  (* host-object comparison: D-side `constant_obj x` into F of the C-side one *)
  map_const {x : T} : constant_obj T x ~> F (constant_obj T x);

  (* 相关说明。 （已译） *)
  fmap_constant (x : T) :
    fmap (constant x) ≈ @map_const x ∘ constant x ∘ unmap_one;
}.

End ConstantFunctor.
