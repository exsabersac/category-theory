Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section TracedMonoidal.

Context {C : Category}.

(** Traced monoidal category. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Traced_monoidal_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/traced+monoidal+category

   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class TracedMonoidal := {
  (* The underlying symmetric monoidal structure (braiding + symmetry). *)
  traced_is_symmetric : @SymmetricMonoidal C;

  (* Trace / partial trace: contracts the loop object u, Tr^u_{x,y}. *)
  trace {x y u} : x ⨂ u ~> y ⨂ u → x ~> y;

  (* Naturality in x (left tightening): precompose by g ⨂ id outside trace. *)
  trace_natural_in_x {x x' y u} {f : x ⨂ u ~> y ⨂ u} {g : x' ~> x} :
    trace (f ∘ g ⨂ id) ≈ trace f ∘ g;
  (* Naturality in y (right tightening): postcompose by g ⨂ id outside trace. *)
  trace_natural_in_y {x y y' u} {f : x ⨂ u ~> y ⨂ u} {g : y ~> y'} :
    trace (g ⨂ id ∘ f) ≈ g ∘ trace f;
  (* Dinaturality / sliding in u: a loop morphism g may slide around the loop. *)
  trace_natural_in_u {x y u u'} {f : x ⨂ u ~> y ⨂ u'} {g : u' ~> u} :
    trace (id ⨂ g ∘ f) ≈ trace (f ∘ id ⨂ g);

  (* Vanishing I: tracing over the unit object leaves f unchanged. *)
  vanishing_unit {x y} {f : x ~> y} :
    trace (unit_right⁻¹ ∘ f ∘ unit_right) ≈ f;
  (* Vanishing ⨂: a trace over u ⨂ v is two nested traces over u then v. *)
  vanishing_tensor {x y u v} {f : x ⨂ (u ⨂ v) ~> y ⨂ (u ⨂ v)} :
    trace f ≈ trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc));

  (* Superposing: an untraced factor c passes through the trace untouched. *)
  superposing {a b c u} {f : a ⨂ u ~> b ⨂ u} :
    trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)
      ≈ id[c] ⨂ trace f;

  (* Yanking: tracing braiding x past itself yields 恒等. （已译） *)
  yanking {x} : trace braid ≈ id[x];
}.
#[export] Existing Instance traced_is_symmetric.

Coercion traced_is_symmetric : TracedMonoidal >-> SymmetricMonoidal.

End TracedMonoidal.
