(*
   本文件为测试：ProbeComponents355。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Initial.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Limit.Components.

(** ** Instrument check — must ERROR ("The command has not failed!"). *)
Fail Fail Check Category.

(*
   本节说明 ProbeComponents355 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IprodSetPin.

Universe uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).
Context (Js : bool → Category@{uo uh uh}).

(* CONTROLS: the elementary vocabulary IS formable at these levels, and
   the controls are APPLIED -- an unapplied polymorphic constant never
   meets [Cu] and would discriminate nothing. *)

Check (fun (A : Type) (f : A → Cu) (p : Cu)
           (pr : ∀ a : A, p ~{Cu}~> f a) => IsIndexedProduct f p pr).

Check (fun (F : SigmaCat Js ⟶ Cu) (p : Cu) => IsALimit F p).

Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (p : Cu) (pr : ∀ k : bool, p ~{Cu}~> L k)
           (HP : IsIndexedProduct L p pr) => coprod_IsALimit F HL HP).

(* Former N1: the donor is formable here. *)
Check (fun (A : Type) (f : A → Cu)
           (P : Limit (DiscreteCat_Functor f)) => iprod f P).

(* Former N2: and so is the target's own corollary over it. *)
Check (fun (F : SigmaCat Js ⟶ Cu) (L : bool → Cu)
           (HL : ∀ k : bool, IsALimit (summand F k) (L k))
           (P : Limit (DiscreteCat_Functor L)) =>
         coprod_IsALimit_iprod F HL P).

End IprodSetPin.

(** ** CONVERSION — the transported diagram is not the summand on the
    nose.  The control is the [≈] form, which the target proves. *)

Section DiagramConversion.

Context {J C : Category}.
Context (D : ComponentDecomposition J).
Context (F : J ⟶ C).

(* CONTROL: the [≈] comparison exists and is what the target delivers. *)
Check (component_diagram_equiv D F).

(* N3. *)
Fail Example probe_component_diagram_strict (k : cd_index D) :
  component_diagram D F k = summand (F ◯ cd_compare D) k := eq_refl.

End DiagramConversion.

(** ** POSITIVE CONTROLS naming the rest of the surface, so that a rename
    of any of these breaks this file at a NON-[Fail] line. *)

Check @coprod_IsALimit.
Check @coprod_IsLimitCone.
Check @coprod_Limit.
Check @coprod_limit_iso.
Check @coprod_limit_iso_legs.
Check @coprod_proj_is_restriction.
Check @coprod_IsALimit_HasIndexedProducts.
Check @coprod_Limit_iprod.
(*
   本节说明 ProbeComponents355 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @coprod_IsALimit_iprod.
Check @component_diagram.
(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @iprod.
Check @Limit.
Check @DiscreteCat_Functor.
Check @ComponentDecomposition.
Check @cd_index.
Check @cd_rep.
Check @cd_part.
Check @cd_join.
Check @cd_sep.
Check @cd_compare.
Check @cd_equivalence.
Check @cd_bundled_equivalence.
Check @components_IsALimit.
Check @components_Limit.
Check @naive_pi0_sum.
Check @naive_pi0_sum_not_connected.
Check @no_ESO_into_naive_pi0_sum.
Check @TwoSum_not_connected.
Check @CoqPair_IsALimit.
Check @CoqPair_med_computes.
