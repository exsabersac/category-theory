Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Adjunction.GAFT.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.SpanningArrow.

Generalizable All Variables.

(*
   本文件为测试：ProbeSpanningArrow448。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check spanning_arrow_448_no_such_constant.

(** ** Positive controls *)

Check @SubFactorsThrough.
Check @Spanning.
Check @spanning_arrow.
Check @PreservesWidePullbacks.
Check @SpanningArrowsOutOf.
Check @SubObj.
Check @sub_top.
Check @sub_le.
Check @sub_top_greatest.
Check @sub_dom.
Check @sub_mono.
Check @spanning_sub.
Check @spanning_factor.
Check @spanning_solution_set.
Check @factors_through_top.
Check @SolutionSet.
Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @GAFT.
Check @GAFT_from_spanning.
Check @Complete.
Check @PreservesImageLimit.
Check @HasWidePullbacks.

(* 相关说明。 （已译） *)

Section Readbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).
Context {x : X} {a : A} (f : x ~> G a).

(* 相关说明。 （已译） *)
Definition p448_b1_flipped : Type :=
  ∀ m : SubObj a, SubFactorsThrough G f m → sub_le m sub_top.
Example p448_b1_vacuous : p448_b1_flipped.
Proof. intros m _; apply sub_top_greatest. Defined.

(* 相关说明。 （已译） *)
Example p448_t_lift : `1 (factors_through_top G f) = f := eq_refl.
Example p448_t_index :
  sol_index (spanning_solution_set G GP x) = SpanningArrowsOutOf G x
  := eq_refl.
Example p448_t_obj (i : SpanningArrowsOutOf G x) :
  sol_obj (spanning_solution_set G GP x) i = `1 i := eq_refl.
Example p448_t_arr (i : SpanningArrowsOutOf G x) :
  sol_arr (spanning_solution_set G GP x) i = `1 (`2 i) := eq_refl.

(*
   本节说明 ProbeSpanningArrow448 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p448_b2 (m : SubObj a) : Type :=
  { k : x ~> G (sub_dom m) & k ∘ fmap[G] (sub_mono m) ≈ f }.

(* B3 -- TYPING, INSTANCE: [GP] EXPLICIT argument the
 已消解的 [spanning_solution_set], omitting it mis-applies the
 next argument: "The term "z" has type "obj[X]" it expected to
 have type "PreservesWidePullbacks G"". （已译） *)
Fail Definition p448_b3 (z : X) : SolutionSet G z :=
  spanning_solution_set G z.

(* B5 -- TYPING: the spanning factor lands in the intersection, not in
   [a]: "has type "x ~{ X }~> fobj[G] (sub_dom (spanning_sub G f))" while
   it is expected to have type "x ~{ X }~> fobj[G] a"".（标题）（已译） *)
Fail Definition p448_b5 : x ~> G a := spanning_factor G GP f.

End Readbacks.

(* 相关说明。 （已译） *)

Section NoWidePullbacks.

Context {A X : Category}.
Context (G : A ⟶ X).
Context {x : X} {a : A} (f : x ~> G a).

(*
   本节说明 ProbeSpanningArrow448 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p448_b4 : SubObj a := spanning_sub G f.

End NoWidePullbacks.

(* 相关说明。 （已译） *)

Section UnannotatedGAFT.

Context {A X : Category}.
Context (G : A ⟶ X).
Context `{HWP : @HasWidePullbacks A}.
Context (GP : PreservesWidePullbacks G).

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p448_b7 (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := GAFT G comp cont (spanning_solution_set G GP).

(* The two now interchangeable, up implicit/explicit shape of
 wide-pullback 论元. If annotations ever put back, this
 line stops 编译. （已译） *)
Definition p448_b7_via_theorem (comp : @Complete A)
  (cont : @PreservesImageLimit A X G) :
  { F : X ⟶ A & F ⊣ G } := @GAFT_from_spanning A X G HWP GP comp cont.

End UnannotatedGAFT.
