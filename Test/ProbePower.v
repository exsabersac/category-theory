(*
   本文件为测试：ProbePower。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Section BigIndex.

Universes o so.
Constraint o < so.

Context (X : SetoidObject@{o o}).

(* Positive control 1: at a small index the power is formable. *)
Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o} nat X).

(* 相关说明。 （已译） *)
Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o} nat X).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@power Sets@{o so} Sets_HasIndexedProducts@{so o}
              SetoidObject@{o o} X).

(* 相关说明。 （已译） *)
Fail Check (@copower Sets@{o so} Sets_HasIndexedCoproducts@{so o}
              SetoidObject@{o o} X).

End BigIndex.

(* * ** (1b) The [Program] form copower-of-[1] 嵌入 pinned to
 [Set], shipped hand-written form not （已译） *)

(* This is the variant Structure/Limit/Power/Hom.v declines to use.  It
   raises no obligation: instance resolution closes [proper_morphism] during
   elaboration, the domain's [≈] being Leibniz [eq]. *)
Program Definition probe_copower_one_from_program (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object := {|
  morphism := fun i : J => existT (fun _ : J => poly_unit) i ttt
|}.

Section ProgramPin.

Universe uj.
Constraint Set < uj.

Context (J : Type@{uj}).

(* Positive control 3: shipped 常值 applies at index. （已译） *)
Check (Sets_copower_one_from J).

(* Positive control 4: so does 同构 built it. （已译） *)
Check (Sets_copower_one J).

(* 相关说明。 （已译） *)
Fail Check (probe_copower_one_from_program J).

End ProgramPin.

(* 相关说明。 （已译） *)

Section Conversion.

Context (J : Type).
Context (X Y : obj[Sets]).
Context (C : Category).
Context (b c : C).

(* 相关说明。 （已译） *)
Definition probe_power_carrier_control :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_power_is_exponent :
  carrier (@power Sets Sets_HasIndexedProducts J X)
  = carrier (Sets_pow J X) := eq_refl.

(* 相关说明。 （已译） *)
Definition probe_copower_carrier_control :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

(* Negative 5: it not product 对象. [Sets_copower_prod] an
 同构 [Sets], not equality 对象. （已译） *)
Fail Definition probe_copower_is_prod :
  @copower Sets Sets_HasIndexedCoproducts J Y
  = (Sets_discrete J × Y)%object := eq_refl.

(* Positive control 7: Riehl's right-hand side [C(X, A)^I] IS a power in
   [Sets], on the nose. *)
Definition probe_rhs_control :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition probe_rhs_is_exponent :
  fobj[power_hom_functor J b] c
  = Sets_pow J {| carrier := @hom C c b ; is_setoid := @homset C c b |}
  := eq_refl.

(* 相关说明。 （已译） *)
Definition probe_transform_control (p : C) (ev : ∀ _ : J, p ~> b)
  (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u
  := eq_refl.

End Conversion.
