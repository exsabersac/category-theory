(*
   本文件为测试：ProbeFunTerminal339。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.Terminal.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Control: so does family 对象 -- shape indexed
 results quantify over. （已译） *)
Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C) => f).

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(* Control: [Cartesian] exists at unconstrained levels.  Same reason as
   the [HasIndexedProducts] control below -- without it the negative
   would survive a rename of [Cartesian] on a reference-not-found
   error.（标题）（已译） *)
Check @Cartesian.

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(*
   本节说明 ProbeFunTerminal339 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @HasIndexedProducts.

(* NEGATIVE 3. *)
Fail Check (fun (C : Category@{uo uh up}) => @HasIndexedProducts C).

(* 相关说明。 （已译） *)
Check @IsIndexedProduct.

(* NEGATIVE 4. *)
Fail Check (fun (C : Category@{uo uh up}) (A : Type) (f : A -> C)
                (p : C) (proj : forall a, p ~> f a) =>
              @IsIndexedProduct C A f p proj).

(* Control: [Fun] exists at unconstrained levels. *)
Check @Fun.

(* NEGATIVE 5. [Fun] does MORE than other four: it identifies hom
 证明 BOTH arguments two hom levels each other. （已译） *)
Fail Check (fun (C D : Category@{uo uh up}) => @Fun C D).

End Donors.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DiagonalPin.

Universe co ch cp dro dh.
Constraint ch < cp.

(* Control: the three objects exist at these levels. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => (C, D, T)).

(* Control: so does the terminal object of D. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) => @terminal_obj D T).

(* Control: so does target's OWN 常值 函子, at exactly
 these levels -- C's hom 证明 strictly apart. （已译） *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh}) (d : D) =>
         @Constant_Functor@{co ch cp dro dh dh} C D d).

(* Control: and its terminal specialization. *)
Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
           (T : @Terminal D) =>
         @Constant_Terminal_Functor@{co ch cp dro dh} C D T).

(* Control: [Diagonal] exists at unconstrained levels. *)
Check @Diagonal.

(* NEGATIVE 6. *)
Fail Check (fun (C : Category@{co ch cp}) (D : Category@{dro dh dh})
                (T : @Terminal D) =>
              fobj[@Diagonal D C] (@terminal_obj D T)).

End DiagonalPin.

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition probe_functor_only
  {C : Category} {A : Type} (f : A -> C) : DiscreteCat A ⟶ C :=
  DiscreteCat_Functor f.

Definition probe_cone_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Cone (DiscreteCat_Functor f).

Definition probe_limit_of_discrete
  {C : Category} {A : Type} (f : A -> C) : Type :=
  Limit (DiscreteCat_Functor f).

(* 相关说明。 （已译） *)

Check @Functor_Category_Terminal.
Check @Constant_Functor.
Check @Constant_Terminal_Functor.
Check @Fun_iprod.
Check @Fun_iprod_proj.
Check @Fun_IsIndexedProduct.
Check @Fun_HasIndexedProducts.
Check @iprod_jointly_monic.
Check @cartesian_bool_IsIndexedProduct.
Check @Fun_bool_iprod_iso.
Check @terminal_empty_IsIndexedProduct.
Check @Fun_empty_iprod_terminal.

(** 本节：The two CONVERSION refutations live target own
 controls; these name constants so rename breaks file
 too. （已译） *)

Check @bool_fam.
Check @Fun_bool_iprod_iso_commutes.
Check @Fun_bool_iprod_iso_inv_commutes.

(*
   本节说明笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
