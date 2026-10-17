Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.Diagonal.Product.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Set Universe Polymorphism.

Generalizable All Variables.

(* [=( c )] lives in functor_scope (Functor/Diagonal.v); this file does not
   import any module that opens it as a side effect, so it is opened here. *)
Open Scope functor_scope.

(** * A worked example of the couniversal-arrow assembly *)

(*
   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CouniversalExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition proj_pair (p : C ∏ C) :
  Diagonal_Product C (fst p × snd p) ~{C ∏ C}~> p :=
  (@exl C _ (fst p) (snd p), @exr C _ (fst p) (snd p)).

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

Program Definition product_couniversal_unique (p : C ∏ C) (d' : C)
  (f : Diagonal_Product C d' ~{C ∏ C}~> p) :
  ∃! g : d' ~{C}~> (fst p × snd p),
    f ≈ proj_pair p ∘ fmap[Diagonal_Product C] g :=
  {| unique_obj := fst f △ snd f |}.
Next Obligation.
  (* existence: the fork factors both components through the projections *)
  intros p d' f; simpl; split.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.
Next Obligation.
  (* uniqueness: any factorizer agrees with the fork, by [ump_products] *)
  intros p d' f v [Hv1 Hv2]; simpl in *.
  symmetry.
  apply ump_products; split.
  - now symmetry.
  - now symmetry.
Qed.

(* Packaged as a [CouniversalArrow]: Mac Lane's "a product is a couniversal
   arrow from the diagonal". *)
Definition product_CUA (p : C ∏ C) :
  CouniversalArrow p (Diagonal_Product C) :=
  couniversal_arrow_from_UMP p (Diagonal_Product C) (fst p × snd p)
    (proj_pair p)
    (product_couniversal_unique p).

(* The couniversal object is the product, and the couniversal arrow is the
   projection pair -- both by convertibility, since
   [couniversal_arrow_from_UMP] is [Defined]. *)
Corollary product_CUA_obj (p : C ∏ C) :
  coarrow_obj (product_CUA p) = (fst p × snd p).
Proof. reflexivity. Qed.

Corollary product_CUA_arrow (p : C ∏ C) :
  coarrow (product_CUA p) = proj_pair p.
Proof. reflexivity. Qed.

(** ** The terminal-object reading, exercised *)

(* [couniversal_arrow_terminal] applied to a real couniversal arrow: the
   product, with its projections, is a TERMINAL object of the comma category
   Δ ↓ =(p) -- Mac Lane's §III.1 Definition 3 read at his own example. *)
Definition product_terminal (p : C ∏ C) :
  @Terminal (Diagonal_Product C ↓ =(p)) :=
  couniversal_arrow_terminal (product_CUA p).

Corollary product_terminal_obj (p : C ∏ C) :
  `1 (@terminal_obj _ (product_terminal p)) = (fst p × snd p, ttt).
Proof. reflexivity. Qed.

(* ... and the passage back keeps both the object and the arrow. *)
Corollary product_terminal_round (p : C ∏ C) :
  coarrow (couniversal_arrow_of_terminal (product_terminal p))
    = coarrow (product_CUA p).
Proof. reflexivity. Qed.

(** ** The adjunction *)

(* Run [AdjunctionFromCouniversalArrows] on that family.  The result is a
   genuine adjunction Δ ⊣ R, produced entirely through the couniversal-arrow
   machinery of Theory/Universal/Arrow/Dual.v. *)
Definition product_via_couniversal_functor : C ∏ C ⟶ C :=
  RightAdjointFunctorFromCouniversalArrows (Diagonal_Product C) product_CUA.

Definition product_via_couniversal :
  Diagonal_Product C ⊣ product_via_couniversal_functor :=
  AdjunctionFromCouniversalArrows (Diagonal_Product C) product_CUA.

(* The object action of the produced right adjoint IS the product, on the nose
   -- the strength the primal GAFT example cannot state, its own functor being
   [Qed]-opaque. *)
Corollary product_via_couniversal_obj (p : C ∏ C) :
  fobj[product_via_couniversal_functor] p = (fst p × snd p).
Proof. reflexivity. Qed.

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary product_via_couniversal_counit (p : C ∏ C) :
  @counit (C ∏ C) C (Diagonal_Product C) product_via_couniversal_functor
          product_via_couniversal p
    ≈ proj_pair p.
Proof. exact (counit_couniversal (Diagonal_Product C) product_CUA p). Qed.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition product_via_couniversal_is_product :
  product_via_couniversal_functor ≈ ×(C) :=
  right_adjoint_iso (Diagonal_Product C)
    product_via_couniversal_functor (×(C))
    product_via_couniversal
    (Diagonal_Product_Adjunction C).

End CouniversalExample.

(** ** A concrete instantiation *)

(*
   本节说明伴随、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sets_product_CUA (p : Sets ∏ Sets) :
  CouniversalArrow p (Diagonal_Product Sets) :=
  @product_CUA Sets Sets_Cartesian p.

Definition Sets_product_via_couniversal :
  Diagonal_Product Sets ⊣ @product_via_couniversal_functor Sets Sets_Cartesian :=
  @product_via_couniversal Sets Sets_Cartesian.

Corollary Sets_product_via_couniversal_obj (p : Sets ∏ Sets) :
  fobj[@product_via_couniversal_functor Sets Sets_Cartesian] p
    = @product_obj Sets Sets_Cartesian (fst p) (snd p).
Proof. reflexivity. Qed.
