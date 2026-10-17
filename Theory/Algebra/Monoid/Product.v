Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(* * * Finite products 范畴 internal monoids （已译） *)

(*
   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonProduct.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** ** The product monoid *)

Section Binary.

Context `{CA : @Cartesian C}.

(* Two 态射 product recovered two components: the
 eta law product, form used repeatedly below. （已译） *)
Lemma prod_fork_eta {x y z : C} (f : z ~> x × y) :
  (exl ∘ f) △ (exr ∘ f) ≈ f.
Proof. rewrite fork_comp; now rewrite fork_exl_exr, id_left. Qed.

Section Data.

Context {x y : C} (X : Monoid x) (Y : Monoid y).

(* 相关说明。 （已译） *)
Definition mon_prod_mu : (x × y) ⨂ (x × y) ~> x × y :=
  (mu[X] ∘ bimap exl exl) △ (mu[Y] ∘ bimap exr exr).

(* The componentwise unit. *)
Definition mon_prod_eta : I ~> x × y := eta[X] △ eta[Y].

Lemma mon_prod_mu_exl : exl ∘ mon_prod_mu ≈ mu[X] ∘ bimap exl exl.
Proof. unfold mon_prod_mu; apply exl_fork. Qed.

Lemma mon_prod_mu_exr : exr ∘ mon_prod_mu ≈ mu[Y] ∘ bimap exr exr.
Proof. unfold mon_prod_mu; apply exr_fork. Qed.

Lemma mon_prod_eta_exl : exl ∘ mon_prod_eta ≈ eta[X].
Proof. unfold mon_prod_eta; apply exl_fork. Qed.

Lemma mon_prod_eta_exr : exr ∘ mon_prod_eta ≈ eta[Y].
Proof. unfold mon_prod_eta; apply exr_fork. Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mon_prod_assoc_leg {z} (Z : Monoid z) (p : x × y ~> z)
      (Hp : p ∘ mon_prod_mu ≈ mu[Z] ∘ bimap p p) :
  p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
    ≈ p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu ∘ to tensor_assoc).
Proof.
  assert (HL : p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
                 ≈ mu[Z] ∘ bimap mu[Z] id ∘ bimap (bimap p p) p).
  { rewrite comp_assoc, Hp.
    rewrite <- comp_assoc, <- bimap_comp, Hp, id_right.
    rewrite <- comp_assoc, <- bimap_comp.
    now rewrite id_left. }
  assert (HR : p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                      ∘ to tensor_assoc)
                 ≈ mu[Z] ∘ bimap id mu[Z] ∘ to tensor_assoc
                     ∘ bimap (bimap p p) p).
  { rewrite !comp_assoc, Hp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (bimap p p)).
    rewrite <- bimap_comp, Hp, id_right.
    assert (Hb : p ⨂ (mu[Z] ∘ p ⨂ p) ≈ id[z] ⨂ mu[Z] ∘ p ⨂ (p ⨂ p))
      by (rewrite <- bimap_comp; now rewrite id_left).
    rewrite Hb, <- comp_assoc.
    now rewrite to_tensor_assoc_natural. }
  rewrite HL, HR.
  now rewrite mu_assoc.
Qed.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Monoid_Product : Monoid (x × y) := {|
  mu  := mon_prod_mu;
  eta := mon_prod_eta
|}.
Next Obligation.
  (* associativity *)
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])).
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                               ∘ to tensor_assoc)).
  apply fork_inv; split.
  - apply (mon_prod_assoc_leg X exl mon_prod_mu_exl).
  - apply (mon_prod_assoc_leg Y exr mon_prod_mu_exr).
Qed.
Next Obligation.
  (* left unit *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_right_left eta[X] exl).
  rewrite <- (bimap_id_right_left eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_left, mu_unit_left.
  rewrite <- !to_unit_left_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.
Next Obligation.
  (* right unit *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_left_right eta[X] exl).
  rewrite <- (bimap_id_left_right eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_right, mu_unit_right.
  rewrite <- !to_unit_right_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.

(* The two projections 幺半群 homomorphisms. （已译） *)
Lemma mon_exl_hom : MonoidHom Monoid_Product X exl.
Proof. split; [ apply mon_prod_mu_exl | apply mon_prod_eta_exl ]. Qed.

Lemma mon_exr_hom : MonoidHom Monoid_Product Y exr.
Proof. split; [ apply mon_prod_mu_exr | apply mon_prod_eta_exr ]. Qed.

(* The pairing of two monoid homomorphisms is a monoid homomorphism. *)
Lemma mon_fork_hom {z} {Z : Monoid z} {f : z ~> x} {g : z ~> y} :
  MonoidHom Z X f → MonoidHom Z Y g → MonoidHom Z Monoid_Product (f △ g).
Proof.
  intros F G.
  split; simpl.
  - unfold mon_prod_mu.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exl_fork.
      apply (@hom_mu _ _ _ _ _ _ _ F).
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exr_fork.
      apply (@hom_mu _ _ _ _ _ _ _ G).
  - unfold mon_prod_eta.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + apply (@hom_eta _ _ _ _ _ _ _ F).
    + apply (@hom_eta _ _ _ _ _ _ _ G).
Qed.

End Data.

(** ** Mon(C) is cartesian *)

(* Binary products Mon(C) binary products C. No 终对象 of
 C used, no compatibility between × ⨂. （已译） *)
#[export] Program Instance Mon_Cartesian : @Cartesian (Mon C) := {|
  product_obj := fun X Y => (`1 X × `1 Y; Monoid_Product `2 X `2 Y);
  fork := fun _ _ _ f g =>
            (`1 f △ `1 g; mon_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; mon_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; mon_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End Binary.

(** ** The terminal monoid *)

Section Nullary.

Context `{TE : @Terminal C}.

(* The terminal object carries a unique monoid structure: both structure maps
   land in 1, so [one_unique] discharges all three laws.  No [Cartesian] is
   used here. *)
Program Definition Terminal_Monoid : Monoid (1 : C) := {|
  mu  := one;
  eta := one
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(* Every morphism into the terminal object is a monoid homomorphism, both
   preservation conditions being equations between morphisms into 1. *)
Lemma mon_one_hom {x : C} (X : Monoid x) :
  MonoidHom X Terminal_Monoid one.
Proof. split; apply one_unique. Qed.

#[export] Program Instance Mon_Terminal : @Terminal (Mon C) := {|
  terminal_obj := ((1 : C); Terminal_Monoid);
  one := fun X => (one; mon_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End Nullary.

(* * ** The forgetful 函子 agrees C's finite products, nose （已译） *)

Section Forget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(*
   本节说明（余）极限、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Mon_Forget_product (X Y : Mon C) :
  fobj[Mon_Forget] (X × Y) = fobj[Mon_Forget] X × fobj[Mon_Forget] Y
  := eq_refl.

Example Mon_Forget_terminal :
  fobj[Mon_Forget] (@terminal_obj (Mon C) Mon_Terminal) = (1 : C)
  := eq_refl.

Example Mon_Forget_exl (X Y : Mon C) :
  fmap[Mon_Forget] (@exl (Mon C) Mon_Cartesian X Y) = exl := eq_refl.

Example Mon_Forget_exr (X Y : Mon C) :
  fmap[Mon_Forget] (@exr (Mon C) Mon_Cartesian X Y) = exr := eq_refl.

Example Mon_Forget_fork (X Y Z : Mon C) (f : X ~> Y) (g : X ~> Z) :
  fmap[Mon_Forget] (@fork (Mon C) Mon_Cartesian _ _ _ f g)
    = fmap[Mon_Forget] f △ fmap[Mon_Forget] g := eq_refl.

Example Mon_Forget_one (X : Mon C) :
  fmap[Mon_Forget] (@one (Mon C) Mon_Terminal X) = one := eq_refl.

End Forget.

(* * ** Reconciling two 幺半群-对象 classes （已译） *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Monoid_of_MonoidObject {x : C} (X : @MonoidObject C M x)
  : Monoid x := {|
  mu           := @mappend _ _ _ X;
  eta          := @mempty _ _ _ X;
  mu_assoc     := @mappend_assoc _ _ _ X;
  mu_unit_left := @mempty_left _ _ _ X;
  mu_unit_right := @mempty_right _ _ _ X
|}.

Definition MonoidObject_of_Monoid {x : C} (X : Monoid x)
  : @MonoidObject C M x := {|
  mempty        := @eta _ _ _ X;
  mappend       := @mu _ _ _ X;
  mempty_left   := @mu_unit_left _ _ _ X;
  mempty_right  := @mu_unit_right _ _ _ X;
  mappend_assoc := @mu_assoc _ _ _ X
|}.

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example monoid_round {x : C} (X : Monoid x) :
  Monoid_of_MonoidObject (MonoidObject_of_Monoid X) = X := eq_refl.

Example monoid_object_round {x : C} (X : @MonoidObject C M x) :
  MonoidObject_of_Monoid (Monoid_of_MonoidObject X) = X := eq_refl.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End MonProduct.

Section AbstractBaseProbe.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Fail Check
  (fun (x y : C) (X : @MonoidObject C CC_Monoidal x)
       (Y : @MonoidObject C CC_Monoidal y) =>
     @Monoid_of_MonoidObject C M (x × y) (Product_Monoid X Y)).

End AbstractBaseProbe.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Comparison.

Context {C : Category}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(* [Structure.Monoid.Monoid x] 定义 [@MonoidObject C CC_Monoidal
 x]; passage above turns it file's [Monoid] at same
 base. （已译） *)

Example Monoid_Product_eta_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @eta C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                          (Monoid_of_MonoidObject X)
                          (Monoid_of_MonoidObject Y))
    = @mempty C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Product_Monoid_as_Monoid {x y : C}
           (X : @MonoidObject C CC_Monoidal x)
           (Y : @MonoidObject C CC_Monoidal y)
  : @Monoid C CC_Monoidal (x × y)
  := @Monoid_of_MonoidObject C CC_Monoidal (x × y) (Product_Monoid X Y).

(* The multiplications NOT same term. Control:
 [Monoid_Product_mu_is_Product_Monoid], immediately below, names every
 常值 occurring command. （已译） *)
Fail Example Monoid_Product_mu_not_strict
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    = @mappend C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

Lemma Monoid_Product_mu_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    ≈ @mappend C CC_Monoidal _ (Product_Monoid X Y).
Proof.
  simpl.
  unfold mon_prod_mu, bimap, toggle, split; simpl.
  rewrite <- fork_comp.
  apply fork_inv; split; rewrite <- comp_assoc.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.

End Comparison.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsWitness.

Definition Mon_Sets_Cartesian
  : @Cartesian (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Cartesian Sets Sets_Product_Monoidal Sets_Cartesian.

Definition Mon_Sets_Terminal
  : @Terminal (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Terminal Sets Sets_Product_Monoidal Sets_Terminal.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (@CC_Monoidal Sets Sets_Cartesian Sets_Terminal).

Fail Example Sets_Product_Monoidal_is_CC_Monoidal :
  Sets_Product_Monoidal = @CC_Monoidal Sets Sets_Cartesian Sets_Terminal
  := eq_refl.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check
  (fun (x y : Sets)
       (X : @MonoidObject Sets CC_Monoidal x)
       (Y : @MonoidObject Sets CC_Monoidal y) =>
     @Monoid_of_MonoidObject Sets Sets_Product_Monoidal
       (@product_obj Sets Sets_Cartesian x y) (Product_Monoid X Y)).

End SetsWitness.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* CONTROLS: hom 恒等 such 范畴 formable at
 exactly these levels, so rejections below about donors and
 not about levels themselves. （已译） *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).
Check (fun (C : Category@{uo uh up}) (x : C) => id[x]).

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.

(* NEGATIVE 1 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

(* NEGATIVE 2 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 3 (FORMABILITY). *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

End UniverseDonors.
