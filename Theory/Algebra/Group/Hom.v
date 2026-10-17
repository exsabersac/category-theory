Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Heunen_Vicary.Cartesian.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Proofs.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Monoid.Product.

Generalizable All Variables.

(* * * Group homomorphisms, 范畴 group 对象, finite products （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/group+object
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GroupHomomorphism.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

(* * ** Reading group 对象 internal 幺半群 （已译） *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition group_monoid {x : C} (G : GroupObject x) : Monoid x :=
  Monoid_of_MonoidObject (@groupobject_is_monoid _ _ _ G).

(*
   本节说明 Hom 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition group_inverse {x : C} (G : GroupObject x) : x ~> x :=
  @Category.Structure.Group.inverse _ _ _ G.

Example group_inverse_is {x : C} (G : GroupObject x) :
  group_inverse G = inverse[x] := eq_refl.

(* 相关说明。 （已译） *)
Example group_monoid_mu {x : C} (G : GroupObject x) :
  mu[group_monoid G] = mappend[G] := eq_refl.

Example group_monoid_eta {x : C} (G : GroupObject x) :
  eta[group_monoid G] = mempty[G] := eq_refl.

(** ** Group homomorphisms *)

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GroupHom {x y : C} (Gx : GroupObject x) (Gy : GroupObject y)
           (f : x ~> y) : Type :=
  MonoidHom (group_monoid Gx) (group_monoid Gy) f.

Lemma group_hom_mappend {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mappend[Gx] ≈ mappend[Gy] ∘ f ⨂ f.
Proof. exact (@hom_mu _ _ _ _ _ _ _ F). Qed.

Lemma group_hom_mempty {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ mempty[Gx] ≈ mempty[Gy].
Proof. exact (@hom_eta _ _ _ _ _ _ _ F). Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Lemma left_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (group_inverse G ⨂ id[x] ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply left_inverse. Qed.

Lemma right_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (id[x] ⨂ group_inverse G ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply right_inverse. Qed.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem GroupHom_inverse {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
        {f : x ~> y} (F : GroupHom Gx Gy f) :
  f ∘ group_inverse Gx ≈ group_inverse Gy ∘ f.
Proof.
  apply left_inverse_unique.
  assert (HB : (f ∘ group_inverse Gx) ⨂ f
                 ≈ f ⨂ f ∘ group_inverse Gx ⨂ id[x]).
  { rewrite <- bimap_comp; now rewrite id_right. }
  rewrite HB; clear HB.
  rewrite comp_assoc.
  rewrite <- (group_hom_mappend F).
  rewrite <- !comp_assoc.
  rewrite left_inverse_r.
  rewrite comp_assoc.
  now rewrite (group_hom_mempty F).
Qed.

(** ** The category of group objects *)

Lemma GroupHom_id {x : C} (G : GroupObject x) : GroupHom G G id.
Proof. exact (MonoidHom_id (group_monoid G)). Qed.

Lemma GroupHom_comp {x y z : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {Gz : GroupObject z} {f : y ~> z} {g : x ~> y} :
  GroupHom Gy Gz f → GroupHom Gx Gy g → GroupHom Gx Gz (f ∘ g).
Proof. exact MonoidHom_comp. Qed.

Lemma GroupHom_equiv {x y : C} {Gx : GroupObject x} {Gy : GroupObject y}
      {f g : x ~> y} : f ≈ g → GroupHom Gx Gy f → GroupHom Gx Gy g.
Proof. exact MonoidHom_equiv. Qed.

(*
   本节说明hom、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GrpCat : Category := {|
  obj     := { x : C & GroupObject x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & GroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; GroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; GroupHom_comp `2 f `2 g)
|}.

(* The forgetful 函子 C, faithful construction: 态射 等价
 [GrpCat] IS 等价 underlying C-态射. （已译） *)
Program Definition GrpCat_Forget : GrpCat ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

#[export] Instance GrpCat_Forget_Faithful : Faithful GrpCat_Forget.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GrpCat_Mon : GrpCat ⟶ Mon C := {|
  fobj := fun X => (`1 X; group_monoid `2 X);
  fmap := fun _ _ f => (`1 f; `2 f)
|}.

#[export] Instance GrpCat_Mon_Faithful : Faithful GrpCat_Mon.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance GrpCat_Mon_Full : Full GrpCat_Mon.
Proof.
  unshelve econstructor.
  - intros X Y g; exact g.
  - intros X Y g; simpl; reflexivity.
Qed.

(*
   本节说明函子、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example grpcat_mon_forget_obj (X : GrpCat) :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X := eq_refl.

Example grpcat_mon_forget_map (X Y : GrpCat) (f : X ~> Y) :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] f) = fmap[GrpCat_Forget] f := eq_refl.

(*
   本节说明函子、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example forget_compose_strict :
  @equiv _ (@Functor_StrictEq_Setoid GrpCat C)
    (Mon_Forget ◯ GrpCat_Mon) GrpCat_Forget.
Proof. exists (fun _ => eq_refl); intros; cat. Qed.

(** ** Binary products *)

Section GrpProduct.

Context `{CA : @Cartesian C}.

(* Two morphisms into a product agree when their components do.  A general
   [Cartesian] fact, declared here for want of a second consumer. *)
Lemma prod_ext {x y z : C} (f g : z ~> x × y) :
  exl ∘ f ≈ exl ∘ g → exr ∘ f ≈ exr ∘ g → f ≈ g.
Proof.
  intros Hl Hr.
  rewrite <- (prod_fork_eta f), <- (prod_fork_eta g).
  apply fork_inv; split; assumption.
Qed.

Section GrpProductData.

Context {x y : C} (X : GroupObject x) (Y : GroupObject y).

(* The componentwise inversion. *)
Definition grp_prod_inverse : x × y ~> x × y :=
  split (group_inverse X) (group_inverse Y).

Notation MU := (mon_prod_mu (group_monoid X) (group_monoid Y)).
Notation ETA := (mon_prod_eta (group_monoid X) (group_monoid Y)).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_prod_left_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : (group_inverse Z ∘ p) ⨂ p
                ≈ group_inverse Z ⨂ id[z] ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (group_inverse Z ⨂ id[z]) ∆z p), comp_assoc.
  rewrite left_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_right_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Hmu : p ∘ MU ≈ mappend[Z] ∘ bimap p p)
      (Hinv : p ∘ grp_prod_inverse ≈ group_inverse Z ∘ p) :
  p ∘ (MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y))
    ≈ mempty[Z] ∘ eliminate.
Proof.
  rewrite !comp_assoc, Hmu.
  rewrite <- (comp_assoc mappend[Z] (bimap p p) _).
  rewrite <- bimap_comp, Hinv, id_right.
  assert (E : p ⨂ (group_inverse Z ∘ p)
                ≈ id[z] ⨂ group_inverse Z ∘ bimap p p)
    by (rewrite <- bimap_comp; now rewrite id_left).
  rewrite E; clear E.
  rewrite <- !comp_assoc.
  rewrite (diagonal_natural _ _ p); simpl.
  rewrite (comp_assoc (id[z] ⨂ group_inverse Z) ∆z p), comp_assoc.
  rewrite right_inverse_r.
  rewrite <- comp_assoc.
  now rewrite eliminate_comp.
Qed.

Lemma grp_prod_eta_leg {z : C} (Z : GroupObject z) (p : x × y ~> z)
      (Heta : p ∘ ETA ≈ mempty[Z]) :
  p ∘ (ETA ∘ @eliminate _ _ _ (x × y))
    ≈ mempty[Z] ∘ @eliminate _ _ _ (x × y).
Proof. now rewrite comp_assoc, Heta. Qed.

Lemma grp_prod_left_inverse :
  MU ∘ grp_prod_inverse ⨂ id[x × y] ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_left_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_left_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

Lemma grp_prod_right_inverse :
  MU ∘ id[x × y] ⨂ grp_prod_inverse ∘ ∆(x × y) ≈ ETA ∘ eliminate.
Proof.
  apply prod_ext.
  - rewrite (grp_prod_right_leg X exl (mon_prod_mu_exl _ _) (exl_split _ _)).
    now rewrite (grp_prod_eta_leg X exl (mon_prod_eta_exl _ _)).
  - rewrite (grp_prod_right_leg Y exr (mon_prod_mu_exr _ _) (exr_split _ _)).
    now rewrite (grp_prod_eta_leg Y exr (mon_prod_eta_exr _ _)).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GroupObject_Product : GroupObject (x × y) :=
  Build_GroupObject (x × y)
    (MonoidObject_of_Monoid
       (Monoid_Product (group_monoid X) (group_monoid Y)))
    grp_prod_inverse grp_prod_left_inverse grp_prod_right_inverse.

(* The underlying monoid of the product group IS #503's product monoid, at
   Leibniz equality: the [Monoid]/[MonoidObject] round trip is definitional
   ([monoid_round], Theory/Algebra/Monoid/Product.v). *)
Example grp_prod_monoid :
  group_monoid GroupObject_Product
    = Monoid_Product (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_inverse_is :
  group_inverse GroupObject_Product = grp_prod_inverse := eq_refl.

Example grp_prod_mappend :
  mappend[GroupObject_Product]
    = mon_prod_mu (group_monoid X) (group_monoid Y) := eq_refl.

Example grp_prod_mempty :
  mempty[GroupObject_Product]
    = mon_prod_eta (group_monoid X) (group_monoid Y) := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_exl_hom : GroupHom GroupObject_Product X exl.
Proof. exact (mon_exl_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_exr_hom : GroupHom GroupObject_Product Y exr.
Proof. exact (mon_exr_hom (group_monoid X) (group_monoid Y)). Qed.

Lemma grp_fork_hom {z : C} {Z : GroupObject z} {f : z ~> x} {g : z ~> y} :
  GroupHom Z X f → GroupHom Z Y g → GroupHom Z GroupObject_Product (f △ g).
Proof. exact (@mon_fork_hom _ _ _ _ _ _ _ _ _ _ _). Qed.

End GrpProductData.

(* Binary products GrpCat, carried binary products C. No terminal
 对象 C used, no compatibility between × ⨂. （已译） *)
#[export] Program Instance GrpCat_Cartesian : @Cartesian GrpCat := {|
  product_obj := fun X Y => (`1 X × `1 Y; GroupObject_Product `2 X `2 Y);
  Cartesian.fork :=
    fun _ _ _ f g => (`1 f △ `1 g; grp_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; grp_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; grp_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply Cartesian.fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End GrpProduct.

(** ** The terminal group object *)

Section GrpTerminal.

Context `{TE : @Terminal C}.

(* The terminal object of C carries a unique group-object structure: every
   structure map lands in 1, so [one_unique] discharges both inverse laws
   just as it discharges the three monoid laws in [Terminal_Monoid]. *)
Definition GroupObject_Terminal : GroupObject (1 : C) :=
  Build_GroupObject (1 : C) (MonoidObject_of_Monoid Terminal_Monoid)
    one (one_unique _ _) (one_unique _ _).

Example grp_terminal_monoid :
  group_monoid GroupObject_Terminal = Terminal_Monoid := eq_refl.

(* Every morphism into 1 is a group homomorphism. *)
Lemma grp_one_hom {x : C} (G : GroupObject x) :
  GroupHom G GroupObject_Terminal one.
Proof. exact (mon_one_hom (group_monoid G)). Qed.

#[export] Program Instance GrpCat_Terminal : @Terminal GrpCat := {|
  terminal_obj := ((1 : C); GroupObject_Terminal);
  one := fun X => (one; grp_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End GrpTerminal.

(* * ** The forgetful 函子 sends finite products C's own （已译） *)

Section GrpForget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Example GrpCat_Forget_product (X Y : GrpCat) :
  fobj[GrpCat_Forget] (X × Y)
    = fobj[GrpCat_Forget] X × fobj[GrpCat_Forget] Y := eq_refl.

Example GrpCat_Forget_terminal :
  fobj[GrpCat_Forget] (@terminal_obj GrpCat GrpCat_Terminal) = (1 : C)
  := eq_refl.

Example GrpCat_Forget_exl (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exl GrpCat GrpCat_Cartesian X Y) = exl := eq_refl.

Example GrpCat_Forget_exr (X Y : GrpCat) :
  fmap[GrpCat_Forget] (@exr GrpCat GrpCat_Cartesian X Y) = exr := eq_refl.

Example GrpCat_Forget_fork (X Y Z : GrpCat) (f : X ~> Y) (g : X ~> Z) :
  fmap[GrpCat_Forget] (@Cartesian.fork GrpCat GrpCat_Cartesian _ _ _ f g)
    = fmap[GrpCat_Forget] f △ fmap[GrpCat_Forget] g := eq_refl.

Example GrpCat_Forget_one (X : GrpCat) :
  fmap[GrpCat_Forget] (@one GrpCat GrpCat_Terminal X) = one := eq_refl.

(* GrpCat_Mon likewise preserves them on the nose. *)
Example GrpCat_Mon_product (X Y : GrpCat) :
  fobj[GrpCat_Mon] (X × Y) = fobj[GrpCat_Mon] X × fobj[GrpCat_Mon] Y
  := eq_refl.

Example GrpCat_Mon_terminal :
  fobj[GrpCat_Mon] (@terminal_obj GrpCat GrpCat_Terminal)
    = @terminal_obj (Mon C) Mon_Terminal := eq_refl.

End GrpForget.

End GroupHomomorphism.

Arguments GrpCat C {CM}.

Section GrpCatIntrinsic.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

Definition GrpCat_Cartesian_tensor : @Cartesian (GrpCat C) :=
  @GrpCat_Cartesian C CM CartesianMonoidal_Cartesian.

Definition GrpCat_Terminal_unit : @Terminal (GrpCat C) :=
  @GrpCat_Terminal C CM (@SemicartesianMonoidal_Terminal C _ _).

Example grpcat_tensor_product (X Y : GrpCat C) :
  fobj[GrpCat_Forget] (@product_obj _ GrpCat_Cartesian_tensor X Y)
    = (fobj[GrpCat_Forget] X ⨂ fobj[GrpCat_Forget] Y)%object := eq_refl.

Example grpcat_unit_terminal :
  fobj[GrpCat_Forget] (@terminal_obj _ GrpCat_Terminal_unit) = @I C _
  := eq_refl.

End GrpCatIntrinsic.

(** ** Probes *)

(*
   本节说明 Hom 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Probes.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CM : @CartesianMonoidal C}.
Context {x y : C} (Gx : @GroupObject C CM x) (Gy : @GroupObject C CM y).
Context (f : x ~> y).

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun z : obj[C] => @GroupObject C M z).

(* CONTROL for negative 1. *)
Check (fun z : obj[C] => @GroupObject C CM z).

(* NEGATIVE 2, TYPING. [MonoidHom] indexed Theory/Algebra/Monoid.v's
 [Monoid], Structure/Monoid.v's [MonoidObject], raw field of
 group 对象 does fit #503's class passage
 ([Monoid_of_MonoidObject], used [group_monoid]) load-bearing.
 "The term "groupobject_is_monoid" has type "MonoidObject x"" （已译） *)
Fail Check (MonoidHom (@groupobject_is_monoid _ _ _ Gx)
                      (@groupobject_is_monoid _ _ _ Gy) f).

(* CONTROLS for negative 2, naming every constant it mentions — including
   [groupobject_is_monoid] itself, whose only other positive occurrence is
   inside [group_monoid]'s body, which PRECEDES the negative. *)
Check (@groupobject_is_monoid C CM x Gx).
Check (MonoidHom (group_monoid Gx) (group_monoid Gy) f).
Check (GroupHom Gx Gy f).
Check (eq_refl : GroupHom Gx Gy f
                   = MonoidHom (group_monoid Gx) (group_monoid Gy) f).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (eq_refl : Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget).

(* CONTROLS for negative 3. *)
Check (fun (X : GrpCat C) => (eq_refl :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X)).
Check (fun (X Y : GrpCat C) (g : X ~> Y) => (eq_refl :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] g) = fmap[GrpCat_Forget] g)).

End Probes.

(* * ** Where hom/证明 identification comes from （已译） *)

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* 相关说明。 （已译） *)
Check (fun (C : Category@{uo uh up}) (a b : C) => a ~> b).
Check (fun (C : Category@{uo uh up}) (a : C) => id[a]).

(* 相关说明。 （已译） *)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.
Check @CartesianMonoidal.
Check @GroupObject.

(* Each reports: "Cannot enforce up = uh because uh < up". *)
Fail Check (fun C : Category@{uo uh up} => @Monoidal C).
Fail Check (fun C : Category@{uo uh up} => @Cartesian C).
Fail Check (fun C : Category@{uo uh up} => @Terminal C).
Fail Check (fun C : Category@{uo uh up} => @CartesianMonoidal C).

End UniverseDonors.
