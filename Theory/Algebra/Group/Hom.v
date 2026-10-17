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

(** * Group homomorphisms, the category of group objects, finite products *)

(*
 nLab:      https://ncatlab.org/nlab/show/group+object
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GroupHomomorphism.

Context {C : Category}.
Context `{CM : @CartesianMonoidal C}.

(** ** Reading a group object as an internal monoid *)

(*
   The underlying 幺半群 of a group 对象, in the [mu]/[eta] presentation

   本节：that [Mon] is indexed by. [groupobject_is_幺半群] lands Structure/幺半群.v's [MonoidObject]; [幺半群_of_MonoidObject] (Theory/代数/幺半群/积.v) renames its fields.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition group_monoid {x : C} (G : GroupObject x) : Monoid x :=
  Monoid_of_MonoidObject (@groupobject_is_monoid _ _ _ G).

(*
   The inversion 态射 of a NAMED group 对象.  Declared because

   本节说明相关定义、性质与动机。 Structure/Group.v's [inverse[G]] notation quotes token [inverse], which makes it keyword: [@inverse _ _ _ G] is then parse error, [inverse[x]] leaves instance resolution. This accessor names instance explicitly;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition group_inverse {x : C} (G : GroupObject x) : x ~> x :=
  @Category.Structure.Group.inverse _ _ _ G.

Example group_inverse_is {x : C} (G : GroupObject x) :
  group_inverse G = inverse[x] := eq_refl.

(* The passage costs nothing: the multiplication and unit of [group_monoid G]
   ARE [G]'s own, at Leibniz equality. *)
Example group_monoid_mu {x : C} (G : GroupObject x) :
  mu[group_monoid G] = mappend[G] := eq_refl.

Example group_monoid_eta {x : C} (G : GroupObject x) :
  eta[group_monoid G] = mempty[G] := eq_refl.

(** ** Group homomorphisms *)

(*
   A 同态 of group 对象 IS a 同态 of the underlying 幺半群

   本节说明相关定义、性质与动机。 对象. There is no inverse-preservation field; that it holds anyway is [GroupHom_inverse] below.

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

(** ** Preservation of the inverse is a THEOREM *)

(* Right-associated readings of the two inverse laws, in the bracketing that
   [rewrite] leaves after [rewrite <- !comp_assoc]. *)
Lemma left_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (group_inverse G ⨂ id[x] ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply left_inverse. Qed.

Lemma right_inverse_r {x : C} {G : GroupObject x} :
  mappend[G] ∘ (id[x] ⨂ group_inverse G ∘ ∆x) ≈ mempty[G] ∘ eliminate.
Proof. rewrite comp_assoc; apply right_inverse. Qed.

(*
   Awodey, 范畴 Theory 2nd ed., Section 4.1: a 态射 of the underlying

   本节说明相关定义、性质与动机。 幺半群 对象 automatically commutes inversions, so internal-group hom class needs no inverse-preservation axiom. The elementwise argument is "f(a⁻¹) is left inverse f(a), left inverses are unique".

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
   本节说明相关定义、性质与动机。 Mac Lane, CWM 2nd ed., Section III.6, Exercise 2 (as scoped issue #343);. Awodey Section 4.1's Group(C).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GrpCat : Category := {|
  obj     := { x : C & GroupObject x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & GroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; GroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; GroupHom_comp `2 f `2 g)
|}.

(* The forgetful functor to C, faithful by construction: morphism equivalence
   in [GrpCat] IS equivalence of the underlying C-morphisms. *)
Program Definition GrpCat_Forget : GrpCat ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

#[export] Instance GrpCat_Forget_Faithful : Faithful GrpCat_Forget.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
   The forgetful 函子 to internal 幺半群.  Its arrow action is the

   本节说明相关定义、性质与动机。 IDENTITY underlying data — 即 exactly content [GroupHom] being [MonoidHom] rather than record extending it.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition GrpCat_Mon : GrpCat ⟶ Mon C := {|
  fobj := fun X => (`1 X; group_monoid `2 X);
  fmap := fun _ _ f => (`1 f; `2 f)
|}.

#[export] Instance GrpCat_Mon_Faithful : Faithful GrpCat_Mon.
Proof. constructor; intros X Y f g E; exact E. Qed.

(*
   本节说明相关定义、性质与动机。 And FULL, which costs three lines because two hom types are. CONVERTIBLE: [fobj[GrpCat_Mon] X ~{Mon C}~> fobj[GrpCat_Mon] Y] is [{f & MonoidHom (group_幺半群 ⟦0⟧2 Y) f}], that IS [X ~{GrpCat}~> Y] [GroupHom]'s 定义.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance GrpCat_Mon_Full : Full GrpCat_Mon.
Proof.
  unshelve econstructor.
  - intros X Y g; exact g.
  - intros X Y g; simpl; reflexivity.
Qed.

(*
   [Mon_Forget ◯ GrpCat_Mon] and [GrpCat_Forget] agree on 对象 and on

   本节说明相关定义、性质与动机。 态射, at Leibniz equality. The whole 函子 RECORDS are not compared;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example grpcat_mon_forget_obj (X : GrpCat) :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X := eq_refl.

Example grpcat_mon_forget_map (X Y : GrpCat) (f : X ~> Y) :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] f) = fmap[GrpCat_Forget] f := eq_refl.

(*
   The two 函子 are moreover EQUAL in [函子_StrictEq_Setoid], with

   本节说明相关定义、性质与动机。 every 对象 component literally [eq_refl]. What negative 3 at end file refutes is strictly stronger claim that 复合 is SAME RECORD [GrpCat_Forget]; [Compose] rebuilds three law fields, so that fails while this succeeds.

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
   本节说明相关定义、性质与动机。 One component left inverse law. [p] is projection: [Hmu] says it. commutes two multiplications, [Hinv] two inversions.

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
   The 积 group 对象.  Its 幺半群 half is #503's [幺半群_积]

   本节说明相关定义、性质与动机。 CONSUMED, not reproved; only inversion two inverse laws are new.

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
   本节说明相关定义、性质与动机。 The projections pairing are group homomorphisms — each is.

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

(* Binary products in GrpCat, carried by binary products of C.  No terminal
   object of C is used, and no compatibility between × and ⨂. *)
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

(** ** The forgetful functor sends the finite products to C's own *)

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
   本节说明相关定义、性质与动机。 Each [Fail] below was stripped once its failure kind read off the. message; kinds are kept lexically apart, TYPING first CONVERSION last.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Probes.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CM : @CartesianMonoidal C}.
Context {x y : C} (Gx : @GroupObject C CM x) (Gy : @GroupObject C CM y).
Context (f : x ~> y).

(*
   NEGATIVE 1, TYPING.  A group 对象 cannot be stated over a bare 幺半

   本节：base: inverse laws need diagonal discard. This is whole scope difference from Theory/代数/幺半群/积.v, which quantifies over arbitrary [M : @幺半 C].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun z : obj[C] => @GroupObject C M z).

(* CONTROL for negative 1. *)
Check (fun z : obj[C] => @GroupObject C CM z).

(* NEGATIVE 2, TYPING.  [MonoidHom] is indexed by Theory/Algebra/Monoid.v's
   [Monoid], not by Structure/Monoid.v's [MonoidObject], so the raw field of
   a group object does not fit and #503's class passage
   ([Monoid_of_MonoidObject], used by [group_monoid]) is load-bearing.
     "The term "groupobject_is_monoid" has type "MonoidObject x"" *)
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
   NEGATIVE 3, CONVERSION.  The two forgetful 函子 agree on 对象 and

   本节说明相关定义、性质与动机。 on 态射 at [eq_refl] (the controls below), but 复合 FUNCTOR RECORD is not [GrpCat_Forget]: [Compose] rebuilds [fmap_respects], [fmap_id] [fmap_comp] fresh proof terms.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (eq_refl : Mon_Forget ◯ GrpCat_Mon = GrpCat_Forget).

(* CONTROLS for negative 3. *)
Check (fun (X : GrpCat C) => (eq_refl :
  fobj[Mon_Forget] (fobj[GrpCat_Mon] X) = fobj[GrpCat_Forget] X)).
Check (fun (X Y : GrpCat C) (g : X ~> Y) => (eq_refl :
  fmap[Mon_Forget] (fmap[GrpCat_Mon] g) = fmap[GrpCat_Forget] g)).

End Probes.

(** ** Where the hom/proof identification comes from *)

(*
   Four FORMABILITY negatives.  Over a 范畴 whose hom and proof levels

   本节说明相关定义、性质与动机。 are declared strictly apart, each four donors this file names is rejected, while hom identity at those very levels are accepted — so identification visible every binder above is inherited from four sources, each sufficient its own, is not introduced

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(* CONTROLS: the levels themselves are fine. *)
Check (fun (C : Category@{uo uh up}) (a b : C) => a ~> b).
Check (fun (C : Category@{uo uh up}) (a : C) => id[a]).

(* CONTROLS that the four donor names resolve, so that a rename cannot make
   the rejections below succeed on a reference-not-found error. *)
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
