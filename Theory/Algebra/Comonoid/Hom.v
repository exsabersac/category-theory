Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(* * * Comonoid homomorphisms 范畴 internal comonoids （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/comonoid

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ComonoidHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class ComonoidHom {x y : C} (Cx : Comonoid x) (Cy : Comonoid y)
      (f : x ~> y) : Type := {
  (* f preserves comultiplication: delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx] *)
  hom_delta   : delta[Cy] ∘ f ≈ (f ⨂ f) ∘ delta[Cx];
  (* f preserves the counit: epsilon[Cy] ∘ f ≈ epsilon[Cx] *)
  hom_epsilon : epsilon[Cy] ∘ f ≈ epsilon[Cx]
}.

(* The identity is a comonoid homomorphism. *)
Lemma ComonoidHom_id {x} (Cx : Comonoid x) : ComonoidHom Cx Cx id.
Proof. split; cat. Qed.

(* Comonoid homomorphisms closed under 复合: paste two
 preservation squares, fusing (f ⨂ f) ∘ (g ⨂ g) (f ∘ g) ⨂ (f ∘ g)
 interchange law [bimap_comp]. （已译） *)
Lemma ComonoidHom_comp {x y z} {Cx : Comonoid x} {Cy : Comonoid y}
      {Cz : Comonoid z} {f : y ~> z} {g : x ~> y} :
  ComonoidHom Cy Cz f → ComonoidHom Cx Cy g → ComonoidHom Cx Cz (f ∘ g).
Proof.
  intros F G.
  split.
  - rewrite comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ F).
    rewrite <- comp_assoc.
    rewrite (@hom_delta _ _ _ _ _ G).
    rewrite comp_assoc.
    now rewrite <- bimap_comp.
  - rewrite comp_assoc.
    rewrite (@hom_epsilon _ _ _ _ _ F).
    apply (@hom_epsilon _ _ _ _ _ G).
Qed.

(* Being a comonoid homomorphism transports along ≈ (bimap respects ≈). *)
Lemma ComonoidHom_equiv {x y} {Cx : Comonoid x} {Cy : Comonoid y}
      {f g : x ~> y} :
  f ≈ g → ComonoidHom Cx Cy f → ComonoidHom Cx Cy g.
Proof.
  intros E F.
  split.
  - rewrite <- E.
    apply (@hom_delta _ _ _ _ _ F).
  - rewrite <- E.
    apply (@hom_epsilon _ _ _ _ _ F).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := intros.

Program Definition Comonoid_Iso {x y : C} (i : x ≅ y) (Cx : Comonoid x) :
  Comonoid y := {|
  delta   := (to i ⨂ to i) ∘ delta[Cx] ∘ from i;
  epsilon := epsilon[Cx] ∘ from i
|}.
Next Obligation.
  (* coassociativity: cancel conjugating iso right, then it is
 [delta_coassoc] Cx pushed across associator's 自然性. （已译） *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : ((to i ⨂ to i) ∘ delta[Cx]) ⨂ to i
                ≈ ((to i ⨂ to i) ⨂ to i) ∘ (delta[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_coassoc _ _ _ Cx).
  normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  normal.
  reflexivity.
Qed.
Next Obligation.
  (* left counit: cancel conjugating iso, apply [delta_counit_left] of
 Cx, close 自然性 left unitor's inverse. （已译） *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : epsilon[Cx] ⨂ to i ≈ (id ⨂ to i) ∘ (epsilon[Cx] ⨂ id)).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_left _ _ _ Cx).
  apply from_unit_left_natural.
Qed.
Next Obligation.
  (* right counit: mirror of the previous obligation. *)
  apply (iso_to_epic i).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  normal.
  assert (E : to i ⨂ epsilon[Cx] ≈ (to i ⨂ id) ∘ (id ⨂ epsilon[Cx])).
  { rewrite <- bimap_comp; cat. }
  rewrite E; clear E.
  rewrite <- comp_assoc.
  rewrite (@delta_counit_right _ _ _ Cx).
  apply from_unit_right_natural.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Both components 同构 comonoid homomorphisms with
 respect transported structure. （已译） *)
Lemma ComonoidHom_Iso_to {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom Cx (Comonoid_Iso i Cx) (to i).
Proof.
  split; simpl.
  - rewrite <- !comp_assoc.
    rewrite iso_from_to; cat.
  - rewrite <- comp_assoc.
    rewrite iso_from_to; cat.
Qed.

Lemma ComonoidHom_Iso_from {x y} (i : x ≅ y) (Cx : Comonoid x) :
  ComonoidHom (Comonoid_Iso i Cx) Cx (from i).
Proof.
  split; simpl.
  - symmetry.
    rewrite comp_assoc.
    normal.
    rewrite !iso_from_to; cat.
  - reflexivity.
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Comon : Category := {|
  obj     := { x : C & Comonoid x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & ComonoidHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; ComonoidHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; ComonoidHom_comp `2 f `2 g)
|}.

(* The forgetful 函子 Comon(C) ⟶ C projects out underlying 对象
 态射; it faithful construction ([Comon_Forget_Faithful]
 below). （已译） *)
Program Definition Comon_Forget : Comon ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithfulness is definitional: morphism equivalence in Comon(C) IS
   equivalence of the underlying C-morphisms, which is what [fmap] projects
   out. *)
#[export] Instance Comon_Forget_Faithful : Faithful Comon_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

End ComonoidHom.

Arguments Comon C {M}.
