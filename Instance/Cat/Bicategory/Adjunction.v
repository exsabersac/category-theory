Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Theory.Adjunction.

Generalizable All Variables.

(** Adjunctions and mates in the bicategory `Cat` *)

(*
 nLab: https://ncatlab.org/nlab/show/mate

   本文件给出伴随实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(* 1. Internal adjunctions in `Cat` coincide with `F ∹ U` and `F ⊣ U`. *)
(* ------------------------------------------------------------------ *)

Section CatAdjunction.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context {U : D ⟶ C}.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* Forward: an internal adjunction supplies the unit/counit data directly, and
   its bicategorical triangle identities give the two zig-zag identities. *)
Program Definition Cat_BicatAdjunction_to_Transform
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ∹ U := {|
  Transformation.unit   := adj_unit   (B:=Cat_Bicategory) F U;
  Transformation.counit := adj_counit (B:=Cat_Bicategory) F U
|}.
Next Obligation.
  (* counit_fmap_unit: εF ∘ Fη = 1, read off the left bicat triangle at X. *)
  intros H X.
  pose proof (adj_triangle_left (B:=Cat_Bicategory) F U X) as TLX.
  simpl in TLX.
  rewrite !fmap_id in TLX.
  rewrite ?id_left, ?id_right in TLX.
  exact TLX.
Qed.
Next Obligation.
  (* fmap_counit_unit: Uε ∘ ηU = 1, read off the right bicat triangle at X. *)
  intros H X.
  pose proof (adj_triangle_right (B:=Cat_Bicategory) F U X) as TRX.
  simpl in TRX.
  rewrite !fmap_id in TRX.
  rewrite ?id_left, ?id_right in TRX.
  exact TRX.
Qed.

(* Backward: the unit/counit data assembles into an internal adjunction, its two
   bicategorical triangle identities holding componentwise by the same collapse,
   where each side reduces to a zig-zag identity of the transform. *)
Program Definition Cat_Transform_to_BicatAdjunction
  (A : F ∹ U) : BicatAdjunction (B:=Cat_Bicategory) F U := {|
  adj_unit   := @Category.Adjunction.Natural.Transformation.unit   _ _ _ _ A;
  adj_counit := @Category.Adjunction.Natural.Transformation.counit _ _ _ _ A
|}.
Next Obligation.
  (* adj_triangle_left, componentwise, is εF ∘ Fη = 1. *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.counit_fmap_unit _ _ _ _ A X).
Qed.
Next Obligation.
  (* adj_triangle_right, componentwise, is Uε ∘ ηU = 1. *)
  intros A X.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  exact (@Category.Adjunction.Natural.Transformation.fmap_counit_unit _ _ _ _ A X).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Cat_BicatAdjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ∹ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_to_Transform.
  - exact Cat_Transform_to_BicatAdjunction.
Qed.

(* Composing with the `F ∹ U ↔ F ⊣ U` bridge (Universal.v): an internal
   adjunction in `Cat` yields a hom-set adjunction, and conversely. *)
Definition Cat_BicatAdjunction_Adjunction
  (H : BicatAdjunction (B:=Cat_Bicategory) F U) : F ⊣ U :=
  Adjunction_from_Transform (Cat_BicatAdjunction_to_Transform H).

Definition Cat_Adjunction_BicatAdjunction
  (A : F ⊣ U) : BicatAdjunction (B:=Cat_Bicategory) F U :=
  Cat_Transform_to_BicatAdjunction (Adjunction_to_Transform (A:=A)).

Theorem Cat_BicatAdjunction_Adjunction_iff :
  BicatAdjunction (B:=Cat_Bicategory) F U  ↔  (F ⊣ U).
Proof.
  split.
  - exact Cat_BicatAdjunction_Adjunction.
  - exact Cat_Adjunction_BicatAdjunction.
Qed.

End CatAdjunction.

(* ------------------------------------------------------------------ *)
(* 2. The two hom-adjunctions in `Cat` are the transpose and the       *)
(*    counit whiskering.                                                *)
(* ------------------------------------------------------------------ *)

Section CatHomAdjunction.

Context {vx vy : Category}.
Context {F : vx ⟶ vy} {U : vy ⟶ vx}.
Context (A : BicatAdjunction (B:=Cat_Bicategory) F U).

(* Precomposition transpose `precomp_to A : (F ◯ c ⟹ d) → (c ⟹ U ◯ d)`, read
   componentwise, is the unit-transpose `⌊−⌋` of the induced adjunction: the
   unitor/associator components of `preΘ` collapse to identities. *)
Lemma Cat_precomp_to_component {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ fmap[U] (σ t) ∘ adj_unit (B:=Cat_Bicategory) F U (fobj[c] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Cat_precomp_to_transpose {w0 : Category}
  {c : w0 ⟶ vx} {d : w0 ⟶ vy} (σ : F ◯ c ⟹ d) (t : w0) :
  transform[precomp_to A σ] t
    ≈ to adj[Cat_BicatAdjunction_Adjunction A] (σ t).
Proof.
  rewrite Cat_precomp_to_component.
  reflexivity.
Qed.

(* Postcomposition transpose `postcomp_to A : (c ⟹ e ◯ F) → (c ◯ U ⟹ e)`, read
   componentwise, is the counit `ε` whiskered by `e`: the unitor/associator
   components of `postΛ` collapse to identities. *)
Lemma Cat_postcomp_to_component {w0 : Category}
  {c : vx ⟶ w0} {e : vy ⟶ w0} (γ : c ⟹ e ◯ F) (t : vy) :
  transform[postcomp_to A γ] t
    ≈ fmap[e] (adj_counit (B:=Cat_Bicategory) F U t) ∘ γ (fobj[U] t).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

End CatHomAdjunction.

(* ------------------------------------------------------------------ *)
(* 3. Mates in `Cat` unfold to the transposes (the payoff).            *)
(* ------------------------------------------------------------------ *)

Section CatMates.

Context {x y x' y' : Category}.
Context {F  : x  ⟶ y }  {U  : y  ⟶ x }  (Af  : BicatAdjunction (B:=Cat_Bicategory) F  U ).
Context {F' : x' ⟶ y'}  {U' : y' ⟶ x'}  (Af' : BicatAdjunction (B:=Cat_Bicategory) F' U').
Context {a : x ⟶ x'} {b : y ⟶ y'}.
Context (σ : F' ◯ a ⟹ b ◯ F).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Cat_mate_unfold_raw (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ (fmap[U'] (σ (fobj[U] Z))
             ∘ adj_unit (B:=Cat_Bicategory) F' U' (fobj[a] (fobj[U] Z))).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

(*
   本节说明伴随、hom、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Cat_mate_unfold (Z : y) :
  transform[mate Af Af' σ] Z
    ≈ fmap[U'] (fmap[b] (adj_counit (B:=Cat_Bicategory) F U Z))
        ∘ to adj[Cat_BicatAdjunction_Adjunction Af'] (σ (fobj[U] Z)).
Proof.
  rewrite Cat_mate_unfold_raw.
  reflexivity.
Qed.

End CatMates.
