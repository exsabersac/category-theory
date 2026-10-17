Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Construction.Postcompose.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Adjunctions limits 函子 范畴 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Postcomposition: [F ◯ −] 函子 between 函子 范畴 （已译） *)

Section Postcomposition.

Context {J X A : Category}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition postcompose (F : X ⟶ A) : [J, X] ⟶ [J, A] := Postcompose (D:=J) F.

Example postcompose_obj (F : X ⟶ A) (S : J ⟶ X) :
  postcompose F S = F ◯ S := eq_refl.

Example postcompose_component (F : X ⟶ A) {S T : J ⟶ X} (θ : S ⟹ T) (j : J) :
  transform[fmap[postcompose F] θ] j = fmap[F] (transform[θ] j) := eq_refl.

End Postcomposition.

(* 相关说明。 （已译） *)

Section PostcomposeAdjunction.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

#[local] Obligation Tactic := idtac.

(*
   本节说明伴随、自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Let η : Id ⟹ G ◯ F := @Transformation.unit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).
Let ε : F ◯ G ⟹ Id := @Transformation.counit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).

Lemma postcompose_unit_natural {x y : X} (f : x ~> y) :
  fmap[G] (fmap[F] f) ∘ @Category.Theory.Adjunction.unit _ _ F G Adj x
    ≈ @Category.Theory.Adjunction.unit _ _ F G Adj y ∘ f.
Proof. exact (naturality[η] _ _ f). Qed.

Lemma postcompose_counit_natural {x y : A} (f : x ~> y) :
  @Category.Theory.Adjunction.counit _ _ F G Adj y ∘ fmap[F] (fmap[G] f)
    ≈ f ∘ @Category.Theory.Adjunction.counit _ _ F G Adj x.
Proof. exact (@naturality_sym _ _ _ _ ε _ _ f). Qed.

(* 相关说明。 （已译） *)
Program Definition postcompose_unit_at (S : J ⟶ X) : S ⟹ G ◯ (F ◯ S) := {|
  transform := fun j => @Category.Theory.Adjunction.unit _ _ F G Adj (S j)
|}.
Next Obligation. intros S x y f; simpl; apply postcompose_unit_natural. Qed.
Next Obligation.
  intros S x y f; simpl; symmetry; apply postcompose_unit_natural.
Qed.

Program Definition postcompose_unit :
  Id ⟹ postcompose (J:=J) G ◯ postcompose (J:=J) F := {|
  transform := postcompose_unit_at
|}.
Next Obligation. intros S T θ j; simpl; apply postcompose_unit_natural. Qed.
Next Obligation.
  intros S T θ j; simpl; symmetry; apply postcompose_unit_natural.
Qed.

(* 相关说明。 （已译） *)
Program Definition postcompose_counit_at (T : J ⟶ A) : F ◯ (G ◯ T) ⟹ T := {|
  transform := fun j => @Category.Theory.Adjunction.counit _ _ F G Adj (T j)
|}.
Next Obligation.
  intros T x y f; simpl; symmetry; apply postcompose_counit_natural.
Qed.
Next Obligation. intros T x y f; simpl; apply postcompose_counit_natural. Qed.

Program Definition postcompose_counit :
  postcompose (J:=J) F ◯ postcompose (J:=J) G ⟹ Id := {|
  transform := postcompose_counit_at
|}.
Next Obligation.
  intros S T θ j; simpl; symmetry; apply postcompose_counit_natural.
Qed.
Next Obligation. intros S T θ j; simpl; apply postcompose_counit_natural. Qed.

(*
   本节说明 FunctorCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition postcompose_adjunction_transform :
  postcompose (J:=J) F ∹ postcompose (J:=J) G := {|
  Transformation.unit   := postcompose_unit;
  Transformation.counit := postcompose_counit
|}.
Next Obligation.
  intros S j; simpl; rewrite !fmap_id.
  apply (@Category.Theory.Adjunction.counit_fmap_unit _ _ F G Adj).
Qed.
Next Obligation.
  intros T j; simpl; rewrite !fmap_id.
  apply (@Category.Theory.Adjunction.fmap_counit_unit _ _ F G Adj).
Qed.

Definition postcompose_adjunction : postcompose (J:=J) F ⊣ postcompose (J:=J) G :=
  Adjunction_from_Transform postcompose_adjunction_transform.

(* 相关说明。 （已译） *)
Example postcompose_unit_component (S : J ⟶ X) (j : J) :
  transform[transform[postcompose_unit] S] j
    = @Category.Theory.Adjunction.unit _ _ F G Adj (S j) := eq_refl.

Example postcompose_counit_component (T : J ⟶ A) (j : J) :
  transform[transform[postcompose_counit] T] j
    = @Category.Theory.Adjunction.counit _ _ F G Adj (T j) := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma postcompose_adjunction_unit (S : J ⟶ X) (j : J) :
  transform[@Category.Theory.Adjunction.unit _ _ _ _ postcompose_adjunction S] j
    ≈ @Category.Theory.Adjunction.unit _ _ F G Adj (S j).
Proof. simpl; rewrite !fmap_id; apply id_left. Qed.

Lemma postcompose_adjunction_counit (T : J ⟶ A) (j : J) :
  transform[@Category.Theory.Adjunction.counit _ _ _ _ postcompose_adjunction T] j
    ≈ @Category.Theory.Adjunction.counit _ _ F G Adj (T j).
Proof. simpl; rewrite !fmap_id; apply id_right. Qed.

End PostcomposeAdjunction.

(* 相关说明。 （已译） *)

Section Precomposition.

Context {C D E : Category}.

(* Theory/Kan/Extension.v's [Induced] [− ◯ F]; 这是 name the
 命题's notation, [F^*]. （已译） *)
Definition precompose (F : C ⟶ D) : [D, E] ⟶ [C, E] := @Induced C D F E.

Example precompose_obj (F : C ⟶ D) (S : D ⟶ E) :
  precompose F S = S ◯ F := eq_refl.

Example precompose_component (F : C ⟶ D) {S T : D ⟶ E} (θ : S ⟹ T) (c : C) :
  transform[fmap[precompose F] θ] c = transform[θ] (F c) := eq_refl.

End Precomposition.

Section PrecomposeAdjunction.

Context {C D E : Category}.
Context {F : C ⟶ D} {G : D ⟶ C}.
Context (Adj : F ⊣ G).

#[local] Obligation Tactic := idtac.

Let η : Id ⟹ G ◯ F := @Transformation.unit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).
Let ε : F ◯ G ⟹ Id := @Transformation.counit _ _ _ _ (Adjunction_to_Transform (A:=Adj)).

(* 相关说明。 （已译） *)
Program Definition precompose_unit_at (S : C ⟶ E) : S ⟹ (S ◯ G) ◯ F := {|
  transform := fun c => fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c)
|}.
Next Obligation.
  intros S x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects; exact (naturality[η] _ _ f).
Qed.
Next Obligation.
  intros S x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects;
  exact (@naturality_sym _ _ _ _ η _ _ f).
Qed.

Program Definition precompose_unit :
  Id ⟹ precompose (E:=E) F ◯ precompose (E:=E) G := {|
  transform := precompose_unit_at
|}.
Next Obligation. intros S T θ c; simpl; apply naturality_sym. Qed.
Next Obligation. intros S T θ c; simpl; apply naturality. Qed.

(* The counit: at [T : D ⟶ E] it is [fmap[T] (ε d)]. *)
Program Definition precompose_counit_at (T : D ⟶ E) : (T ◯ F) ◯ G ⟹ T := {|
  transform := fun d => fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d)
|}.
Next Obligation.
  intros T x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects; exact (naturality[ε] _ _ f).
Qed.
Next Obligation.
  intros T x y f; simpl.
  rewrite <- !fmap_comp; apply fmap_respects;
  exact (@naturality_sym _ _ _ _ ε _ _ f).
Qed.

Program Definition precompose_counit :
  precompose (E:=E) G ◯ precompose (E:=E) F ⟹ Id := {|
  transform := precompose_counit_at
|}.
Next Obligation. intros S T θ d; simpl; apply naturality_sym. Qed.
Next Obligation. intros S T θ d; simpl; apply naturality. Qed.

(* 相关说明。 （已译） *)
Program Definition precompose_adjunction_transform :
  precompose (E:=E) G ∹ precompose (E:=E) F := {|
  Transformation.unit   := precompose_unit;
  Transformation.counit := precompose_counit
|}.
Next Obligation.
  intros S d; simpl.
  rewrite <- fmap_comp,
    (@Category.Theory.Adjunction.fmap_counit_unit _ _ F G Adj), !fmap_id.
  reflexivity.
Qed.
Next Obligation.
  intros T c; simpl.
  rewrite <- fmap_comp,
    (@Category.Theory.Adjunction.counit_fmap_unit _ _ F G Adj), !fmap_id.
  reflexivity.
Qed.

Definition precompose_adjunction : precompose (E:=E) G ⊣ precompose (E:=E) F :=
  Adjunction_from_Transform precompose_adjunction_transform.

Example precompose_unit_component (S : C ⟶ E) (c : C) :
  transform[transform[precompose_unit] S] c
    = fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c) := eq_refl.

Example precompose_counit_component (T : D ⟶ E) (d : D) :
  transform[transform[precompose_counit] T] d
    = fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d) := eq_refl.

(* Likewise delivered 伴随's own accessors. （已译） *)
Lemma precompose_adjunction_unit (S : C ⟶ E) (c : C) :
  transform[@Category.Theory.Adjunction.unit _ _ _ _ precompose_adjunction S] c
    ≈ fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c).
Proof. simpl; rewrite !fmap_id; apply id_left. Qed.

Lemma precompose_adjunction_counit (T : D ⟶ E) (d : D) :
  transform[@Category.Theory.Adjunction.counit _ _ _ _ precompose_adjunction T] d
    ≈ fmap[T] (@Category.Theory.Adjunction.counit _ _ F G Adj d).
Proof. simpl; rewrite !fmap_id; apply id_right. Qed.

End PrecomposeAdjunction.

(* 相关说明。 （已译） *)

Section Square.

Context {J X A : Category}.
Context (F : X ⟶ A).

#[local] Obligation Tactic := idtac.

(* The left adjoints commute — but NOT nose: [(postcompose F ◯ Δ) x]
 has [fmap := fun _ _ _ => fmap[F] id] where [Δ (F x)] has [id] (探针
 N1). They agree up natural 同构 whose every component is
 恒等.（已译） *)
Program Definition square_at (x : X) :
  (postcompose (J:=J) F ◯ @Diagonal X J) x ≅[Fun] (@Diagonal A J ◯ F) x := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j k f; simpl; rewrite fmap_id; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.

Program Definition square_iso :
  postcompose (J:=J) F ◯ @Diagonal X J ≅[Fun] @Diagonal A J ◯ F := {|
  to   := {| transform := fun x => to   (square_at x) |};
  from := {| transform := fun x => from (square_at x) |}
|}.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x y f j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.
Next Obligation. intros x j; simpl; cat. Qed.

(* The same square 函子 equality, oriented transport below. （已译） *)
Definition square_equiv :
  @Diagonal A J ◯ F ≈ postcompose (J:=J) F ◯ @Diagonal X J :=
  iso_equiv (iso_sym square_iso).

End Square.

Section Remark.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (LX : HasLimitsOfShape J X).
Context (LA : HasLimitsOfShape J A).

(* Left column then top row: [Δ_X ⊣ Lim_X] composed with
   [postcompose F ⊣ postcompose G]. *)
Definition left_route :
  (postcompose (J:=J) F ◯ @Diagonal X J)
    ⊣ (LimitFunctor LX ◯ postcompose (J:=J) G) :=
  Adjunction_Compose (Diagonal_Limit_Adjunction LX) (postcompose_adjunction Adj).

(* Bottom row then right column: [F ⊣ G] composed with [Δ_A ⊣ Lim_A]. *)
Definition right_route :
  (@Diagonal A J ◯ F) ⊣ (G ◯ LimitFunctor LA) :=
  Adjunction_Compose Adj (Diagonal_Limit_Adjunction LA).

(* Transport left route across square, so both routes are
 伴随 SAME 左伴随. （已译） *)
Definition left_route' :
  (@Diagonal A J ◯ F) ⊣ (LimitFunctor LX ◯ postcompose (J:=J) G) :=
  adjunction_along_left_iso (square_equiv F) left_route.

(* Uniqueness of right adjoints (Theory/Adjunction.v's [right_adjoint_iso])
   — not a re-proof. *)
Theorem Lim_commutes_right_adjoint :
  LimitFunctor LX ◯ postcompose (J:=J) G ≈ G ◯ LimitFunctor LA.
Proof using A Adj F G J LA LX X.
  exact (right_adjoint_iso _ _ _ left_route' right_route).
Qed.

(* The same statement as a natural isomorphism in [[[J, A], X]]. *)
Definition Lim_commutes_nat_iso :
  LimitFunctor LX ◯ postcompose (J:=J) G ≅[Fun] G ◯ LimitFunctor LA :=
  equiv_iso Lim_commutes_right_adjoint.

(* Pointwise: [lim (G ◯ T) ≅ G (lim T)], the classical reading of RAPL. *)
Definition lim_of_right_adjoint (T : J ⟶ A) :
  lim_obj LX (G ◯ T) ≅ G (lim_obj LA T) :=
  projT1 Lim_commutes_right_adjoint T.

End Remark.

(** ** The cone-level conclusion *)

Section ConeLevel.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (LA : HasLimitsOfShape J A).

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition right_adjoint_carries_lim_counit (T : J ⟶ A) :
  IsLimitCone (FCone G (@limit_cone _ _ _ (LA T))) :=
  right_adjoint_PreservesLimitCone Adj T (@limit_cone _ _ _ (LA T))
    (limit_limitcone (LA T)).

Example carried_leg_is_counit (T : J ⟶ A) (j : J) :
  cone_leg (FCone G (@limit_cone _ _ _ (LA T))) j
    ≈ fmap[G] (transform[lim_counit LA T] j).
Proof.
  rewrite FCone_leg, lim_counit_is_limit_leg; reflexivity.
Qed.

End ConeLevel.
