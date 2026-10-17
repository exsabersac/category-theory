Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Adjunction.
Require Import Category.Instance.Two.
Require Import Category.Instance.One.

Generalizable All Variables.

(* * * The conjugate bijection mates bijection at 恒等 bounding cells （已译） *)

(*
   本文件给出双范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---- the missing dual of Cat_mate_unfold_raw ---- *)

Section MateInvUnfold.

Context {x y x' y' : Category}.
Context {F  : x  ⟶ y } {U  : y  ⟶ x } (Af  : BicatAdjunction (B:=Cat_Bicategory) F  U ).
Context {F' : x' ⟶ y'} {U' : y' ⟶ x'} (Af' : BicatAdjunction (B:=Cat_Bicategory) F' U').
Context {a : x ⟶ x'} {b : y ⟶ y'}.
Context (t : a ◯ U ⟹ U' ◯ b).

Theorem Cat_mate_inv_unfold_raw (Z : x) :
  transform[mate_inv Af Af' t] Z
    ≈ adj_counit (B:=Cat_Bicategory) F' U' (fobj[b] (fobj[F] Z))
        ∘ fmap[F'] (transform[t] (fobj[F] Z)
             ∘ fmap[a] (adj_unit (B:=Cat_Bicategory) F U Z)).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

End MateInvUnfold.

(* ---- padding and agreement ---- *)

Section Agreement.

Context {C D : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A  : F  ⊣ U).
Context (A' : F' ⊣ U').

#[local] Obligation Tactic := idtac.

Program Definition Cat_conj_padL (σ : F' ⟹ F) : (F' ◯ Id) ⟹ (Id ◯ F) :=
  {| transform := fun x => transform[σ] x |}.
Next Obligation. intros σ x y f; apply (naturality σ). Qed.
Next Obligation. intros σ x y f; apply (naturality_sym σ). Qed.

Program Definition Cat_conj_unpadL (s : (F' ◯ Id) ⟹ (Id ◯ F)) : F' ⟹ F :=
  {| transform := fun x => transform[s] x |}.
Next Obligation. intros s x y f; apply (naturality s). Qed.
Next Obligation. intros s x y f; apply (naturality_sym s). Qed.

Program Definition Cat_conj_padR (τ : U ⟹ U') : (Id ◯ U) ⟹ (U' ◯ Id) :=
  {| transform := fun a => transform[τ] a |}.
Next Obligation. intros τ a b g; apply (naturality τ). Qed.
Next Obligation. intros τ a b g; apply (naturality_sym τ). Qed.

Program Definition Cat_conj_unpadR (t : (Id ◯ U) ⟹ (U' ◯ Id)) : U ⟹ U' :=
  {| transform := fun a => transform[t] a |}.
Next Obligation. intros t a b g; apply (naturality t). Qed.
Next Obligation. intros t a b g; apply (naturality_sym t). Qed.

Definition Cat_conj_mate (σ : F' ⟹ F) : U ⟹ U' :=
  Cat_conj_unpadR
    (mate (Cat_Adjunction_BicatAdjunction A)
          (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
          (Cat_conj_padL σ)).

Definition Cat_conj_mate_inv (τ : U ⟹ U') : F' ⟹ F :=
  Cat_conj_unpadL
    (mate_inv (Cat_Adjunction_BicatAdjunction A)
              (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
              (Cat_conj_padR τ)).

Theorem Cat_conj_mate_component (σ : F' ⟹ F) (Z : C) :
  transform[mate (Cat_Adjunction_BicatAdjunction A)
                 (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
                 (Cat_conj_padL σ)] Z
    ≈ transform[conj_mate A A' σ] Z.
Proof.
  rewrite Cat_mate_unfold_raw.
  simpl.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite ?fmap_id, ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem Cat_conj_mate_agrees (σ : F' ⟹ F) :
  Cat_conj_mate σ ≈ conj_mate A A' σ.
Proof. intro Z; apply Cat_conj_mate_component. Qed.

Theorem Cat_conj_mate_inv_component (τ : U ⟹ U') (Z : D) :
  transform[mate_inv (Cat_Adjunction_BicatAdjunction A)
                     (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
                     (Cat_conj_padR τ)] Z
    ≈ transform[conj_mate_inv A A' τ] Z.
Proof.
  rewrite Cat_mate_inv_unfold_raw.
  simpl.
  rewrite (from_adj_counit (H:=A')).
  rewrite ?fmap_id, ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem Cat_conj_mate_inv_agrees (τ : U ⟹ U') :
  Cat_conj_mate_inv τ ≈ conj_mate_inv A A' τ.
Proof. intro Z; apply Cat_conj_mate_inv_component. Qed.

(* the pad/unpad pair Sets 同构, so conjugate_bijection is
 literally mate_iso conjugated padding （已译） *)

Program Definition Cat_conj_padL_iso :
  @Isomorphism Sets (conj_dom (F:=F) (F':=F'))
                    (@mate_dom Cat_Bicategory D C D C F F' Id Id) := {|
  to   := {| morphism := Cat_conj_padL |};
  from := {| morphism := Cat_conj_unpadL |}
|}.
Next Obligation. intros s1 s2 Hs x; exact (Hs x). Qed.
Next Obligation. intros s1 s2 Hs x; exact (Hs x). Qed.
Next Obligation. intros s x; reflexivity. Qed.
Next Obligation. intros s x; reflexivity. Qed.

Program Definition Cat_conj_unpadR_iso :
  @Isomorphism Sets (@mate_cod Cat_Bicategory D C D C U U' Id Id)
                    (conj_cod (U:=U) (U':=U')) := {|
  to   := {| morphism := Cat_conj_unpadR |};
  from := {| morphism := Cat_conj_padR |}
|}.
Next Obligation. intros t1 t2 Ht a; exact (Ht a). Qed.
Next Obligation. intros t1 t2 Ht a; exact (Ht a). Qed.
Next Obligation. intros t a; reflexivity. Qed.
Next Obligation. intros t a; reflexivity. Qed.

Theorem conjugate_bijection_is_mate_iso (σ : F' ⟹ F) :
  to (conjugate_bijection A A') σ
    ≈ to Cat_conj_unpadR_iso
        (to (mate_iso (Cat_Adjunction_BicatAdjunction A)
                      (Cat_Adjunction_BicatAdjunction A')
                      (a:=Id[D]) (b:=Id[C]))
            (to Cat_conj_padL_iso σ)).
Proof. intro Z; symmetry; apply Cat_conj_mate_component. Qed.

End Agreement.

(* ---- boundary: non-恒等 bounding cells mate an
 invertible 2-cell need not invertible ---- （已译） *)

Program Definition ConstY : _1 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Definition twoTerm (x : TwoObj) : x ~{_2}~> TwoY :=
  match x with
  | TwoX => TwoXY
  | TwoY => TwoIdY
  end.

Program Definition adjE : Erase _2 ⊣ ConstY :=
  Build_Adjunction' (F:=Erase _2) (U:=ConstY)
    (fun x y => {| to   := {| morphism := fun _ => twoTerm x |}
                 ; from := {| morphism := fun _ => ttt |} |}) _ _.
Next Obligation. now apply Two_thin. Qed.
Next Obligation. now destruct x0. Qed.
Next Obligation. now apply Two_thin. Qed.
Next Obligation. now apply Two_thin. Qed.

Definition BAf  : BicatAdjunction (B:=Cat_Bicategory) (Id[_2]) (Id[_2]) :=
  Cat_Adjunction_BicatAdjunction Adjunction_Id.

Definition BAf' : BicatAdjunction (B:=Cat_Bicategory) (Erase _2) ConstY :=
  Cat_Adjunction_BicatAdjunction adjE.

Definition boundary_square : (Erase _2 ◯ Id[_2]) ⟹ (Erase _2 ◯ Id[_2]) := nat_id.

Program Definition boundary_square_iso :
  @IsIsomorphism (@bicat Cat_Bicategory _2 _1) _ _ boundary_square :=
  {| two_sided_inverse := boundary_square |}.

Definition boundary_mate :=
  mate BAf BAf' (a:=Id[_2]) (b:=Erase _2) boundary_square.

Theorem mate_of_iso_not_invertible :
  @IsIsomorphism (@bicat Cat_Bicategory _2 _2) _ _ boundary_mate → False.
Proof.
  intro H.
  exact (TwoHom_Y_X_absurd
           (transform[two_sided_inverse (IsIsomorphism:=H)] TwoX)).
Qed.

Theorem boundary_mate_component (Z : _2) :
  transform[boundary_mate] Z ≈ twoTerm Z.
Proof.
  unfold boundary_mate.
  rewrite Cat_mate_unfold_raw.
  now apply Two_thin.
Qed.
