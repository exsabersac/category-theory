Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.

Generalizable All Variables.

(** * Colimits of the Type-valued [Top]: what is formable, and the walls *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/quotient+space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** Coproducts at an index universe at or below the points *)

Section TSigma.

Universes o i.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → TopSpace@{o}).

Definition tsig_setoid : SetoidObject@{o o} :=
  Sets_icoprod_obj (fun k => top_carrier (X k)).

(* The final topology for the injections, Type-valued: a predicate is open
   when it respects the points' equality and every restriction to a
   summand is open. *)
Definition tsig_open (W : tsig_setoid → Type@{o}) : Type@{o} :=
  ((∀ p q : tsig_setoid, p ≈ q → W p → W q) ∧
   (∀ k : Ix, IsOpen (X k) (fun x => W (existT _ k x))))%type.

Lemma tsig_open_respects (U V : tsig_setoid → Type@{o}) :
  (∀ p, U p ↔ V p) → tsig_open U → tsig_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros p q e v. apply (fst (H q)), (Hp p q e), (snd (H p)), v.
  - intro k.
    exact (open_respects (X k) _ _ (fun x => H (existT _ k x)) (Ho k)).
Qed.

Lemma tsig_open_proper (U : tsig_setoid → Type@{o}) :
  tsig_open U → ∀ p q : tsig_setoid, p ≈ q → U p → U q.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma tsig_open_union (I : Type@{o}) (U : I → tsig_setoid → Type@{o}) :
  (∀ j, tsig_open (U j)) → tsig_open (fun p => { j : I & U j p }).
Proof.
  intro HU; split.
  - intros p q e [j u]; exact (j; fst (HU j) p q e u).
  - intro k. exact (open_union (X k) I (fun j x => U j (existT _ k x))
                      (fun j => snd (HU j) k)).
Qed.

Lemma tsig_open_whole : tsig_open (fun _ => poly_unit@{o}).
Proof. split; [intros; exact ttt|intro k; exact (open_whole (X k))]. Qed.

Lemma tsig_open_inter (U V : tsig_setoid → Type@{o}) :
  tsig_open U → tsig_open V → tsig_open (fun p => U p ∧ V p).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros p q e [u v]; exact (HpU p q e u, HpV p q e v).
  - intro k; exact (open_inter (X k) _ _ (HoU k) (HoV k)).
Qed.

Definition TSigma : TopSpace@{o} := {|
  top_carrier   := tsig_setoid;
  IsOpen        := tsig_open;
  open_respects := tsig_open_respects;
  open_proper   := tsig_open_proper;
  open_union    := tsig_open_union;
  open_whole    := tsig_open_whole;
  open_inter    := tsig_open_inter
|}.

Example TSigma_carrier : top_carrier TSigma = tsig_setoid := eq_refl.

Example TSigma_open (W : tsig_setoid → Type@{o}) :
  IsOpen TSigma W = tsig_open W := eq_refl.

End TSigma.

Section TSigmaUMP.

Universes o h i.
Constraint o < h.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → Top@{h o}).

Definition tsig_inj (k : Ix) : X k ~{Top@{h o}}~> TSigma Ix X :=
  Build_ContinuousMorphism (X k) (TSigma Ix X)
    (Sets_icoprod_inj (fun k => top_carrier (X k)) k)
    (fun W HW => snd HW k).

Lemma tsig_case_cont (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  Continuous (TSigma Ix X) Z
    (Sets_icoprod_case (fun k => top_carrier (X k)) (top_carrier Z)
       (fun k => continuous_map (iota k))).
Proof.
  intros W HW; split.
  - intros p q e w.
    exact (open_proper Z W HW _ _
             (proper_morphism (Sets_icoprod_case (fun k => top_carrier (X k))
                (top_carrier Z) (fun k => continuous_map (iota k))) p q e) w).
  - intro k. exact (continuity (iota k) W HW).
Qed.

Definition tsig_case (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  TSigma Ix X ~{Top@{h o}}~> Z :=
  Build_ContinuousMorphism _ _ _ (tsig_case_cont Z iota).

Definition tsig_desc (Z : Top@{h o}) (iota : ∀ k, X k ~{Top@{h o}}~> Z) :
  ∃! u : TSigma Ix X ~{Top@{h o}}~> Z, ∀ k, u ∘ tsig_inj k ≈ iota k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tsig_case Z iota).
  - intros k x; reflexivity.
  - intros v Hv [k x]; simpl. symmetry. exact (Hv k x).
Defined.

End TSigmaUMP.

(* Indexed coproducts of the Type-valued [Top], at index types at or below
   the points' universe. *)
Definition Top_HasIndexedCoproducts_small@{o h +| o < h +} :
  HasIndexedCoproducts Top@{h o} :=
  @Build_HasIndexedCoproducts Top@{h o}
    (fun A f => TSigma A f)
    (fun A f k => tsig_inj A f k)
    (fun A f => Build_IsIndexedCoproduct f _ _
                  (fun c iota => tsig_desc A f c iota)).

(** ** Coequalizers: the quotient topology on the [Sets] coequalizer *)

Section TCoeq.

Universes o h.
Constraint o < h.

Context {x y : Top@{h o}} (f g : x ~{Top@{h o}}~> y).

Definition tcoeq_obj : TopSpace@{o} :=
  TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
    (sets_coeq_proj (continuous_map f) (continuous_map g)).

Definition tcoeq_proj : y ~{Top@{h o}}~> tcoeq_obj := tquot_proj y _ _.

Lemma tcoeq_cofork : tcoeq_proj ∘ f ≈ tcoeq_proj ∘ g.
Proof. intro a; simpl. exact (cq_glue _ _ a). Qed.

(* The descended map on points: a coforking map respects the relation the
   pair generates (Instance/Sets/Coequalizer.v's [coeq_rel_of_cofork]). *)
Definition tcoeq_med {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  SetoidMorphism@{o o o} (SetsCoeq (continuous_map f) (continuous_map g))
    (top_carrier z) :=
  @Build_SetoidMorphism _
    (is_setoid (SetsCoeq (continuous_map f) (continuous_map g))) _
    (is_setoid (top_carrier z))
    (continuous_map k)
    (fun b1 b2 H =>
       coeq_rel_of_cofork (continuous_map f) (continuous_map g)
         (continuous_map k) Hk b1 b2 H).

Definition tcoeq_desc {z : Top@{h o}} (k : y ~{Top@{h o}}~> z)
  (Hk : k ∘ f ≈ k ∘ g) :
  ∃! u : tcoeq_obj ~{Top@{h o}}~> z, u ∘ tcoeq_proj ≈ k.
Proof.
  unshelve eapply Build_Unique.
  - exact (tquot_desc y (SetsCoeq (continuous_map f) (continuous_map g))
      (sets_coeq_proj (continuous_map f) (continuous_map g)) z k
      (tcoeq_med k Hk) (fun b => reflexivity _)).
  - intro b; reflexivity.
  - intros v Hv b. simpl. symmetry. exact (Hv b).
Defined.

Definition tcoeq_IsCoequalizer :
  IsCoequalizer f g tcoeq_obj tcoeq_proj :=
  @Build_IsCoequalizer Top@{h o} x y f g tcoeq_obj tcoeq_proj tcoeq_cofork
    (fun z k Hk => tcoeq_desc k Hk).

End TCoeq.

Definition Top_HasCoequalizers@{o h +| o < h +} : HasCoequalizers Top@{h o} :=
  @Build_HasCoequalizers Top@{h o}
    (fun x y f g =>
       (tcoeq_obj f g; (tcoeq_proj f g; tcoeq_IsCoequalizer f g))).

(* The coequalizer IS the quotient topology on the [Sets] coequalizer of
   the underlying maps, on the nose. *)
Example Top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.
