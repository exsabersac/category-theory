Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Isomorphism.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Functoriality of the comma construction. *)

(*
   nLab: https://ncatlab.org/nlab/show/comma+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaToolkit.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition comma_med_iso {S : A ⟶ C} {T : B ⟶ C} (X : S ↓ T)
        (k : S (fst ``X) ~{C}~> T (snd ``X)) (Heq : k ≈ `2 X) :
  @Isomorphism (S ↓ T) (``X; k) X := {|
  to   := ((id, id); _);
  from := ((id, id); _)
|}.
Next Obligation.
  rewrite !fmap_id, id_left, id_right.
  now symmetry.
Qed.
Next Obligation.
  rewrite !fmap_id, id_left, id_right.
  exact Heq.
Qed.
Next Obligation. split; simpl; apply id_left. Qed.
Next Obligation. split; simpl; apply id_left. Qed.

End CommaToolkit.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Ltac comma_id_carrier :=
  intros; simpl; split; rewrite id_left, id_right; reflexivity.

Section CommaOneSided.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

(** The action first (source) 函子 论元, CONTRAVARIANT: a
 transformation σ : S' ⟹ S induces 函子 (S ↓ T) ⟶ (S' ↓ T). （已译） *)

Program Definition Comma_map_left {S S' : A ⟶ C} {T : B ⟶ C} (σ : S' ⟹ S) :
  (S ↓ T) ⟶ (S' ↓ T) := {|
  fobj := fun X => (``X; `2 X ∘ transform[σ] (fst ``X));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite naturality_sym.
  rewrite comp_assoc.
  rewrite (`2 f).
  now rewrite <- comp_assoc.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

(** The action second (target) 函子 论元, COVARIANT: a
 transformation τ : T ⟹ T' induces 函子 (S ↓ T) ⟶ (S ↓ T'). （已译） *)

Program Definition Comma_map_right {S : A ⟶ C} {T T' : B ⟶ C} (τ : T ⟹ T') :
  (S ↓ T) ⟶ (S ↓ T') := {|
  fobj := fun X => (``X; transform[τ] (snd ``X) ∘ `2 X);
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (`2 f).
  rewrite comp_assoc.
  rewrite naturality_sym.
  now rewrite <- comp_assoc.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Comma_map {S S' : A ⟶ C} {T T' : B ⟶ C}
           (σ : S' ⟹ S) (τ : T ⟹ T') : (S ↓ T) ⟶ (S' ↓ T') :=
  Comma_map_left σ ◯ Comma_map_right τ.

End CommaOneSided.

Section CommaMapLemmas.

Context {A B C : Category}.
Context {S S' : A ⟶ C}.
Context {T T' : B ⟶ C}.

#[local] Obligation Tactic := simpl; intros.

Lemma Comma_map_fobj (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  fobj[Comma_map σ τ] X
    = (``X; transform[τ] (snd ``X) ∘ `2 X ∘ transform[σ] (fst ``X)).
Proof. reflexivity. Qed.

Lemma Comma_map_fmap (σ : S' ⟹ S) (τ : T ⟹ T') (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_map σ τ] f) = ``f.
Proof. reflexivity. Qed.

(** [Comma_map] respects ≈ of both transformations. *)

Program Definition comma_map_equiv_iso
        (σ σ' : S' ⟹ S) (τ τ' : T ⟹ T')
        (Hσ : ∀ a, transform[σ] a ≈ transform[σ'] a)
        (Hτ : ∀ b, transform[τ] b ≈ transform[τ'] b) (X : S ↓ T) :
  Comma_map σ τ X ≅ Comma_map σ' τ' X :=
  comma_med_iso (Comma_map σ' τ' X)
    (transform[τ] (snd ``X) ∘ `2 X ∘ transform[σ] (fst ``X)) _.
Next Obligation. now rewrite Hσ, Hτ. Qed.

Lemma Comma_map_respects (σ σ' : S' ⟹ S) (τ τ' : T ⟹ T')
      (Hσ : ∀ a, transform[σ] a ≈ transform[σ'] a)
      (Hτ : ∀ b, transform[τ] b ≈ transform[τ'] b) :
  Comma_map σ τ ≈ Comma_map σ' τ'.
Proof.
  exists (comma_map_equiv_iso σ σ' τ τ' Hσ Hτ); comma_id_carrier.
Qed.

(* * * The exchange law.

 [Comma_map σ τ] two one-sided composites agree. One order is
 literally same 函子 data, other differs exactly one
 associativity step. （已译） *)

(** One order 定义: equality whole 函子 RECORDS, not
 merely 对象 态射 actions. （已译） *)

Lemma Comma_map_left_right (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map σ τ = Comma_map_left σ ◯ Comma_map_right τ.
Proof. reflexivity. Qed.

(** The other order agrees underlying pair every 对象, on
 every 态射, nose. （已译） *)

Lemma Comma_map_exchange_pair (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  `1 (fobj[Comma_map_right τ ◯ Comma_map_left σ] X)
    = `1 (fobj[Comma_map_left σ ◯ Comma_map_right τ] X).
Proof. reflexivity. Qed.

Lemma Comma_map_exchange_fmap (σ : S' ⟹ S) (τ : T ⟹ T')
      (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_map_right τ ◯ Comma_map_left σ] f)
    = `1 (fmap[Comma_map_left σ ◯ Comma_map_right τ] f).
Proof. reflexivity. Qed.

(** ...and their mediating morphisms differ by exactly one associativity. *)

Lemma Comma_map_exchange_med (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  `2 (fobj[Comma_map_right τ ◯ Comma_map_left σ] X)
    ≈ `2 (fobj[Comma_map_left σ ◯ Comma_map_right τ] X).
Proof. simpl; apply comp_assoc. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition comma_map_exchange_iso (σ : S' ⟹ S) (τ : T ⟹ T')
        (X : S ↓ T) :
  (Comma_map_right τ ◯ Comma_map_left σ) X ≅ Comma_map σ τ X :=
  comma_med_iso (Comma_map σ τ X)
    (transform[τ] (snd ``X) ∘ (`2 X ∘ transform[σ] (fst ``X))) _.
Next Obligation. apply comp_assoc. Qed.

Lemma Comma_map_right_left (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map_right τ ◯ Comma_map_left σ ≈ Comma_map σ τ.
Proof.
  exists (comma_map_exchange_iso σ τ); comma_id_carrier.
Qed.

(** 本节：The exchange law proper: two one-sided actions commute. （已译） *)

Theorem Comma_map_exchange (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map_right τ ◯ Comma_map_left σ ≈ Comma_map_left σ ◯ Comma_map_right τ.
Proof.
  rewrite <- Comma_map_left_right.
  apply Comma_map_right_left.
Qed.

End CommaMapLemmas.

(* * * Identity 复合 laws arrow action. （已译） *)

Section CommaMapLaws.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

Program Definition comma_map_id_iso {S : A ⟶ C} {T : B ⟶ C} (X : S ↓ T) :
  Comma_map (@nat_id _ _ S) (@nat_id _ _ T) X ≅ Id X :=
  comma_med_iso X (fmap[T] (@id B (snd ``X)) ∘ `2 X ∘ fmap[S] (@id A (fst ``X)))
    _.
Next Obligation.
  rewrite !fmap_id, id_left.
  apply id_right.
Qed.

Lemma Comma_map_id {S : A ⟶ C} {T : B ⟶ C} :
  Comma_map (@nat_id _ _ S) (@nat_id _ _ T) ≈ @Id (S ↓ T).
Proof.
  exists comma_map_id_iso; comma_id_carrier.
Qed.

Program Definition comma_map_comp_iso
        {S1 S2 S3 : A ⟶ C} {T1 T2 T3 : B ⟶ C}
        (σ1 : S2 ⟹ S1) (σ2 : S3 ⟹ S2) (τ1 : T1 ⟹ T2) (τ2 : T2 ⟹ T3)
        (X : S1 ↓ T1) :
  Comma_map (nat_compose σ1 σ2) (nat_compose τ2 τ1) X
    ≅ (Comma_map σ2 τ2 ◯ Comma_map σ1 τ1) X :=
  comma_med_iso ((Comma_map σ2 τ2 ◯ Comma_map σ1 τ1) X)
    ((transform[τ2] (snd ``X) ∘ transform[τ1] (snd ``X)) ∘ `2 X
       ∘ (transform[σ1] (fst ``X) ∘ transform[σ2] (fst ``X))) _.
Next Obligation. now rewrite !comp_assoc. Qed.

Lemma Comma_map_comp {S1 S2 S3 : A ⟶ C} {T1 T2 T3 : B ⟶ C}
      (σ1 : S2 ⟹ S1) (σ2 : S3 ⟹ S2) (τ1 : T1 ⟹ T2) (τ2 : T2 ⟹ T3) :
  Comma_map (nat_compose σ1 σ2) (nat_compose τ2 τ1)
    ≈ Comma_map σ2 τ2 ◯ Comma_map σ1 τ1.
Proof.
  exists (comma_map_comp_iso σ1 σ2 τ1 τ2); comma_id_carrier.
Qed.

End CommaMapLaws.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaBifunctor.

Context {A B C : Category}.

#[local] Obligation Tactic := idtac.

Program Definition Comma_Bifunctor : (([A, C])^op ∏ ([B, C])) ⟶ Cat := {|
  fobj := fun ST => (fst ST ↓ snd ST);
  fmap := fun _ _ στ => Comma_map (fst στ) (snd στ)
|}.
Next Obligation.
  intros ST ST' στ στ' Hst.
  apply Comma_map_respects; intros; [ sapply (fst Hst) | sapply (snd Hst) ].
Qed.
Next Obligation. intros; apply Comma_map_id. Qed.
Next Obligation. intros; apply Comma_map_comp. Qed.

(** 本节：Acceptance: bifunctor's two actions comma construction and
 [Comma_map] nose. （已译） *)

Lemma Comma_Bifunctor_fobj (S : A ⟶ C) (T : B ⟶ C) :
  fobj[Comma_Bifunctor] (S, T) = (S ↓ T).
Proof. reflexivity. Qed.

Lemma Comma_Bifunctor_fmap (ST ST' : (([A, C])^op ∏ ([B, C]))%category)
      (στ : ST ~> ST') :
  fmap[Comma_Bifunctor] στ = Comma_map (fst στ) (snd στ).
Proof. reflexivity. Qed.

End CommaBifunctor.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Monomorphic Universe comma_bifun_hom.
Monomorphic Constraint Set < comma_bifun_hom.

Definition Comma_Bifunctor_above_Set
           (A B C : Category@{comma_bifun_hom comma_bifun_hom
                              comma_bifun_hom}) :=
  @Comma_Bifunctor A B C.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaIsoRestriction.

Context {A B C : Category}.

Lemma Comma_Iso_to_Left_fobj (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X : x ↓ z) :
  fobj[Comma_Iso_to_Left x y iso z] X
    = fobj[Comma_map_left (from iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Left_fmap (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X Y : x ↓ z) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_to_Left x y iso z] f)
    = `1 (fmap[Comma_map_left (from iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Left_fobj (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X : y ↓ z) :
  fobj[Comma_Iso_from_Left x y iso z] X
    = fobj[Comma_map_left (to iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Left_fmap (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X Y : y ↓ z) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_from_Left x y iso z] f)
    = `1 (fmap[Comma_map_left (to iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Right_fobj (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X : z ↓ x) :
  fobj[Comma_Iso_to_Right x y iso z] X
    = fobj[Comma_map_right (to iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Right_fmap (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X Y : z ↓ x) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_to_Right x y iso z] f)
    = `1 (fmap[Comma_map_right (to iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Right_fobj (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X : z ↓ y) :
  fobj[Comma_Iso_from_Right x y iso z] X
    = fobj[Comma_map_right (from iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Right_fmap (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X Y : z ↓ y) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_from_Right x y iso z] f)
    = `1 (fmap[Comma_map_right (from iso)] f).
Proof. reflexivity. Qed.

(** The same four agreements restated at level Cat's hom-等价. （已译） *)

Lemma Comma_Iso_to_Left_is_map_left
      (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  Comma_Iso_to_Left x y iso z ≈ Comma_map_left (from iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_from_Left_is_map_left
      (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  Comma_Iso_from_Left x y iso z ≈ Comma_map_left (to iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_to_Right_is_map_right
      (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  Comma_Iso_to_Right x y iso z ≈ Comma_map_right (to iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_from_Right_is_map_right
      (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  Comma_Iso_from_Right x y iso z ≈ Comma_map_right (from iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := simpl; intros.

Program Definition Comma_Bifunctor_domain_iso
        {x x' : A ⟶ C} {y y' : B ⟶ C}
        (iso1 : x ≅[Fun] x') (iso2 : y ≅[Fun] y') :
  @Isomorphism (([A, C])^op ∏ ([B, C])) (x, y) (x', y') := {|
  to   := (from iso1, to iso2);
  from := (to iso1, from iso2)
|}.
Next Obligation.
  split; simpl.
  - apply (iso_to_from iso1).
  - apply (iso_to_from iso2).
Qed.
Next Obligation.
  split; simpl.
  - apply (iso_from_to iso1).
  - apply (iso_from_to iso2).
Qed.

Definition Comma_Bifunctor_Iso
        {x x' : A ⟶ C} {y y' : B ⟶ C}
        (iso1 : x ≅[Fun] x') (iso2 : y ≅[Fun] y') :
  (x ↓ y) ≅[Cat] (x' ↓ y') :=
  fobj_iso Comma_Bifunctor (x, y) (x', y')
           (Comma_Bifunctor_domain_iso iso1 iso2).

End CommaIsoRestriction.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaReindex.

Context {A B C A' B' C' : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.
Context {S' : A' ⟶ C'} {T' : B' ⟶ C'}.

Context (F : A ⟶ A') (G : B ⟶ B') (K : C ⟶ C').

Context (α : ∀ a : A, S' (F a) ~{C'}~> K (S a)).
Context (α_natural : ∀ (a a' : A) (u : a ~> a'),
            α a' ∘ fmap[S'] (fmap[F] u) ≈ fmap[K] (fmap[S] u) ∘ α a).

Context (β : ∀ b : B, K (T b) ~{C'}~> T' (G b)).
Context (β_natural : ∀ (b b' : B) (v : b ~> b'),
            β b' ∘ fmap[K] (fmap[T] v) ≈ fmap[T'] (fmap[G] v) ∘ β b).

#[local] Obligation Tactic := simpl; intros.

Program Definition Comma_reindex : (S ↓ T) ⟶ (S' ↓ T') := {|
  fobj := fun X =>
    ((F (fst ``X), G (snd ``X));
     β (snd ``X) ∘ fmap[K] (`2 X) ∘ α (fst ``X));
  fmap := fun _ _ f => ((fmap[F] (fst ``f), fmap[G] (snd ``f)); _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite α_natural.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (β _)).
  rewrite <- fmap_comp.
  rewrite (`2 f).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite β_natural.
  now rewrite <- !comp_assoc.
Qed.
Next Obligation.
  intros [[u v] pf] [[u' v'] pf'] [e0 e1]; simpl in *.
  split; simpl.
  - now rewrite e0.
  - now rewrite e1.
Qed.
Next Obligation. split; simpl; apply fmap_id. Qed.
Next Obligation. split; simpl; apply fmap_comp. Qed.

End CommaReindex.

Arguments Comma_reindex {A B C A' B' C' S T S' T'} F G K α α_natural β β_natural.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaReindexSpecializes.

Context {A B C : Category}.
Context {S S' : A ⟶ C}.
Context {T T' : B ⟶ C}.

Lemma comma_reindex_alpha (σ : S' ⟹ S) :
  ∀ (a a' : A) (u : a ~> a'),
    transform[σ] a' ∘ fmap[S'] (fmap[Id] u)
      ≈ fmap[Id] (fmap[S] u) ∘ transform[σ] a.
Proof. intros; simpl; apply naturality_sym. Qed.

Lemma comma_reindex_beta (τ : T ⟹ T') :
  ∀ (b b' : B) (v : b ~> b'),
    transform[τ] b' ∘ fmap[Id] (fmap[T] v)
      ≈ fmap[T'] (fmap[Id] v) ∘ transform[τ] b.
Proof. intros; simpl; apply naturality_sym. Qed.

Definition Comma_reindex_at_Id (σ : S' ⟹ S) (τ : T ⟹ T') :
  (S ↓ T) ⟶ (S' ↓ T') :=
  Comma_reindex Id Id Id
    (fun a => transform[σ] a) (comma_reindex_alpha σ)
    (fun b => transform[τ] b) (comma_reindex_beta τ).

Lemma Comma_reindex_fobj_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  fobj[Comma_reindex_at_Id σ τ] X = fobj[Comma_map σ τ] X.
Proof. destruct X as [[a b] h]; reflexivity. Qed.

Lemma Comma_reindex_fmap_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T')
      (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_reindex_at_Id σ τ] f) = `1 (fmap[Comma_map σ τ] f).
Proof. destruct f as [[u v] pf]; reflexivity. Qed.

Theorem Comma_reindex_recovers_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_reindex_at_Id σ τ ≈ Comma_map σ τ.
Proof.
  unshelve eexists.
  - intro X.
    destruct X as [[a b] h].
    exact iso_id.
  - intros [[a b] h] [[a' b'] h'] [[u v] pf]; simpl.
    split; now rewrite id_left, id_right.
Qed.

End CommaReindexSpecializes.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommaReindexPostcompose.

Context {A B C C' : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.

Lemma comma_post_alpha (K : C ⟶ C') :
  ∀ (a a' : A) (u : a ~> a'),
    id ∘ fmap[K ◯ S] (fmap[Id] u) ≈ fmap[K] (fmap[S] u) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

Lemma comma_post_beta (K : C ⟶ C') :
  ∀ (b b' : B) (v : b ~> b'),
    id ∘ fmap[K] (fmap[T] v) ≈ fmap[K ◯ T] (fmap[Id] v) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

(** Post-composing both defining 函子 K: ambient 范畴 moves
 C C', mediating 态射 carried K. （已译） *)

Definition Comma_postcompose (K : C ⟶ C') :
  (S ↓ T) ⟶ ((K ◯ S) ↓ (K ◯ T)) :=
  @Comma_reindex A B C A B C' S T (K ◯ S) (K ◯ T)
    Id Id K (fun _ => id) (comma_post_alpha K)
            (fun _ => id) (comma_post_beta K).

Lemma Comma_postcompose_med (K : C ⟶ C') (X : S ↓ T) :
  `2 (fobj[Comma_postcompose K] X) ≈ fmap[K] (`2 X).
Proof. simpl; rewrite id_left, id_right; reflexivity. Qed.

End CommaReindexPostcompose.

Section CommaReindexPrecompose.

Context {A B A' B' C : Category}.
Context {S : A' ⟶ C} {T : B' ⟶ C}.

Lemma comma_pre_alpha (F : A ⟶ A') :
  ∀ (a a' : A) (u : a ~> a'),
    id ∘ fmap[S] (fmap[F] u) ≈ fmap[Id] (fmap[S ◯ F] u) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

Lemma comma_pre_beta (G : B ⟶ B') :
  ∀ (b b' : B) (v : b ~> b'),
    id ∘ fmap[Id] (fmap[T ◯ G] v) ≈ fmap[T] (fmap[G] v) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

(** Pre-composing defining 函子 F G: two domains move
 A, B A', B', mediating 态射 untouched. （已译） *)

Definition Comma_precompose (F : A ⟶ A') (G : B ⟶ B') :
  ((S ◯ F) ↓ (T ◯ G)) ⟶ (S ↓ T) :=
  @Comma_reindex A B C A' B' C (S ◯ F) (T ◯ G) S T
    F G Id (fun _ => id) (comma_pre_alpha F)
           (fun _ => id) (comma_pre_beta G).

Lemma Comma_precompose_pair (F : A ⟶ A') (G : B ⟶ B')
      (X : (S ◯ F) ↓ (T ◯ G)) :
  `1 (fobj[Comma_precompose F G] X) = (F (fst ``X), G (snd ``X)).
Proof. reflexivity. Qed.

Lemma Comma_precompose_med (F : A ⟶ A') (G : B ⟶ B')
      (X : (S ◯ F) ↓ (T ◯ G)) :
  `2 (fobj[Comma_precompose F G] X) ≈ `2 X.
Proof. simpl; rewrite id_left, id_right; reflexivity. Qed.

End CommaReindexPrecompose.
