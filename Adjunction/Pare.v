Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Construction.Karoubi.Universal.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/idempotent
    nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+category
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record PareData (A X : Category) := {
  pare_G : A ⟶ X;
  pare_K : X ⟶ A;
  pare_eps : pare_K ◯ pare_G ⟹ Id[A];
  pare_rho : Id[X] ⟹ pare_G ◯ pare_K;
  pare_triangle (a : A) :
    fmap[pare_G] (pare_eps a) ∘ pare_rho (pare_G a) ≈ id
}.

Arguments pare_G {_ _} _.
Arguments pare_K {_ _} _.
Arguments pare_eps {_ _} _.
Arguments pare_rho {_ _} _.
Arguments pare_triangle {_ _} _ _.

Section Pare.

Context {A X : Category}.
Context (P : PareData A X).

Let G := pare_G P.
Let K := pare_K P.
Let eps : ∀ a : A, K (G a) ~> a := pare_eps P.
Let rho : ∀ x : X, x ~> G (K x) := pare_rho P.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pare_assoc_fobj :
  @fobj A X ((G ◯ K) ◯ G) = @fobj A X (G ◯ (K ◯ G)) := eq_refl.
Example pare_assoc_fmap :
  @fmap A X ((G ◯ K) ◯ G) = @fmap A X (G ◯ (K ◯ G)) := eq_refl.
Example pare_unitor_fobj :
  @fobj A X (Id[X] ◯ G) = @fobj A X G := eq_refl.
Example pare_unitor_fmap :
  @fmap A X (Id[X] ◯ G) = @fmap A X G := eq_refl.

(* 相关说明。 （已译） *)
Definition pare_Geps : G ◯ (K ◯ G) ⟹ G ◯ Id[A] := G ⊳ (pare_eps P).
Definition pare_rhoG : Id[X] ◯ G ⟹ (G ◯ K) ◯ G := (pare_rho P) ⊲ G.
Definition pare_epsK : (K ◯ G) ◯ K ⟹ Id[A] ◯ K := (pare_eps P) ⊲ K.
Definition pare_Krho : K ◯ Id[X] ⟹ K ◯ (G ◯ K) := K ⊳ (pare_rho P).

Example pare_Geps_at (a : A) :
  transform[pare_Geps] a = fmap[G] (eps a) := eq_refl.
Example pare_rhoG_at (a : A) :
  transform[pare_rhoG] a = rho (G a) := eq_refl.
Example pare_epsK_at (x : X) :
  transform[pare_epsK] x = eps (K x) := eq_refl.
Example pare_Krho_at (x : X) :
  transform[pare_Krho] x = fmap[K] (rho x) := eq_refl.

Lemma pare_tri (a : A) : fmap[G] (eps a) ∘ rho (G a) ≈ id.
Proof. exact (pare_triangle P a). Qed.

Lemma pare_rho_nat {x y : X} (f : x ~> y) :
  fmap[G] (fmap[K] f) ∘ rho x ≈ rho y ∘ f.
Proof. exact (naturality (pare_rho P) _ _ f). Qed.

Lemma pare_eps_nat {a b : A} (g : a ~> b) :
  g ∘ eps a ≈ eps b ∘ fmap[K] (fmap[G] g).
Proof. exact (naturality (pare_eps P) _ _ g). Qed.

(* ---------------------------------------------------------------------- *)
(** ** The idempotent εK ∘ Kρ *)

Lemma pare_idem_natural {x y : X} (f : x ~> y) :
  fmap[K] f ∘ (eps (K x) ∘ fmap[K] (rho x))
    ≈ (eps (K y) ∘ fmap[K] (rho y)) ∘ fmap[K] f.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_idem : K ⟹ K := {|
  transform := λ x, eps (K x) ∘ fmap[K] (rho x)
|}.
Next Obligation. apply pare_idem_natural. Qed.
Next Obligation. symmetry; apply pare_idem_natural. Qed.

Example pare_idem_at (x : X) :
  transform[pare_idem] x
    = transform[pare_epsK] x ∘ transform[pare_Krho] x := eq_refl.

Lemma pare_eps_absorb (a : A) :
  eps a ∘ (eps (K (G a)) ∘ fmap[K] (rho (G a))) ≈ eps a.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_tri.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_idem_idem (x : X) :
  (eps (K x) ∘ fmap[K] (rho x)) ∘ (eps (K x) ∘ fmap[K] (rho x))
    ≈ eps (K x) ∘ fmap[K] (rho x).
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[K] (rho x)) (eps (K x)) (fmap[K] (rho x))).
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (eps (K (G (K x))))).
  rewrite comp_assoc.
  rewrite pare_eps_absorb.
  reflexivity.
Qed.

Definition pare_idem_Idempotent : @Idempotent ([X, A]) K pare_idem.
Proof. constructor; intro x; apply pare_idem_idem. Qed.

(* ---------------------------------------------------------------------- *)
(* * ** From splitting 左伴随 （已译） *)

Section FromSplitting.

Context (F : X ⟶ A).
Context (r : K ⟹ F) (s : F ⟹ K).
Context (Hsr : ∀ x, s x ∘ r x ≈ pare_idem x).
Context (Hrs : ∀ x, r x ∘ s x ≈ id).

(* [Hsr] unfolded components εK ∘ Kρ; two statements are
 convertible, so 这是 [Hsr] itself no 证明 step. （已译） *)
Lemma pare_split_law (x : X) :
  s x ∘ r x ≈ eps (K x) ∘ fmap[K] (rho x).
Proof using All. exact (Hsr x). Qed.

Definition pare_unit : Id[X] ⟹ G ◯ F := (G ⊳ r) ∙ (pare_rho P).
Definition pare_counit : F ◯ G ⟹ Id[A] := (pare_eps P) ∙ (s ⊲ G).

Example pare_unit_at (x : X) :
  transform[pare_unit] x = fmap[G] (r x) ∘ rho x := eq_refl.
Example pare_counit_at (a : A) :
  transform[pare_counit] a = eps a ∘ s (G a) := eq_refl.

Lemma pare_s_nat {x y : X} (h : x ~> y) :
  fmap[K] h ∘ s x ≈ s y ∘ fmap[F] h.
Proof. exact (naturality s _ _ h). Qed.

Lemma pare_tri_one (x : X) :
  (eps (F x) ∘ s (G (F x))) ∘ fmap[F] (fmap[G] (r x) ∘ rho x) ≈ id.
Proof using All.
  rewrite <- comp_assoc.
  rewrite <- pare_s_nat.
  rewrite fmap_comp.
  (* 相关说明。 （已译） *)
  rewrite <- comp_assoc.
  rewrite comp_assoc.
  rewrite <- pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (eps (K x)) (fmap[K] (rho x)) (s x)).
  rewrite <- pare_split_law.
  rewrite <- comp_assoc.
  rewrite Hrs.
  rewrite id_right.
  rewrite Hrs.
  reflexivity.
Qed.

Lemma pare_tri_two (a : A) :
  fmap[G] (eps a ∘ s (G a)) ∘ (fmap[G] (r (G a)) ∘ rho (G a)) ≈ id.
Proof using All.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[G] (s (G a))) (fmap[G] (r (G a))) (rho (G a))).
  rewrite <- fmap_comp.
  rewrite pare_split_law.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite pare_rho_nat.
  rewrite (comp_assoc (fmap[G] (eps (K (G a))))).
  rewrite pare_tri.
  rewrite id_left.
  rewrite pare_tri.
  reflexivity.
Qed.

Definition pare_Adjunction : F ∹ G := {|
  unit             := pare_unit;
  counit           := pare_counit;
  counit_fmap_unit := λ x, pare_tri_one x;
  fmap_counit_unit := λ a, pare_tri_two a
|}.

Example pare_Adjunction_unit :
  unit[pare_Adjunction] = pare_unit := eq_refl.
Example pare_Adjunction_counit :
  counit[pare_Adjunction] = pare_counit := eq_refl.
Example pare_Adjunction_unit_at (x : X) :
  transform[unit[pare_Adjunction]] x = fmap[G] (r x) ∘ rho x := eq_refl.
Example pare_Adjunction_counit_at (a : A) :
  transform[counit[pare_Adjunction]] a = eps a ∘ s (G a) := eq_refl.

End FromSplitting.

(* ---------------------------------------------------------------------- *)
(* * ** From 左伴随 splitting （已译） *)

Section FromAdjunction.

Context (F : X ⟶ A).
Context (Adj : F ∹ G).

Let eta : ∀ x : X, x ~> G (F x) := unit[Adj].
Let del : ∀ a : A, F (G a) ~> a := counit[Adj].

Lemma pare_eta_nat {x y : X} (h : x ~> y) :
  fmap[G] (fmap[F] h) ∘ eta x ≈ eta y ∘ h.
Proof. exact (naturality unit[Adj] _ _ h). Qed.

Lemma pare_del_nat {a b : A} (g : a ~> b) :
  g ∘ del a ≈ del b ∘ fmap[F] (fmap[G] g).
Proof. exact (naturality counit[Adj] _ _ g). Qed.

Lemma pare_adj_tri_one (x : X) : del (F x) ∘ fmap[F] (eta x) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Adj x). Qed.

Lemma pare_adj_tri_two (a : A) : fmap[G] (del a) ∘ eta (G a) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ Adj a). Qed.

Lemma pare_r_natural {x y : X} (h : x ~> y) :
  fmap[F] h ∘ (eps (F x) ∘ fmap[K] (eta x))
    ≈ (eps (F y) ∘ fmap[K] (eta y)) ∘ fmap[K] h.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_eta_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_r : K ⟹ F := {|
  transform := λ x, eps (F x) ∘ fmap[K] (eta x)
|}.
Next Obligation. apply pare_r_natural. Qed.
Next Obligation. symmetry; apply pare_r_natural. Qed.

Lemma pare_s_natural {x y : X} (h : x ~> y) :
  fmap[K] h ∘ (del (K x) ∘ fmap[F] (rho x))
    ≈ (del (K y) ∘ fmap[F] (rho y)) ∘ fmap[F] h.
Proof.
  rewrite comp_assoc.
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Definition pare_s : F ⟹ K := {|
  transform := λ x, del (K x) ∘ fmap[F] (rho x)
|}.
Next Obligation. apply pare_s_natural. Qed.
Next Obligation. symmetry; apply pare_s_natural. Qed.

Lemma pare_eps_of_s (a : A) :
  eps a ∘ (del (K (G a)) ∘ fmap[F] (rho (G a))) ≈ del a.
Proof.
  rewrite comp_assoc.
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_tri.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_del_of_r (a : A) :
  del a ∘ (eps (F (G a)) ∘ fmap[K] (eta (G a))) ≈ eps a.
Proof.
  rewrite comp_assoc.
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_adj_tri_two.
  rewrite fmap_id.
  rewrite id_right.
  reflexivity.
Qed.

Lemma pare_split_rs (x : X) :
  (eps (F x) ∘ fmap[K] (eta x)) ∘ (del (K x) ∘ fmap[F] (rho x)) ≈ id.
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[K] (eta x)) (del (K x)) (fmap[F] (rho x))).
  rewrite pare_del_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_rho_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (del (K (G (F x))))).
  rewrite comp_assoc.
  rewrite pare_eps_of_s.
  rewrite pare_adj_tri_one.
  reflexivity.
Qed.

Lemma pare_split_sr (x : X) :
  (del (K x) ∘ fmap[F] (rho x)) ∘ (eps (F x) ∘ fmap[K] (eta x))
    ≈ eps (K x) ∘ fmap[K] (rho x).
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap[F] (rho x)) (eps (F x)) (fmap[K] (eta x))).
  rewrite pare_eps_nat.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite pare_eta_nat.
  rewrite fmap_comp.
  rewrite (comp_assoc (eps (F (G (K x))))).
  rewrite comp_assoc.
  rewrite pare_del_of_r.
  reflexivity.
Qed.

Program Definition pare_SplitIdempotent : @SplitIdempotent ([X, A]) K F := {|
  split_idem   := pare_idem;
  split_idem_r := pare_r;
  split_idem_s := pare_s
|}.
Next Obligation. apply pare_split_sr. Qed.
Next Obligation.
  rewrite pare_split_rs.
  symmetry; apply fmap_id.
Qed.

End FromAdjunction.

(* ---------------------------------------------------------------------- *)
(* * ** The biconditional, Cauchy-complete 推论 （已译） *)

Definition PareSplits : Type :=
  ∃ (F : X ⟶ A) (S : @SplitIdempotent ([X, A]) K F),
    @split_idem ([X, A]) K F S ≈ pare_idem.

Definition PareLeftAdjoint : Type := ∃ F : X ⟶ A, F ∹ G.

Definition pare_adjunction_of_split (F : X ⟶ A)
           (S : @SplitIdempotent ([X, A]) K F)
           (HS : @split_idem ([X, A]) K F S ≈ pare_idem) : F ∹ G.
Proof.
  refine (pare_Adjunction F (@split_idem_r ([X, A]) K F S)
                            (@split_idem_s ([X, A]) K F S) _ _).
  - intro x.
    transitivity (@split_idem ([X, A]) K F S x).
    + exact (@split_idem_sr ([X, A]) K F S x).
    + exact (HS x).
  - intro x.
    transitivity (fmap[F] (@id X x)).
    + exact (@split_idem_rs ([X, A]) K F S x).
    + apply fmap_id.
Defined.

(*
   本节说明 Pare 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pare_adjunction_of_split_unit (F : X ⟶ A)
        (S : @SplitIdempotent ([X, A]) K F)
        (HS : @split_idem ([X, A]) K F S ≈ pare_idem) :
  unit[pare_adjunction_of_split F S HS]
    = pare_unit F (@split_idem_r ([X, A]) K F S) := eq_refl.

Example pare_adjunction_of_split_counit (F : X ⟶ A)
        (S : @SplitIdempotent ([X, A]) K F)
        (HS : @split_idem ([X, A]) K F S ≈ pare_idem) :
  counit[pare_adjunction_of_split F S HS]
    = pare_counit F (@split_idem_s ([X, A]) K F S) := eq_refl.

Definition pare_splits_of_adjunction (F : X ⟶ A) (Adj : F ∹ G) : PareSplits.
Proof.
  refine (existT _ F (existT _ (pare_SplitIdempotent F Adj) _)).
  reflexivity.
Defined.

Theorem pare_left_adjoint_iff_splits : PareLeftAdjoint ↔ PareSplits.
Proof.
  split.
  - intros [F Adj].
    exact (pare_splits_of_adjunction F Adj).
  - intros [F [S HS]].
    exact (existT _ F (pare_adjunction_of_split F S HS)).
Defined.

Definition pare_splits_of_CauchyComplete
           (HS : CauchyComplete ([X, A])) : PareSplits :=
  @split_of ([X, A]) HS K pare_idem pare_idem_Idempotent.

Definition pare_left_adjoint_of_CauchyComplete
           (HS : CauchyComplete ([X, A])) : PareLeftAdjoint :=
  snd pare_left_adjoint_iff_splits (pare_splits_of_CauchyComplete HS).

End Pare.

(* ---------------------------------------------------------------------- *)
(** ** Inhabitation *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pare_of_adjunction {A X : Category} {F : X ⟶ A} {G : A ⟶ X}
           (Adj : F ∹ G) : PareData A X := {|
  pare_G        := G;
  pare_K        := F;
  pare_eps      := counit[Adj];
  pare_rho      := unit[Adj];
  pare_triangle := λ a, @fmap_counit_unit _ _ _ _ Adj a
|}.

Lemma pare_of_adjunction_idem {A X : Category} {F : X ⟶ A} {G : A ⟶ X}
      (Adj : F ∹ G) (x : X) : pare_idem (pare_of_adjunction Adj) x ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Adj x). Qed.

(* A uniform family -- not closed term, never instantiated here at
 concrete 范畴: everything 恒等 范畴. （已译） *)
Program Definition pare_triv_rho (C : Category) : Id[C] ⟹ Id[C] ◯ Id[C] :=
  {| transform := λ _, id |}.

Program Definition pare_triv_eps (C : Category) : Id[C] ◯ Id[C] ⟹ Id[C] :=
  {| transform := λ _, id |}.

Program Definition pare_triv (C : Category) : PareData C C := {|
  pare_G   := Id[C];
  pare_K   := Id[C];
  pare_eps := pare_triv_eps C;
  pare_rho := pare_triv_rho C
|}.

Lemma pare_triv_idem (C : Category) (x : C) :
  pare_idem (pare_triv C) x ≈ id.
Proof. simpl; cat. Qed.

(* The assembly run end end inhabitant: 恒等 idempotent
 splits identities, what comes back out Id ∹ Id. （已译） *)
Definition pare_triv_left_adjoint (C : Category) : Id[C] ∹ Id[C].
Proof.
  refine (pare_Adjunction (pare_triv C) Id[C] nat_id nat_id _ _).
  - intro x; simpl; cat.
  - intro x; simpl; cat.
Defined.
