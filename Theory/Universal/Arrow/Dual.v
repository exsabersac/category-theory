Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Opposite.

Generalizable All Variables.

(*
   本文件给出对偶形式。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

(** * Couniversal arrows *)

(*
   nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/opposite+category
   Paper: Mac Lane, "Duality for groups", Bull. Amer. Math. Soc. 56, 1950

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CouniversalArrow.

Context {C : Category}.
Context {D : Category}.

(** ** The comma-packaged encoding *)

(* A couniversal arrow from F to c.  Definitionally a [UniversalArrow] in the
   opposite categories; every accessor below reads it back covariantly. *)
Definition CouniversalArrow (c : C) (F : D ⟶ C) : Type :=
  @UniversalArrow (C^op) (D^op) c (Opposite_Functor F).

(*
   本节说明余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Existing Class CouniversalArrow.

Section Accessors.

Context {c : C}.
Context {F : D ⟶ C}.
Context (U : CouniversalArrow c F).

(* The couniversal object a : D.  Objects of `D^op` ARE objects of `D`, so
   this is [arrow_obj] with no transport. *)
Definition coarrow_obj : D := @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U.

(* The couniversal morphism ε : F a ~> c.  Its op-side type is
   `c ~{C^op}~> (F^op) a`, which is literally `F a ~{C}~> c`; the covariant
   ascription below is accepted by conversion alone. *)
Definition coarrow : F coarrow_obj ~{C}~> c :=
  @arrow (C^op) (D^op) c (Opposite_Functor F) U.

End Accessors.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ump_couniversal_arrows {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) {d : D} (h : F d ~{C}~> c) :
  ∃! g : d ~{D}~> coarrow_obj U, h ≈ coarrow U ∘ fmap[F] g :=
  @ump_universal_arrows (C^op) (D^op) c (Opposite_Functor F) U d h.

(* Conversely, the couniversal mapping property reconstructs the couniversal
   arrow.  Again a definitional op-read of [universal_arrow_from_UMP]. *)
Definition couniversal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D)
  (ε : F d ~{C}~> c)
  (u : ∀ (d' : D) (f : F d' ~{C}~> c), ∃! g : d' ~{D}~> d, f ≈ ε ∘ fmap[F] g)
  : CouniversalArrow c F :=
  @universal_arrow_from_UMP (C^op) (D^op) c (Opposite_Functor F) d ε u.

(** ** The terminal-object reading (Mac Lane §III.1 Definition 3) *)

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary terminal_is_initial_op {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : @Initial ((F ↓ =(c))^op).
Proof. exact T. Defined.

Definition couniversal_arrow_terminal {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) : @Terminal (F ↓ =(c)).
Proof.
  unshelve eapply Build_Terminal.
  - (* the terminal object is the couniversal pair (a, ε) *)
    exact (((coarrow_obj U, ttt); coarrow U)).
  - (* the unique arrow into it is the UMP mediator *)
    intros [[d u] h]; simpl in *.
    exists (unique_obj (ump_couniversal_arrows U h), ttt).
    simpl.
    (* [simpl] has already reduced fmap[=(c)] ttt to id[c] *)
    rewrite id_left.
    symmetry.
    exact (unique_property (ump_couniversal_arrows U h)).
  - (* two arrows into it agree: the D-components by UMP uniqueness, the
       1-components because `1` has exactly one arrow *)
    intros [[d u] h] [[f1 f2] Hf] [[g1 g2] Hg]; simpl in *.
    rewrite ?fmap_id, ?id_left in Hf, Hg.
    split.
    + rewrite <- (uniqueness (ump_couniversal_arrows U h) f1 (symmetry Hf)).
      exact (uniqueness (ump_couniversal_arrows U h) g1 (symmetry Hg)).
    + now destruct f2, g2.
Defined.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary couniversal_arrow_terminal_obj {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) :
  `1 (@terminal_obj _ (couniversal_arrow_terminal U)) = (coarrow_obj U, ttt).
Proof. reflexivity. Qed.

(* ... and back: a terminal object of F ↓ =(c) is a couniversal arrow. *)
Definition couniversal_arrow_of_terminal {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : CouniversalArrow c F.
Proof.
  destruct T as [t one one_unique].
  destruct t as [[a u] ε]; simpl in *.
  unshelve eapply (couniversal_arrow_from_UMP c F a ε).
  intros d' f.
  (*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  assert (sq : ∀ v : d' ~{D}~> a, f ≈ ε ∘ fmap[F] v →
                 ε ∘ fmap[F] v ≈ id{C} ∘ f).
  { intros v Hv.
    rewrite id_left.
    now symmetry. }
  destruct (one (((d', ttt); f))) as [[g1 g2] Hg]; simpl in Hg.
  rewrite id_left in Hg.
  unshelve eexists g1.
  - now symmetry.
  - intros v Hv.
    exact (fst (one_unique (((d', ttt); f))
                           ((g1, ttt); sq g1 (symmetry Hg))
                           ((v, ttt); sq v Hv))).
Defined.

(** ** Uniqueness up to a unique isomorphism *)

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CouniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

(* The canonical mediating morphism: the unique factorization of the FIRST
   couniversal arrow through the SECOND (dual to the primal orientation). *)
Definition cua_med (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ~{D}~> coarrow_obj U2 :=
  @ua_med (C^op) (D^op) c (Opposite_Functor F) U2 U1.

Lemma cua_med_commutes (U1 U2 : CouniversalArrow c F) :
  coarrow U2 ∘ fmap[F] (cua_med U1 U2) ≈ coarrow U1.
Proof. exact (@ua_med_commutes (C^op) (D^op) c (Opposite_Functor F) U2 U1). Qed.

(* Any morphism commuting with the two couniversal arrows IS the mediator. *)
Lemma cua_med_unique (U1 U2 : CouniversalArrow c F)
      (g : coarrow_obj U1 ~{D}~> coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] g ≈ coarrow U1 → cua_med U1 U2 ≈ g.
Proof.
  exact (@ua_med_unique (C^op) (D^op) c (Opposite_Functor F) U2 U1 g).
Qed.

Lemma cua_med_id (U1 : CouniversalArrow c F) : cua_med U1 U1 ≈ id.
Proof. exact (@ua_med_id (C^op) (D^op) c (Opposite_Functor F) U1). Qed.

Lemma cua_med_comp (U1 U2 U3 : CouniversalArrow c F) :
  cua_med U2 U3 ∘ cua_med U1 U2 ≈ cua_med U1 U3.
Proof. exact (@ua_med_comp (C^op) (D^op) c (Opposite_Functor F) U3 U2 U1). Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition couniversal_arrow_iso (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ≅ coarrow_obj U2 :=
  @Isomorphism_Opposite (D^op) _ _
    (@universal_arrow_iso (C^op) (D^op) c (Opposite_Functor F) U1 U2).

Corollary couniversal_arrow_iso_to (U1 U2 : CouniversalArrow c F) :
  to (couniversal_arrow_iso U1 U2) ≈ cua_med U1 U2.
Proof. reflexivity. Qed.

Corollary couniversal_arrow_iso_from (U1 U2 : CouniversalArrow c F) :
  from (couniversal_arrow_iso U1 U2) ≈ cua_med U2 U1.
Proof. reflexivity. Qed.

Lemma couniversal_arrow_iso_unique (U1 U2 : CouniversalArrow c F)
      (v : coarrow_obj U1 ≅ coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] (to v) ≈ coarrow U1 →
  couniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply cua_med_unique.
Qed.

(* Awodey's Proposition 1.10, dualized: exactly one isomorphism of the
   couniversal objects carries the second couniversal arrow to the first. *)
Program Definition couniversal_arrow_unique
        (U1 U2 : CouniversalArrow c F) :
  Unique (fun i : coarrow_obj U1 ≅ coarrow_obj U2 =>
            coarrow U2 ∘ fmap[F] (to i) ≈ coarrow U1) := {|
  unique_obj      := couniversal_arrow_iso U1 U2;
  unique_property := cua_med_commutes U1 U2
|}.
Next Obligation. exact (couniversal_arrow_iso_unique U1 U2 v X). Qed.

End CouniversalArrowUnique.

(** ** From couniversal arrows to a right adjoint *)

Context (F : @Functor D C).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RightAdjointFunctorFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) : @Functor C D :=
  Opposite_Functor
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H).

(* The object action is [coarrow_obj] by convertibility -- what makes the
   op-route usable rather than merely type-correct. *)
Corollary right_adjoint_obj (H : forall c : C, CouniversalArrow c F) (c : C) :
  fobj[RightAdjointFunctorFromCouniversalArrows H] c = coarrow_obj (H c).
Proof. reflexivity. Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AdjunctionFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) :
  F ⊣ RightAdjointFunctorFromCouniversalArrows H :=
  Opposite_Adjunction
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H)
    (Opposite_Functor F)
    (@AdjunctionFromUniversalArrows (C^op) (D^op) (Opposite_Functor F) H).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma counit_couniversal (H : forall c : C, CouniversalArrow c F) (c : C) :
  @counit C D F (RightAdjointFunctorFromCouniversalArrows H)
          (AdjunctionFromCouniversalArrows H) c ≈ coarrow (H c).
Proof.
  unfold counit; simpl.
  rewrite fmap_id.
  apply id_right.
Qed.

(** ** The direct encoding *)

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ACouniversalArrow (c : C) (G : D ⟶ C) (a : D) : Type :=
  @AUniversalArrow (C^op) (D^op) c (Opposite_Functor G) a.

Existing Class ACouniversalArrow.

(* The couniversal morphism ε : F a ~> c, covariantly. *)
Definition couniversal_arrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : G a ~{C}~> c :=
  @universal_arrow (C^op) (D^op) c (Opposite_Functor G) a U.

(* ... and its universal property, in the orientation the primal field has
   ([fmap ∘ arrow ≈ f] there, [arrow ∘ fmap ≈ f] here). *)
Definition couniversal_arrow_couniversal {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) {d : D} {f : G d ~{C}~> c} :
  Unique (fun g : d ~{D}~> a => couniversal_arrow U ∘ fmap[G] g ≈ f) :=
  @universal_arrow_universal (C^op) (D^op) c (Opposite_Functor G) a U d f.

(* Two couniversal arrows at the same object are equivalent when their
   underlying morphisms agree; the op-read of [AUniversalArrowEquiv]. *)
#[export] Instance ACouniversalArrowEquiv (c : C) (G : D ⟶ C) (a : D) :
  Setoid (ACouniversalArrow c G a) :=
  @AUniversalArrowEquiv (C^op) (D^op) c (Opposite_Functor G) a.

Section ACouniversalArrowUnique.

Context {c : C}.
Context {G : D ⟶ C}.

Definition acua_med {a b : D} (U1 : ACouniversalArrow c G a)
           (U2 : ACouniversalArrow c G b) : a ~{D}~> b :=
  @aua_med (C^op) (D^op) c (Opposite_Functor G) b a U2 U1.

Lemma acua_med_commutes {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) :
  couniversal_arrow U2 ∘ fmap[G] (acua_med U1 U2) ≈ couniversal_arrow U1.
Proof.
  exact (@aua_med_commutes (C^op) (D^op) c (Opposite_Functor G) b a U2 U1).
Qed.

Lemma acua_med_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (g : a ~{D}~> b) :
  couniversal_arrow U2 ∘ fmap[G] g ≈ couniversal_arrow U1 → acua_med U1 U2 ≈ g.
Proof.
  exact (@aua_med_unique (C^op) (D^op) c (Opposite_Functor G) b a U2 U1 g).
Qed.

Lemma acua_med_id {a : D} (U1 : ACouniversalArrow c G a) : acua_med U1 U1 ≈ id.
Proof. exact (@aua_med_id (C^op) (D^op) c (Opposite_Functor G) a U1). Qed.

Lemma acua_med_comp {a b e : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (U3 : ACouniversalArrow c G e) :
  acua_med U2 U3 ∘ acua_med U1 U2 ≈ acua_med U1 U3.
Proof.
  exact (@aua_med_comp (C^op) (D^op) c (Opposite_Functor G) e b a U3 U2 U1).
Qed.

Definition acouniversal_arrow_iso {a b : D} (U1 : ACouniversalArrow c G a)
        (U2 : ACouniversalArrow c G b) : a ≅ b :=
  @Isomorphism_Opposite (D^op) _ _
    (@auniversal_arrow_iso (C^op) (D^op) c (Opposite_Functor G) a b U1 U2).

Lemma acouniversal_arrow_iso_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (v : a ≅ b) :
  couniversal_arrow U2 ∘ fmap[G] (to v) ≈ couniversal_arrow U1 →
  acouniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply acua_med_unique.
Qed.

Program Definition acouniversal_arrow_unique {a b : D}
        (U1 : ACouniversalArrow c G a) (U2 : ACouniversalArrow c G b) :
  Unique (fun i : a ≅ b =>
            couniversal_arrow U2 ∘ fmap[G] (to i) ≈ couniversal_arrow U1) := {|
  unique_obj      := acouniversal_arrow_iso U1 U2;
  unique_property := acua_med_commutes U1 U2
|}.
Next Obligation. exact (acouniversal_arrow_iso_unique U1 U2 v X). Qed.

End ACouniversalArrowUnique.

(** ** The two encodings agree *)

(*
   本节说明 Dual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ACouniversalArrow_of_CouniversalArrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) : ACouniversalArrow c G (coarrow_obj U).
Proof.
  unshelve econstructor.
  - exact (coarrow U).
  - intros d f.
    unshelve eexists (unique_obj (ump_couniversal_arrows U f)).
    + symmetry; exact (unique_property (ump_couniversal_arrows U f)).
    + intros v Hv.
      exact (uniqueness (ump_couniversal_arrows U f) v (symmetry Hv)).
Defined.

Definition CouniversalArrow_of_ACouniversalArrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : CouniversalArrow c G.
Proof.
  unshelve eapply (couniversal_arrow_from_UMP c G a (couniversal_arrow U)).
  intros d' f.
  unshelve eexists (unique_obj (@couniversal_arrow_couniversal c G a U d' f)).
  - symmetry.
    exact (unique_property (@couniversal_arrow_couniversal c G a U d' f)).
  - intros v Hv.
    exact (uniqueness (@couniversal_arrow_couniversal c G a U d' f) v
             (symmetry Hv)).
Defined.

(* The passage keeps the arrow on the nose in one direction ... *)
Corollary ACouniversalArrow_of_CouniversalArrow_arrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) :
  couniversal_arrow (ACouniversalArrow_of_CouniversalArrow U) = coarrow U.
Proof. reflexivity. Qed.

(* ... and in the other. *)
Corollary CouniversalArrow_of_ACouniversalArrow_arrow {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow (CouniversalArrow_of_ACouniversalArrow U) = couniversal_arrow U.
Proof. reflexivity. Qed.

Corollary CouniversalArrow_of_ACouniversalArrow_obj {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow_obj (CouniversalArrow_of_ACouniversalArrow U) = a.
Proof. reflexivity. Qed.

End CouniversalArrow.

Arguments CouniversalArrow {C D} c F.
Arguments ACouniversalArrow {C D} c G a.
