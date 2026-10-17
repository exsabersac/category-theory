Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Structure.SlicedInverse.

(*
    nLab: https://ncatlab.org/nlab/show/quotient+space
    nLab: https://ncatlab.org/nlab/show/topological+concrete+category
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出严格情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** Right-adjoint-right-inverses ARE left-adjoint-left-inverses *)

(* The two records carry the same four fields; only the parameter moves,
   from the left adjoint to the right one. *)
Definition rari_lali@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C}
  (P : RightAdjointRightInverse S) : LeftAdjointLeftInverse (rari_right P) :=
  {| lali_left := S; lali_adj := rari_adj P;
     lali_obj := rari_obj P; lali_counit := rari_counit P |}.

Definition lali_rari@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X}
  (P : LeftAdjointLeftInverse R) : RightAdjointRightInverse (lali_left P) :=
  {| rari_right := R; rari_adj := lali_adj P;
     rari_obj := lali_obj P; rari_counit := lali_counit P |}.

Example rari_lali_left@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_left (rari_lali P) = S := eq_refl.

Example lali_rari_right@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_right (lali_rari P) = R := eq_refl.

(* Both round trips are the identity on the nose (record eta). *)
Example rari_lali_rari@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_rari (rari_lali P) = P := eq_refl.

Example lali_rari_lali@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_lali (lali_rari P) = P := eq_refl.

(** ** The dual of Proposition 1, over left-adjoint-right-inverses *)

(* Coequalizers from sliced left-adjoint-right-inverses, over
   Theory/Equivalence/Strict.v's [LeftAdjointRightInverse].  The
   right-inverse clause is not consulted: only [lari_left] and [lari_adj]
   occur in the body. *)
Definition coequalizers_from_sliced_LARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) :
  @HasCoequalizers A :=
  coequalizers_from_sliced_left_adjoints G
    (fun a => lari_left (L a)) (fun a => lari_adj (L a)).

Example coequalizers_from_sliced_LARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)
    = `1 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_LARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g))
    = `2 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(** ** What the right-inverse clause adds, dually *)

Lemma coslice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Coslice C u} (e : p = q) :
  `1 (@id_cast (@Coslice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* A coequalizer moved along a Leibniz equation of apexes. *)
Definition IsCoequalizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : b ~> q} {e' : b ~> q'}
  (p : q = q') :
  e' ≈ id_cast p ∘ e → IsCoequalizer f g q e → IsCoequalizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_left in He.
  unshelve econstructor.
  - rewrite He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (coeq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section LARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (L : LeftAdjointRightInverse (Cosliced G y)).

Definition lari_universal :
  UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y) :=
  adj_unit_universal_op (lari_adj L) (Q; q).

Example lari_coeq_obj :
  cosliced_coeq_obj G q lari_universal = `1 (lari_left L (Q; q)) := eq_refl.

Example lari_coeq_arrow :
  cosliced_coeq_arrow G q lari_universal = `2 (lari_left L (Q; q)) := eq_refl.

(* The lifted object sits under Q: Leibniz, from the field [lari_obj]. *)
Definition lari_under : Q = G (`1 (lari_left L (Q; q))) :=
  f_equal (@projT1 _ _) (eq_sym (lari_obj L (Q; q))).

Lemma lari_arrow_under :
  fmap[G] (`2 (lari_left L (Q; q))) ≈ id_cast lari_under ∘ q.
Proof using Type.
  pose proof (`2 (@unit _ _ _ _ (lari_adj L) (Q; q))) as H; simpl in H.
  rewrite H.
  apply compose_respects; [|reflexivity].
  transitivity (`1 (@id_cast (@Coslice X (G y)) _ _
                     (eq_sym (lari_obj L (Q; q))))).
  - exact (lari_unit L (Q; q)).
  - rewrite (coslice_id_cast_1 (eq_sym (lari_obj L (Q; q)))).
    reflexivity.
Qed.

(* G carries the lifted coequalizer onto a coequalizer of the images. *)
Definition lari_preserves :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (lari_left L (Q; q)))) (fmap[G] (`2 (lari_left L (Q; q)))) :=
  IsCoequalizer_transport lari_under lari_arrow_under E.

End LARIPreserves.

Definition coequalizers_from_sliced_LARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L)
                         x y f g)))) :=
  lari_preserves G f g _ (`2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L y).

(** ** Faithfulness cannot be dropped from the dual either *)

Lemma parallel_pair_uncoforked {q : Parallel} (e : ParY ~{Parallel}~> q) :
  e ∘ par_arrow_one ≈ e ∘ par_arrow_two → False.
Proof.
  destruct q, e as [b h].
  - destruct (ParHom_Y_X_absurd _ h).
  - inversion h; subst. simpl. discriminate.
Qed.

Definition Parallel_no_coequalizers : @HasCoequalizers Parallel → False :=
  fun H =>
    parallel_pair_uncoforked
      (`1 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))
      (cofork (`2 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))).

Program Definition One_HasCoequalizers@{o h} :
  @HasCoequalizers _1@{o h h} := {|
  coeq := fun x y f g => (y; (id; {| cofork := _; coeq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma coslice_one_hom_eq@{o h +} (u : _1@{o h h})
  (x y : @Coslice _1@{o h h} u) (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseCoslice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(* The left adjoint of [Cosliced B a] is constant at the initial object
   (a; id) of the coslice under [a]. *)
Program Definition erase_coslice_left :
  @Coslice _1 (B a) ⟶ @Coslice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_coslice_hom_iso (c : @Coslice _1 (B a))
  (h : @Coslice Parallel a) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice Parallel a) (erase_coslice_left c) h;
       is_setoid := @homset (@Coslice Parallel a) (erase_coslice_left c) h |}
    {| carrier := @hom (@Coslice _1 (B a)) c (Cosliced B a h);
       is_setoid := @homset (@Coslice _1 (B a)) c (Cosliced B a h) |} := {|
  to := {| morphism := fun _ => (ttt; _) |};
  from := {| morphism := fun _ => (`2 h; _) |}
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; exact (symmetry (@id_right Parallel _ _ (`2 h))). Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite Hv; apply id_right.
Qed.

Definition erase_coslice_adj : erase_coslice_left ⊣ Cosliced B a.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ erase_coslice_left (Cosliced B a)
       erase_coslice_hom_iso).
  - intros x y z f g; simpl.
    reflexivity.
  - intros x y z f g; simpl.
    reflexivity.
Defined.

Definition erase_coslice_LARI : LeftAdjointRightInverse (Cosliced B a).
Proof.
  unshelve refine {| lari_left := erase_coslice_left;
                     lari_adj := erase_coslice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply coslice_one_hom_eq.
Defined.

End EraseCoslice.

Definition cosliced_LARI_without_faithfulness :
  (∀ a : Parallel, LeftAdjointRightInverse (Cosliced (Erase Parallel) a))
  * @HasCoequalizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasCoequalizers Parallel → False) :=
  (erase_coslice_LARI, One_HasCoequalizers, Erase_Parallel_not_faithful,
   Parallel_no_coequalizers).

(* The dual with the faithfulness hypothesis deleted is false. *)
Definition prop1_dual_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasCoequalizers X →
     (∀ a : A, LeftAdjointRightInverse (Cosliced G a)) →
     @HasCoequalizers A)
  → False :=
  fun P => Parallel_no_coequalizers
             (P Parallel _1 (Erase Parallel) One_HasCoequalizers
                erase_coslice_LARI).
