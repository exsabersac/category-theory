Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(** * Choosing right adjoints functorially *)

(*
   nLab: https://ncatlab.org/nlab/show/mate

   本文件给出选择相关伴随。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(** ** (A) The full subcategory of the functors that have a right adjoint *)

(* "Has a right adjoint", as DATA: a chosen U together with a chosen
   adjunction.  `∃` is [sigT] here, so this is Mac Lane's "choosing one
   RF for each F" already made constructive -- there is nothing left for
   a choice principle to do. *)
Definition HasRightAdjoint {C D : Category} (F : D ⟶ C) : Type :=
  ∃ U : C ⟶ D, F ⊣ U.

(* Mac Lane's S: the FULL subcategory of A^X = [D, C] on those objects.
   [shom] is the terminal predicate, so every ambient transformation
   between selected functors is retained. *)
Definition LeftAdjSub (C D : Category) : Subcategory ([D, C]) :=
  @Build_Subcategory ([D, C])
    (fun F : D ⟶ C => HasRightAdjoint F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition LeftAdjCat (C D : Category) : Category :=
  Sub ([D, C]) (LeftAdjSub C D).

(* THE PIVOT.  An object of S IS an object of #395's category of
   adjunctions, on the nose: both are {F & {U & F ⊣ U}}. *)
Example leftadj_obj (C D : Category) : obj[LeftAdjCat C D] = AdjObj C D
  := eq_refl.

Definition LeftAdjSub_Full (C D : Category) :
  Category.Construction.Subcategory.Full ([D, C]) (LeftAdjSub C D) :=
  fun _ _ _ _ _ => I.

(* ------------------------------------------------------------------ *)
(** ** (B) R : S^op ⟶ X^A *)

(* Object part: the chosen right adjoint.  Arrow part: the conjugate.
   The three obligations are the three conjugate laws BY NAME; none of
   them is closed by the library's default obligation tactic. *)
Program Definition RightAdjointFunctor (C D : Category) :
  Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (x : AdjObj C D);
  fmap := fun x y f =>
            conj_mate (adjobj_adj (x : AdjObj C D))
                      (adjobj_adj (y : AdjObj C D)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. now apply conj_mate_id. Qed.
Next Obligation. now apply conj_mate_compose. Qed.

(* Two readbacks, and they are not the same kind.  The first records the
   ORIENTATION of the arrow action -- which [conj_mate] argument is which
   -- so that a later edit swapping them is caught here; it is a
   projection out of the transparent record and reads back the written
   body.  The second is not a projection: it computes the identity of
   [Opposite (LeftAdjCat C D)] all the way down to [nat_id].  Neither
   direction may be left to elaboration, because [Program] does NOT
   reject a swapped arrow action -- measured on this very definition, it
   defers the resulting type error into an obligation, and the breakdown
   surfaces only at the section close. *)
Example raf_fmap_variance (C D : Category)
        (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor C D] f
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (y : AdjObj C D)) (`1 f) := eq_refl.

Example raf_id_is_conj_mate_id (C D : Category)
        (x : Opposite (LeftAdjCat C D)) :
  fmap[RightAdjointFunctor C D] (@id (Opposite (LeftAdjCat C D)) x)
    = conj_mate (adjobj_adj (x : AdjObj C D))
                (adjobj_adj (x : AdjObj C D)) nat_id := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (C) S against #395's category of adjunctions *)

(* Identity on objects; on an arrow, the bare σ is paired with its mate.
   This is literally Instance/Adj/Forgetful.v's [AdjForgetLeft_Full]
   [prefmap], read as a functor. *)
Program Definition SubToAdj (C D : Category) : LeftAdjCat C D ⟶ Adj C D := {|
  fobj := fun x => (x : AdjObj C D);
  fmap := fun x y f =>
            {| conj_left  := `1 f
             ; conj_right := conj_mate (adjobj_adj (y : AdjObj C D))
                                       (adjobj_adj (x : AdjObj C D)) (`1 f) |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ _). Qed.
Next Obligation.
  intros f g Hfg; split; simpl; [ exact Hfg | now apply conj_mate_respects ].
Qed.
Next Obligation. split; simpl; [ reflexivity | now apply conj_mate_id ]. Qed.
Next Obligation.
  split; simpl; [ reflexivity | now apply conj_mate_compose ].
Qed.

(* R IS #395's second forgetful functor transported along that
   comparison: both actions agree on the nose. *)
Definition RAF_via (C D : Category) : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  AdjForgetRight C D ◯ Opposite_Functor (SubToAdj C D).

Example raf_obj_via (C D : Category) (x : Opposite (LeftAdjCat C D)) :
  fobj[RAF_via C D] x = fobj[RightAdjointFunctor C D] x := eq_refl.

Example raf_map_via (C D : Category) (x y : Opposite (LeftAdjCat C D))
        (f : x ~> y) :
  fmap[RAF_via C D] f = fmap[RightAdjointFunctor C D] f := eq_refl.

(* And the first forgetful functor, composed the same way, IS the
   inclusion of the subcategory -- again on both actions. *)
Definition LI_via (C D : Category) : LeftAdjCat C D ⟶ [D, C] :=
  AdjForgetLeft C D ◯ SubToAdj C D.

Example incl_obj_via (C D : Category) (x : LeftAdjCat C D) :
  fobj[LI_via C D] x = fobj[Incl ([D, C]) (LeftAdjSub C D)] x := eq_refl.

Example incl_map_via (C D : Category) (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[LI_via C D] f = fmap[Incl ([D, C]) (LeftAdjSub C D)] f := eq_refl.

#[export]
Program Instance SubToAdj_Faithful (C D : Category) :
  Category.Theory.Functor.Faithful (SubToAdj C D).
Next Obligation. destruct X as [Hl _]; exact Hl. Qed.

(* Fullness is where [conj_mate_uniq] is spent: the chosen preimage of a
   conjugate pair is its σ, and recovering the pair needs that the mate
   is THE conjugate of that σ. *)
#[export]
Program Instance SubToAdj_Full (C D : Category) :
  Category.Theory.Functor.Full (SubToAdj C D) := {|
  prefmap := fun x y g => (conj_left g; I)
|}.
Next Obligation.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law g).
Qed.

(* Essential surjectivity is free: the two categories have the same
   objects, and typeclass resolution fills [eso_iso] with [iso_id]
   (Theory/Isomorphism.v), leaving no obligation.  It is [#[local]], as
   the tree's two other concrete [EssentiallySurjective] witnesses are
   (Instance/FdVect.v, Construction/Reflective/Idempotent.v):
   the class carries a CHOSEN preimage and must not become globally
   resolvable; [SubToAdj_Equivalence] below still finds it. *)
#[local]
Program Instance SubToAdj_ESO (C D : Category) :
  EssentiallySurjective (SubToAdj C D) := {|
  eso_obj := fun d => (d : LeftAdjCat C D)
|}.

Definition SubToAdj_Equivalence (C D : Category) :
  EquivalenceOfCategories (SubToAdj C D) := FF_ESO_Equivalence (SubToAdj C D).

Program Definition AdjToSub (C D : Category) : Adj C D ⟶ LeftAdjCat C D := {|
  fobj := fun x => (x : LeftAdjCat C D);
  fmap := fun x y f => (conj_left f; I)
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. simpl; reflexivity. Qed.

Example rt_adj_obj (C D : Category) (x : Adj C D) :
  fobj[SubToAdj C D ◯ AdjToSub C D] x = x := eq_refl.

Example rt_sub_obj (C D : Category) (x : LeftAdjCat C D) :
  fobj[AdjToSub C D ◯ SubToAdj C D] x = x := eq_refl.

(* The strongest available identification.  `≅[StrictCat]` is an
   ISOMORPHISM OF CATEGORIES; `≅[Cat]` would be only an equivalence. *)
Program Definition SubAdj_strict_iso (C D : Category) :
  @Isomorphism StrictCat (LeftAdjCat C D) (Adj C D) := {|
  to := SubToAdj C D; from := AdjToSub C D
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  split; simpl; [ reflexivity | ].
  symmetry; apply conj_mate_uniq; exact (conj_pair_law f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** (D)(a) Two choices for one F *)

(* The subcategory is full, so the ambient identity of F lifts twice and
   the two memberships give ISOMORPHIC objects of S. *)
Definition choice_iso_in_Sub (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) :
  ((F; p) : LeftAdjCat C D) ≅[LeftAdjCat C D] (F; q) :=
  Full_membership_iso ([D, C]) (LeftAdjSub C D) (LeftAdjSub_Full C D) F p q.

(* R carries that isomorphism to the mate of the identity, on the nose,
   on BOTH legs. *)
Example raf_choice_iso_to (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (to (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; q) : AdjObj C D))
                (adjobj_adj ((F; p) : AdjObj C D)) nat_id := eq_refl.

Example raf_choice_iso_from (C D : Category) (F : D ⟶ C)
        (p q : HasRightAdjoint F) :
  fmap[RightAdjointFunctor C D] (from (choice_iso_in_Sub C D F p q))
    = conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id := eq_refl.

(* The two chosen right adjoints are naturally isomorphic.  This is the
   in-tree [right_adjoint_iso] recorded at a membership pair; it is
   [Qed], so its components do not reduce, and nothing below uses it. *)
Definition choice_right_adjoints_iso (C D : Category) (F : D ⟶ C)
           (p q : HasRightAdjoint F) : `1 p ≈ `1 q :=
  right_adjoint_iso F (`1 p) (`1 q) (`2 p) (`2 q).

(* The inverse law holds up to `≈` and not on the nose: it is
   [conj_mate_compose] followed by [conj_mate_id], with one
   identity-cancellation between them. *)
Lemma raf_choice_inverse (C D : Category) (F : D ⟶ C)
      (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  ≈ nat_id.
Proof.
  rewrite <- conj_mate_compose.
  transitivity (conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                          (adjobj_adj ((F; p) : AdjObj C D)) nat_id).
  - apply conj_mate_respects; intro a; simpl; cat.
  - now apply conj_mate_id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** (D)(b) A choice function as an explicit argument *)

(* The two conjugate laws restated with [D, C]'s and [C, D]'s own
   composition and identity in place of `∙` and [nat_id].  [rewrite],
   unlike [apply], will not cross those delta steps, and these are the
   forms the obligations of a functor INTO a functor category present. *)
Lemma cm_comp_fun {C D : Category} {F1 U1 F2 U2 F3 U3}
      (A1 : @Adjunction C D F1 U1) (A2 : @Adjunction C D F2 U2)
      (A3 : @Adjunction C D F3 U3)
      (s : F2 ⟹ F1) (s' : F3 ⟹ F2) :
  @compose ([C, D]) _ _ _ (conj_mate A2 A3 s') (conj_mate A1 A2 s)
    ≈ conj_mate A1 A3 (@compose ([D, C]) _ _ _ s s').
Proof. symmetry; now apply conj_mate_compose. Qed.

Lemma cm_id_fun {C D : Category} {F1 U1} (A1 : @Adjunction C D F1 U1) :
  conj_mate A1 A1 (@id ([D, C]) F1) ≈ @id ([C, D]) U1.
Proof. now apply conj_mate_id. Qed.

(* Mac Lane's "choosing one RF for each F", quantified: a function
   re-choosing a right adjoint for every member of S.  The name avoids
   the taken [Choice]. *)
Definition RightAdjChoice (C D : Category) : Type :=
  ∀ F : D ⟶ C, HasRightAdjoint F → HasRightAdjoint F.

Definition ch_obj {C D : Category} (ch : RightAdjChoice C D)
           (x : LeftAdjCat C D) : AdjObj C D := (`1 x; ch (`1 x) (`2 x)).

Program Definition RightAdjointFunctor_ch (C D : Category)
        (ch : RightAdjChoice C D) : Opposite (LeftAdjCat C D) ⟶ [C, D] := {|
  fobj := fun x => adjobj_right (ch_obj ch x);
  fmap := fun x y f =>
    conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply conj_mate_respects. Qed.
Next Obligation. apply cm_id_fun. Qed.
Next Obligation. symmetry; apply cm_comp_fun. Qed.

Lemma raf_ch_fmap (C D : Category) (ch : RightAdjChoice C D)
      (x y : Opposite (LeftAdjCat C D)) (f : x ~> y) :
  fmap[RightAdjointFunctor_ch C D ch] f
    = conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch y)) (`1 f).
Proof. reflexivity. Qed.

Definition ci_to (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch x) ~{[C, D]}~> adjobj_right (ch_obj ch' x) :=
  conj_mate (adjobj_adj (ch_obj ch x)) (adjobj_adj (ch_obj ch' x))
            (@id ([D, C]) (`1 x)).

Definition ci_from (C D : Category) (ch ch' : RightAdjChoice C D)
           (x : LeftAdjCat C D) :
  adjobj_right (ch_obj ch' x) ~{[C, D]}~> adjobj_right (ch_obj ch x) :=
  conj_mate (adjobj_adj (ch_obj ch' x)) (adjobj_adj (ch_obj ch x))
            (@id ([D, C]) (`1 x)).

Program Definition ci_iso (C D : Category) (ch ch' : RightAdjChoice C D)
        (x : LeftAdjCat C D) :
  @Isomorphism ([C, D]) (adjobj_right (ch_obj ch x))
                        (adjobj_right (ch_obj ch' x)) := {|
  to := ci_to C D ch ch' x; from := ci_from C D ch ch' x
|}.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch' x))
                          (adjobj_adj (ch_obj ch' x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.
Next Obligation.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  transitivity (conj_mate (adjobj_adj (ch_obj ch x))
                          (adjobj_adj (ch_obj ch x)) (@id ([D, C]) (`1 x))).
  - apply conj_mate_respects; intro a; simpl; cat.
  - apply cm_id_fun.
Qed.

(* These two readbacks exist because [rewrite] must get past [to] and
   [from] of a [Program]-built isomorphism; note also that [simpl] must
   NOT be run before the [cm_comp_fun] rewrites below, since it unfolds
   [conj_mate] and destroys the pattern. *)
Lemma ci_iso_to_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : to (ci_iso C D ch ch' x) = ci_to C D ch ch' x.
Proof. reflexivity. Qed.

Lemma ci_iso_from_eq (C D : Category) (ch ch' : RightAdjChoice C D)
      (x : LeftAdjCat C D) : from (ci_iso C D ch ch' x) = ci_from C D ch ch' x.
Proof. reflexivity. Qed.

(* INDEPENDENCE OF THE CHOICE.  Any two choice functions give naturally
   isomorphic functors -- `≈` at [C, D]'s functor setoid is exactly a
   natural isomorphism.  The components are mates of identities and the
   naturality square is [conj_mate_compose] read twice, once on each
   side; no property of either choice is used. *)
Theorem choice_independence (C D : Category) (ch ch' : RightAdjChoice C D) :
  RightAdjointFunctor_ch C D ch ≈ RightAdjointFunctor_ch C D ch'.
Proof.
  exists (ci_iso C D ch ch').
  intros x y f.
  rewrite ci_iso_to_eq, ci_iso_from_eq, !raf_ch_fmap.
  unfold ci_to, ci_from.
  rewrite cm_comp_fun.
  rewrite cm_comp_fun.
  apply conj_mate_respects.
  intro a; simpl; cat.
Qed.

(* (a) is (b) at the canonical choice: keep the adjoint the object
   already carries.  The three projections return on the nose. *)
Definition ch_canonical (C D : Category) : RightAdjChoice C D := fun _ h => h.

Example ch_canonical_left (C D : Category) (x : LeftAdjCat C D) :
  adjobj_left (ch_obj (ch_canonical C D) x) = adjobj_left (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_right (C D : Category) (x : LeftAdjCat C D) :
  adjobj_right (ch_obj (ch_canonical C D) x) = adjobj_right (x : AdjObj C D)
  := eq_refl.

Example ch_canonical_adj (C D : Category) (x : LeftAdjCat C D) :
  adjobj_adj (ch_obj (ch_canonical C D) x) = adjobj_adj (x : AdjObj C D)
  := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (E) Non-vacuity: S is inhabited and proper at the walking arrow *)

(* [_2] is thin, so any two parallel arrows coincide; the three-line
   proof is from Instance/Two.v's own [TwoHom_inv] and
   [TwoHom_Y_X_absurd].  (Instance/Two/Monoidal.v has the same lemma
   under the name [two_thin]; requiring that module would cost 17
   modules against the base of 28, that is, in place of Instance/Two --
   measured.) *)
Lemma two_arrows_agree {x y : TwoObj} (f g : TwoHom x y) : f = g.
Proof.
  destruct x, y;
    try (now rewrite (TwoHom_inv _ _ f), (TwoHom_inv _ _ g)).
  exact (False_rect _ (TwoHom_Y_X_absurd f)).
Qed.

Program Definition TwoConst (a : TwoObj) : _2 ⟶ _2 := {|
  fobj := fun _ => a;
  fmap := fun _ _ _ => @id _2 a
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. apply two_arrows_agree. Qed.

Definition two_to_Y (x : TwoObj) : x ~{_2}~> TwoY :=
  match x with TwoX => TwoXY | TwoY => TwoIdY end.

Definition two_from_X (y : TwoObj) : TwoX ~{_2}~> y :=
  match y with TwoX => TwoIdX | TwoY => TwoXY end.

#[local] Obligation Tactic := repeat intro; apply two_arrows_agree.

(* Every hom-set in sight is a singleton: _2(TwoX, y) is inhabited for
   every y and _2(x, TwoY) for every x, and _2 is thin. *)
Program Definition two_const_hom_iso (x y : TwoObj) :
  @Isomorphism Sets
    {| carrier := @hom _2 (fobj[TwoConst TwoX] x) y
     ; is_setoid := @homset _2 (fobj[TwoConst TwoX] x) y |}
    {| carrier := @hom _2 x (fobj[TwoConst TwoY] y)
     ; is_setoid := @homset _2 x (fobj[TwoConst TwoY] y) |} := {|
  to   := {| morphism := fun _ => two_to_Y x |};
  from := {| morphism := fun _ => two_from_X y |}
|}.

#[local] Obligation Tactic := intros.

(* The constant functor at TwoX is left adjoint to the constant functor
   at TwoY -- an adjunction between two functors neither of which is the
   identity. *)
Definition two_const_adj : TwoConst TwoX ⊣ TwoConst TwoY.
Proof.
  apply (@Build_Adjunction' _2 _2 (TwoConst TwoX) (TwoConst TwoY)
                            two_const_hom_iso);
  intros; apply two_arrows_agree.
Defined.

Definition two_left_adjoint_object : LeftAdjCat _2 _2 :=
  (TwoConst TwoX; (TwoConst TwoY; two_const_adj)).

(* R at that object returns the chosen right adjoint, on the nose. *)
Example two_raf_value :
  fobj[RightAdjointFunctor _2 _2] two_left_adjoint_object = TwoConst TwoY
  := eq_refl.

(* Not a degenerate witness: the two constant functors differ, and the
   left adjoint of the object is not the identity functor. *)
Lemma two_const_functors_differ :
  fobj[TwoConst TwoX] TwoX = fobj[TwoConst TwoY] TwoX → False.
Proof. discriminate. Qed.

Lemma two_left_adjoint_not_identity :
  fobj[adjobj_left two_left_adjoint_object] TwoY = fobj[Id[_2]] TwoY → False.
Proof. discriminate. Qed.

(* PROPERNESS.  The constant functor at TwoY has no right adjoint: from
   an adjunction, the inverse transpose of the identity of R(TwoX) is an
   arrow TwoY ~> TwoX, and there is none. *)
Lemma two_const_Y_no_right_adjoint (R : _2 ⟶ _2)
      (A : TwoConst TwoY ⊣ R) : False.
Proof.
  exact (TwoHom_Y_X_absurd
           (from (@adj _2 _2 (TwoConst TwoY) R A (fobj[R] TwoX) TwoX)
                 (@id _2 (fobj[R] TwoX)))).
Qed.

Lemma two_left_adjoint_proper : HasRightAdjoint (TwoConst TwoY) → False.
Proof. intros [R A]; exact (two_const_Y_no_right_adjoint R A). Qed.
