Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FunnyAssoc.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

(** ** The forward direction: flattening *)

(*
   本节说明 Associator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition FunnyAssocInnerL_sep (e : E) :
  SepFunctorial (E:=C □ (D □ E)) (fun (c : C) (d : D) => (c, (d, e))) := {|
  sf_lmap := fun c c' f d => lstep f;
  sf_rmap := fun c d d' g => @rstep C (D □ E) c (d, e) (d', e) (lstep g)
|}.
Next Obligation.
  proper.
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  apply feq_consR; [ | apply feq_refl ].
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation. exact (feq_idL fnil). Qed.
Next Obligation.
  eapply feq_trans; [ | apply rstep_id ].
  apply feq_consR; [ apply lstep_id | apply feq_refl ].
Qed.
Next Obligation.
  apply feq_sym; apply feq_fuseL.
Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseR.
  - apply feq_consR; [ apply feq_fuseL | apply feq_refl ].
Qed.

Definition FunnyAssocInnerL (e : E) : (C □ D) ⟶ (C □ (D □ E)) :=
  FunnyUP (FunnyAssocInnerL_sep e).

(* Flattening itself: on an outer left step the whole inner word is fed to
   [FunnyAssocInnerL e], so functoriality in that coordinate is exactly
   functoriality of the inner functor ([ffold_respects]/[ffold_app]). *)
Program Definition FunnyAssocTo_sep :
  SepFunctorial (E:=C □ (D □ E))
    (fun (p : C □ D) (e : E) => (fst p, (snd p, e))) := {|
  sf_lmap := fun p p' w e =>
    @fmap (C □ D) (C □ (D □ E)) (FunnyAssocInnerL e) p p' w;
  sf_rmap := fun p e e' h =>
    @rstep C (D □ E) (fst p) (snd p, e) (snd p, e') (rstep h)
|}.
Next Obligation.
  proper.
  now apply (ffold_respects (FunnyAssocInnerL_sep _)).
Qed.
Next Obligation.
  proper.
  apply feq_consR; [ | apply feq_refl ].
  apply feq_consR; [ assumption | apply feq_refl ].
Qed.
Next Obligation. apply feq_refl. Qed.
Next Obligation.
  eapply feq_trans; [ | apply rstep_id ].
  apply feq_consR; [ apply rstep_id | apply feq_refl ].
Qed.
Next Obligation. now apply (ffold_app (FunnyAssocInnerL_sep _)). Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseR.
  - apply feq_consR; [ apply feq_fuseR | apply feq_refl ].
Qed.

Definition FunnyAssocTo : ((C □ D) □ E) ⟶ (C □ (D □ E)) :=
  FunnyUP FunnyAssocTo_sep.

(** ** The backward direction: un-flattening *)

Program Definition FunnyAssocInnerR_sep (c : C) :
  SepFunctorial (E:=(C □ D) □ E) (fun (d : D) (e : E) => ((c, d), e)) := {|
  sf_lmap := fun d d' g e => @lstep (C □ D) E (c, d) (c, d') e (rstep g);
  sf_rmap := fun d e e' h => rstep h
|}.
Next Obligation.
  proper.
  apply feq_consL; [ | apply feq_refl ].
  apply feq_consR; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  apply feq_consR; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  eapply feq_trans; [ | apply lstep_id ].
  apply feq_consL; [ apply rstep_id | apply feq_refl ].
Qed.
Next Obligation. exact (feq_idR fnil). Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseL.
  - apply feq_consL; [ apply feq_fuseR | apply feq_refl ].
Qed.
Next Obligation.
  apply feq_sym; apply feq_fuseR.
Qed.

Definition FunnyAssocInnerR (c : C) : (D □ E) ⟶ ((C □ D) □ E) :=
  FunnyUP (FunnyAssocInnerR_sep c).

Program Definition FunnyAssocFrom_sep :
  SepFunctorial (E:=(C □ D) □ E)
    (fun (c : C) (q : D □ E) => ((c, fst q), snd q)) := {|
  sf_lmap := fun c c' f q =>
    @lstep (C □ D) E (c, fst q) (c', fst q) (snd q) (lstep f);
  sf_rmap := fun c q q' W =>
    @fmap (D □ E) ((C □ D) □ E) (FunnyAssocInnerR c) q q' W
|}.
Next Obligation.
  proper.
  apply feq_consL; [ | apply feq_refl ].
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  proper.
  now apply (ffold_respects (FunnyAssocInnerR_sep _)).
Qed.
Next Obligation.
  eapply feq_trans; [ | apply lstep_id ].
  apply feq_consL; [ apply lstep_id | apply feq_refl ].
Qed.
Next Obligation. apply feq_refl. Qed.
Next Obligation.
  apply feq_sym.
  eapply feq_trans.
  - apply feq_fuseL.
  - apply feq_consL; [ apply feq_fuseL | apply feq_refl ].
Qed.
Next Obligation. now apply (ffold_app (FunnyAssocInnerR_sep _)). Qed.

Definition FunnyAssocFrom : (C □ (D □ E)) ⟶ ((C □ D) □ E) :=
  FunnyUP FunnyAssocFrom_sep.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma FunnyAssocTo_lstep {p p' : C □ D} (e : E) (w : p ~{C □ D}~> p') :
  @fmap ((C □ D) □ E) (C □ (D □ E)) FunnyAssocTo (p, e) (p', e)
        (@lstep (C □ D) E p p' e w)
    = @fmap (C □ D) (C □ (D □ E)) (FunnyAssocInnerL e) p p' w.
Proof. exact (fapp_nil_r _). Qed.

Lemma FunnyAssocTo_rstep {p : C □ D} {e e' : E} (h : e ~{E}~> e') :
  @fmap ((C □ D) □ E) (C □ (D □ E)) FunnyAssocTo (p, e) (p, e')
        (@rstep (C □ D) E p e e' h)
    = @rstep C (D □ E) (fst p) (snd p, e) (snd p, e')
        (@rstep D E (snd p) e e' h).
Proof. reflexivity. Qed.

Lemma FunnyAssocFrom_lstep {c c' : C} (f : c ~{C}~> c') (q : D □ E) :
  @fmap (C □ (D □ E)) ((C □ D) □ E) FunnyAssocFrom (c, q) (c', q)
        (@lstep C (D □ E) c c' q f)
    = @lstep (C □ D) E (c, fst q) (c', fst q) (snd q)
        (@lstep C D c c' (fst q) f).
Proof. reflexivity. Qed.

Lemma FunnyAssocFrom_rstep (c : C) {q q' : D □ E} (W : q ~{D □ E}~> q') :
  @fmap (C □ (D □ E)) ((C □ D) □ E) FunnyAssocFrom (c, q) (c, q')
        (@rstep C (D □ E) c q q' W)
    = @fmap (D □ E) ((C □ D) □ E) (FunnyAssocInnerR c) q q' W.
Proof. exact (fapp_nil_r _). Qed.

(*
   本节说明 Associator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma from_innerL (e : E) {c c' : C} {d d' : D}
  (w : FunHom (C:=C) (D:=D) c d c' d') :
  @fmap (C □ (D □ E)) ((C □ D) □ E) FunnyAssocFrom (c, (d, e)) (c', (d', e))
        (@fmap (C □ D) (C □ (D □ E)) (FunnyAssocInnerL e) (c, d) (c', d') w)
    ≈ @lstep (C □ D) E (c, d) (c', d') e w.
Proof.
  induction w as [ c0 d0 | c1 c2 d1 f c3 d3 w IHw | c1 d1 d2 g c3 d3 w IHw ].
  - (* fnil: both sides are the identity of C □ D as a singleton *)
    exact (feq_sym _ _ (feq_idL fnil)).
  - (* fconsL f w: the C-step re-nests as a singleton left step *)
    eapply feq_trans;
      [ | exact (@feq_fuseL (C □ D) E (c1, d1) (c2, d1) (c3, d3) e
                   (lstep f) w (c3, d3) e fnil) ].
    apply feq_consL; [ apply feq_refl | exact IHw ].
  - (* fconsR g w: the D-step re-nests as a singleton right step *)
    eapply feq_trans;
      [ | exact (@feq_fuseL (C □ D) E (c1, d1) (c1, d2) (c3, d3) e
                   (rstep g) w (c3, d3) e fnil) ].
    apply feq_consL; [ apply feq_refl | exact IHw ].
Qed.

Lemma to_innerR (c : C) {d d' : D} {e e' : E}
  (W : FunHom (C:=D) (D:=E) d e d' e') :
  @fmap ((C □ D) □ E) (C □ (D □ E)) FunnyAssocTo ((c, d), e) ((c, d'), e')
        (@fmap (D □ E) ((C □ D) □ E) (FunnyAssocInnerR c) (d, e) (d', e') W)
    ≈ @rstep C (D □ E) c (d, e) (d', e') W.
Proof.
  induction W as [ d0 e0 | d1 d2 e1 g d3 e3 W IHW | d1 e1 e2 h d3 e3 W IHW ].
  - exact (feq_sym _ _ (feq_idR fnil)).
  - eapply feq_trans;
      [ | exact (@feq_fuseR C (D □ E) c (d1, e1) (d2, e1) (d3, e3)
                   (lstep g) W c (d3, e3) fnil) ].
    apply feq_consR; [ apply feq_refl | exact IHW ].
  - eapply feq_trans;
      [ | exact (@feq_fuseR C (D □ E) c (d1, e1) (d1, e2) (d3, e3)
                   (rstep h) W c (d3, e3) fnil) ].
    apply feq_consR; [ apply feq_refl | exact IHW ].
Qed.

(* The same facts, phrased through the round-trip composites. *)
Lemma from_to_lstep (e : E) {c c' : C} {d d' : D}
  (w : FunHom (C:=C) (D:=D) c d c' d') :
  @fmap (C □ (D □ E)) ((C □ D) □ E) FunnyAssocFrom (c, (d, e)) (c', (d', e))
        (@fmap ((C □ D) □ E) (C □ (D □ E)) FunnyAssocTo ((c, d), e) ((c', d'), e)
               (@lstep (C □ D) E (c, d) (c', d') e w))
    ≈ @lstep (C □ D) E (c, d) (c', d') e w.
Proof.
  rewrite FunnyAssocTo_lstep.
  apply from_innerL.
Qed.

Lemma to_from_rstep (c : C) {d d' : D} {e e' : E}
  (W : FunHom (C:=D) (D:=E) d e d' e') :
  @fmap ((C □ D) □ E) (C □ (D □ E)) FunnyAssocTo ((c, d), e) ((c, d'), e')
        (@fmap (C □ (D □ E)) ((C □ D) □ E) FunnyAssocFrom (c, (d, e)) (c, (d', e'))
               (@rstep C (D □ E) c (d, e) (d', e') W))
    ≈ @rstep C (D □ E) c (d, e) (d', e') W.
Proof.
  rewrite FunnyAssocFrom_rstep.
  apply to_innerR.
Qed.

(** ** The round trips, as strict equalities of functors *)

Lemma funny_assoc_from_to :
  @equiv _ (@Functor_StrictEq_Setoid ((C □ D) □ E) ((C □ D) □ E))
    (FunnyAssocFrom ◯ FunnyAssocTo) Id.
Proof.
  apply (Funny_strict_eq (FunnyAssocFrom ◯ FunnyAssocTo) Id
           (fun p e => match p with (c, d) => eq_refl end)).
  - intros [c d] [c' d'] w e.
    exact (from_to_lstep e w).
  - intros [c d] e e' h.
    (* rstep h round-trips on the nose *)
    apply feq_refl.
Qed.

Lemma funny_assoc_to_from :
  @equiv _ (@Functor_StrictEq_Setoid (C □ (D □ E)) (C □ (D □ E)))
    (FunnyAssocTo ◯ FunnyAssocFrom) Id.
Proof.
  apply (Funny_strict_eq (FunnyAssocTo ◯ FunnyAssocFrom) Id
           (fun c q => match q with (d, e) => eq_refl end)).
  - intros c c' f [d e].
    (* lstep f round-trips on the nose *)
    apply feq_refl.
  - intros c [d e] [d' e'] W.
    exact (to_from_rstep c W).
Qed.

Definition Funny_assoc : ((C □ D) □ E) ≅[StrictCat] (C □ (D □ E)) :=
  @Build_Isomorphism StrictCat ((C □ D) □ E) (C □ (D □ E))
    FunnyAssocTo FunnyAssocFrom funny_assoc_to_from funny_assoc_from_to.

End FunnyAssoc.

(* The deliverable Cat-iso, free via the comparison functor. *)
Definition Funny_assoc_cat {C D E : Category} :
  ((C □ D) □ E) ≅[Cat] (C □ (D □ E)) :=
  fobj_iso StrictCat_to_Cat _ _ Funny_assoc.

(** ** Naturality in all three arguments

    Both routes around each square send every generating step to the same
    generating step, so after the word inductions every leaf closes by
    reflexivity. *)

Lemma FunnyAssocTo_natural_word {C C' D D' E E' : Category}
  (F : C ⟶ C') (G : D ⟶ D') (H : E ⟶ E') (e : E)
  {c c' : C} {d d' : D} (w : FunHom (C:=C) (D:=D) c d c' d') :
  @fmap (C □ (D □ E)) (C' □ (D' □ E')) (FunnyBimap F (FunnyBimap G H))
        (c, (d, e)) (c', (d', e))
        (@fmap (C □ D) (C □ (D □ E)) (FunnyAssocInnerL e) (c, d) (c', d') w)
    ≈ @fmap (C' □ D') (C' □ (D' □ E')) (FunnyAssocInnerL (H e))
        (F c, G d) (F c', G d')
        (@fmap (C □ D) (C' □ D') (FunnyBimap F G) (c, d) (c', d') w).
Proof.
  induction w as [ c0 d0 | c1 c2 d1 f c3 d3 w IHw | c1 d1 d2 g c3 d3 w IHw ].
  - apply feq_refl.
  - apply feq_consL; [ reflexivity | exact IHw ].
  - apply feq_consR; [ apply feq_refl | exact IHw ].
Qed.

Lemma FunnyAssoc_natural {C C' D D' E E' : Category}
  (F : C ⟶ C') (G : D ⟶ D') (H : E ⟶ E') :
  @equiv _ (@Functor_StrictEq_Setoid ((C □ D) □ E) (C' □ (D' □ E')))
    (FunnyBimap F (FunnyBimap G H) ◯ FunnyAssocTo)
    (FunnyAssocTo ◯ FunnyBimap (FunnyBimap F G) H).
Proof.
  apply (Funny_strict_eq
           (FunnyBimap F (FunnyBimap G H) ◯ FunnyAssocTo)
           (FunnyAssocTo ◯ FunnyBimap (FunnyBimap F G) H)
           (fun _ _ => eq_refl)).
  - intros p p' w e.
    exact (feq_trans _ _ _
             (ffold_respects (FunnyBimap_sep F (FunnyBimap G H))
                (feq_fapp_fnil _))
             (feq_trans _ _ _
                (FunnyAssocTo_natural_word F G H e w)
                (feq_sym _ _ (feq_fapp_fnil _)))).
  - intros p e e' h.
    apply feq_refl.
Qed.

Lemma FunnyAssocFrom_natural_word {C C' D D' E E' : Category}
  (F : C ⟶ C') (G : D ⟶ D') (H : E ⟶ E') (c : C)
  {d d' : D} {e e' : E} (W : FunHom (C:=D) (D:=E) d e d' e') :
  @fmap ((C □ D) □ E) ((C' □ D') □ E') (FunnyBimap (FunnyBimap F G) H)
        ((c, d), e) ((c, d'), e')
        (@fmap (D □ E) ((C □ D) □ E) (FunnyAssocInnerR c) (d, e) (d', e') W)
    ≈ @fmap (D' □ E') ((C' □ D') □ E') (FunnyAssocInnerR (F c))
        (G d, H e) (G d', H e')
        (@fmap (D □ E) (D' □ E') (FunnyBimap G H) (d, e) (d', e') W).
Proof.
  induction W as [ d0 e0 | d1 d2 e1 g d3 e3 W IHW | d1 e1 e2 h d3 e3 W IHW ].
  - apply feq_refl.
  - apply feq_consL; [ apply feq_refl | exact IHW ].
  - apply feq_consR; [ reflexivity | exact IHW ].
Qed.

Lemma FunnyAssocFrom_natural {C C' D D' E E' : Category}
  (F : C ⟶ C') (G : D ⟶ D') (H : E ⟶ E') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ (D □ E)) ((C' □ D') □ E'))
    (FunnyBimap (FunnyBimap F G) H ◯ FunnyAssocFrom)
    (FunnyAssocFrom ◯ FunnyBimap F (FunnyBimap G H)).
Proof.
  apply (Funny_strict_eq
           (FunnyBimap (FunnyBimap F G) H ◯ FunnyAssocFrom)
           (FunnyAssocFrom ◯ FunnyBimap F (FunnyBimap G H))
           (fun _ _ => eq_refl)).
  - intros c c' f q.
    apply feq_refl.
  - intros c q q' W.
    exact (feq_trans _ _ _
             (ffold_respects (FunnyBimap_sep (FunnyBimap F G) H)
                (feq_fapp_fnil _))
             (feq_trans _ _ _
                (FunnyAssocFrom_natural_word F G H c W)
                (feq_sym _ _ (feq_fapp_fnil _)))).
Qed.
