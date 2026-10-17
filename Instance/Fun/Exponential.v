Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.

Open Scope category_scope.

Generalizable All Variables.

(** * Exponentials of presheaves: [C^op, Sets] is cartesian closed *)

(*
 Book:      Riehl, Category Theory in Context, 2nd ed., §4.4,
 Book:      Riehl, ibid., §6.5 Exercise 6.5.iii, printed p. 248
 nLab:      https://ncatlab.org/nlab/show/exponential+object
 nLab:      closed+monoidal+structure+on+presheaves (same site), which
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A: the exponential presheaf -- Awodey display (8.5) *)

Section PshExpSec.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (P Q : C^op ⟶ Sets).

(* Display (8.5): Q^P(c) is the hom-setoid of the presheaf category at
   the representable on c times P.  Instance/Fun.v's [[[ , ]]]( , )
   notation packages exactly that as an object of [Sets]. *)
Definition PshExp_obj (c : C) : Sets :=
  [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q ).

(* Awodey's Q^P(h) = Hom(y h × 1_P, Q): precomposition with the
   representable's action on h, crossed with the identity of P.  The
   variance comes out on the nose with no transport, because
   [Curried_CoHom C] is [Curried_Hom C^op] and its source is [(C^op)^op],
   which is [C] definitionally: for [h : c ~{C^op}~> c'] the arrow
   [fmap[Curried_CoHom C] h] runs from the representable at [c'] to the
   representable at [c], which is the direction precomposition wants. *)
Definition PshExp_fmap (c c' : C) (h : c ~{C^op}~> c') :
  PshExp_obj c ~{Sets}~> PshExp_obj c'.
Proof.
  unshelve econstructor.
  - refine (fun alpha => nat_compose alpha _).
    exact (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
  - proper. exact (X x0 _).
Defined.

(* The two functor laws are PROVED, not inherited.  [fmap_id] is the one
   the default obligation tactic closes; a third [Next Obligation] is
   rejected for want of a goal. *)
Program Definition PshExp : C^op ⟶ Sets := {|
  fobj := PshExp_obj;
  fmap := PshExp_fmap
|}.
Next Obligation.
  proper.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; now rewrite X.
Qed.
Next Obligation.
  simpl; intros.
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

End PshExpSec.

(** ** B: the transposition, both ways *)

Section Transpose.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X P Q : C^op ⟶ Sets).

(* Riehl's beta_c(x), component at d: the function taking f : c -> d and
   z in P d to alpha_d ((X f) x, z). *)
Program Definition to_exp_inner_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  (d : C^op) :
  fobj[@product_obj _ PshCart (Curried_CoHom C c) P] d ~{Sets}~> fobj[Q] d :=
  {| morphism := fun hp => alpha d (fmap[X] (fst hp) x, snd hp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl in *.
  apply proper_morphism; split; simpl;
    [ exact (@fmap_respects _ _ X _ _ _ _ Hu x) | exact Hv ].
Qed.

Definition to_exp_inner
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C) (x : fobj[X] c)
  : @product_obj _ PshCart (Curried_CoHom C c) P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_inner_comp alpha c x).
  - intros d e f hp; simpl.
    etransitivity;
      [ exact (@naturality _ _ _ _ alpha _ _ f
                 (fmap[X] (fst hp) x, snd hp)) | ].
    simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
    symmetry; exact (@fmap_comp _ _ X _ _ _ f (fst hp) x).
Defined.

Program Definition to_exp_comp
  (alpha : @product_obj _ PshCart X P ⟹ Q) (c : C^op) :
  fobj[X] c ~{Sets}~> fobj[PshExp P Q] c :=
  {| morphism := fun x => to_exp_inner alpha c x |}.
Next Obligation.
  intros u v Huv d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  now apply proper_morphism.
Qed.

(* Riehl's beta : H ==> G^F.  Awodey's transpose of Hom(X × P, Q) into
   Hom(X, Q^P). *)
Definition to_exp (alpha : @product_obj _ PshCart X P ⟹ Q)
  : X ⟹ PshExp P Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (to_exp_comp alpha).
  - intros c c' f x d hp; simpl.
    apply proper_morphism; split; simpl; [ | reflexivity ].
    exact (@fmap_comp _ _ X _ _ _ (fst hp) f x).
Defined.

(* The counit route: alpha_c (x, p) = (beta_c x)_c (id_c, p), which is
   Riehl's ev composed with beta × F. *)
Program Definition from_exp_comp (beta : X ⟹ PshExp P Q) (c : C^op) :
  fobj[@product_obj _ PshCart X P] c ~{Sets}~> fobj[Q] c :=
  {| morphism := fun xp => (beta c (fst xp)) c (id[c], snd xp) |}.
Next Obligation.
  intros u v [Hu Hv]; simpl.
  etransitivity;
    [ exact (@proper_morphism _ _ _ _ (transform[beta] c) _ _ Hu c
               (id[c], snd u)) | ].
  apply proper_morphism; split; simpl; [ reflexivity | exact Hv ].
Qed.

Definition from_exp (beta : X ⟹ PshExp P Q)
  : @product_obj _ PshCart X P ⟹ Q.
Proof.
  unshelve eapply Build_Transform'.
  - exact (from_exp_comp beta).
  - intros c c' f xp; simpl.
    transitivity ((beta c (fst xp)) c' (f, fmap[P] f (snd xp))).
    + etransitivity;
        [ exact (@naturality _ _ _ _ (beta c (fst xp)) _ _ f
                   (id[c], snd xp)) | ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
    + etransitivity;
        [ | exact (@naturality _ _ _ _ beta _ _ f (fst xp) c'
                     (id[c'], fmap[P] f (snd xp))) ].
      simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
      unfold op; cat.
Defined.

(* One round trip is exactly [fmap_id] of X. *)
Lemma from_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  from_exp (to_exp alpha) ≈[[C^op, Sets]] alpha.
Proof.
  intros c xp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@fmap_id _ _ X c (fst xp)).
Qed.

(* The other is Riehl's Yoneda step, and it needs no Yoneda: the
   [naturality] field of beta at [fst hp], plus one identity law. *)
Lemma to_from_exp (beta : X ⟹ PshExp P Q) :
  to_exp (from_exp beta) ≈[[C^op, Sets]] beta.
Proof.
  intros c x d hp; simpl.
  symmetry.
  etransitivity;
    [ | exact (@naturality _ _ _ _ beta _ _ (fst hp) x d
                 (id[d], snd hp)) ].
  simpl; apply proper_morphism; split; simpl; [ | reflexivity ].
  unfold op; cat.
Qed.

(* Proposition 8.13 / Riehl (4.4.12), as an isomorphism of hom-setoids in
   [Sets].  Only the two isomorphism laws are written: the two
   respectfulness obligations are closed by the default tactic. *)
Program Definition presheaf_exp_iso :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp P Q )) := {|
  to   := {| morphism := to_exp |};
  from := {| morphism := from_exp |}
|}.
Next Obligation. exact (to_from_exp x x0 x1 x2 (h, c)). Qed.
Next Obligation. exact (from_to_exp x x0 (c, c0)). Qed.

End Transpose.

(** ** C: naturality in X -- Awodey's "And these isos are clearly
       natural in X" *)

Section NaturalX.

Context {C : Category}.

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

Context (X X' P Q : C^op ⟶ Sets).

(* One appeal to the naturality field of g -- its [naturality_sym]
   orientation -- and nothing else. *)
Lemma to_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (alpha : @product_obj _ PshCart X P ~{[C^op, Sets]}~> Q) :
  to_exp X' P Q (alpha ∘[[C^op, Sets]] @first _ PshCart _ _ P g)
    ≈[[C^op, Sets]] to_exp X P Q alpha ∘[[C^op, Sets]] g.
Proof.
  intros c x d hp; simpl.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  exact (@naturality_sym _ _ _ _ g _ _ (fst hp) x).
Qed.

(* The other direction is DEFINITIONAL: [reflexivity] closes it. *)
Lemma from_exp_natural_X (g : X' ~{[C^op, Sets]}~> X)
  (beta : X ~{[C^op, Sets]}~> PshExp P Q) :
  from_exp X' P Q (beta ∘[[C^op, Sets]] g)
    ≈[[C^op, Sets]] from_exp X P Q beta
                      ∘[[C^op, Sets]] @first _ PshCart _ _ P g.
Proof.
  intros c xp; simpl.
  reflexivity.
Qed.

End NaturalX.

(** ** D: Theorem 8.14, first clause *)

(* The universe binders are load-bearing and the trailing [+] is
   required; see the header.  [ump_exponents'] is the one written
   obligation: its goal normalises [op id ∘ id] to [id] by
   [fmap_respects] and then applies [fmap_id]. *)
#[export] Program Instance Functor_Category_Closed@{o h so +}
  (C : Category@{o h h}) :
  @Closed ([C^op, Sets@{h so}])
    (@Functor_Category_Cartesian (C^op) Sets@{h so} Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(* Riehl's Set^C, the covariant reading of the same theorem: a [:=] with
   no tactic and no transport, since [(C^op)^op] is [C].  Annotated like
   the instance so that it is delivered at the same universes; written
   unannotated it minimizes to [Category@{u0 u0 u0}] and is refused where
   the instance is accepted (measured; the probe pins the annotated form
   as a control at that very C). *)
Definition Functor_Category_Closed_cov@{o h so +} (C : Category@{o h h}) :
  @Closed ([C, Sets@{h so}])
    (@Functor_Category_Cartesian C Sets@{h so} Sets_Cartesian) :=
  Functor_Category_Closed (C^op).

(* The terminal presheaf is #339's, specialised.  With
   [Functor_Category_Cartesian] this completes the finite-product half of
   Theorem 8.14. *)
Definition presheaf_terminal (C : Category) : @Terminal ([C^op, Sets]) :=
  @Functor_Category_Terminal (C^op) Sets Sets_Terminal.

(** ** E: readbacks *)

Section Readbacks.
Context {C : Category}.
Context (X P Q : C^op ⟶ Sets).

#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* Awodey display (8.5) on the nose. *)
Example exp_obj_is_display85 (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]]( @product_obj _ PshCart (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's exponential IS the presheaf built above. *)
Example exponent_obj_is_PshExp :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

(* The class's transposes ARE the two maps built above. *)
Example curry_is_to_exp (alpha : @product_obj _ PshCart X P ⟹ Q) :
  @curry' _ _ (Functor_Category_Closed C) X P Q alpha = to_exp X P Q alpha
  := eq_refl.

Example uncurry_is_from_exp (beta : X ⟹ PshExp P Q) :
  @uncurry' _ _ (Functor_Category_Closed C) X P Q beta = from_exp X P Q beta
  := eq_refl.

(* Riehl's counit formula, at [≈] and not at [eq_refl]; see the header
   for the residue and the probe for the refutation. *)
Lemma eval_is_at_identity (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy).
Proof.
  simpl; apply proper_morphism; split; simpl;
    [ unfold op; cat | reflexivity ].
Qed.
End Readbacks.

Example presheaf_terminal_is_donor (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(** ** F: at C := 1 the construction recovers [Sets_Closed] *)

Section AtOne.
Context (P Q : _1^op ⟶ Sets).

#[local] Notation OneCart :=
  (@Functor_Category_Cartesian (_1^op) Sets Sets_Cartesian).

Program Definition one_exp_to :
  fobj[PshExp P Q] ttt
    ~{Sets}~> @exponent_obj Sets Sets_Cartesian Sets_Closed
                 (fobj[P] ttt) (fobj[Q] ttt) :=
  {| morphism := fun alpha => {| morphism := fun p => alpha ttt (ttt, p) |} |}.
Next Obligation.
  proper.
  apply proper_morphism; split; simpl; [ reflexivity | assumption ].
Qed.

(* The [match] is forced: [obj[1]] is [poly_unit], which has no eta here,
   so a component written as a plain function elaborates its second
   projection at the wrong object and the definition is rejected. *)
Program Definition one_from_comp
  (g : @exponent_obj Sets Sets_Cartesian Sets_Closed
         (fobj[P] ttt) (fobj[Q] ttt)) (d : obj[_1^op])
  : fobj[@product_obj _ OneCart (Curried_CoHom _1 ttt) P] d
      ~{Sets}~> fobj[Q] d :=
  match d with
  | ttt => {| morphism := fun hp => g (snd hp) |}
  end.
Next Obligation. proper. now apply proper_morphism. Qed.

Program Definition one_exp_from :
  @exponent_obj Sets Sets_Cartesian Sets_Closed (fobj[P] ttt) (fobj[Q] ttt)
    ~{Sets}~> fobj[PshExp P Q] ttt :=
  {| morphism := fun g => {| transform := one_from_comp g |} |}.
Next Obligation.
  destruct x, y, f, p; simpl.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation.
  destruct x, y, f, p; simpl.
  symmetry.
  etransitivity; [ exact (@fmap_id _ _ Q ttt (g c)) | ].
  symmetry; apply proper_morphism; exact (@fmap_id _ _ P ttt c).
Qed.
Next Obligation. proper; destruct x0; exact (X H). Qed.

Program Definition one_exp_iso :
  @Isomorphism Sets (fobj[PshExp P Q] ttt)
    (@exponent_obj Sets Sets_Cartesian Sets_Closed
       (fobj[P] ttt) (fobj[Q] ttt)) :=
  {| to := one_exp_to; from := one_exp_from |}.
Next Obligation. destruct x0, p; reflexivity. Qed.
End AtOne.
