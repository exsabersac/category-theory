Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance edgeset.

(*
   nLab:      https://ncatlab.org/nlab/show/free+groupoid
   nLab:      https://ncatlab.org/nlab/show/groupoid
   nLab:      https://ncatlab.org/nlab/show/quotient+category
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Riehl, Category Theory in Context, §4.2, printed p. 139 (free ⊣
   Book: Higgins, Categories and Groupoids, Van Nostrand 1971, reprinted
   Book: Brown, Topology and Groupoids, 2006 (free groupoids, and the case

   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SignedQuiver.

Universes o h p.
Context (G : Quiver@{o h p}).

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sedge (x y : G) : Type@{h} := (edges x y + edges y x)%type.

Definition sedge_equiv {x y : G} (a b : sedge x y) : Type@{p} :=
  match a, b with
  | inl e, inl e' => e ≈ e'
  | inr e, inr e' => e ≈ e'
  | _, _ => False
  end.

Definition sedge_equivalence (x y : G) : Equivalence (@sedge_equiv x y).
Proof.
  constructor.
  - intros [e|e]; simpl; reflexivity.
  - intros [e|e] [e'|e'] H; simpl in *;
      solve [ contradiction | now symmetry ].
  - intros [e|e] [e'|e'] [e''|e''] H1 H2; simpl in *;
      solve [ contradiction | now transitivity e' ].
Defined.

Definition SignedQuiver : Quiver@{o h p} := {|
  nodes   := @nodes G;
  edges   := sedge;
  edgeset := fun x y => {| equiv        := @sedge_equiv x y;
                           setoid_equiv := sedge_equivalence x y |}
|}.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sflip (x y : G) (a : sedge x y) : sedge y x :=
  match a with
  | inl e => inr e
  | inr e => inl e
  end.

Lemma sflip_involutive (x y : G) (a : sedge x y) :
  sflip y x (sflip x y a) = a.
Proof. now destruct a. Qed.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeSigned : Category@{o h p} := FreeOnQuiver SignedQuiver.

(** A generator, positive and negative. *)
Definition spos {x y : G} (e : edges x y) : x ~{FreeSigned}~> y :=
  tlist_singleton (B:=@edges SignedQuiver) (inl e).

Definition sneg {x y : G} (e : edges x y) : y ~{FreeSigned}~> x :=
  tlist_singleton (B:=@edges SignedQuiver) (inr e).

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive FreeGroupoidRel : ∀ x y : FreeSigned,
    (x ~{FreeSigned}~> y) → (x ~{FreeSigned}~> y) → Type :=
  | fgr_left  {x y : G} (e : edges x y) :
      FreeGroupoidRel x x (sneg e ∘ spos e) id
  | fgr_right {x y : G} (e : edges x y) :
      FreeGroupoidRel y y (spos e ∘ sneg e) id.

(** ** The free groupoid *)
Definition FreeGroupoid : Category@{o h p} :=
  QuotientCong FreeSigned FreeGroupoidRel.

(** 本节：The projection words classes. （已译） *)
Definition FreeGroupoidProj : FreeSigned ⟶ FreeGroupoid :=
  QuotientCongProj FreeGroupoidRel.

(** A signed generator, read as a morphism of the free groupoid. *)
Definition fgen {x y : G} (a : @edges SignedQuiver x y)
  : x ~{FreeGroupoid}~> y := tlist_singleton a.

(** A positive generator, i.e. the image of an edge of [G]. *)
Definition fgpos {x y : G} (e : edges x y) : x ~{FreeGroupoid}~> y :=
  fgen (inl e).

(** ...and a negative one. *)
Definition fgneg {x y : G} (e : edges x y) : y ~{FreeGroupoid}~> x :=
  fgen (inr e).

(** 本节：The two imposed equations, holding free groupoid. （已译） *)
Lemma fg_cancel_left {x y : G} (e : edges x y) :
  fgneg e ∘ fgpos e ≈ @id FreeGroupoid x.
Proof. exact (cc_gen (fgr_left e)). Qed.

Lemma fg_cancel_right {x y : G} (e : edges x y) :
  fgpos e ∘ fgneg e ≈ @id FreeGroupoid y.
Proof. exact (cc_gen (fgr_right e)). Qed.

(** 本节：Both at once, arbitrary SIGNED generator: flip generator
 left inverse it. The case split sign, each branch
 one two imposed equations. （已译） *)
Lemma fgen_flip_left {x y : G} (a : @edges SignedQuiver x y) :
  fgen (sflip x y a) ∘ fgen a ≈ @id FreeGroupoid x.
Proof.
  destruct a as [e|e].
  - exact (fg_cancel_left e).
  - exact (fg_cancel_right e).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fginv {x y : G} (f : x ~{FreeGroupoid}~> y)
  : y ~{FreeGroupoid}~> x := tlist_rev sflip f.

(** Inversion is involutive on the nose, before any quotient is taken. *)
Lemma fginv_involutive {x y : G} (f : x ~{FreeGroupoid}~> y) :
  fginv (fginv f) = f.
Proof. exact (tlist_rev_involutive sflip sflip_involutive f). Qed.

(** The anti-homomorphism law, likewise at Leibniz [=]. *)
Lemma fginv_compose {x y z : G}
  (f : y ~{FreeGroupoid}~> z) (g : x ~{FreeGroupoid}~> y) :
  fginv (f ∘ g) = fginv g ∘ fginv f.
Proof. exact (tlist_rev_app_distr sflip g f). Qed.

(** Reversing a one-letter word flips its sign, again at Leibniz [=]. *)
Lemma fginv_gen {x y : G} (a : @edges SignedQuiver x y) :
  fginv (fgen a) = fgen (sflip x y a).
Proof.
  unfold fginv, fgen, tlist_singleton.
  rewrite tlist_rev_equation_2, tlist_rev_equation_1.
  now rewrite tlist_app_tnil_l.
Qed.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fginv_left {x y : G} (f : x ~{FreeGroupoid}~> y) :
  fginv f ∘ f ≈ @id FreeGroupoid x.
Proof.
  induction f.
  - transitivity (@compose FreeGroupoid y y y id id).
    + apply compose_respects; [ | reflexivity ].
      unfold fginv; rewrite tlist_rev_equation_1; reflexivity.
    + apply id_left.
  - rewrite (tlist_app_cons b f).
    change ((b ::: tnil) +++ f)
      with (@compose FreeGroupoid i j y f (fgen b)).
    rewrite fginv_compose, fginv_gen.
    rewrite <- comp_assoc, (comp_assoc (fginv f) f (fgen b)).
    rewrite IHf, id_left.
    apply fgen_flip_left.
Qed.

(** ...and other side, applying previous 引理 at [fginv f]
 using involutivity. No second induction. （已译） *)
Lemma fginv_right {x y : G} (f : x ~{FreeGroupoid}~> y) :
  f ∘ fginv f ≈ @id FreeGroupoid y.
Proof.
  transitivity (@compose FreeGroupoid y x y (fginv (fginv f)) (fginv f)).
  - apply compose_respects; [ | reflexivity ].
    now rewrite fginv_involutive.
  - apply fginv_left.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeGroupoid_IsGroupoid : IsGroupoid FreeGroupoid :=
  fun x y f =>
    {| two_sided_inverse := fginv f;
       is_right_inverse  := fginv_right f;
       is_left_inverse   := fginv_left f |}.

(** 本节：The chosen inverse [Structure/Groupoid.v]'s [ginv] IS word reversal,
 definitionally: [ginv] projects [two_sided_inverse] out record
 just built. （已译） *)
Example fg_ginv_is_reversal {x y : G} (f : x ~{FreeGroupoid}~> y) :
  ginv FreeGroupoid_IsGroupoid f = fginv f := eq_refl.

(* * ** The unit: quiver homomorphism 进入 underlying quiver （已译） *)

Definition FreeGroupoidUnit
  : QuiverHomomorphism G (QuiverOfCat FreeGroupoid).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - exact (fun x y e => fgpos e).
  - intros x y e e' He.
    apply cc_equiv.
    unfold fgpos, fgen, tlist_singleton; simpl.
    exists eq_refl; [ exact He | reflexivity ].
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeGroupoidUMP.

Context {D : Category}.
Context (Dg : IsGroupoid D).
Context (F : QuiverHomomorphism G (QuiverOfCat D)).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition signed_hom : QuiverHomomorphism SignedQuiver (QuiverOfCat D).
Proof using D Dg F G.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (@fnodes _ _ F).
  - intros x y a.
    exact (match a with
           | inl e => @fedgemap _ _ F x y e
           | inr e => ginv Dg (@fedgemap _ _ F y x e)
           end).
  - intros x y [e|e] [e'|e'] Ha; simpl in Ha;
      solve [ contradiction
            | now apply (@fedgemap_respects _ _ F)
            | now rewrite (@fedgemap_respects _ _ F _ _ _ _ Ha) ].
Defined.

(** The 函子 out free CATEGORY signed quiver. （已译） *)
Definition signed_functor : FreeSigned ⟶ D :=
  InducedFunctor SignedQuiver signed_hom.

(** On one-letter word it signed extension. (The [id_left] the
 path fold's trailing 恒等 singleton path.) （已译） *)
Lemma signed_functor_gen {x y : G} (a : @edges SignedQuiver x y) :
  fmap[signed_functor] (tlist_singleton a)
    ≈ @fedgemap _ _ signed_hom x y a.
Proof. simpl; now rewrite id_left. Qed.

(** It merges cancellation relations — 这是 假设
 [QuotientCongLift] 所消耗, [cc_kernel] extends it whole
 generated congruence no second induction. （已译） *)
Lemma signed_functor_merges :
  ∀ x y (f g : x ~{FreeSigned}~> y), FreeGroupoidRel x y f g →
    fmap[signed_functor] f ≈ fmap[signed_functor] g.
Proof.
  intros x y f g Hr; destruct Hr as [x' y' e|x' y' e];
    rewrite fmap_comp, fmap_id;
    unfold spos, sneg;
    rewrite !signed_functor_gen; simpl.
  - apply (ginv_left Dg).
  - apply (ginv_right Dg).
Qed.

(** The induced 函子 out free groupoid. （已译） *)
Definition FreeGroupoidFunctor : FreeGroupoid ⟶ D :=
  QuotientCongLift FreeGroupoidRel signed_functor signed_functor_merges.

(** 本节：It agrees [F] nodes, nose... （已译） *)
Lemma FreeGroupoidFunctor_obj (x : G) :
  fobj[FreeGroupoidFunctor] x = @fnodes _ _ F x.
Proof. reflexivity. Qed.

(** 本节：...and generating edges, up [≈]. （已译） *)
Lemma FreeGroupoidFunctor_gen {x y : G} (e : edges x y) :
  fmap[FreeGroupoidFunctor] (fgpos e) ≈ @fedgemap _ _ F x y e.
Proof. exact (signed_functor_gen (inl e)). Qed.

(** 本节：The negative generators forced: images inverses. （已译） *)
Lemma FreeGroupoidFunctor_neg {x y : G} (e : edges x y) :
  fmap[FreeGroupoidFunctor] (fgneg e) ≈ ginv Dg (@fedgemap _ _ F x y e).
Proof. exact (signed_functor_gen (inr e)). Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Unique.

Context (K : FreeGroupoid ⟶ D).
Context (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x).
Context (Hgen : ∀ (x y : G) (e : edges x y),
            hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
              ≈ @fedgemap _ _ F x y e).

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma unique_neg {x y : G} (e : edges x y) :
  hom_cast (Hobj y) (Hobj x) (fmap[K] (fgneg e))
    ≈ ginv Dg (@fedgemap _ _ F x y e).
Proof using D Dg F G Hgen Hobj K.
  symmetry.
  apply (ginv_unique_l Dg).
  rewrite <- (Hgen x y e).
  rewrite (hom_cast_comp (Hobj x) (Hobj y) (Hobj x)).
  rewrite <- fmap_comp.
  rewrite (fg_cancel_left e).
  rewrite fmap_id.
  apply hom_cast_id.
Qed.

(** 本节：The same signed generator either sign. （已译） *)
Lemma unique_gen {x y : G} (a : @edges SignedQuiver x y) :
  hom_cast (Hobj x) (Hobj y) (fmap[K] (fgen a))
    ≈ @fedgemap _ _ signed_hom x y a.
Proof using D Dg F G Hgen Hobj K.
  destruct a as [e|e].
  - exact (Hgen x y e).
  - exact (unique_neg e).
Qed.

(** Uniqueness on every word, by the path induction of
    [Construction/Free/Quiver/Presented.v]'s [PresentedFunctor_unique]. *)
Lemma FreeGroupoidFunctor_unique :
  ∀ (x y : G) (f : x ~{FreeGroupoid}~> y),
    hom_cast (Hobj x) (Hobj y) (fmap[K] f) ≈ fmap[FreeGroupoidFunctor] f.
Proof using D Dg F G Hgen Hobj K.
  intros x y f.
  induction f.
  - change (@tnil _ _ y) with (@id FreeGroupoid y).
    rewrite fmap_id; simpl; rewrite hom_cast_id.
    reflexivity.
  - assert (RW : @equiv _ (@homset FreeGroupoid i y) (b ::: f)
                   (@compose FreeGroupoid i j y f (fgen b))).
    { apply cc_equiv; unfold fgen, tlist_singleton; simpl.
      now rewrite <- tlist_app_cons. }
    rewrite RW, fmap_comp.
    rewrite <- (hom_cast_comp (Hobj i) (Hobj j) (Hobj y)).
    rewrite IHf, unique_gen.
    rewrite fmap_comp.
    apply compose_respects; [ reflexivity | ].
    symmetry; exact (signed_functor_gen b).
Qed.

End Unique.

End FreeGroupoidUMP.

End SignedQuiver.

Arguments sedge G x y : assert.
Arguments SignedQuiver G : assert.
Arguments FreeSigned G : assert.
Arguments FreeGroupoid G : assert.
Arguments spos {G x y} e.
Arguments sneg {G x y} e.
Arguments fgen {G x y} a.
Arguments fgpos {G x y} e.
Arguments fgneg {G x y} e.
Arguments fginv {G x y} f.
Arguments fg_cancel_left {G x y} e.
Arguments fg_cancel_right {G x y} e.
Arguments fgen_flip_left {G x y} a.
Arguments fginv_involutive {G x y} f.
Arguments fginv_compose {G x y z} f g.
Arguments fginv_gen {G x y} a.
Arguments fginv_left {G x y} f.
Arguments fginv_right {G x y} f.
Arguments sflip_involutive {G} x y a.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeGroupoidUniversal.

Context (G : Quiver) {D : Category}.
Context (Dg : IsGroupoid D).

Theorem free_groupoid_universal
  (F : QuiverHomomorphism G (QuiverOfCat D)) :
  { K : FreeGroupoid G ⟶ D &
  { Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x &
    ((∀ (x y : G) (e : edges x y),
        hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
          ≈ @fedgemap _ _ F x y e) *
     (∀ (K' : FreeGroupoid G ⟶ D)
        (Hobj' : ∀ x : G, fobj[K'] x = @fnodes _ _ F x),
        (∀ (x y : G) (e : edges x y),
           hom_cast (Hobj' x) (Hobj' y) (fmap[K'] (fgpos e))
             ≈ @fedgemap _ _ F x y e) →
        ∀ (x y : G) (f : x ~{FreeGroupoid G}~> y),
          hom_cast (Hobj' x) (Hobj' y) (fmap[K'] f)
            ≈ hom_cast (Hobj x) (Hobj y) (fmap[K] f)))%type } }.
Proof using D Dg G.
  exists (FreeGroupoidFunctor G Dg F), (fun _ => eq_refl).
  split.
  - intros x y e. exact (FreeGroupoidFunctor_gen G Dg F e).
  - intros K' Hobj' Hgen x y f.
    exact (FreeGroupoidFunctor_unique G Dg F K' Hobj' Hgen x y f).
Qed.

End FreeGroupoidUniversal.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fg_restrict {G : Quiver} {D : Category} (S : FreeGroupoid G ⟶ D)
  : QuiverHomomorphism G (QuiverOfCat D) :=
  QuiverComp (FreeGroupoidUnit G) (QuiverHomomorphismOfFunctor _ _ S).

(** On generators the restriction is [S] itself, definitionally — a Leibniz
    equality of morphisms, stated at that strength deliberately, in the
    manner of [QuotientLift_proj] ([Construction/Quotient.v]). *)
Lemma fg_restrict_gen {G : Quiver} {D : Category} (S : FreeGroupoid G ⟶ D)
  {x y : G} (e : edges x y) :
  @fedgemap _ _ (fg_restrict S) x y e = fmap[S] (fgpos e).
Proof. reflexivity. Qed.

(** 本节：...and restriction re-extends [S] every word. （已译） *)
Lemma fg_restrict_recovers {G : Quiver} {D : Category} (Dg : IsGroupoid D)
  (S : FreeGroupoid G ⟶ D) (x y : G) (f : x ~{FreeGroupoid G}~> y) :
  fmap[S] f ≈ fmap[FreeGroupoidFunctor G Dg (fg_restrict S)] f.
Proof.
  refine (FreeGroupoidFunctor_unique G Dg (fg_restrict S) S
            (fun _ => eq_refl) _ x y f).
  intros a b e; reflexivity.
Qed.

(** The round trip at STRICT strength: an equality of functors in
    [StrictCat], via [Construction/Quotient.v]'s [strict_of_hom_cast]. *)
Lemma fg_restrict_recovers_strict {G : Quiver} {D : Category}
  (Dg : IsGroupoid D) (S : FreeGroupoid G ⟶ D) :
  @equiv _ (@Functor_StrictEq_Setoid (FreeGroupoid G) D)
    S (FreeGroupoidFunctor G Dg (fg_restrict S)).
Proof.
  apply (strict_of_hom_cast S (FreeGroupoidFunctor G Dg (fg_restrict S))
           (fun _ => eq_refl)).
  intros x y f.
  exact (fg_restrict_recovers Dg S x y f).
Qed.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fg_extend_restrict {G : Quiver} {D : Category} (Dg : IsGroupoid D)
  (F : QuiverHomomorphism G (QuiverOfCat D)) :
  @equiv _ (@homset QuiverCategory G (QuiverOfCat D))
    (fg_restrict (FreeGroupoidFunctor G Dg F)) F.
Proof.
  exists (fun _ => eq_refl).
  intros x y e; simpl.
  exact (FreeGroupoidFunctor_gen G Dg F e).
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fg_proj_obj {G : Quiver} (x : G) :
  fobj[FreeGroupoidProj G] x = x.
Proof. reflexivity. Qed.

Lemma fg_hom_type {G : Quiver} (x y : G) :
  (x ~{FreeGroupoid G}~> y) = (x ~{FreeSigned G}~> y).
Proof. reflexivity. Qed.

Definition FreeGroupoidProj_Full {G : Quiver} : Full (FreeGroupoidProj G) :=
  @QuotientProj_Full (FreeSigned G) (CongClosure (FreeGroupoidRel G))
    (CongClosure_Congruence (FreeGroupoidRel G)).

(* 相关说明。 （已译） *)

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_signed_no_cancellation {G : Quiver} {x y : G} (e : edges x y) :
  @equiv _ (@homset (FreeSigned G) x x) (sneg e ∘ spos e) id → False.
Proof.
  intro H.
  pose proof (tlist'_equiv_lengths (SignedQuiver G) x x x
                (spos e +++ sneg e) tnil eq_refl H) as Hl.
  unfold spos, sneg, tlist_singleton in Hl.
  rewrite tlist_app_length in Hl.
  simpl in Hl.
  discriminate.
Qed.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_signed_not_groupoid {G : Quiver} {x y : G} (e : edges x y) :
  IsGroupoid (FreeSigned G) → False.
Proof.
  intro Hg.
  pose proof (@is_left_inverse _ _ _ _ (Hg x y (spos e))) as Hinv.
  pose proof (tlist'_equiv_lengths (SignedQuiver G) x x x
                (spos e +++ @two_sided_inverse _ _ _ _ (Hg x y (spos e)))
                tnil eq_refl Hinv) as Hl.
  rewrite tlist_app_length in Hl.
  unfold spos, tlist_singleton in Hl.
  simpl in Hl.
  discriminate.
Qed.

(** 本节：Hence projection not faithful: it identifies two-letter word
 empty one. Fong Spivak's "equations merge, but never add",
 both halves hand. （已译） *)
Theorem fg_proj_not_faithful {G : Quiver} {x y : G} (e : edges x y) :
  Faithful (FreeGroupoidProj G) → False.
Proof.
  intro HF.
  apply (free_signed_no_cancellation e).
  apply (@fmap_inj _ _ _ HF).
  exact (fg_cancel_left e).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FGLoopQuiver : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => unit).

(** The loop, 态射 free groupoid. （已译） *)
Definition loop_gen : ttt ~{FreeGroupoid FGLoopQuiver}~> ttt :=
  @fgpos FGLoopQuiver ttt ttt tt.

Definition loop_to_Z2
  : QuiverHomomorphism FGLoopQuiver (QuiverOfCat (Deloop Bool_Xor_Grp)).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (fun _ => ttt).
  - exact (fun _ _ _ => true).
  - intros a b u v Huv; reflexivity.
Defined.

Definition loop_Z2 : FreeGroupoid FGLoopQuiver ⟶ Deloop Bool_Xor_Grp :=
  FreeGroupoidFunctor FGLoopQuiver deloop_bool_groupoid loop_to_Z2.

Theorem loop_generator_not_identity :
  loop_gen ≈ @id (FreeGroupoid FGLoopQuiver) ttt → False.
Proof.
  intro H.
  assert (Hb : @equiv _ (@homset (Deloop Bool_Xor_Grp) ttt ttt)
                 (fmap[loop_Z2] loop_gen)
                 (fmap[loop_Z2] (@id (FreeGroupoid FGLoopQuiver) ttt)))
    by (now rewrite H).
  rewrite fmap_id in Hb.
  rewrite (FreeGroupoidFunctor_gen FGLoopQuiver deloop_bool_groupoid
             loop_to_Z2 (x:=ttt) (y:=ttt) tt) in Hb.
  simpl in Hb.
  discriminate.
Qed.

(** 本节：...and it IS invertible, negative generator inverse —
 whole point passing groupoid. （已译） *)
Example loop_generator_invertible :
  ginv (FreeGroupoid_IsGroupoid FGLoopQuiver) loop_gen
    = @fgneg FGLoopQuiver ttt ttt tt.
Proof. reflexivity. Qed.
