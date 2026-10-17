Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Determination.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.

(*
    nLab: https://ncatlab.org/nlab/show/topological+concrete+category
    nLab: https://ncatlab.org/nlab/show/subspace+topology
    nLab: https://ncatlab.org/nlab/show/quotient+space
    nLab: https://ncatlab.org/nlab/show/over+category
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    Book: Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
    Book: Adamek, Herrlich and Strecker, "Abstract and Concrete

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** The sliced 函子 [G/a] [a/G] （已译） *)

(* Mac Lane's G↓a : (A↓a) ⟶ (X↓Ga), on this library's [Slice] encoding:
   an object (d; h : d ~> a) goes to (G d; G h), an arrow m to G m. *)
Program Definition Sliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Slice A a ⟶ @Slice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

(* 相关说明。 （已译） *)
Program Definition Cosliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Coslice A a ⟶ @Coslice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

Example Sliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Slice A a) :
  Sliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Sliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Slice A a)
  (m : h ~> k) : `1 (fmap[Sliced G a] m) = fmap[G] (`1 m) := eq_refl.

Example Cosliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Coslice A a) :
  Cosliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Cosliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Coslice A a)
  (m : h ~> k) : `1 (fmap[Cosliced G a] m) = fmap[G] (`1 m) := eq_refl.

(** ** Right-adjoint-right-inverses *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RightAdjointRightInverse@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} (S : A ⟶ C) : Type := {
  rari_right : C ⟶ A;
  rari_adj : S ⊣ rari_right;
  rari_obj (c : C) : S (rari_right c) = c;
  rari_counit (c : C) :
    @counit C A S rari_right rari_adj c ≈ id_cast (rari_obj c)
}.

Arguments rari_right {A C S} _.
Arguments rari_adj {A C S} _.
Arguments rari_obj {A C S} _ _.
Arguments rari_counit {A C S} _ _.

(* * ** The unit 伴随 泛箭头, duality （已译） *)

(* Adjunction/Determination.v's [adj_counit_couniversal] read at the
 opposite 伴随. Both readbacks below [eq_refl]. （已译） *)
Definition adj_unit_universal_op@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (c : D) : UniversalArrow c U :=
  adj_counit_couniversal (Opposite_Adjunction F U A) c.

Example adj_unit_universal_op_obj@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow_obj _ _ c U (adj_unit_universal_op A c) = F c := eq_refl.

Example adj_unit_universal_op_arrow@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow _ _ c U (adj_unit_universal_op A c) = @unit _ _ F U A c := eq_refl.

(** ** Proposition 1, pointwise *)

(*
   本节说明伴随、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section SlicedEqualizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (U : CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x)).
Context `{GF : @Faithful A X G}.

(* Mac Lane's L s and L t : L s ~> x. *)
Definition sliced_eq_obj : A := `1 (coarrow_obj U).

Definition sliced_eq_arrow : sliced_eq_obj ~> x := `2 (coarrow_obj U).

(* 相关说明。 （已译） *)
Lemma sliced_fork : f ∘ sliced_eq_arrow ≈ g ∘ sliced_eq_arrow.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (coarrow U)) as He; simpl in He.
  unfold sliced_eq_arrow.
  rewrite <- He.
  rewrite !comp_assoc.
  rewrite (fork_eq E).
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition sliced_desc {z : A} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  ∃! u : z ~> sliced_eq_obj, sliced_eq_arrow ∘ u ≈ h.
Proof using E U.
  assert (HGh : fmap[G] f ∘ fmap[G] h ≈ fmap[G] g ∘ fmap[G] h).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := eq_desc E (fmap[G] h) HGh).
  pose (k := (unique_obj D; unique_property D)
             : @hom (@Slice X (G x)) (Sliced G x (z; h)) (S; s)).
  pose (D' := ump_couniversal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - exact (`2 (unique_obj D')).
  - intros v Hv.
    pose (vv := (v; Hv) : @hom (@Slice A x) (z; h) (coarrow_obj U)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite comp_assoc.
    rewrite (`2 (coarrow U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition sliced_equalizer :
  IsEqualizer f g sliced_eq_obj sliced_eq_arrow :=
  {| fork_eq := sliced_fork; eq_desc := @sliced_desc |}.

End SlicedEqualizer.

Section CoslicedCoequalizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (U : UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y)).
Context `{GF : @Faithful A X G}.

Definition cosliced_coeq_obj : A := `1 (@arrow_obj _ _ _ _ U).

Definition cosliced_coeq_arrow : y ~> cosliced_coeq_obj :=
  `2 (@arrow_obj _ _ _ _ U).

Lemma cosliced_cofork :
  cosliced_coeq_arrow ∘ f ≈ cosliced_coeq_arrow ∘ g.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (@arrow _ _ _ _ U)) as He; simpl in He.
  unfold cosliced_coeq_arrow.
  rewrite He.
  rewrite <- !comp_assoc.
  rewrite (cofork E).
  reflexivity.
Qed.

Definition cosliced_desc {z : A} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : cosliced_coeq_obj ~> z, u ∘ cosliced_coeq_arrow ≈ h.
Proof using E U.
  assert (HGh : fmap[G] h ∘ fmap[G] f ≈ fmap[G] h ∘ fmap[G] g).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := coeq_desc E (fmap[G] h) HGh).
  assert (Hk : fmap[G] h ≈ unique_obj D ∘ q)
    by (symmetry; exact (unique_property D)).
  pose (k := (unique_obj D; Hk)
             : @hom (@Coslice X (G y)) (Q; q) (Cosliced G y (z; h))).
  pose (D' := ump_universal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - symmetry; exact (`2 (unique_obj D')).
  - intros v Hv.
    assert (Hv' : h ≈ v ∘ cosliced_coeq_arrow) by (symmetry; exact Hv).
    pose (vv := (v; Hv')
                : @hom (@Coslice A y) (@arrow_obj _ _ _ _ U) (z; h)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite <- comp_assoc.
    rewrite <- (`2 (@arrow _ _ _ _ U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition cosliced_coequalizer :
  IsCoequalizer f g cosliced_coeq_obj cosliced_coeq_arrow :=
  {| cofork := cosliced_cofork; coeq_desc := @cosliced_desc |}.

End CoslicedCoequalizer.

(* 相关说明。 （已译） *)

(* The downstairs equalizer read out projections, not [match],
 so 对象 arrow readbacks below hold at [eq_refl]. （已译） *)
Definition equalizers_from_sliced_right_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (R : ∀ a : A, @Slice X (G a) ⟶ @Slice A a)
  (adjR : ∀ a : A, Sliced G a ⊣ R a) : @HasEqualizers A :=
  {| equalizer := fun x y f g =>
       let S := `1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let s := `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_counit_couniversal (adjR x) ((S; s) : @Slice X (G x)) in
       (sliced_eq_obj G s U;
        (sliced_eq_arrow G s U; sliced_equalizer G f g s E U)) |}.

(* 相关说明。 （已译） *)
Definition equalizers_from_sliced_RARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A :=
  equalizers_from_sliced_right_adjoints G
    (fun a => rari_right (L a)) (fun a => rari_adj (L a)).

(* 相关说明。 （已译） *)
Example equalizers_from_sliced_RARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example equalizers_from_sliced_RARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g))
    = `2 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition coequalizers_from_sliced_left_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) : @HasCoequalizers A :=
  {| coeq := fun x y f g =>
       let Q := `1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let q := `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_unit_universal_op (adjL y) ((Q; q) : @Coslice X (G y)) in
       (cosliced_coeq_obj G q U;
        (cosliced_coeq_arrow G q U; cosliced_coequalizer G f g q E U)) |}.

Example coequalizers_from_sliced_left_adjoints_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g)
    = `1 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_left_adjoints_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g))
    = `2 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* 相关说明。 （已译） *)

Lemma slice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Slice C u} (e : p = q) :
  `1 (@id_cast (@Slice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* An equalizer moved along a Leibniz equation of apexes. *)
Definition IsEqualizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : q ~> a} {e' : q' ~> a}
  (p : q' = q) :
  e' ≈ e ∘ id_cast p → IsEqualizer f g q e → IsEqualizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_right in He.
  unshelve econstructor.
  - rewrite He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (eq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section RARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (L : RightAdjointRightInverse (Sliced G x)).

Definition rari_couniversal :
  CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x) :=
  adj_counit_couniversal (rari_adj L) (S; s).

Example rari_eq_obj :
  sliced_eq_obj G s rari_couniversal = `1 (rari_right L (S; s)) := eq_refl.

Example rari_eq_arrow :
  sliced_eq_arrow G s rari_couniversal = `2 (rari_right L (S; s)) := eq_refl.

(* The lifted 对象 sits over S: Leibniz, field [rari_obj]. （已译） *)
Definition rari_over : G (`1 (rari_right L (S; s))) = S :=
  f_equal (@projT1 _ _) (rari_obj L (S; s)).

Lemma rari_arrow_over :
  fmap[G] (`2 (rari_right L (S; s))) ≈ s ∘ id_cast rari_over.
Proof using Type.
  pose proof (`2 (@counit _ _ _ _ (rari_adj L) (S; s))) as H; simpl in H.
  rewrite <- H.
  apply compose_respects; [reflexivity|].
  transitivity (`1 (@id_cast (@Slice X (G x)) _ _ (rari_obj L (S; s)))).
  - exact (rari_counit L (S; s)).
  - rewrite (slice_id_cast_1 (rari_obj L (S; s))).
    reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition rari_preserves :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (rari_right L (S; s)))) (fmap[G] (`2 (rari_right L (S; s)))) :=
  IsEqualizer_transport rari_over rari_arrow_over E.

End RARIPreserves.

(* 相关说明。 （已译） *)
Definition equalizers_from_sliced_RARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L)
                         x y f g)))) :=
  rari_preserves G f g _ (`2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L x).

(* 相关说明。 （已译） *)

(* [Parallel]'s two arrows have no fork at all, so [Parallel] has no
   equalizers; its erasure to [_1] is not faithful; and every other
   hypothesis of Proposition 1 holds there. *)
Definition par_arrow_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_arrow_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Lemma parallel_pair_unforked {q : Parallel} (e : q ~> ParX) :
  par_arrow_one ∘ e ≈ par_arrow_two ∘ e → False.
Proof.
  destruct q, e as [b h].
  - inversion h; subst. simpl. discriminate.
  - destruct (ParHom_Y_X_absurd _ h).
Qed.

Definition Parallel_no_equalizers : @HasEqualizers Parallel → False :=
  fun H =>
    parallel_pair_unforked
      (`1 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))
      (fork_eq
         (`2 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))).

Lemma Erase_Parallel_not_faithful : Faithful (Erase Parallel) → False.
Proof.
  intros [inj].
  pose proof (inj _ _ par_arrow_one par_arrow_two eq_refl) as H.
  discriminate H.
Qed.

(* Annotated: unannotated, this witness minimizes its hom level to [Set]. *)
Program Definition One_HasEqualizers@{o h} : @HasEqualizers _1@{o h h} := {|
  equalizer := fun x y f g => (x; (id; {| fork_eq := _; eq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma slice_one_hom_eq@{o h +} (u : _1@{o h h}) (x y : @Slice _1@{o h h} u)
  (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseSlice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(* The 右伴随 [Sliced B a] 常值 at 终对象
 (a; id) slice over [a]. （已译） *)
Program Definition erase_slice_right : @Slice _1 (B a) ⟶ @Slice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_slice_hom_iso (h : @Slice Parallel a)
  (c : @Slice _1 (B a)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice _1 (B a)) (Sliced B a h) c;
       is_setoid := @homset (@Slice _1 (B a)) (Sliced B a h) c |}
    {| carrier := @hom (@Slice Parallel a) h (erase_slice_right c);
       is_setoid := @homset (@Slice Parallel a) h (erase_slice_right c) |} := {|
  to := {| morphism := fun _ => (`2 h; _) |};
  from := {| morphism := fun _ => (ttt; _) |}
|}.
Next Obligation. intros; apply id_left. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; destruct c as [[] []]; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite <- Hv; apply id_left.
Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.

Definition erase_slice_adj : Sliced B a ⊣ erase_slice_right.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ (Sliced B a) erase_slice_right erase_slice_hom_iso).
  - intros x y z f g; simpl.
    symmetry; exact (`2 g).
  - intros x y z f g.
    change (`2 x ≈ id ∘ `2 x).
    symmetry; apply id_left.
Defined.

Definition erase_slice_RARI : RightAdjointRightInverse (Sliced B a).
Proof.
  unshelve refine {| rari_right := erase_slice_right;
                     rari_adj := erase_slice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply slice_one_hom_eq.
Defined.

End EraseSlice.

Definition sliced_RARI_without_faithfulness :
  (∀ a : Parallel, RightAdjointRightInverse (Sliced (Erase Parallel) a))
  * @HasEqualizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasEqualizers Parallel → False) :=
  (erase_slice_RARI, One_HasEqualizers, Erase_Parallel_not_faithful,
   Parallel_no_equalizers).

(* Proposition 1 faithfulness 假设 deleted false. （已译） *)
Definition prop1_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasEqualizers X →
     (∀ a : A, RightAdjointRightInverse (Sliced G a)) → @HasEqualizers A)
  → False :=
  fun P => Parallel_no_equalizers
             (P Parallel _1 (Erase Parallel) One_HasEqualizers
                erase_slice_RARI).
