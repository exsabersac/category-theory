(*
   本文件为测试：ProbeSubspace457。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Determination.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.SlicedInverse.Strict.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Sets.Powerset.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* The instrument *)
Fail Check probe457_absent_name.

(* * ** Structure/SlicedInverse.v: sliced 函子 Proposition 1 （已译） *)

(* CONTROL: [Sliced_fobj] and [Cosliced_fobj], restated. *)
Example p457_sliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Slice A a) :
  Sliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example p457_cosliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Coslice A a) :
  Cosliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

(* 相关说明。 （已译） *)
Definition p457_prop1@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A :=
  equalizers_from_sliced_RARI G L.

Example p457_prop1_by_adjoints@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) :
  equalizers_from_sliced_RARI G L
    = equalizers_from_sliced_right_adjoints G (fun a => rari_right (L a))
        (fun a => rari_adj (L a)) := eq_refl.

(* 相关说明。 （已译） *)
Example p457_prop1_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example p457_prop1_arrow@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g))
    = `2 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* 相关说明。 （已译） *)
Definition p457_eq_by_match@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A.
Proof.
  constructor; intros x y f g.
  destruct (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g)) as [S [s E]].
  pose (U := adj_counit_couniversal (rari_adj (L x))
               ((S; s) : @Slice X (G x))).
  exact (sliced_eq_obj G s U;
         (sliced_eq_arrow G s U; sliced_equalizer G f g s E U)).
Defined.

(* N1 *)
Fail Example p457_eq_by_match_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (p457_eq_by_match G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* CONTROL: [rari_eq_obj] restated, and [rari_over] at its Leibniz type. *)
Example p457_rari_eq_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x y : A} (f g : x ~> y) {S : X}
  (s : S ~> G x) (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s)
  (L : RightAdjointRightInverse (Sliced G x)) :
  sliced_eq_obj G s (rari_couniversal G s L) = `1 (rari_right L (S; s)) :=
  eq_refl.

Definition p457_rari_over@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x : A} {S : X} (s : S ~> G x)
  (L : RightAdjointRightInverse (Sliced G x)) :
  G (`1 (rari_right L (S; s))) = S :=
  rari_over G s L.

(* N2 *)
Fail Example p457_rari_over_refl@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x : A} {S : X} (s : S ~> G x)
  (L : RightAdjointRightInverse (Sliced G x)) :
  G (`1 (rari_right L (S; s))) = S := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p457_erase_eq :=
  @equalizer _1 One_HasEqualizers _ _
    (fmap[Erase Parallel] par_arrow_one) (fmap[Erase Parallel] par_arrow_two).

Definition p457_erase_U :=
  rari_couniversal (Erase Parallel) (`1 (`2 p457_erase_eq))
    (erase_slice_RARI ParX).

(* CONTROL: descent at [Erase Parallel], where no [Faithful] instance
   exists: [sliced_desc] takes none. *)
Definition p457_desc_at_erase :=
  @sliced_desc _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_eq)) (`2 (`2 p457_erase_eq)) p457_erase_U.

(* 相关说明。 （已译） *)
Definition p457_fork_refuted_at_erase :
  par_arrow_one
    ∘ sliced_eq_arrow (Erase Parallel) (`1 (`2 p457_erase_eq)) p457_erase_U
  ≈ par_arrow_two
    ∘ sliced_eq_arrow (Erase Parallel) (`1 (`2 p457_erase_eq)) p457_erase_U
  → False :=
  parallel_pair_unforked _.

(* N3 *)
Fail Definition p457_fork_at_erase :=
  @sliced_fork _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_eq)) (`2 (`2 p457_erase_eq)) p457_erase_U _.

(* CONTROL: the same application at [PForget], its faithfulness found by
   resolution, IS Instance/Top/Subspace.v's [PTop_HasEqualizers]. *)
Definition p457_prop1_at_pforget@{o so +| o < so +} :=
  @equalizers_from_sliced_RARI _ _ PForget@{o so} _
    (@HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
       Sets_HasPullbacks)
    subspace_RARI.

Example p457_prop1_at_pforget_is_ptop@{o so +| o < so +} :
  @eq (@HasEqualizers PTopCat@{o so}) p457_prop1_at_pforget
    PTop_HasEqualizers := eq_refl.

(* N4 *)
Fail Definition p457_prop1_at_erase :=
  @equalizers_from_sliced_RARI _ _ (Erase Parallel) _ One_HasEqualizers
    erase_slice_RARI.

(* The dual, over [Erase Parallel]'s coslices. *)
Definition p457_erase_coeq :=
  @coeq _1 One_HasCoequalizers _ _
    (fmap[Erase Parallel] par_arrow_one) (fmap[Erase Parallel] par_arrow_two).

Definition p457_erase_V :=
  lari_universal (Erase Parallel) (`1 (`2 p457_erase_coeq))
    (erase_coslice_LARI ParY).

Definition p457_codesc_at_erase :=
  @cosliced_desc _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_coeq)) (`2 (`2 p457_erase_coeq)) p457_erase_V.

Definition p457_cofork_refuted_at_erase :
  cosliced_coeq_arrow (Erase Parallel) (`1 (`2 p457_erase_coeq)) p457_erase_V
    ∘ par_arrow_one
  ≈ cosliced_coeq_arrow (Erase Parallel) (`1 (`2 p457_erase_coeq))
      p457_erase_V ∘ par_arrow_two
  → False :=
  parallel_pair_uncoforked _.

(* CONTROL: cofork 引理, at stated type, faithfulness. （已译） *)
Definition p457_cofork@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x y : A} (f g : x ~> y) {Q : X}
  (q : G y ~> Q) (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q)
  (U : UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y))
  `{GF : @Faithful A X G} :
  cosliced_coeq_arrow G q U ∘ f ≈ cosliced_coeq_arrow G q U ∘ g :=
  cosliced_cofork G f g q E U.

(* N5 *)
Fail Definition p457_cofork_at_erase :=
  @cosliced_cofork _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_coeq)) (`2 (`2 p457_erase_coeq)) p457_erase_V _.

(* CONTROL: the same application at [PForget] IS
   [PTop_HasCoequalizers]. *)
Definition p457_prop1_dual_at_pforget@{o so +| o < so +} :=
  @coequalizers_from_sliced_LARI _ _ PForget@{o so} _ Sets_HasCoequalizers
    quotient_LARI.

Example p457_prop1_dual_at_pforget_is_ptop@{o so +| o < so +} :
  @eq (@HasCoequalizers PTopCat@{o so}) p457_prop1_dual_at_pforget
    PTop_HasCoequalizers := eq_refl.

(* N6 *)
Fail Definition p457_prop1_dual_at_erase :=
  @coequalizers_from_sliced_LARI _ _ (Erase Parallel) _ One_HasCoequalizers
    erase_coslice_LARI.

(* 相关说明。 （已译） *)
Section ForkUsing.

Local Set Warnings "-undo-batch-mode".

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (U : CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x)).
Context `{GF : @Faithful A X G}.

(* CONTROL: descent under [Proof using E U]. *)
Lemma p457_desc_using {z : A} (k : z ~> x) (Hk : f ∘ k ≈ g ∘ k) :
  ∃! u : z ~> sliced_eq_obj G s U, sliced_eq_arrow G s U ∘ u ≈ k.
Proof using E U. exact (sliced_desc G f g s E U k Hk). Qed.

Lemma p457_fork_using :
  Faithful G → f ∘ sliced_eq_arrow G s U ≈ g ∘ sliced_eq_arrow G s U.
Proof using E U.
  intros _. exact (sliced_fork G f g s E U).
(* N7 *)
Fail Qed.
Restart.
  intros GF'. exact (@sliced_fork _ _ G _ _ f g _ s E U GF').
Qed.

End ForkUsing.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p457_prop1_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasEqualizers X →
     (∀ a : A, RightAdjointRightInverse (Sliced G a)) → @HasEqualizers A)
  → False :=
  prop1_needs_faithfulness.

Definition p457_prop1_dual_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasCoequalizers X →
     (∀ a : A, LeftAdjointRightInverse (Cosliced G a)) → @HasCoequalizers A)
  → False :=
  prop1_dual_needs_faithfulness.

(* 相关说明。 （已译） *)

(* CONTROL: round trip, dual's 对象 readback, restated. （已译） *)
Example p457_rari_lali_rari@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_rari (rari_lali P) = P := eq_refl.

Definition p457_prop1_dual@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) :
  @HasCoequalizers A :=
  coequalizers_from_sliced_LARI G L.

Example p457_prop1_dual_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)
    = `1 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* * ** Instance/Top/Prop.v: 范畴 forgetful 函子 （已译） *)

(* CONTROL: homs sit at points' universe, under CLOSED binder
 [@{o}]; 范畴 forgetful 函子 land ONE [Sets]. （已译） *)
Definition p457_pmor_at_o@{o} (X Y : PTop@{o}) : Type@{o} := PMor@{o} X Y.

Definition p457_ptopcat@{o so | o < so +} : Category@{so o o} :=
  PTopCat@{o so}.

Definition p457_pforget@{o so | o < so +} : PTopCat@{o so} ⟶ Sets@{o so} :=
  PForget@{o so}.

Example p457_pforget_fobj@{o so | o < so +} (X : PTop@{o}) :
  fobj[PForget@{o so}] X = pt_carrier X := eq_refl.

Example p457_pforget_fmap@{o so | o < so +} {X Y : PTop@{o}}
  (f : X ~{PTopCat@{o so}}~> Y) : fmap[PForget@{o so}] f = pmap f := eq_refl.

Definition p457_pforget_faithful@{o so | o < so +} :
  Faithful PForget@{o so} := _.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Record p457_PTopIdx@{o} := {
  p457_pi_carrier :> SetoidObject@{o o};
  p457_PIOpen : (p457_pi_carrier → Prop) → Prop;
  p457_piopen_respects (U V : p457_pi_carrier → Prop) :
    (∀ x, U x <-> V x) → p457_PIOpen U → p457_PIOpen V;
  p457_piopen_proper (U : p457_pi_carrier → Prop) :
    p457_PIOpen U → ∀ x y : p457_pi_carrier, x ≈ y → U x → U y;
  p457_piopen_union (I : Type@{o}) (U : I → p457_pi_carrier → Prop) :
    (∀ i, p457_PIOpen (U i)) → p457_PIOpen (fun x => ex (fun i => U i x));
  p457_piopen_whole : p457_PIOpen (fun _ => True);
  p457_piopen_inter (U V : p457_pi_carrier → Prop) :
    p457_PIOpen U → p457_PIOpen V → p457_PIOpen (fun x => U x /\ V x)
}.

(* 相关说明。 （已译） *)
Definition p457_idx_witness_index@{o +} (X : p457_PTopIdx@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X) (I : Type@{o})
  (V : I → S → Prop) :=
  { p : (I * (X → Prop))%type &
    (p457_PIOpen X (snd p) /\ ∀ s, V (fst p) s <-> snd p (h s)) }.

(* CONTROL: above [Set] it is a union index. *)
Definition p457_idx_union_above@{o | Set < o +} (X : p457_PTopIdx@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (I : Type@{o}) (V : I → S → Prop) :=
  p457_piopen_union X (p457_idx_witness_index X S h I V).

(* N8 *)
Fail Definition p457_idx_union_at_set (X : p457_PTopIdx@{Set})
  (S : SetoidObject@{Set Set}) (h : SetoidMorphism@{Set Set Set} S X)
  (I : Set) (V : I → S → Prop) :=
  p457_piopen_union X (p457_idx_witness_index X S h I V).

(* CONTROL: design (a) gives (b) above [Set] ... *)
Lemma p457_idx_to_family@{o | Set < o +} (X : p457_PTopIdx@{o})
  (F : (X → Prop) → Prop) :
  (∀ U, F U → p457_PIOpen X U) →
  p457_PIOpen X (fun x => ex (fun U => F U /\ U x)).
Proof.
  intro HF.
  apply (p457_piopen_respects X
           (fun x => ex (fun i : { U : X → Prop | F U } => proj1_sig i x))).
  - intro x; split.
    + intros [[U FU] u]; exists U; split; assumption.
    + intros [U [FU u]]; exists (exist _ U FU); exact u.
  - apply p457_piopen_union. intros [U FU]; exact (HF U FU).
Qed.

(* 相关说明。 （已译） *)
(* N9 *)
Fail Definition p457_idx_to_family_at_set (X : p457_PTopIdx@{Set})
  (F : (X → Prop) → Prop) :=
  p457_piopen_union X { U : X → Prop | F U }.

(* 相关说明。 （已译） *)
Definition p457_psub_at_set (X : PTop@{Set}) (S : SetoidObject@{Set Set})
  (h : SetoidMorphism@{Set Set Set} S X) : PTop@{Set} := PSub X S h.

Definition p457_union_indexed@{o i} (X : PTop@{o}) (I : Type@{i})
  (U : I → pt_carrier X → Prop) :
  (∀ k, POpen X (U k)) → POpen X (fun x => ex (fun k => U k x)) :=
  popen_union_indexed X I U.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Example p457_pdiscrete_carrier@{o} (S : SetoidObject@{o o}) :
  pt_carrier (PDiscrete S) = S := eq_refl.

Example p457_pdiscrete_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  POpen (PDiscrete S) U = pdisc_open S U := eq_refl.

Example p457_pdisc_open_body@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  pdisc_open S U = (∀ x y : S, x ≈ y → U x → U y) := eq_refl.

Definition p457_pdisc_axioms@{o} (S : SetoidObject@{o o}) :=
  conj (pdisc_open_respects S)
    (conj (pdisc_open_proper S)
       (conj (pdisc_open_union S)
          (conj (pdisc_open_whole S) (pdisc_open_inter S)))).

Definition p457_pdisc_cont@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : @PCont (PDiscrete S) Y f :=
  pdisc_cont S Y f.

Example p457_pdisc_mor_map@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : pmap (pdisc_mor S Y f) = f := eq_refl.

Example p457_pconst_at@{o} (S : SetoidObject@{o o}) (Y : PTop@{o}) (y : Y)
  (s : S) : pconst S Y y s = y := eq_refl.

(* 相关说明。 （已译） *)
Example p457_ppoint@{o} :
  pt_carrier PPoint@{o} = unit_setoid_object@{o o} := eq_refl.

Example p457_pbool@{o} :
  pt_carrier PBool@{o} = bool_setoid_object@{o o} := eq_refl.

Definition p457_pbool_points_distinct@{o} :
  @equiv _ PBool@{o} false true → False := PBool_points_distinct.

(* 相关说明。 （已译） *)

(* CONTROL: book's opens verbatim, universal properties over
 ARBITRARY spaces, Exercise 7.32's 定义, restated. （已译） *)
Example p457_psub_open@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} S X) (V : S → Prop) :
  POpen (PSub X S h) V
  = ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s)) := eq_refl.

Definition p457_psub_universal@{o +} (X : PTop@{o}) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} S X) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z (PSub X S h) g <-> @PCont Z X (setoid_morphism_compose h g) :=
  psub_universal X S h Z g.

Definition p457_pquot_universal@{o +} (X : PTop@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} X T) (Z : PTop@{o})
  (k : SetoidMorphism@{o o o} T Z) :
  @PCont (PQuot X T q) Z k <-> @PCont X Z (setoid_morphism_compose k q) :=
  pquot_universal X T q Z k.

Example p457_ex732_def@{o +} (X : PTop@{o}) (P : X → Prop)
  (A : ex732_Y X P → Prop) :
  POpen (ex732_Sub X P) A
  = ex (fun B : X → Prop =>
          POpen X B /\ ∀ y : ex732_Y X P, A y <-> B (proj1_sig y)) :=
  eq_refl.

Definition p457_ex732_part3@{o +} (X : PTop@{o}) (P : X → Prop) :
  @PCont (ex732_Sub X P) X (ex732_incl X P) :=
  ex732_part3 X P.

(* * ** Instance/Top/Subspace.v: 对象 equations （已译） *)

(* CONTROL: at explicit pair 对象 equation holds at [eq_refl],
 at variable first component does. （已译） *)
Example p457_psub_obj_pair@{o so +| o < so +} (X : PTop@{o})
  (S : SetoidObject@{o o}) (h : S ~{Sets@{o so}}~> PForget@{o so} X) :
  Sliced PForget@{o so} X (PSub_Functor X (S; h)) = (S; h) := eq_refl.

Example p457_psub_obj_carrier@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  `1 (Sliced PForget@{o so} X (PSub_Functor X c)) = `1 c := eq_refl.

(* CONTROL: at a variable it holds by [psub_obj], Leibniz. *)
Definition p457_psub_obj@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c := psub_obj X c.

(* N10 *)
Fail Example p457_psub_obj_refl@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c := eq_refl.

Example p457_pquot_obj_pair@{o so +| o < so +} (X : PTop@{o})
  (T : SetoidObject@{o o}) (q : PForget@{o so} X ~{Sets@{o so}}~> T) :
  Cosliced PForget@{o so} X (PQuot_Functor X (T; q)) = (T; q) := eq_refl.

Definition p457_pquot_obj@{o so +| o < so +} (X : PTop@{o})
  (c : @Coslice Sets@{o so} (PForget@{o so} X)) :
  Cosliced PForget@{o so} X (PQuot_Functor X c) = c := pquot_obj X c.

(* N11 *)
Fail Example p457_pquot_obj_refl@{o so +| o < so +} (X : PTop@{o})
  (c : @Coslice Sets@{o so} (PForget@{o so} X)) :
  Cosliced PForget@{o so} X (PQuot_Functor X c) = c := eq_refl.

(* The object equation closed [Qed] instead of [Defined]. *)
Lemma p457_psub_obj_opaque@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c.
Proof. destruct c; reflexivity. Qed.

(* 相关说明。 （已译） *)
Definition p457_psub_counit@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  @counit _ _ _ _ (psub_adjunction X) c ≈ id_cast (psub_obj X c) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* N12 *)
Fail Definition p457_psub_counit_opaque@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  @counit _ _ _ _ (psub_adjunction X) c ≈ id_cast (p457_psub_obj_opaque X c) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* 相关说明。 （已译） *)

(* CONTROL: subspace quotient constructions two records, at
 types #457's plan states, adjoints subspace's
 对象 equation read back. （已译） *)
Definition p457_subspace_RARI@{o so +| o < so +} :
  ∀ X : PTop@{o}, RightAdjointRightInverse (Sliced PForget@{o so} X) :=
  subspace_RARI.

Definition p457_quotient_LARI@{o so +| o < so +} :
  ∀ X : PTop@{o}, LeftAdjointRightInverse (Cosliced PForget@{o so} X) :=
  quotient_LARI.

Example p457_subspace_RARI_right@{o so +| o < so +} (X : PTop@{o}) :
  @rari_right _ _ (Sliced PForget@{o so} X) (subspace_RARI X)
    = PSub_Functor X := eq_refl.

Example p457_subspace_RARI_obj@{o so +| o < so +} (X : PTop@{o}) :
  @rari_obj _ _ (Sliced PForget@{o so} X) (subspace_RARI X) = psub_obj X :=
  eq_refl.

Example p457_quotient_LARI_left@{o so +| o < so +} (X : PTop@{o}) :
  @lari_left _ _ (Cosliced PForget@{o so} X) (quotient_LARI X)
    = PQuot_Functor X := eq_refl.

(* 相关说明。 （已译） *)
Definition p457_ptop_equalizers@{o so +| o < so +} :
  @HasEqualizers PTopCat@{o so} := PTop_HasEqualizers.

Definition p457_ptop_coequalizers@{o so +| o < so +} :
  @HasCoequalizers PTopCat@{o so} := PTop_HasCoequalizers.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p457_ptop_equalizer_obj@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = PSub x
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g)))) := eq_refl.

Example p457_ptop_equalizer_arrow@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@equalizer _ PTop_HasEqualizers x y f g))
    = psub_incl x
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g)))) := eq_refl.

Example p457_ptop_equalizer_rari@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = `1 (rari_right (subspace_RARI x)
            (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g));
             `1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal
                                     Sets Sets_Terminal Sets_HasPullbacks)
                       _ _ (fmap[PForget] f) (fmap[PForget] g))))) :=
  eq_refl.

Example p457_ptop_coequalizer_obj@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@coeq _ PTop_HasCoequalizers x y f g)
    = PQuot y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

Example p457_ptop_coequalizer_arrow@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@coeq _ PTop_HasCoequalizers x y f g))
    = pquot_proj y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p457_pbool_subspace_RARI@{o so +| o < so +} :
  RightAdjointRightInverse (Sliced PForget@{o so} PBool@{o}) :=
  PBool_subspace_RARI.

Definition p457_pbool_quotient_LARI@{o so +| o < so +} :
  LeftAdjointRightInverse (Cosliced PForget@{o so} PBool@{o}) :=
  PBool_quotient_LARI.

Example p457_pbool_subspace_RARI_right@{o so +| o < so +} :
  @rari_right _ _ (Sliced PForget@{o so} PBool@{o}) PBool_subspace_RARI
    = PSub_Functor PBool := eq_refl.

Example p457_pbool_quotient_LARI_left@{o so +| o < so +} :
  @lari_left _ _ (Cosliced PForget@{o so} PBool@{o}) PBool_quotient_LARI
    = PQuot_Functor PBool := eq_refl.

(* 相关说明。 （已译） *)
Example p457_pbool_true_map@{o} :
  pmap pbool_true@{o} = pconst bool_setoid_object PBool true := eq_refl.

Definition p457_pbool_maps_differ@{o so | o < so +} :
  pid PBool ≈[PTopCat@{o so}] pbool_true → False := pbool_maps_differ.

Example p457_ppoint_maps@{o} :
  pmap ppoint_false@{o} = pconst unit_setoid_object PBool false
  /\ pmap ppoint_true@{o} = pconst unit_setoid_object PBool true :=
  conj eq_refl eq_refl.

Definition p457_ppoint_maps_differ@{o so | o < so +} :
  ppoint_false ≈[PTopCat@{o so}] ppoint_true → False := ppoint_maps_differ.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p457_pbool_equalizer_obj@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = PSub PBool
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ setoid_morphism_id (pconst bool_setoid_object PBool true)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true)))) := eq_refl.

Example p457_pbool_equalizer_rari@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = `1 (rari_right PBool_subspace_RARI@{o so _ _}
            (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true));
             `1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal
                                     Sets Sets_Terminal Sets_HasPullbacks)
                       _ _ setoid_morphism_id
                       (pconst bool_setoid_object PBool true))))) :=
  eq_refl.

Definition p457_pbool_equalizer_points@{o so +| o < so +} (b : bool) :
  ex (fun e : pt_carrier (`1 PBool_equalizer@{o so _ _ _ _ _}) =>
        pmap (`1 (`2 PBool_equalizer@{o so _ _ _ _ _})) e = b)
  <-> b = true :=
  PBool_equalizer_points b.

(*
   本节说明 ProbeSubspace457 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example p457_pbool_coequalizer_obj@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = PQuot PBool
        (SetsCoeq (pconst unit_setoid_object PBool false)
                  (pconst unit_setoid_object PBool true))
        (sets_coeq_proj (pconst unit_setoid_object PBool false)
                        (pconst unit_setoid_object PBool true)) := eq_refl.

Example p457_pbool_coequalizer_lari@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = `1 (lari_left PBool_quotient_LARI@{o so _ _}
            (SetsCoeq (pconst unit_setoid_object PBool false)
                      (pconst unit_setoid_object PBool true);
             sets_coeq_proj (pconst unit_setoid_object PBool false)
                            (pconst unit_setoid_object PBool true)))
  := eq_refl.

Definition p457_pbool_coequalizer_points@{o so +| o < so +} (b : bool) :
  @equiv _ (`1 PBool_coequalizer@{o so _ _ _ _ _ _}) b true :=
  PBool_coequalizer_points b.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p457_tsub_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o1} :=
  tsub_open X S h V.

Definition p457_tsub_open_body@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* N13 *)
Fail Definition p457_tsub_open_at_o@{o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* 相关说明。 （已译） *)
Definition p457_tquot@{o +} (X : TopSpace@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} (top_carrier X) T) : TopSpace@{o} :=
  TQuot X T q.

(* 相关说明。 （已译） *)
Definition p457_tsub_axioms@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :=
  (tsub_open_respects@{o o1} X S h, tsub_open_proper@{o o1} X S h,
   tsub_open_union@{o o1} X S h, tsub_open_whole@{o o1} X S h,
   tsub_open_inter@{o o1} X S h).

Definition p457_tquot_package@{o +} (X : TopSpace@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} (top_carrier X) T) :
  TopSpace@{o} := {|
  top_carrier   := T;
  IsOpen        := tquot_open X T q;
  open_respects := tquot_open_respects X T q;
  open_proper   := tquot_open_proper X T q;
  open_union    := tquot_open_union X T q;
  open_whole    := tquot_open_whole X T q;
  open_inter    := tquot_open_inter X T q |}.

(* N14 *)
Fail Definition p457_tsub_package@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  TopSpace@{o} := {|
  top_carrier   := S;
  IsOpen        := tsub_open@{o o1} X S h;
  open_respects := tsub_open_respects X S h;
  open_proper   := tsub_open_proper X S h;
  open_union    := tsub_open_union X S h;
  open_whole    := tsub_open_whole X S h;
  open_inter    := tsub_open_inter X S h |}.

(* CONTROL: the universal properties over ARBITRARY spaces, restated. *)
Definition p457_tsub_universal@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  tsub_continuous@{o o1} X S h Z g
    ↔ Continuous Z X (setoid_morphism_compose h g) :=
  tsub_universal X S h Z g.

Definition p457_tquot_universal@{o +} (X : TopSpace@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} (top_carrier X) T)
  (Z : TopSpace@{o}) (k : SetoidMorphism@{o o o} T (top_carrier Z)) :
  Continuous (TQuot X T q) Z k
    ↔ Continuous X Z (setoid_morphism_compose k q) :=
  tquot_universal X T q Z k.

(* 相关说明。 （已译） *)

(* CONTROL: 对象 slice UNLIFTED [Sets] carries the
 discrete topology at points' universe; one LIFTED [Sets]
 carries it one universe up. （已译） *)
Definition p457_unlifted_slice_space@{o so +| o < so +} (X : TopSpace@{o})
  (x : @Slice Sets@{o so} (top_carrier X)) : TopSpace@{o} :=
  Discrete_Top (`1 x).

Definition p457_lifted_slice_space_h@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Slice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{h} :=
  Discrete_Top (`1 x).

(* N15 *)
Fail Definition p457_lifted_slice_space@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Slice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{o} :=
  Discrete_Top (`1 x).

(* 相关说明。 （已译） *)
Definition p457_unlifted_coslice_space@{o so +| o < so +} (X : TopSpace@{o})
  (x : @Coslice Sets@{o so} (top_carrier X)) : TopSpace@{o} :=
  Discrete_Top (`1 x).

Definition p457_lifted_coslice_space_h@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Coslice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{h} :=
  Discrete_Top (`1 x).

(* N16 *)
Fail Definition p457_lifted_coslice_space@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Coslice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{o} :=
  Discrete_Top (`1 x).

(* CONTROL: [Top_Forget] 进入 LIFTED [Sets], restated; type a
 函子 进入 [Sets] whose 对象 point setoids not
 formed. （已译） *)
Definition p457_top_forget@{o h so +| o < h, h < so +} :
  Top@{h o} ⟶ Sets@{h so} :=
  Top_Forget@{o h so}.

(* N17 *)
Fail Definition p457_top_to_point_sets@{o h +| o < h +} :=
  (Top@{h o} ⟶ Sets@{o h}).

(* CONTROL: type 函子 进入 lifted [Sets@{h so}] is
 formed; Instance/Top/Forgetful.v's own [Sets@{o so}], the
 universe [so] 对象 fresh, it not. （已译） *)
Definition p457_top_to_lifted_sets@{o h so +| o < h +} :=
  (Top@{h o} ⟶ Sets@{h so}).

(* N26 *)
Fail Definition p457_top_to_point_sets_so@{o h so +| o < h +} :=
  (Top@{h o} ⟶ Sets@{o so}).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p457_top_forget_under@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Coslice Top@{h o} X ⟶ @Coslice Sets@{h so} (Top_Forget@{o h so} X) :=
  Top_Forget_under X.

Definition p457_tquot_functor@{o h so +| o < h, o < so +} (X : TopSpace@{o}) :
  @Coslice Sets@{o so} (top_carrier X) ⟶ @Coslice Top@{h o} X :=
  TQuot_Functor X.

Example p457_tquot_adj_to_map@{o h so +| o < h, o < so +} (X : TopSpace@{o})
  (x : @Coslice Sets@{o so} (top_carrier X)) (y : @Coslice Top@{h o} X)
  (k : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  `1 (to (tquot_adj X x y) k) = continuous_map (`1 k) := eq_refl.

(* CONTROL: [Top_Forget_under X y] IS the lift of [tstrip_under X y]. *)
Example p457_forget_under_lift@{o h so +| o < h, h < so +} (X : TopSpace@{o})
  (y : @Coslice Top@{h o} X) :
  Top_Forget_under@{o h so} X y
    = (Setoid_Lift (`1 (tstrip_under X y));
       SetoidMorphism_Lift (`2 (tstrip_under X y))) := eq_refl.

(* N18 *)
Fail Definition p457_tquot_adjunction@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :=
  (TQuot_Functor@{o h so _} X ⊣ Top_Forget_under@{o h so} X).

(* The stripped object equation: Leibniz, [eq_refl] only at a pair. *)
Example p457_tquot_obj_stripped_pair@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (T : SetoidObject@{o o})
  (q : top_carrier X ~{Sets@{o so}}~> T) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X (T; q)) = (T; q) := eq_refl.

Definition p457_tquot_obj_stripped@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c :=
  tquot_obj_stripped X c.

(* N19 *)
Fail Example p457_tquot_obj_stripped_refl@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c := eq_refl.

(* The stripped object equation closed [Qed] instead of [Defined]. *)
Lemma p457_tquot_obj_stripped_opaque@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c.
Proof. destruct c; reflexivity. Qed.

(* CONTROL: transposed 恒等 [id_cast] inverse of
 [tquot_obj_stripped], tactic [tquot_unit_stripped] proved
 with. （已译） *)
Definition p457_tquot_unit@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj X c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (tquot_obj_stripped X c)) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* N25 *)
Fail Definition p457_tquot_unit_opaque@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj X c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (p457_tquot_obj_stripped_opaque X c)) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* 相关说明。 （已译） *)

(* Scout A's local encoding, rebuilt: V is open when it respects [≈] and
   each point of V MERELY has an open of X around its image whose preimage
   lies in V.  Instance/Sets/Powerset.v's [Powerset_squash] is the
   truncation. *)
Definition p457_sq_box@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (s : S) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ U (h s) ∧ (∀ t : S, U (h t) → V t))%type }.

Definition p457_sq_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  ((∀ s t : S, s ≈ t → V s → V t)
   ∧ (∀ s : S, V s → Powerset_squash@{o1} (p457_sq_box@{o o1} X S h V s)))%type.

Lemma p457_sq_map@{o1} {A B : Type@{o1}} (f : A → B) :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B.
Proof. intros a Q k; exact (a Q (fun x => k (f x))). Qed.

Lemma p457_sq_pair@{o1} {A B : Type@{o1}} :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B →
  Powerset_squash@{o1} (A * B)%type.
Proof. intros a b Q k; exact (a Q (fun x => b Q (fun y => k (x, y)))). Qed.

(* CONTROL: it IS a space at the points' universe. *)
Definition p457_sq_subspace@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  TopSpace@{o}.
Proof.
  unshelve refine {| top_carrier := S; IsOpen := p457_sq_open@{o o1} X S h |}.
  - intros U V H [Hp Hb]; split.
    + intros s t e v. apply (fst (H t)), (Hp s t e), (snd (H s)), v.
    + intros s v. apply (p457_sq_map (A := p457_sq_box X S h U s)).
      * intros [B [HB [Bs Hin]]]. exists B.
        repeat split; try assumption.
        intros t b; exact (fst (H t) (Hin t b)).
      * exact (Hb s (snd (H s) v)).
  - intros U [Hp _]; exact Hp.
  - intros I U HU; split.
    + intros s t e [i u]; exact (i; fst (HU i) s t e u).
    + intros s [i u]. apply (p457_sq_map (A := p457_sq_box X S h (U i) s)).
      * intros [B [HB [Bs Hin]]]. exists B.
        repeat split; try assumption.
        intros t b; exact (i; Hin t b).
      * exact (snd (HU i) s u).
  - split.
    + intros; exact ttt.
    + intros s _. apply Powerset_squash_intro.
      exists (fun _ => poly_unit@{o}).
      repeat split; try exact ttt; try apply open_whole.
  - intros U V [HpU HbU] [HpV HbV]; split.
    + intros s t e [u v]; exact (HpU s t e u, HpV s t e v).
    + intros s [u v].
      apply (p457_sq_map (A := (p457_sq_box X S h U s
                                * p457_sq_box X S h V s)%type)).
      * intros [[A [HA [As HinA]]] [B [HB [Bs HinB]]]].
        exists (fun x => (A x ∧ B x)%type).
        split; [apply open_inter; assumption|].
        split; [split; assumption|].
        intros t [a b]; exact (HinA t a, HinB t b).
      * apply p457_sq_pair; [exact (HbU s u) | exact (HbV s v)].
Defined.

(* CONTROL: [h] continuous out it, "only if" half the
 普遍性质 holds. （已译） *)
Lemma p457_sq_h_cont@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  Continuous (p457_sq_subspace@{o o1} X S h) X h.
Proof.
  intros U HU; split.
  - intros s t e u. exact (open_proper X U HU (h s) (h t)
                             (proper_morphism h s t e) u).
  - intros s u. apply Powerset_squash_intro.
    exists U; repeat split; try assumption.
    intros t b; exact b.
Qed.

Lemma p457_sq_only_if@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  Continuous Z (p457_sq_subspace@{o o1} X S h) g →
  Continuous Z X (setoid_morphism_compose h g).
Proof. intros Hg U HU. exact (Hg _ (p457_sq_h_cont X S h U HU)). Qed.

(* 相关说明。 （已译） *)
Lemma p457_sq_global_to_local@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) :
  (∀ s t : S, s ≈ t → V s → V t) →
  tsub_open@{o o1} X S h V → p457_sq_open@{o o1} X S h V.
Proof.
  intros Hp [U [HU HVU]]; split; [exact Hp|].
  intros s v. apply Powerset_squash_intro.
  exists U; repeat split; [exact HU | exact (fst (HVU s) v) |].
  intros t b; exact (snd (HVU t) b).
Qed.

(* CONTROL: the squashed box eliminates into a proposition. *)
Definition p457_sq_elim_prop@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V)
  (z0 : top_carrier Z) (v : V (g z0)) :=
  (snd HV (g z0) v) True.

(* N20 *)
Fail Definition p457_sq_elim_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V)
  (z0 : top_carrier Z) (v : V (g z0)) :=
  (snd HV (g z0) v) (IsOpen Z (fun z => V (g z))).

(* CONTROL: a union indexed by the points of Z. *)
Definition p457_union_by_points@{o +} (Z : TopSpace@{o}) :=
  @open_union Z (top_carrier Z).

(* N21 *)
Fail Definition p457_sq_union_by_boxes@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (z0 : top_carrier Z) :=
  @open_union Z (p457_sq_box@{o o1} X S h V (g z0)).

(* N22 *)
Fail Definition p457_sq_local_to_global@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V) (s0 : S)
  (v : V s0) :=
  (snd HV s0 v)
    { U : top_carrier X → Type@{o} &
      (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* 相关说明。 （已译） *)

(* Instance/Top/Kolmogorov.v's small-opens idea: quantifying over opens
   valued at [s < o] puts the predicate at [o] ... *)
Definition p457_small_sub_open@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  { U : top_carrier X → Type@{s} &
    (IsOpen X U ∧ (∀ s0 : S, V s0 ↔ U (h s0)))%type }.

(* 相关说明。 （已译） *)
Definition p457_small_union_at_s@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_small_sub_open@{s o} X S h V)
  (I : Type@{s}) (U : I → top_carrier X → Type@{s}) :
  top_carrier X → Type@{s} :=
  fun x => { i : I & U i x }.

(* ... but over an index at [o], the index [open_union] takes, it is not. *)
(* N23 *)
Fail Definition p457_small_union_at_o@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_small_sub_open@{s o} X S h V)
  (I : Type@{o}) (U : I → top_carrier X → Type@{s}) :
  top_carrier X → Type@{s} :=
  fun x => { i : I & U i x }.

(* A two-level record, its opens valued one universe above the points. *)
Record p457_Top2@{o o1} := {
  p457_t2_carrier :> SetoidObject@{o o};
  p457_IsOpen2 : (p457_t2_carrier → Type@{o}) → Type@{o1};
  p457_open2_respects (U V : p457_t2_carrier → Type@{o}) :
    (∀ x, U x ↔ V x) → p457_IsOpen2 U → p457_IsOpen2 V;
  p457_open2_proper (U : p457_t2_carrier → Type@{o}) :
    p457_IsOpen2 U → ∀ x y : p457_t2_carrier, x ≈ y → U x → U y;
  p457_open2_union (I : Type@{o}) (U : I → (p457_t2_carrier → Type@{o})) :
    (∀ i, p457_IsOpen2 (U i)) → p457_IsOpen2 (fun x => { i : I & U i x });
  p457_open2_whole : p457_IsOpen2 (fun _ => poly_unit@{o});
  p457_open2_inter (U V : p457_t2_carrier → Type@{o}) :
    p457_IsOpen2 U → p457_IsOpen2 V → p457_IsOpen2 (fun x => U x ∧ V x)
}.

(* CONTROL: it hosts the book's subspace predicate ... *)
Definition p457_sub2_open@{o o1 +| o < o1 +} (X : p457_Top2@{o o1})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (V : S → Type@{o}) : Type@{o1} :=
  { U : X → Type@{o} &
    (p457_IsOpen2 X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* ... and its continuity is a type one universe up ... *)
Definition p457_cont2@{o o1 +| o < o1 +} (X Y : p457_Top2@{o o1})
  (f : SetoidMorphism@{o o o} X Y) : Type@{o1} :=
  ∀ U : Y → Type@{o}, p457_IsOpen2 Y U → p457_IsOpen2 X (fun x => U (f x)).

(* ... not at the points' universe. *)
(* N24 *)
Fail Definition p457_cont2_at_o@{o o1 +| o < o1 +} (X Y : p457_Top2@{o o1})
  (f : SetoidMorphism@{o o o} X Y) : Type@{o} :=
  ∀ U : Y → Type@{o}, p457_IsOpen2 Y U → p457_IsOpen2 X (fun x => U (f x)).

(** ** Guard block *)

(* Structure/SlicedInverse.v: 73 names, 19 obligations *)
Check @Sliced.
Check @Cosliced.
Check @Sliced_fobj.
Check @Sliced_fmap.
Check @Cosliced_fobj.
Check @Cosliced_fmap.
Check @rari_right.
Check @rari_adj.
Check @rari_obj.
Check @rari_counit.
Check @adj_unit_universal_op.
Check @adj_unit_universal_op_obj.
Check @adj_unit_universal_op_arrow.
Check @sliced_eq_obj.
Check @sliced_eq_arrow.
Check @sliced_fork.
Check @sliced_desc.
Check @sliced_equalizer.
Check @cosliced_coeq_obj.
Check @cosliced_coeq_arrow.
Check @cosliced_cofork.
Check @cosliced_desc.
Check @cosliced_coequalizer.
Check @equalizers_from_sliced_right_adjoints.
Check @equalizers_from_sliced_RARI.
Check @equalizers_from_sliced_RARI_obj.
Check @equalizers_from_sliced_RARI_arrow.
Check @coequalizers_from_sliced_left_adjoints.
Check @coequalizers_from_sliced_left_adjoints_obj.
Check @coequalizers_from_sliced_left_adjoints_arrow.
Check @slice_id_cast_1.
Check @IsEqualizer_transport.
Check @rari_couniversal.
Check @rari_eq_obj.
Check @rari_eq_arrow.
Check @rari_over.
Check @rari_arrow_over.
Check @rari_preserves.
Check @equalizers_from_sliced_RARI_preserved.
Check @par_arrow_one.
Check @par_arrow_two.
Check @parallel_pair_unforked.
Check @Parallel_no_equalizers.
Check @Erase_Parallel_not_faithful.
Check @One_HasEqualizers.
Check @slice_one_hom_eq.
Check @erase_slice_right.
Check @erase_slice_hom_iso.
Check @erase_slice_adj.
Check @erase_slice_RARI.
Check @sliced_RARI_without_faithfulness.
Check @prop1_needs_faithfulness.
Check @RightAdjointRightInverse.
Check @Build_RightAdjointRightInverse.
Check @SlicedInverse.Sliced_obligation_1.
Check @SlicedInverse.Sliced_obligation_2.
Check @SlicedInverse.Sliced_obligation_3.
Check @SlicedInverse.Sliced_obligation_4.
Check @SlicedInverse.Cosliced_obligation_1.
Check @SlicedInverse.Cosliced_obligation_2.
Check @SlicedInverse.Cosliced_obligation_3.
Check @SlicedInverse.Cosliced_obligation_4.
Check @SlicedInverse.One_HasEqualizers_obligation_1.
Check @SlicedInverse.One_HasEqualizers_obligation_2.
Check @SlicedInverse.erase_slice_right_obligation_1.
Check @SlicedInverse.erase_slice_right_obligation_2.
Check @SlicedInverse.erase_slice_right_obligation_3.
Check @SlicedInverse.erase_slice_hom_iso_obligation_1.
Check @SlicedInverse.erase_slice_hom_iso_obligation_2.
Check @SlicedInverse.erase_slice_hom_iso_obligation_3.
Check @SlicedInverse.erase_slice_hom_iso_obligation_4.
Check @SlicedInverse.erase_slice_hom_iso_obligation_5.
Check @SlicedInverse.erase_slice_hom_iso_obligation_6.

(* Structure/SlicedInverse/Strict.v: 39 names, 11 obligations *)
Check @rari_lali.
Check @lali_rari.
Check @rari_lali_left.
Check @lali_rari_right.
Check @rari_lali_rari.
Check @lali_rari_lali.
Check @coequalizers_from_sliced_LARI.
Check @coequalizers_from_sliced_LARI_obj.
Check @coequalizers_from_sliced_LARI_arrow.
Check @coslice_id_cast_1.
Check @IsCoequalizer_transport.
Check @lari_universal.
Check @lari_coeq_obj.
Check @lari_coeq_arrow.
Check @lari_under.
Check @lari_arrow_under.
Check @lari_preserves.
Check @coequalizers_from_sliced_LARI_preserved.
Check @parallel_pair_uncoforked.
Check @Parallel_no_coequalizers.
Check @One_HasCoequalizers.
Check @coslice_one_hom_eq.
Check @erase_coslice_left.
Check @erase_coslice_hom_iso.
Check @erase_coslice_adj.
Check @erase_coslice_LARI.
Check @cosliced_LARI_without_faithfulness.
Check @prop1_dual_needs_faithfulness.
Check @Strict.One_HasCoequalizers_obligation_1.
Check @Strict.One_HasCoequalizers_obligation_2.
Check @Strict.erase_coslice_left_obligation_1.
Check @Strict.erase_coslice_left_obligation_2.
Check @Strict.erase_coslice_left_obligation_3.
Check @Strict.erase_coslice_hom_iso_obligation_1.
Check @Strict.erase_coslice_hom_iso_obligation_2.
Check @Strict.erase_coslice_hom_iso_obligation_3.
Check @Strict.erase_coslice_hom_iso_obligation_4.
Check @Strict.erase_coslice_hom_iso_obligation_5.
Check @Strict.erase_coslice_hom_iso_obligation_6.

(* Instance/Top/Prop.v: 51 names, 8 obligations *)
Check @pt_carrier.
Check @POpen.
Check @popen_respects.
Check @popen_proper.
Check @popen_union.
Check @popen_whole.
Check @popen_inter.
Check @popen_union_indexed.
Check @popen_const.
Check @popen_empty.
Check @PCont.
Check @pcont_respects.
Check @pmap.
Check @pcont.
Check @PMor_Setoid.
Check @pid.
Check @pcompose.
Check @pcompose_respects.
Check @PTopCat.
Check @PForget.
Check @PForget_fobj.
Check @PForget_fmap.
Check @PForget_Faithful.
Check @PTop.
Check @Build_PTop.
Check @PMor.
Check @Build_PMor.
Check @pdisc_open.
Check @pdisc_open_respects.
Check @pdisc_open_proper.
Check @pdisc_open_union.
Check @pdisc_open_whole.
Check @pdisc_open_inter.
Check @PDiscrete.
Check @PDiscrete_carrier.
Check @PDiscrete_open.
Check @pdisc_cont.
Check @pdisc_mor.
Check @pdisc_mor_map.
Check @pconst.
Check @PPoint.
Check @PBool.
Check @PBool_points_distinct.
Check @Top.Prop.PMor_Setoid_obligation_1.
Check @Top.Prop.PTopCat_obligation_1.
Check @Top.Prop.PTopCat_obligation_2.
Check @Top.Prop.PTopCat_obligation_3.
Check @Top.Prop.PTopCat_obligation_4.
Check @Top.Prop.PForget_obligation_1.
Check @Top.Prop.PForget_obligation_2.
Check @Top.Prop.PForget_obligation_3.

(* Instance/Top/Subspace.v: 111 names, 26 obligations *)
Check @psub_open.
Check @psub_open_respects.
Check @psub_open_proper.
Check @psub_open_union.
Check @psub_open_whole.
Check @psub_open_inter.
Check @PSub.
Check @PSub_carrier.
Check @PSub_open.
Check @psub_incl_cont.
Check @psub_incl.
Check @psub_universal.
Check @psub_lift.
Check @psub_lift_map.
Check @psub_lift_comm.
Check @ex732_Y.
Check @ex732_incl.
Check @ex732_Sub.
Check @ex732_def.
Check @ex732_part1.
Check @ex732_part2.
Check @ex732_part3.
Check @ex732_incl_mor.
Check @pquot_open.
Check @pquot_open_respects.
Check @pquot_open_proper.
Check @pquot_open_union.
Check @pquot_open_whole.
Check @pquot_open_inter.
Check @PQuot.
Check @PQuot_carrier.
Check @PQuot_open.
Check @pquot_proj_cont.
Check @pquot_proj.
Check @pquot_universal.
Check @pquot_desc.
Check @pquot_desc_map.
Check @pquot_desc_comm.
Check @PForget_over.
Check @PForget_under.
Check @PForget_over_Sliced.
Check @PForget_under_Cosliced.
Check @PSub_Functor.
Check @PSub_Functor_obj.
Check @psub_adj_iso.
Check @psub_adj_to_map.
Check @psub_adj_from_map.
Check @psub_adjunction.
Check @psub_obj.
Check @psub_obj_pair.
Check @psub_counit.
Check @PQuot_Functor.
Check @PQuot_Functor_obj.
Check @pquot_adj_iso.
Check @pquot_adj_to_map.
Check @pquot_adj_from_map.
Check @pquot_adjunction.
Check @pquot_obj.
Check @pquot_obj_pair.
Check @pquot_unit.
Check @subspace_RARI.
Check @subspace_RARI_right.
Check @quotient_LARI.
Check @quotient_LARI_left.
Check @PTop_HasEqualizers.
Check @PTop_equalizer_obj.
Check @PTop_equalizer_arrow.
Check @PTop_HasCoequalizers.
Check @PTop_coequalizer_obj.
Check @PTop_coequalizer_arrow.
Check @PBool_subspace_RARI.
Check @PBool_quotient_LARI.
Check @pbool_true.
Check @pbool_maps_differ.
Check @PBool_equalizer.
Check @PBool_equalizer_obj.
Check @PBool_equalizer_rari.
Check @PBool_equalizer_points.
Check @ppoint_false.
Check @ppoint_true.
Check @ppoint_maps_differ.
Check @PBool_coequalizer.
Check @PBool_coequalizer_obj.
Check @PBool_coequalizer_lari.
Check @PBool_coequalizer_points.
Check @Subspace.ex732_Y_obligation_1.
Check @Subspace.ex732_incl_obligation_1.
Check @Subspace.PSub_Functor_obligation_1.
Check @Subspace.PSub_Functor_obligation_2.
Check @Subspace.PSub_Functor_obligation_3.
Check @Subspace.PSub_Functor_obligation_4.
Check @Subspace.PSub_Functor_obligation_5.
Check @Subspace.psub_adj_iso_obligation_1.
Check @Subspace.psub_adj_iso_obligation_2.
Check @Subspace.psub_adj_iso_obligation_3.
Check @Subspace.psub_adj_iso_obligation_4.
Check @Subspace.psub_adj_iso_obligation_5.
Check @Subspace.psub_adj_iso_obligation_6.
Check @Subspace.psub_adj_iso_obligation_7.
Check @Subspace.PQuot_Functor_obligation_1.
Check @Subspace.PQuot_Functor_obligation_2.
Check @Subspace.PQuot_Functor_obligation_3.
Check @Subspace.PQuot_Functor_obligation_4.
Check @Subspace.PQuot_Functor_obligation_5.
Check @Subspace.pquot_adj_iso_obligation_1.
Check @Subspace.pquot_adj_iso_obligation_2.
Check @Subspace.pquot_adj_iso_obligation_3.
Check @Subspace.pquot_adj_iso_obligation_4.
Check @Subspace.pquot_adj_iso_obligation_5.
Check @Subspace.pquot_adj_iso_obligation_6.
Check @Subspace.pquot_adj_iso_obligation_7.

(* Instance/Top/Subspace/TypeValued.v: 69 names, 26 obligations *)
Check @tcont_respects.
Check @tquot_open.
Check @tquot_open_respects.
Check @tquot_open_proper.
Check @tquot_open_union.
Check @tquot_open_whole.
Check @tquot_open_inter.
Check @TQuot.
Check @TQuot_carrier.
Check @TQuot_open.
Check @tquot_proj_cont.
Check @tquot_proj.
Check @tquot_universal.
Check @tquot_desc.
Check @tquot_desc_map.
Check @tsub_open.
Check @tsub_open_respects.
Check @tsub_open_proper.
Check @tsub_open_union.
Check @tsub_open_whole.
Check @tsub_open_inter.
Check @tsub_preimage_open.
Check @tsub_continuous.
Check @tsub_universal.
Check @tsub_lift.
Check @Top_Forget_over.
Check @Top_Forget_under.
Check @TQuot_Functor.
Check @tstrip_under.
Check @tstrip_under_lift.
Check @tstrip_under_map.
Check @tquot_adj.
Check @tquot_adj_to_map.
Check @tquot_adj_from_map.
Check @tquot_adj_nat_l.
Check @tquot_adj_nat_r.
Check @tquot_obj_stripped.
Check @tquot_obj_stripped_pair.
Check @tquot_unit_stripped.
Check @tsub_hom.
Check @tsub_hom_setoid.
Check @tsub_adj.
Check @tsub_adj_to_map.
Check @TypeValued.Top_Forget_over_obligation_1.
Check @TypeValued.Top_Forget_over_obligation_2.
Check @TypeValued.Top_Forget_over_obligation_3.
Check @TypeValued.Top_Forget_over_obligation_4.
Check @TypeValued.Top_Forget_under_obligation_1.
Check @TypeValued.Top_Forget_under_obligation_2.
Check @TypeValued.Top_Forget_under_obligation_3.
Check @TypeValued.Top_Forget_under_obligation_4.
Check @TypeValued.TQuot_Functor_obligation_1.
Check @TypeValued.TQuot_Functor_obligation_2.
Check @TypeValued.TQuot_Functor_obligation_3.
Check @TypeValued.TQuot_Functor_obligation_4.
Check @TypeValued.TQuot_Functor_obligation_5.
Check @TypeValued.tquot_adj_obligation_1.
Check @TypeValued.tquot_adj_obligation_2.
Check @TypeValued.tquot_adj_obligation_3.
Check @TypeValued.tquot_adj_obligation_4.
Check @TypeValued.tquot_adj_obligation_5.
Check @TypeValued.tsub_hom_setoid_obligation_1.
Check @TypeValued.tsub_adj_obligation_1.
Check @TypeValued.tsub_adj_obligation_2.
Check @TypeValued.tsub_adj_obligation_3.
Check @TypeValued.tsub_adj_obligation_4.
Check @TypeValued.tsub_adj_obligation_5.
Check @TypeValued.tsub_adj_obligation_6.
Check @TypeValued.tsub_adj_obligation_7.
