Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Projective injective 对象 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/projective+object

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Projective {C : Category} (p : C) := {
  projective_lift {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
    ∃ h : p ~> b, g ∘ h ≈ f
}.

Definition proj_lift {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) : p ~> b :=
  `1 (projective_lift g He f).

Definition proj_lift_comm {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
  g ∘ proj_lift g He f ≈ f :=
  `2 (projective_lift g He f).

Notation "'Injective' C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.
Notation "@Injective C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.

Definition injective_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  ∃ h : b ~> q, h ∘ m ≈ f :=
  @projective_lift (C^op) q Q b a m (op_Epic_of_Monic m Hm) f.

Definition inj_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) : b ~> q :=
  `1 (injective_extend m Hm f).

Definition inj_extend_comm {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  inj_extend m Hm f ∘ m ≈ f :=
  `2 (injective_extend m Hm f).

Example inj_is_op_proj {C : Category} (q : C) :
  @Injective C q = @Projective (C^op) q := eq_refl.

Example inj_stmt_readback {C : Category} {q a b : C} (m : a ~> b) (f : a ~> q) :
  (∃ h : b ~{C}~> q, h ∘[C] m ≈ f)
    = (∃ h : q ~{C^op}~> b, m ∘[C^op] h ≈ f) := eq_refl.

(* * ** The hom-函子 characterization （已译） *)

Example hom_fmap_is_postcomp {C : Category} (p : C) {b c : C} (g : b ~> c)
  (h : p ~> b) : fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

(* 相关说明。 （已译） *)
Example proj_is_hom_surjectivity {C : Category} (p : C) {b c : C}
  (g : b ~> c) :
  (∀ f : p ~> c, ∃ h : p ~> b, fmap[[Hom p ,─]] g h ≈ f)
    = (∀ f : p ~> c, ∃ h : p ~> b, g ∘ h ≈ f) := eq_refl.

Definition projective_hom_surjective {C : Category} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g) :
  surjective (fmap[[Hom p ,─]] g) :=
  {| surj := fun f => @projective_lift C p P b c g He f |}.

Theorem projective_hom_epic {C : Category} {p : C} (P : @Projective C p)
  {b c : C} (g : b ~> c) (He : Epic g) :
  @Epic Sets _ _ (fmap[[Hom p ,─]] g).
Proof.
  apply surjective_implies_epic.
  intro f.
  exact (@projective_lift C p P b c g He f).
Defined.

Theorem hom_epic_projective {C : Category} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :
  @Projective C p.
Proof.
  construct.
  exact (epic_implies_surjective (fmap[[Hom p ,─]] g) (H b c g He) f).
Defined.

Definition projective_iff_hom_preserves_epi {C : Category} (p : C) :
  @Projective C p
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :=
  (fun P b c g He => @projective_hom_epic C p P b c g He,
   @hom_epic_projective C p).

(* The dual, at C^op: [Hom ─,q] over C IS [Hom q,─] over C^op, definitionally. *)
Example cohom_is_op_hom {C : Category} (q : C) :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Definition injective_cohom_epic {C : Category} {q : C} (Q : @Injective C q)
  {a b : C} (m : a ~> b) (Hm : Monic m) :
  @Epic Sets _ _ (fmap[[Hom ─, q]] m) :=
  @projective_hom_epic (C^op) q Q b a m (op_Epic_of_Monic m Hm).

Definition cohom_epic_injective {C : Category} (q : C)
  (H : ∀ (a b : C) (m : a ~> b), Monic m → @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :
  @Injective C q :=
  @hom_epic_projective (C^op) q
    (fun b a m Hm => H a b m (@Monic_of_op_Epic C a b m Hm)).

Definition injective_iff_cohom_preserves_mono {C : Category} (q : C) :
  @Injective C q
    ↔ (∀ (a b : C) (m : a ~> b), Monic m →
         @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :=
  (fun Q a b m Hm => @injective_cohom_epic C q Q a b m Hm,
   @cohom_epic_injective C q).

(* 相关说明。 （已译） *)

Definition ortho_lift_exists {C : Category} {a b x y : C}
  (e : a ~> b) (m : x ~> y) (O : Orthogonal e m)
  {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
  ∃ d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v) :=
  (unique_obj (ortho_lift comm); unique_property (ortho_lift comm)).

Definition ortho_zero_Projective {C : Category} `{I : @Initial C} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → Orthogonal (zero (x:=p)) g) :
  @Projective C p.
Proof.
  construct.
  destruct (ortho_lift_exists _ _ (H b c g He) (u:=zero) (v:=f)
              (ltac:(apply zero_unique))) as [d [_ Hd]].
  exists d; exact Hd.
Defined.

Definition Projective_ortho_weak {C : Category} `{I : @Initial C} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g)
  (u : @initial_obj C I ~> b) (v : p ~> c) (comm : g ∘ u ≈ v ∘ zero) :
  ∃ d : p ~> b, (d ∘ zero ≈ u) ∧ (g ∘ d ≈ v).
Proof.
  destruct (@projective_lift C p P b c g He v) as [d Hd].
  exists d; split; [ apply zero_unique | exact Hd ].
Defined.

(** ** Closure facts *)

Definition Retraction_Projective {C : Category} {p q : C} (r : p ~> q)
  (R : Retraction r) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ r)) as [h Hh].
  exists (h ∘ retract).
  rewrite comp_assoc, Hh, <- comp_assoc, retract_comp; cat.
Defined.

Definition Section_Projective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ section)) as [h Hh].
  exists (h ∘ s).
  rewrite comp_assoc, Hh, <- comp_assoc, section_comp; cat.
Defined.

Definition Coprod_Projective {C : Category} `{O : @Cocartesian C} {p q : C}
  (P : @Projective C p) (Q : @Projective C q) :
  @Projective C (@Coprod C O p q).
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ inl)) as [h1 H1].
  destruct (@projective_lift C q Q b c g He (f ∘ inr)) as [h2 H2].
  exists (h1 ▽ h2).
  rewrite <- merge_comp, H1, H2, merge_comp, merge_inl_inr; cat.
Defined.

Definition IndexedCoprod_Projective {C : Category} {A : Type} (fam : A → C)
  (s : C) (inj : ∀ a : A, fam a ~> s) (H : IsIndexedCoproduct fam s inj)
  (P : ∀ a : A, @Projective C (fam a)) : @Projective C s.
Proof.
  construct.
  pose (lifts := fun a : A =>
          @projective_lift C (fam a) (P a) b c g He (f ∘ inj a)).
  pose (D := @icoprod_desc C A fam s inj H b (fun a => `1 (lifts a))).
  pose (E := @icoprod_desc C A fam s inj H c (fun a => f ∘ inj a)).
  exists (unique_obj D).
  transitivity (unique_obj E).
  - symmetry; apply (uniqueness E).
    intro a.
    rewrite <- comp_assoc, (unique_property D a).
    exact (`2 (lifts a)).
  - apply (uniqueness E).
    intro a; reflexivity.
Defined.

(* 相关说明。 （已译） *)

Example op_op_Cartesian {C : Category} : @Cartesian C = @Cocartesian (C^op) :=
  eq_refl.

Example op_Coprod_is_product {C : Category} `{O : @Cartesian C} (p q : C) :
  @Coprod (C^op) O p q = @product_obj C O p q := eq_refl.

Definition Prod_Injective {C : Category} `{O : @Cartesian C} {p q : C}
  (P : @Injective C p) (Q : @Injective C q) :
  @Injective C (@product_obj C O p q) :=
  @Coprod_Projective (C^op) O p q P Q.

Definition Section_Injective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Injective C p) : @Injective C q :=
  @Retraction_Projective (C^op) p q s (op_Retraction_of_Section s S) P.

(* The hypothesis is stated in C's own vocabulary: [IsIndexedCoproduct] over
   [C^op] IS [IsIndexedProduct] over C (Structure/Limit/Coproduct.v). *)
Definition IndexedProd_Injective {C : Category} {A : Type} (fam : A → C)
  (s : C) (proj : ∀ a : A, s ~> fam a)
  (H : @IsIndexedProduct C A fam s proj)
  (P : ∀ a : A, @Injective C (fam a)) : @Injective C s :=
  @IndexedCoprod_Projective (C^op) A fam s proj H P.

(** ** Witnesses *)

Definition Retraction_lifts {C : Category} {p b c : C} (g : b ~> c)
  (R : Retraction g) (f : p ~> c) : ∃ h : p ~> b, g ∘ h ≈ f.
Proof.
  exists (retract ∘ f).
  rewrite comp_assoc, retract_comp; cat.
Defined.

Definition every_epi_splits_Projective {C : Category}
  (S : ∀ (b c : C) (g : b ~> c), Epic g → Retraction g) (p : C) :
  @Projective C p.
Proof.
  construct.
  exact (Retraction_lifts g (S b c g He) f).
Defined.

Definition initial_obj_Projective {C : Category} `{I : @Initial C} :
  @Projective C (@initial_obj C I).
Proof.
  construct.
  exists zero.
  apply zero_unique.
Defined.

Definition terminal_obj_Injective {C : Category} `{T : @Terminal C} :
  @Injective C (@terminal_obj C T) :=
  @initial_obj_Projective (C^op) T.

Program Definition LeibnizSetoid@{o p} (T : Type@{o}) : SetoidObject@{o p} :=
  {| carrier := T; is_setoid := {| equiv := @eq T |} |}.

Definition Sets_Leibniz_Projective@{h p} (T : Type@{p}) :
  @Projective Sets@{p h} (LeibnizSetoid@{p p} T).
Proof.
  construct.
  unshelve eexists.
  - refine {| morphism :=
                fun t => `1 (epic_implies_surjective@{h p} g He (f t)) |}.
    now intros t t' Ht; rewrite Ht.
  - intro t; simpl.
    exact (`2 (epic_implies_surjective@{h p} g He (f t))).
Defined.

Lemma TwoY_not_Projective : @Projective _2 TwoY → False.
Proof.
  intro P.
  exact (TwoHom_Y_X_absurd
           (`1 (@projective_lift _2 TwoY P TwoX TwoY TwoXY TwoXY_epic id))).
Qed.

Program Definition two_X_initial : @Initial _2 := {| terminal_obj := TwoX |}.
Next Obligation. destruct x; [ exact TwoIdX | exact TwoXY ]. Defined.
Next Obligation. apply Two_thin. Qed.

Definition TwoX_Projective : @Projective _2 TwoX :=
  @initial_obj_Projective _2 two_X_initial.

(* Projectivity is not a vacuous property of _2: it holds at TwoX and not
   at TwoY. *)
Definition two_projective_not_all :
  @Projective _2 TwoX * (@Projective _2 TwoY → False) :=
  (TwoX_Projective, TwoY_not_Projective).

(* * ** The price "every 对象 projective" （已译） *)

(* In any 范畴, projectivity codomain epi splits it: take
 恒等 map lift. （已译） *)
Definition Projective_codomain_splits {C : Category} {b c : C} (g : b ~> c)
  (P : @Projective C c) (He : Epic g) : Retraction g :=
  {| retract      := `1 (@projective_lift C c P b c g He id)
   ; retract_comp := `2 (@projective_lift C c P b c g He id) |}.

Definition all_projective_iff_every_epi_splits {C : Category} :
  (∀ p : C, @Projective C p)
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → Retraction g) :=
  (fun HP b c g He => Projective_codomain_splits g (HP c) He,
   fun HS => fun p => @every_epi_splits_Projective C HS p).

(* Over [Sets] that principle is not merely unavailable: it DECIDES EVERY
   PROPOSITION.  Instance/Sets/Regular.v proves [BlanketSplitting → LEM]
   axiom-free by a Diaconescu-shaped countermodel; "every setoid is
   projective" implies [BlanketSplitting] in one line. *)
Definition sets_all_projective_entails_splitting :
  (∀ p : @obj Sets, @Projective Sets p) → BlanketSplitting :=
  fun HP A B a0 f E => Projective_codomain_splits f (HP B) E.

Definition sets_all_projective_entails_LEM :
  (∀ p : @obj Sets, @Projective Sets p) → ∀ P : Prop, (P + (P → False))%type :=
  fun HP => blanket_splitting_entails_LEM
              (sets_all_projective_entails_splitting HP).

