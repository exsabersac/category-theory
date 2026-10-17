Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/tensor+algebra
 nLab:      https://ncatlab.org/nlab/show/free+object
 nLab:      https://ncatlab.org/nlab/show/composition+of+adjoints
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_algebra
 Wikipedia: https://en.wikipedia.org/wiki/Monoid_ring
 Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 Book: Mac Lane, ibid., §IV.8, Theorem 1 (adjoints compose) --

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** Formal ring expressions over an abelian group *)

Section FreeRingOnAb.

Context (A : AbObject).

Inductive FRTerm : Type :=
  | fr_gen  : carrier (cmon_setoid A) → FRTerm
  | fr_zero : FRTerm
  | fr_one  : FRTerm
  | fr_plus : FRTerm → FRTerm → FRTerm
  | fr_neg  : FRTerm → FRTerm
  | fr_mul  : FRTerm → FRTerm → FRTerm.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive fr_eq : FRTerm → FRTerm → Prop :=
  (* congruence for each former, saturating under A's own [≈] *)
  | fre_gen {a b : carrier (cmon_setoid A)} :
      a ≈ b → fr_eq (fr_gen a) (fr_gen b)
  | fre_plus {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_plus s t) (fr_plus s' t')
  | fre_neg {s s'} : fr_eq s s' → fr_eq (fr_neg s) (fr_neg s')
  | fre_mul {s s' t t'} :
      fr_eq s s' → fr_eq t t' → fr_eq (fr_mul s t) (fr_mul s' t')

  (* (0, +, -) is an abelian group *)
  | fre_add_assoc (s t u : FRTerm) :
      fr_eq (fr_plus (fr_plus s t) u) (fr_plus s (fr_plus t u))
  | fre_add_comm (s t : FRTerm) : fr_eq (fr_plus s t) (fr_plus t s)
  | fre_add_zero_l (s : FRTerm) : fr_eq (fr_plus fr_zero s) s
  | fre_neg_l (s : FRTerm) : fr_eq (fr_plus (fr_neg s) s) fr_zero

  (* (1, ·) is a monoid -- NOT assumed commutative *)
  | fre_mul_assoc (s t u : FRTerm) :
      fr_eq (fr_mul (fr_mul s t) u) (fr_mul s (fr_mul t u))
  | fre_mul_one_l (s : FRTerm) : fr_eq (fr_mul fr_one s) s
  | fre_mul_one_r (s : FRTerm) : fr_eq (fr_mul s fr_one) s

  (* · distributes over + on both sides *)
  | fre_distr_l (s t u : FRTerm) :
      fr_eq (fr_mul s (fr_plus t u)) (fr_plus (fr_mul s t) (fr_mul s u))
  | fre_distr_r (s t u : FRTerm) :
      fr_eq (fr_mul (fr_plus s t) u) (fr_plus (fr_mul s u) (fr_mul t u))

  (* the insertion of A is a homomorphism of abelian groups *)
  | fre_gen_zero : fr_eq (fr_gen (cmon_zero A)) fr_zero
  | fre_gen_plus (a b : carrier (cmon_setoid A)) :
      fr_eq (fr_gen (cmon_plus A a b)) (fr_plus (fr_gen a) (fr_gen b))

  | fre_sym {s t} : fr_eq s t → fr_eq t s
  | fre_trans {s t u} : fr_eq s t → fr_eq t u → fr_eq s u.

Lemma fr_refl (s : FRTerm) : fr_eq s s.
Proof.
  induction s.
  - exact (fre_gen (reflexivity _)).
  - exact (fre_trans (fre_sym (fre_add_zero_l fr_zero))
                     (fre_add_zero_l fr_zero)).
  - exact (fre_trans (fre_sym (fre_mul_one_l fr_one))
                     (fre_mul_one_l fr_one)).
  - exact (fre_plus IHs1 IHs2).
  - exact (fre_neg IHs).
  - exact (fre_mul IHs1 IHs2).
Qed.

Lemma fr_eq_Equivalence : Equivalence fr_eq.
Proof.
  constructor.
  - exact fr_refl.
  - exact (fun s t => fre_sym).
  - exact (fun s t u => fre_trans).
Qed.

Definition fr_Setoid : Setoid FRTerm := {|
  equiv        := fr_eq;
  setoid_equiv := fr_eq_Equivalence
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma fr_idem_zero (s : FRTerm) :
  fr_eq s (fr_plus s s) → fr_eq s fr_zero.
Proof.
  intro H.
  refine (fre_sym _).
  refine (fre_trans (fre_sym (fre_neg_l s)) _).
  refine (fre_trans (fre_plus (fr_refl (fr_neg s)) H) _).
  refine (fre_trans (fre_sym (fre_add_assoc (fr_neg s) s s)) _).
  refine (fre_trans (fre_plus (fre_neg_l s) (fr_refl s)) _).
  exact (fre_add_zero_l s).
Qed.

Lemma fr_mul_zero_l (s : FRTerm) : fr_eq (fr_mul fr_zero s) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_r fr_zero fr_zero s)).
  exact (fre_sym (fre_mul (fre_add_zero_l fr_zero) (fr_refl s))).
Qed.

Lemma fr_mul_zero_r (s : FRTerm) : fr_eq (fr_mul s fr_zero) fr_zero.
Proof.
  apply fr_idem_zero.
  refine (fre_trans _ (fre_distr_l s fr_zero fr_zero)).
  exact (fre_sym (fre_mul (fr_refl s) (fre_add_zero_l fr_zero))).
Qed.

(** ** The free ring on the abelian group A *)

Definition FreeRngAbObject : RingObject := {|
  ring_rig := {|
    rig_setoid := {| carrier := FRTerm; is_setoid := fr_Setoid |};
    rig_zero := fr_zero;
    rig_add := fr_plus;
    rig_one := fr_one;
    rig_mul := fr_mul;
    rig_add_respects := fun _ _ Hs _ _ Ht => fre_plus Hs Ht;
    rig_mul_respects := fun _ _ Hs _ _ Ht => fre_mul Hs Ht;
    rig_add_assoc := fre_add_assoc;
    rig_add_comm := fre_add_comm;
    rig_add_zero_l := fre_add_zero_l;
    rig_mul_assoc := fre_mul_assoc;
    rig_mul_one_l := fre_mul_one_l;
    rig_mul_one_r := fre_mul_one_r;
    rig_distr_l := fre_distr_l;
    rig_distr_r := fre_distr_r;
    rig_mul_zero_l := fr_mul_zero_l;
    rig_mul_zero_r := fr_mul_zero_r;
    (* [fr_eq] IS a [Prop]-valued relation, so it is its own [Prop] mirror
       and both implications are the identity. *)
    rig_prop := @PropEquiv_of_relation _ fr_Setoid fr_eq
                  (fun _ _ h => h) (fun _ _ h => h)
  |};
  ring_neg := fr_neg;
  ring_neg_respects := fun _ _ Hs => fre_neg Hs;
  ring_neg_l := fre_neg_l
|}.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_rng_ab_carrier_is_FRTerm :
  carrier (Ab_Forget (Rng_Forget_Ab FreeRngAbObject)) = FRTerm := eq_refl.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_rng_ab_equiv_is_fr_eq (s t : FRTerm) :
  (@equiv _ (is_setoid (rig_setoid FreeRngAbObject)) s t) = fr_eq s t
  := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition free_rng_ab_insert : A ~{Ab}~> Rng_Forget_Ab FreeRngAbObject.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fr_gen |}.
    intros a b H; exact (fre_gen H).
  - exact fre_gen_zero.
  - exact fre_gen_plus.
Defined.

Example free_rng_ab_insert_is_gen (a : carrier (cmon_setoid A)) :
  cmon_map free_rng_ab_insert a = fr_gen a := eq_refl.

(** ** The ring extension of a homomorphism on generators *)

Section Extension.

Context (R : RingObject).
Context (h : A ~{Ab}~> Rng_Forget_Ab R).

Fixpoint fr_eval (t : FRTerm) : carrier (rig_setoid R) :=
  match t with
  | fr_gen a    => cmon_map h a
  | fr_zero     => rig_zero R
  | fr_one      => rig_one R
  | fr_plus s t => rig_add R (fr_eval s) (fr_eval t)
  | fr_neg s    => ring_neg R (fr_eval s)
  | fr_mul s t  => rig_mul R (fr_eval s) (fr_eval t)
  end.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fr_eval_respects (s t : FRTerm) : fr_eq s t → fr_eval s ≈ fr_eval t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s t u | s t | s | s
    | s t u | s | s
    | s t u | s t u
    | | a b
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism (cmon_map h) _ _ Hab).
  - apply pequiv_from.
    exact (rig_add_respects R _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ring_neg_respects R _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rig_mul_respects R _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from; exact (rig_add_assoc R _ _ _).
  - apply pequiv_from; exact (rig_add_comm R _ _).
  - apply pequiv_from; exact (rig_add_zero_l R _).
  - apply pequiv_from; exact (ring_neg_l R _).
  - apply pequiv_from; exact (rig_mul_assoc R _ _ _).
  - apply pequiv_from; exact (rig_mul_one_l R _).
  - apply pequiv_from; exact (rig_mul_one_r R _).
  - apply pequiv_from; exact (rig_distr_l R _ _ _).
  - apply pequiv_from; exact (rig_distr_r R _ _ _).
  - apply pequiv_from; exact (cmon_map_zero h).
  - apply pequiv_from; exact (cmon_map_plus h a b).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition free_rng_ab_extend : FreeRngAbObject ~{Rng}~> R := {|
  rig_map := {| morphism := fr_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fr_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

Example free_rng_ab_extend_generators (a : carrier (cmon_setoid A)) :
  rig_map free_rng_ab_extend (fr_gen a) = cmon_map h a := eq_refl.

Example free_rng_ab_extend_zero :
  rig_map free_rng_ab_extend fr_zero = rig_zero R := eq_refl.

Example free_rng_ab_extend_one :
  rig_map free_rng_ab_extend fr_one = rig_one R := eq_refl.

Example free_rng_ab_extend_plus (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_plus s t)
    = rig_add R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_mul (s t : FRTerm) :
  rig_map free_rng_ab_extend (fr_mul s t)
    = rig_mul R (rig_map free_rng_ab_extend s)
                (rig_map free_rng_ab_extend t) := eq_refl.

Example free_rng_ab_extend_neg (s : FRTerm) :
  rig_map free_rng_ab_extend (fr_neg s)
    = ring_neg R (rig_map free_rng_ab_extend s) := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_rng_ab_extend_unique (g : FreeRngAbObject ~{Rng}~> R)
  (Hg : ∀ a : carrier (cmon_setoid A),
          rig_map g (fr_gen a) ≈ cmon_map h a) (t : FRTerm) :
  rig_map g t ≈ fr_eval t.
Proof.
  induction t as [ a | | | t1 IHt1 t2 IHt2 | t IHt | t1 IHt1 t2 IHt2 ];
    simpl.
  - exact (Hg a).
  - exact (rig_map_zero g).
  - exact (rig_map_one g).
  - refine (transitivity (rig_map_add g t1 t2) _).
    exact (rig_add_respects R _ _ IHt1 _ _ IHt2).
  - refine (transitivity (RigHom_neg FreeRngAbObject R g t) _).
    exact (ring_neg_respects R _ _ IHt).
  - refine (transitivity (rig_map_mul g t1 t2) _).
    exact (rig_mul_respects R _ _ IHt1 _ _ IHt2).
Qed.

End Extension.

Arguments fr_eval {R} h t.
Arguments free_rng_ab_extend {R} h.

(** ** The universal property, in the shape [universal_arrow_from_UMP]
       consumes *)
Theorem free_rng_ab_universal :
  ∀ (R : RingObject) (h : A ~{Ab}~> Rng_Forget_Ab R),
    ∃! g : FreeRngAbObject ~{Rng}~> R,
      h ≈ fmap[Rng_Forget_Ab] g ∘ free_rng_ab_insert.
Proof.
  intros R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; symmetry; exact (Hg a).
Qed.

End FreeRingOnAb.

Arguments fr_gen {A} a.
Arguments fr_zero {A}.
Arguments fr_one {A}.
Arguments fr_plus {A} s t.
Arguments fr_neg {A} s.
Arguments fr_mul {A} s t.
Arguments fr_eq {A} s t.
Arguments fr_refl {A} s.
Arguments fre_gen {A a b} _.
Arguments fre_plus {A s s' t t'} _ _.
Arguments fre_neg {A s s'} _.
Arguments fre_mul {A s s' t t'} _ _.
Arguments fre_add_assoc {A} s t u.
Arguments fre_add_comm {A} s t.
Arguments fre_add_zero_l {A} s.
Arguments fre_neg_l {A} s.
Arguments fre_mul_assoc {A} s t u.
Arguments fre_mul_one_l {A} s.
Arguments fre_mul_one_r {A} s.
Arguments fre_distr_l {A} s t u.
Arguments fre_distr_r {A} s t u.
Arguments fre_gen_zero {A}.
Arguments fre_gen_plus {A} a b.
Arguments fre_sym {A s t} _.
Arguments fre_trans {A s t u} _ _.
Arguments fr_eval {A R} h t.
Arguments free_rng_ab_extend {A R} h.
Arguments fr_eval_respects {A} R h s t _.
Arguments free_rng_ab_extend_unique {A} R h g _ t.

(** ** The universal arrow, the free functor and the adjunction *)

Definition free_rng_ab_universal_arrow (A : Ab)
  : UniversalArrow A Rng_Forget_Ab :=
  universal_arrow_from_UMP A Rng_Forget_Ab (FreeRngAbObject A)
    (free_rng_ab_insert A) (free_rng_ab_universal A).

Program Definition free_rng_ab_AUniversalArrow (A : Ab)
  : AUniversalArrow A Rng_Forget_Ab (FreeRngAbObject A) := {|
  universal_arrow := free_rng_ab_insert A
|}.
Next Obligation.
  intros A R h.
  unshelve eexists.
  - exact (free_rng_ab_extend h).
  - intro a; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_rng_ab_extend_unique R h g).
    intro a; exact (Hg a).
Qed.

Definition FreeRngAb : Ab ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Forget_Ab
    free_rng_ab_universal_arrow.

Definition free_rng_ab_adjunction : FreeRngAb ⊣ Rng_Forget_Ab :=
  AdjunctionFromUniversalArrows Rng_Forget_Ab free_rng_ab_universal_arrow.

Example FreeRngAb_obj (A : Ab) : FreeRngAb A = FreeRngAbObject A := eq_refl.

Example free_rng_ab_arrow_is_insert (A : Ab) :
  @arrow _ _ A Rng_Forget_Ab (free_rng_ab_universal_arrow A)
    = free_rng_ab_insert A := eq_refl.

Definition free_rng_ab_unit (A : Ab)
  : A ~{Ab}~> Rng_Forget_Ab (FreeRngAb A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A.

Example free_rng_ab_unit_is_insert (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (free_rng_ab_unit A) a = fr_gen a := eq_refl.

Definition free_rng_ab_counit (R : Rng)
  : FreeRngAb (Rng_Forget_Ab R) ~{Rng}~> R :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_rng_ab_adjunction R.

Lemma free_rng_ab_counit_generator (R : Rng)
  (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_rng_ab_adjunction R a).
Qed.

Theorem free_rng_ab_counit_evaluates (R : Rng)
  (t : FRTerm (Rng_Forget_Ab R)) :
  rig_map (free_rng_ab_counit R) t
    ≈ fr_eval (@id Ab (Rng_Forget_Ab R)) t.
Proof.
  apply (free_rng_ab_extend_unique R (@id Ab (Rng_Forget_Ab R))
           (free_rng_ab_counit R)).
  intro a; exact (free_rng_ab_counit_generator R a).
Qed.

Lemma free_rng_ab_fmap_generators {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) ≈ fr_gen (cmon_map u a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_rng_ab_universal_arrow A)
              (@arrow _ _ B Rng_Forget_Ab
                 (free_rng_ab_universal_arrow B) ∘ u)) a).
Qed.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The evaluation respects pointwise-`≈` homomorphisms. *)
Lemma fr_eval_pointwise@{u p +} {A : Ab@{u p}} {R : Rng@{u p}}
  (h h' : A ~{Ab@{u p}}~> Rng_Forget_Ab R) (H : h ≈ h') (t : FRTerm A) :
  fr_eval h t ≈ fr_eval h' t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - exact (H a).
  - reflexivity.
  - reflexivity.
  - exact (rig_add_respects R _ _ IH1 _ _ IH2).
  - exact (ring_neg_respects R _ _ IH).
  - exact (rig_mul_respects R _ _ IH1 _ _ IH2).
Qed.

(* The natural bijection Rng(F A, R) ≅ Ab(A, U R): forward g ↦ U g ∘
   insert, backward the extension. *)
Definition free_rng_ab_hom_iso@{u p +} (A : Ab@{u p}) (R : Rng@{u p}) :
  @Isomorphism Sets@{p u}
    {| carrier := @hom Rng@{u p} (FreeRngAb A) R
     ; is_setoid := @homset Rng@{u p} (FreeRngAb A) R |}
    {| carrier := @hom Ab@{u p} A (Rng_Forget_Ab R)
     ; is_setoid := @homset Ab@{u p} A (Rng_Forget_Ab R) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom Rng (FreeRngAb A) R
        ; is_setoid := @homset Rng (FreeRngAb A) R |}
       {| carrier := @hom Ab A (Rng_Forget_Ab R)
        ; is_setoid := @homset Ab A (Rng_Forget_Ab R) |}
       (@Build_SetoidMorphism
          (@hom Rng (FreeRngAb A) R) (@homset Rng (FreeRngAb A) R)
          (@hom Ab A (Rng_Forget_Ab R)) (@homset Ab A (Rng_Forget_Ab R))
          (fun g => fmap[Rng_Forget_Ab] g ∘[Ab] free_rng_ab_insert A) _)
       (@Build_SetoidMorphism
          (@hom Ab A (Rng_Forget_Ab R)) (@homset Ab A (Rng_Forget_Ab R))
          (@hom Rng (FreeRngAb A) R) (@homset Rng (FreeRngAb A) R)
          (fun h => free_rng_ab_extend h) _) _ _).
  - intros g g' H a. exact (H (fr_gen a)).
  - intros h h' H t. exact (fr_eval_pointwise h h' H t).
  - intros h a. reflexivity.
  - intros g t. simpl. symmetry.
    apply (free_rng_ab_extend_unique R _ g). intro a. reflexivity.
Defined.

Definition free_rng_ab_adjunction_hom@{u p +} :
  @Adjunction@{u p p u p p p p u p u} Rng@{u p} Ab@{u p}
    FreeRngAb Rng_Forget_Ab.
Proof.
  unshelve refine
    (@Build_Adjunction' Rng Ab FreeRngAb Rng_Forget_Ab
       free_rng_ab_hom_iso _ _).
  - intros A B R f g a. simpl.
    apply (proper_morphism (rig_map f)).
    exact (free_rng_ab_fmap_generators g a).
  - intros A R R' f g a. reflexivity.
Defined.

(* Its counit is the evaluation of the identity, by conversion. *)
Example free_rng_ab_hom_counit@{u p +} (R : Rng@{u p})
  (t : FRTerm (Rng_Forget_Ab R)) :
  rig_map (@counit _ _ _ _ free_rng_ab_adjunction_hom R) t
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R)) t := eq_refl.

(* Its unit and its forward transpose ARE those of
   [free_rng_ab_adjunction]. *)
Example free_rng_ab_hom_unit@{u p +} (A : Ab@{u p}) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction_hom A
    = @Category.Theory.Adjunction.unit _ _ _ _ free_rng_ab_adjunction A
  := eq_refl.

Example free_rng_ab_hom_to@{u p +} (A : Ab@{u p}) (R : Rng@{u p})
  (g : FreeRngAb A ~{Rng@{u p}}~> R) :
  to (@adj _ _ _ _ free_rng_ab_adjunction_hom A R) g
    = to (@adj _ _ _ _ free_rng_ab_adjunction A R) g := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LeftAdjointComparison.

Context {C D : Category}.
Context {U : C ⟶ D}.

(* The forward transpose of an adjunction is injective, being one leg of
   an isomorphism of hom-setoids. *)
Lemma to_adj_injective {F : D ⟶ C} (AF : F ⊣ U) {x : D} {y : C}
  (f g : F x ~> y) :
  to (@adj _ _ _ _ AF x y) f ≈ to (@adj _ _ _ _ AF x y) g → f ≈ g.
Proof.
  intro H.
  refine (transitivity
            (symmetry (@to_adj_comp_law _ _ _ _ AF x y f)) _).
  refine (transitivity _ (@to_adj_comp_law _ _ _ _ AF x y g)).
  exact (@from_adj_respects _ _ _ _ AF x y _ _ H).
Qed.

(* Naturality of the unit along an ARBITRARY morphism of D.  The in-tree
   [unit_comp] (Theory/Adjunction.v) states naturality only along a
   morphism [x ~> U y], which is a different statement. *)
Lemma unit_natural {F : D ⟶ C} (AF : F ⊣ U) {x y : D} (u : x ~> y) :
  @Category.Theory.Adjunction.unit _ _ _ _ AF y ∘ u
    ≈ fmap[U] (fmap[F] u)
        ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x.
Proof.
  unfold Category.Theory.Adjunction.unit.
  rewrite <- (@to_adj_nat_l _ _ _ _ AF x y (F y) id u).
  rewrite <- (@to_adj_nat_r _ _ _ _ AF x (F x) (F y) (fmap[F] u) id).
  rewrite id_left, id_right.
  reflexivity.
Qed.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adj_left_compare {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ~> F' x :=
  from (@adj _ _ _ _ AF x (F' x))
       (@Category.Theory.Adjunction.unit _ _ _ _ AF' x).

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem adj_left_compare_unit {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  fmap[U] (adj_left_compare AF AF' x)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _ AF x
    ≈ @Category.Theory.Adjunction.unit _ _ _ _ AF' x.
Proof.
  refine (transitivity
            (symmetry (@to_adj_unit _ _ _ _ AF x (F' x)
                         (adj_left_compare AF AF' x))) _).
  exact (@from_adj_comp_law _ _ _ _ AF x (F' x) _).
Qed.

(* One round-trip argument; the other round trip is this lemma at the
   swapped pair. *)
Lemma adj_left_compare_round {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D) :
  adj_left_compare AF' AF x ∘ adj_left_compare AF AF' x ≈ id[F x].
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F x)
               (adj_left_compare AF' AF x)
               (adj_left_compare AF AF' x)) _).
  refine (transitivity
            (compose_respects _ _ (reflexivity _) _ _
               (@from_adj_comp_law _ _ _ _ AF x (F' x) _)) _).
  (* [unit] IS [⌊id⌋] by definition, so the last step is [reflexivity]. *)
  exact (adj_left_compare_unit AF' AF x).
Qed.

Definition adj_left_compare_iso {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) (x : D)
  : F x ≅ F' x := {|
  to := adj_left_compare AF AF' x;
  from := adj_left_compare AF' AF x;
  iso_to_from := adj_left_compare_round AF' AF x;
  iso_from_to := adj_left_compare_round AF AF' x
|}.

Lemma adj_left_compare_natural {F F' : D ⟶ C} (AF : F ⊣ U) (AF' : F' ⊣ U)
  {x y : D} (u : x ~> y) :
  adj_left_compare AF AF' y ∘ fmap[F] u
    ≈ fmap[F'] u ∘ adj_left_compare AF AF' x.
Proof.
  apply (to_adj_injective AF).
  refine (transitivity
            (@to_adj_nat_l _ _ _ _ AF x y (F' y)
               (adj_left_compare AF AF' y) u) _).
  refine (transitivity
            (compose_respects _ _
               (@from_adj_comp_law _ _ _ _ AF y (F' y) _)
               _ _ (reflexivity u)) _).
  refine (transitivity (unit_natural AF' u) _).
  symmetry.
  refine (transitivity
            (@to_adj_nat_r _ _ _ _ AF x (F' x) (F' y)
               (fmap[F'] u) (adj_left_compare AF AF' x)) _).
  exact (compose_respects _ _ (reflexivity _) _ _
           (@from_adj_comp_law _ _ _ _ AF x (F' x) _)).
Qed.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition left_adjoints_agree {F F' : D ⟶ C}
  (AF : F ⊣ U) (AF' : F' ⊣ U) : F ≈ F'.
Proof.
  exists (adj_left_compare_iso AF AF').
  intros x y u; simpl.
  rewrite <- comp_assoc.
  rewrite <- adj_left_compare_natural.
  rewrite comp_assoc.
  rewrite adj_left_compare_round.
  rewrite id_left.
  reflexivity.
Defined.

End LeftAdjointComparison.

(** * Mac Lane §IV.8 Exercise 2: the free ring in two ways *)

Definition RngUnderlyingAb : Rng ⟶ Sets := Ab_Forget ◯ Rng_Forget_Ab.
Definition RngUnderlyingMon : Rng ⟶ Sets := Mon_Forget ◯ Rng_Forget_Mon.

Example rng_underlying_fobj_agree (R : Rng) :
  fobj[RngUnderlyingAb] R = fobj[RngUnderlyingMon] R := eq_refl.

Example rng_underlying_fmap_agree (R S : Rng) (f : R ~> S) :
  fmap[RngUnderlyingAb] f = fmap[RngUnderlyingMon] f := eq_refl.

(** ** Route one: sets ⟶ abelian groups ⟶ rings *)

Definition free_ring_via_ab : Sets ⟶ Rng := FreeRngAb ◯ FreeAb.

Definition free_ring_via_ab_adjunction
  : free_ring_via_ab ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_ab_adjunction free_rng_ab_adjunction.

(** ** Route two: sets ⟶ monoids ⟶ rings *)

Definition free_ring_via_mon : Sets ⟶ Rng :=
  MonoidRingFunctor ◯ FreeMonSets.

Definition free_ring_via_mon_adjunction
  : free_ring_via_mon ⊣ RngUnderlyingMon :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(*
   本节说明伴随、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_ring_via_mon_adjunction_ab
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  @Build_Adjunction Rng Sets free_ring_via_mon RngUnderlyingAb
    (@adj _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@to_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_l _ _ _ _ free_ring_via_mon_adjunction)
    (@from_adj_nat_r _ _ _ _ free_ring_via_mon_adjunction).

(** ** The two composites agree *)

Definition free_ring_composites_agree : free_ring_via_ab ≈ free_ring_via_mon
  := left_adjoints_agree free_ring_via_ab_adjunction
       free_ring_via_mon_adjunction_ab.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ring_composites_agree_via_left_adjoint_iso :
  free_ring_via_ab ≈ free_ring_via_mon :=
  left_adjoint_iso RngUnderlyingAb free_ring_via_ab free_ring_via_mon
    free_ring_via_ab_adjunction free_ring_via_mon_adjunction_ab.

Definition free_ring_comparison (X : Sets)
  : free_ring_via_ab X ~{Rng}~> free_ring_via_mon X :=
  adj_left_compare free_ring_via_ab_adjunction
    free_ring_via_mon_adjunction_ab X.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ring_comparison_is_agree_component (X : Sets) :
  to (projT1 free_ring_composites_agree X) = free_ring_comparison X
  := eq_refl.

Theorem free_ring_composites_agree_unit (X : Sets) :
  fmap[RngUnderlyingAb] (free_ring_comparison X)
    ∘ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_ab_adjunction X
    ≈ @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction_ab X.
Proof.
  exact (adj_left_compare_unit free_ring_via_ab_adjunction
           free_ring_via_mon_adjunction_ab X).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example free_ring_via_ab_obj (X : Sets) :
  free_ring_via_ab X = FreeRngAbObject (FreeAbObject X) := eq_refl.

Example free_ring_via_mon_obj (X : Sets) :
  free_ring_via_mon X = ZMonRing (FreeMonSetsObject X) := eq_refl.

(* The retyping is inert on the unit: the two adjunctions have the SAME
   forward transpose, hence the same unit, on the nose. *)
Example retype_adj_agrees (X : Sets) (R : Rng)
  (f : free_ring_via_mon X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_mon_adjunction_ab X R) f
    = to (@adj _ _ _ _ free_ring_via_mon_adjunction X R) f := eq_refl.

Example retype_unit_agrees (X : Sets) :
  @Category.Theory.Adjunction.unit _ _ _ _
      free_ring_via_mon_adjunction_ab X
    = @Category.Theory.Adjunction.unit _ _ _ _
        free_ring_via_mon_adjunction X := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section NonDegeneracy.

(* The hypotheses appear only in proofs, so they must be named for the
   section to discharge them as explicit arguments -- the
   Theory/EckmannHilton.v idiom. *)
Local Set Default Proof Using "All".

Context (A : AbObject).
Context (R : RingObject).
Context (Hne : rig_one R ≈ rig_zero R → False).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fr_zero_probe : A ~{Ab}~> Rng_Forget_Ab R.
Proof.
  unshelve refine {| cmon_map := _ |}.
  - unshelve refine {| morphism := fun _ => rig_zero R |}.
    intros a b Hab; reflexivity.
  - simpl; reflexivity.
  - intros a b; simpl; symmetry; exact (rig_add_zero_l R (rig_zero R)).
Defined.

(* The free ring is not the zero ring. *)
Theorem free_rng_ab_zero_not_one : fr_eq (@fr_zero A) fr_one → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

(* No generator is the unit -- the insertion of A does not meet the
   scalars.  True of EVERY generator of EVERY abelian group. *)
Theorem free_rng_ab_gen_not_one (a : carrier (cmon_setoid A)) :
  fr_eq (fr_gen a) (@fr_one A) → False.
Proof.
  intro He.
  apply Hne; symmetry.
  exact (fr_eval_respects R fr_zero_probe _ _ He).
Qed.

End NonDegeneracy.

Arguments fr_zero_probe A {R}.
Arguments free_rng_ab_zero_not_one A {R} Hne _.
Arguments free_rng_ab_gen_not_one A {R} Hne a _.

(** ** The integers embed in the free ring on the integers *)

Lemma int_one_not_zero : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. intro H; compute in H; discriminate H. Qed.

(* [Rng_Forget_Ab Int_Ring] IS Instance/Ab/Free.v's [ab_int], so the
   identity of [Ab] is already a probe and no new homomorphism is
   needed. *)
Definition rng_int_probe : ab_int ~{Ab}~> Rng_Forget_Ab Int_Ring :=
  @id Ab ab_int.

Theorem int_free_rng_gen_injective (m n : Z) :
  fr_eq (@fr_gen ab_int m) (@fr_gen ab_int n) → m = n.
Proof. exact (fr_eval_respects Int_Ring rng_int_probe _ _). Qed.

Theorem int_free_rng_gens_distinct :
  fr_eq (@fr_gen ab_int 2%Z) (@fr_gen ab_int 3%Z) → False.
Proof. intro H; discriminate (int_free_rng_gen_injective _ _ H). Qed.

Theorem int_free_rng_gen_not_one :
  fr_eq (@fr_gen ab_int 1%Z) fr_one → False.
Proof.
  exact (free_rng_ab_gen_not_one ab_int int_one_not_zero 1%Z).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ut2_two_probe : AbTwoGens ~{Sets}~> Ab_Forget (Rng_Forget_Ab UT2).
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens =>
                  if b then ut2_e11 else ut2_e12
  |}.
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

Definition rng_ut2_probe
  : FreeAbObject AbTwoGens ~{Ab}~> Rng_Forget_Ab UT2 :=
  free_ab_extend ut2_two_probe.

Definition rng_two_gens : AbObject := FreeAbObject AbTwoGens.

Definition rng_gx : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens true).
Definition rng_gy : FRTerm rng_two_gens :=
  @fr_gen rng_two_gens (@fa_gen AbTwoGens false).

Example rng_gxgy_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gx rng_gy)
    = ut2_e12 := eq_refl.

Example rng_gygx_computes :
  rig_map (free_rng_ab_extend rng_ut2_probe) (fr_mul rng_gy rng_gx)
    = ut2_zero := eq_refl.

Theorem free_rng_ab_not_commutative :
  fr_eq (fr_mul rng_gx rng_gy) (fr_mul rng_gy rng_gx) → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

Theorem free_rng_ab_two_gens_distinct : fr_eq rng_gx rng_gy → False.
Proof.
  intro He.
  pose proof (fr_eval_respects UT2 rng_ut2_probe _ _ He) as H.
  compute in H; discriminate H.
Qed.

(* The object just probed IS the ab-route free ring on the two-element
   setoid, so the witness exercises the composite of the exercise and not
   a construction beside it. *)
Example rng_two_gens_is_via_ab :
  FreeRngAbObject rng_two_gens = free_ring_via_ab AbTwoGens := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_ring_via_ab_transpose (X : Sets) (R : Rng)
  (f : free_ring_via_ab X ~{Rng}~> R) :
  to (@adj _ _ _ _ free_ring_via_ab_adjunction X R) f
    = to (@adj _ _ _ _ free_ab_adjunction X (Rng_Forget_Ab R))
        (to (@adj _ _ _ _ free_rng_ab_adjunction (FreeAb X) R) f)
  := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** CONVERSION negatives *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example rng_underlying_records_agree :
  RngUnderlyingAb = RngUnderlyingMon := eq_refl.

(*
   本节说明伴随、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition rng_mon_route_ascribed
  : free_ring_via_mon ⊣ RngUnderlyingAb :=
  Adjunction_Compose free_mon_sets_adjunction zmring_adjunction.

(* The two composites are non-convertible terms denoting isomorphic
   rings on the same
   generating setoid, so [free_ring_composites_agree] is not an
   isomorphism between a thing and itself. *)
Fail Example rng_routes_convertible :
  free_ring_via_ab AbTwoGens = free_ring_via_mon AbTwoGens := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example rng_counit_computes (R : Rng) (a : carrier (rig_setoid R)) :
  rig_map (free_rng_ab_counit R) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

(* Likewise the free functor's action on an arrow is defined by universal
   factorization rather than by a formula, so relabelling generators is
   the theorem [free_rng_ab_fmap_generators] and not a computation. *)
Fail Example rng_fmap_generator_computes {A B : Ab} (u : A ~{Ab}~> B)
  (a : carrier (cmon_setoid A)) :
  rig_map (fmap[FreeRngAb] u) (fr_gen a) = fr_gen (cmon_map u a)
  := eq_refl.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Positive controls naming the two constants the negatives below name,
   so that renaming either breaks this file instead of turning a [Fail]
   vacuously green.  Unconstrained, these elaborate. *)
Check (Rng_Forget_Mon : Rng ⟶ MonSets).
Check (Rig_Forget_Mon : Rig ⟶ MonSets).

Section MonRouteSetPin.

Universe uo uh.
Constraint Set < uh.

(* Positive controls: the abelian route's two forgetful functors DO
   elaborate at a ring whose homs live strictly above [Set]. *)
Check (Rng_Forget_Ab : Rng@{uo uh} ⟶ Ab).
Check (Rig_Forget_CMon : Rig@{uo uh} ⟶ CMon).

Fail Check (Rng_Forget_Mon : Rng@{uo uh} ⟶ MonSets).
Fail Check (Rig_Forget_Mon : Rig@{uo uh} ⟶ MonSets).

End MonRouteSetPin.

(** ** Instrument check

    A [Fail] that must fail for a reason having nothing to do with this
    file, so that a broken [Fail] mechanism would be visible. *)
Fail Example rng_instrument_check : (0%Z = 1%Z) := eq_refl.
