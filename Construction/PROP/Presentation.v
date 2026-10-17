Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.

From Coq Require Import Arith.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/generators+and+relations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Symmetric monoidal theories *)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition EqSystem (S : Signature) : Type :=
  ∀ m n : nat, Term S m n → Term S m n → Prop.

(** A symmetric monoidal theory: generators plus equations. *)
Record SMT : Type := {
  smt_sig : Signature;
  smt_eqs : EqSystem smt_sig
}.

Section Presented.

Context (E : SMT).

Notation Σ := (smt_sig E).

Open Scope nat_scope.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive TermEqW : forall {m n}, Term Σ m n → Term Σ m n → Prop :=

  (** Every free equation holds in the presented PROP. *)
  | TEW_termeq {m n} (s t : Term Σ m n) :
      TermEq Σ s t → TermEqW s t

  (** 本节：Every axiom theory holds presented PROP. （已译） *)
  | TEW_ax {m n} (s t : Term Σ m n) :
      smt_eqs E m n s t → TermEqW s t

  (** Closure under symmetry and transitivity. *)
  | TEW_sym {m n} (s t : Term Σ m n) :
      TermEqW s t → TermEqW t s
  | TEW_trans {m n} (s t u : Term Σ m n) :
      TermEqW s t → TermEqW t u → TermEqW s u

  (** Closure under the two composition operations. *)
  | TEW_comp {m n p} (f f' : Term Σ n p) (g g' : Term Σ m n) :
      TermEqW f f' → TermEqW g g' →
      TermEqW (T_comp f g) (T_comp f' g')
  | TEW_tens {m1 n1 m2 n2} (f f' : Term Σ m1 n1) (g g' : Term Σ m2 n2) :
      TermEqW f f' → TermEqW g g' →
      TermEqW (T_tens f g) (T_tens f' g').

(** [TermEqW] is a hom-congruence on [FreeCat Σ] in the sense of
    [Construction/Quotient.v]: it contains the hom-setoid equivalence
    ([TermEq Σ], via [TEW_termeq]) and is closed under [T_comp]. *)
#[export] Instance TermEqW_Congruence :
  @HomCongruence (FreeCat Σ) (fun m n : nat => @TermEqW m n) :=
  @Build_HomCongruence (FreeCat Σ) (fun m n : nat => @TermEqW m n)
    (fun (m n : nat) (s t : Term Σ m n) H => TEW_termeq s t H)
    (fun (m n : nat) (s t : Term Σ m n) H => TEW_sym s t H)
    (fun (m n : nat) (s t u : Term Σ m n) H1 H2 => TEW_trans s t u H1 H2)
    (fun (m n p : nat) (f f' : Term Σ n p) (g g' : Term Σ m n) Hf Hg =>
       TEW_comp f f' g g' Hf Hg).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PresentedCat : Category :=
  @Quotient (FreeCat Σ) (fun m n : nat => @TermEqW m n) TermEqW_Congruence.

(** A term, viewed 态射 presented 范畴 (the
 carrier hom [PresentedCat] IS [Term Σ]). （已译） *)
Definition quot {m n : nat} (t : Term Σ m n) : m ~{PresentedCat}~> n := t.

(** The projection 函子: 恒等 对象 态射. （已译） *)
Definition PresentedProj : FreeCat Σ ⟶ PresentedCat :=
  @QuotientProj (FreeCat Σ) (fun m n : nat => @TermEqW m n) TermEqW_Congruence.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：Reflexivity theory congruence, via embedding. （已译） *)
Definition TermEqW_refl {m n : nat} (t : Term Σ m n) : TermEqW t t :=
  TEW_termeq t t (TE_refl t).

(* * ** The tensor presented 范畴

 The parallel-复合 bifunctor descends quotient
 because [TermEqW] closed under [T_tens]. （已译） *)

Definition Presented_Tensor : PresentedCat ∏ PresentedCat ⟶ PresentedCat :=
  @Quotient_bifunctor (FreeCat Σ) (fun m n : nat => @TermEqW m n)
    TermEqW_Congruence (FreeCat_Tensor Σ)
    (fun x y f g Hf Hg => TEW_tens (fst f) (fst g) (snd f) (snd g) Hf Hg).

(*
   本节说明幺半结构、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Presented_Monoidal : @Monoidal PresentedCat := {|
  I            := 0;
  tensor       := Presented_Tensor;
  unit_left    := fun x => Quotient_iso (FreeCat_unit_left Σ x);
  unit_right   := fun x => Quotient_iso (FreeCat_unit_right Σ x);
  tensor_assoc := fun x y z => Quotient_iso (FreeCat_tensor_assoc Σ x y z);
  to_unit_left_natural := fun x y g =>
    TEW_termeq _ _ (@to_unit_left_natural _ (FreeCat_Monoidal Σ) x y g);
  from_unit_left_natural := fun x y g =>
    TEW_termeq _ _ (@from_unit_left_natural _ (FreeCat_Monoidal Σ) x y g);
  to_unit_right_natural := fun x y g =>
    TEW_termeq _ _ (right_unit_natural Σ g);
  from_unit_right_natural := fun x y g =>
    TEW_termeq _ _ (right_unit_natural_from Σ g);
  to_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
    TEW_termeq _ _ (assoc_natural Σ g h i);
  from_tensor_assoc_natural := fun _ _ _ _ _ _ g h i =>
    TEW_termeq _ _ (assoc_natural_from Σ g h i);
  triangle_identity := fun x y =>
    TEW_termeq _ _ (free_triangle Σ x y);
  pentagon_identity := fun x y z w =>
    TEW_termeq _ _ (free_pentagon Σ x y z w)
|}.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Presented_Braided : @BraidedMonoidal PresentedCat := {|
  braided_is_monoidal := Presented_Monoidal;  (* THE shared record *)
  braid := fun m n => T_braid m n;
  braid_natural := fun x y g z w h =>
    TEW_termeq _ _ (free_braid_square Σ g h);
  hexagon_identity := fun x y z =>
    TEW_termeq _ _ (free_hexagon Σ x y z);
  hexagon_identity_sym := fun x y z =>
    TEW_termeq _ _ (free_hexagon_sym Σ x y z)
|}.

Program Definition Presented_Symmetric : @SymmetricMonoidal PresentedCat := {|
  symmetric_is_braided := Presented_Braided;
  braid_invol := fun x y =>
    TEW_termeq _ _ (free_braid_invol Σ x y)
|}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Presented_Strict : @StrictMonoidal PresentedCat := {|
  strict_is_monoidal    := Presented_Monoidal;  (* THE shared record *)
  strict_assoc_obj      := fun x y z => eq_sym (Nat.add_assoc x y z);
  strict_unit_left_obj  := fun x => Nat.add_0_l x;
  strict_unit_right_obj := fun x => Nat.add_0_r x
|}.
Next Obligation. exact (TermEqW_refl _). Qed.
Next Obligation. exact (TermEqW_refl _). Qed.
Next Obligation. exact (TermEqW_refl _). Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PresentedPROP : PROP := {|
  prop_cat       := PresentedCat;
  prop_strict    := Presented_Strict;
  prop_symmetric := Presented_Symmetric;
  prop_monoidal_coherence := eq_refl;
  prop_of_nat    := fun n : nat => n;
  prop_unit_zero := eq_refl;
  prop_tensor_plus := fun m n => eq_refl
|}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：The tensor-then-project project-then-tensor composites that
 tensor comparison relates. （已译） *)
Definition Presented_ap_dom : FreeCat Σ ∏ FreeCat Σ ⟶ PresentedCat :=
  Presented_Tensor ◯ (PresentedProj ∏⟶ PresentedProj).

Definition Presented_ap_cod : FreeCat Σ ∏ FreeCat Σ ⟶ PresentedCat :=
  PresentedProj ◯ FreeCat_Tensor Σ.

(** Both directions tensor comparison families of
 identities; 自然性 [tm_id_swap]. （已译） *)
Definition Presented_ap_to : Presented_ap_dom ⟹ Presented_ap_cod :=
  @Build_Transform' (FreeCat Σ ∏ FreeCat Σ) PresentedCat
    Presented_ap_dom Presented_ap_cod
    (fun p => T_id (fst p + snd p))
    (fun p q f => TEW_termeq _ _ (tm_id_swap (T_tens (fst f) (snd f)))).

Definition Presented_ap_from : Presented_ap_cod ⟹ Presented_ap_dom :=
  @Build_Transform' (FreeCat Σ ∏ FreeCat Σ) PresentedCat
    Presented_ap_cod Presented_ap_dom
    (fun p => T_id (fst p + snd p))
    (fun p q f => TEW_termeq _ _ (tm_id_swap (T_tens (fst f) (snd f)))).

(** The 恒等 components inverse up [TermEqW] (恒等
 自然变换 复合-with-tensor 函子 has
 components [T_tens (T_id _) (T_id _)]). （已译） *)
Program Definition Presented_ap_iso :
  Presented_ap_dom ≅[[FreeCat Σ ∏ FreeCat Σ, PresentedCat]] Presented_ap_cod := {|
  to   := Presented_ap_to;
  from := Presented_ap_from;
  iso_to_from := fun p =>
    TEW_termeq _ _ (tm_comp_id_tens (fst p) (snd p));
  iso_from_to := fun p =>
    TEW_termeq _ _ (tm_comp_id_tens (fst p) (snd p))
|}.

Program Definition PresentedProj_Monoidal :
  @MonoidalFunctor (FreeCat Σ) PresentedCat
    (FreeCat_Monoidal Σ) Presented_Monoidal PresentedProj := {|
  pure_iso := iso_id;
  ap_functor_iso := Presented_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z => @tensor_assoc PresentedCat Presented_Monoidal x y z;
  monoidal_unit_left := fun x =>
    TEW_termeq _ _ (TE_sym _ _ (tm_collapse_r (T_cast (Nat.add_0_l x))));
  monoidal_unit_right := fun x =>
    TEW_termeq _ _ (TE_sym _ _ (tm_collapse_r (T_cast (Nat.add_0_r x))));
  monoidal_assoc := fun x y z =>
    TEW_termeq _ _
      (TE_trans _ _ _
         (tm_collapse_r (T_cast (eq_sym (Nat.add_assoc x y z))))
         (TE_sym _ _
            (tm_collapse_l (T_cast (eq_sym (Nat.add_assoc x y z))))))
|}.

(** Both comparison maps projection identities the
 nose, so projection STRICT monoidal, [eq_refl] 对象
 equalities. （已译） *)

Lemma PresentedProj_pure_id :
  to (@pure_iso _ _ _ _ PresentedProj PresentedProj_Monoidal)
  ≈[PresentedCat] @id PresentedCat 0.
Proof. exact (TermEqW_refl _). Qed.

Lemma PresentedProj_ap_id (x y : nat) :
  to (@ap_iso _ _ _ _ PresentedProj PresentedProj_Monoidal x y)
  ≈[PresentedCat] @id PresentedCat (x + y).
Proof. exact (TermEqW_refl _). Qed.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition PresentedProj_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) PresentedCat
    (FreeCat_Monoidal Σ) Presented_Monoidal PresentedProj := {|
  strict_functor_is_monoidal := PresentedProj_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (TermEqW_refl _). Qed.
Next Obligation. exact (TermEqW_refl _). Qed.

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PresentedProj_braid (m n : nat) :
  fmap[PresentedProj] (@braid (FreeCat Σ) (FreeCat_Braided Σ) m n)
    ∘ to (@ap_iso _ _ _ _ PresentedProj PresentedProj_Monoidal m n)
  ≈[PresentedCat]
  to (@ap_iso _ _ _ _ PresentedProj PresentedProj_Monoidal n m)
    ∘ @braid PresentedCat Presented_Braided m n.
Proof.
  exact (TEW_termeq _ _ (tm_id_swap (T_braid m n))).
Qed.

Program Definition PresentedProj_Braided :
  @BraidedMonoidalFunctor (FreeCat Σ) PresentedCat
    (FreeCat_Braided Σ) Presented_Braided PresentedProj := {|
  braided_is_strong := PresentedProj_Monoidal
|}.
Next Obligation.
  exact (TEW_termeq _ _ (tm_id_swap (T_braid x y))).
Qed.

(** A braided monoidal functor between symmetric monoidal categories
    IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition PresentedProj_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat Σ) PresentedCat
    (FreeCat_Symmetric Σ) Presented_Symmetric PresentedProj :=
  PresentedProj_Braided.

(* 相关说明。 （已译） *)

(** The coherence between strict symmetric [Monoidal] paths
 reflexivity 证明 itself. （已译） *)
Example PresentedPROP_coherence_is_refl :
  @prop_monoidal_coherence PresentedPROP = eq_refl := eq_refl.

(** Tensor-on-对象 literally addition, [eq_refl] 证明. （已译） *)
Example PresentedPROP_tensor_plus_is_refl (m n : nat) :
  @prop_tensor_plus PresentedPROP m n = eq_refl := eq_refl.

(** The projection 函子 acts 恒等 terms. （已译） *)
Example PresentedProj_fmap_id_on_terms {m n : nat} (t : Term Σ m n) :
  fmap[PresentedProj] t = quot t := eq_refl.

(** Every axiom theory holds presented 范畴. （已译） *)
Example Presented_axioms_hold {m n : nat} (s t : Term Σ m n)
  (H : smt_eqs E m n s t) : quot s ≈[PresentedCat] quot t := TEW_ax s t H.

End Presented.

Arguments TermEqW E {m n} _ _.
Arguments PresentedCat E : assert.
Arguments quot E {m n} t : assert.
Arguments PresentedProj E : assert.
Arguments Presented_Tensor E : assert.
Arguments Presented_Monoidal E : assert.
Arguments Presented_Braided E : assert.
Arguments Presented_Symmetric E : assert.
Arguments Presented_Strict E : assert.
Arguments PresentedPROP E : assert.
Arguments PresentedProj_Monoidal E : assert.
Arguments PresentedProj_Strict E : assert.
Arguments PresentedProj_braid E m n : assert.
Arguments PresentedProj_Braided E : assert.
Arguments PresentedProj_Symmetric E : assert.
