Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TransportedAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {C' : Category}.
Context {D' : Category}.

(* The 伴随 being transported, variable convention of
 Theory/Adjunction.v: F 左伴随. （已译） *)
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* The 等价 codomain side F ... （已译） *)
Context {G : C ⟶ C'}.
Context (EC : @EquivalenceOfCategories C C' G).

(* ... 等价 domain side. （已译） *)
Context {K : D ⟶ D'}.
Context (ED : @EquivalenceOfCategories D D' K).

(* 相关说明。 （已译） *)
Local Notation Ginv := (@quasi_inverse C C' G EC).
Local Notation Kinv := (@quasi_inverse D D' K ED).

(* The domain-side constituent K⁻¹ ⊣ K: adjoint-等价 伴随
 reversed 等价, whose carrying 函子 Kinv whose
 quasi-inverse K itself. （已译） *)
Definition transported_adj_dom : Kinv ⊣ K :=
  equiv_adjunction (@EquivalenceOfCategories_sym D D' K ED).

(* The codomain-side constituent G ⊣ G⁻¹: adjoint-等价
 伴随 EC itself. （已译） *)
Definition transported_adj_cod : G ⊣ Ginv :=
  equiv_adjunction EC.

(* 相关说明。 （已译） *)
Definition transported_left_adjoint : D' ⟶ C' := G ◯ (F ◯ Kinv).

Definition transported_right_adjoint : C' ⟶ D' := (K ◯ U) ◯ Ginv.

(* The transported 伴随: paste K⁻¹ ⊣ K, F ⊣ U G ⊣ G⁻¹ two
 applications [Adjunction_Compose]. （已译） *)
Definition Transported_Adjunction :
  transported_left_adjoint ⊣ transported_right_adjoint :=
  Adjunction_Compose (Adjunction_Compose transported_adj_dom A)
    transported_adj_cod.

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Transported_Adjunction_to {d : D'} {c : C'}
  (f : G (F (Kinv d)) ~{C'}~> c) :
  to (@adj _ _ _ _ Transported_Adjunction d c) f
    ≈ to (@adj _ _ _ _ transported_adj_dom d (U (Ginv c)))
        (to (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (to (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c) f)).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Corollary Transported_Adjunction_from {d : D'} {c : C'}
  (g : d ~{D'}~> K (U (Ginv c))) :
  from (@adj _ _ _ _ Transported_Adjunction d c) g
    ≈ from (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c)
        (from (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (from (@adj _ _ _ _ transported_adj_dom d (U (Ginv c))) g)).
Proof. reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Transported_Adjunction_unit {d : D'} :
  @unit _ _ _ _ Transported_Adjunction d
    ≈ fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
        ∘ (fmap[K] (@unit _ _ _ _ A (Kinv d))
             ∘ @unit _ _ _ _ transported_adj_dom d).
Proof.
  transitivity
    (fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
       ∘ @unit _ _ _ _ (Adjunction_Compose transported_adj_dom A) d).
  - apply (Adjunction_Compose_unit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    apply (Adjunction_Compose_unit transported_adj_dom A).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Transported_Adjunction_counit {c : C'} :
  @counit _ _ _ _ Transported_Adjunction c
    ≈ @counit _ _ _ _ transported_adj_cod c
        ∘ fmap[G] (@counit _ _ _ _ A (Ginv c)
                     ∘ fmap[F] (@counit _ _ _ _ transported_adj_dom
                                  (U (Ginv c)))).
Proof.
  transitivity
    (@counit _ _ _ _ transported_adj_cod c
       ∘ fmap[G] (@counit _ _ _ _ (Adjunction_Compose transported_adj_dom A)
                    (Ginv c))).
  - apply (Adjunction_Compose_counit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    now rewrite (Adjunction_Compose_counit transported_adj_dom A).
Qed.

(* 相关说明。 （已译） *)
Corollary transported_adj_cod_counit (c : C') :
  @counit _ _ _ _ transported_adj_cod c
    ≈ to (@equivalence_counit_at C C' G EC c).
Proof. exact (equiv_adjunction_counit_at EC c). Qed.

(* The counit domain-side constituent counit-cell component
 reversed 等价 (whose counit cell symmetrized unit
 cell ED). （已译） *)
Corollary transported_adj_dom_counit (d : D) :
  @counit _ _ _ _ transported_adj_dom d
    ≈ to (@equivalence_counit_at D' D Kinv
            (@EquivalenceOfCategories_sym D D' K ED) d).
Proof.
  exact (equiv_adjunction_counit_at (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

(* 相关说明。 （已译） *)
Corollary transported_adj_cod_fmap_unit (x : C) :
  fmap[G] (@unit _ _ _ _ transported_adj_cod x)
    ≈ from (@equivalence_counit_at C C' G EC (G x)).
Proof. exact (equiv_adjunction_fmap_unit EC x). Qed.

(* ... K⁻¹-image domain-side unit inverse counit-cell
 component reversed 等价. （已译） *)
Corollary transported_adj_dom_fmap_unit (d : D') :
  fmap[Kinv] (@unit _ _ _ _ transported_adj_dom d)
    ≈ from (@equivalence_counit_at D' D Kinv
              (@EquivalenceOfCategories_sym D D' K ED) (Kinv d)).
Proof.
  exact (equiv_adjunction_fmap_unit (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

End TransportedAdjunction.
