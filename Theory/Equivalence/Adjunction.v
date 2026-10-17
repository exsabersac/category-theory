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

(* The adjunction being transported, in the variable convention of
   Theory/Adjunction.v: F is the left adjoint. *)
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* The equivalence on the codomain side of F ... *)
Context {G : C ⟶ C'}.
Context (EC : @EquivalenceOfCategories C C' G).

(* ... and the equivalence on its domain side. *)
Context {K : D ⟶ D'}.
Context (ED : @EquivalenceOfCategories D D' K).

(* Section-local shorthands for the two chosen quasi-inverses; the printed
   statements expand them back to [quasi_inverse]. *)
Local Notation Ginv := (@quasi_inverse C C' G EC).
Local Notation Kinv := (@quasi_inverse D D' K ED).

(* The domain-side constituent K⁻¹ ⊣ K: the adjoint-equivalence adjunction
   of the reversed equivalence, whose carrying functor is Kinv and whose
   quasi-inverse is K itself. *)
Definition transported_adj_dom : Kinv ⊣ K :=
  equiv_adjunction (@EquivalenceOfCategories_sym D D' K ED).

(* The codomain-side constituent G ⊣ G⁻¹: the adjoint-equivalence
   adjunction of EC itself. *)
Definition transported_adj_cod : G ⊣ Ginv :=
  equiv_adjunction EC.

(* The transported adjoints: conjugate each of F and U by the two
   equivalences. *)
Definition transported_left_adjoint : D' ⟶ C' := G ◯ (F ◯ Kinv).

Definition transported_right_adjoint : C' ⟶ D' := (K ◯ U) ◯ Ginv.

(* The transported adjunction: paste K⁻¹ ⊣ K, F ⊣ U and G ⊣ G⁻¹ by two
   applications of [Adjunction_Compose]. *)
Definition Transported_Adjunction :
  transported_left_adjoint ⊣ transported_right_adjoint :=
  Adjunction_Compose (Adjunction_Compose transported_adj_dom A)
    transported_adj_cod.

(*
   The 正向 transpose of the 复合 is the pasting of the three

   本节：constituent 正向 transposes, definitionally: transpose through codomain 等价, then through original 伴随, then through domain 等价.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Transported_Adjunction_to {d : D'} {c : C'}
  (f : G (F (Kinv d)) ~{C'}~> c) :
  to (@adj _ _ _ _ Transported_Adjunction d c) f
    ≈ to (@adj _ _ _ _ transported_adj_dom d (U (Ginv c)))
        (to (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (to (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c) f)).
Proof. reflexivity. Qed.

(* ... and dually for the inverse transpose, in the opposite order. *)
Corollary Transported_Adjunction_from {d : D'} {c : C'}
  (g : d ~{D'}~> K (U (Ginv c))) :
  from (@adj _ _ _ _ Transported_Adjunction d c) g
    ≈ from (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c)
        (from (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (from (@adj _ _ _ _ transported_adj_dom d (U (Ginv c))) g)).
Proof. reflexivity. Qed.

(*
   The unit of the 复合: the domain-side unit, followed by the

   本节说明相关定义、性质与动机。 K-image unit A, followed (K ◯ U)-image codomain-side unit — [伴随_Compose_unit] applied twice.

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
   The counit of the 复合, dually: the G-image of (the F-image of the

   本节说明相关定义、性质与动机。 domain-side counit, followed counit A), followed codomain-side counit — [伴随_Compose_counit] applied twice.

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

(* The counit of the codomain-side constituent is the counit-cell
   component of EC. *)
Corollary transported_adj_cod_counit (c : C') :
  @counit _ _ _ _ transported_adj_cod c
    ≈ to (@equivalence_counit_at C C' G EC c).
Proof. exact (equiv_adjunction_counit_at EC c). Qed.

(* The counit of the domain-side constituent is the counit-cell component
   of the reversed equivalence (whose counit cell is the symmetrized unit
   cell of ED). *)
Corollary transported_adj_dom_counit (d : D) :
  @counit _ _ _ _ transported_adj_dom d
    ≈ to (@equivalence_counit_at D' D Kinv
            (@EquivalenceOfCategories_sym D D' K ED) d).
Proof.
  exact (equiv_adjunction_counit_at (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

(* The G-image of the codomain-side unit is an inverse counit-cell
   component of EC ... *)
Corollary transported_adj_cod_fmap_unit (x : C) :
  fmap[G] (@unit _ _ _ _ transported_adj_cod x)
    ≈ from (@equivalence_counit_at C C' G EC (G x)).
Proof. exact (equiv_adjunction_fmap_unit EC x). Qed.

(* ... and the K⁻¹-image of the domain-side unit is an inverse counit-cell
   component of the reversed equivalence. *)
Corollary transported_adj_dom_fmap_unit (d : D') :
  fmap[Kinv] (@unit _ _ _ _ transported_adj_dom d)
    ≈ from (@equivalence_counit_at D' D Kinv
              (@EquivalenceOfCategories_sym D D' K ED) (Kinv d)).
Proof.
  exact (equiv_adjunction_fmap_unit (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

End TransportedAdjunction.
