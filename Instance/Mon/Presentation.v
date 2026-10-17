Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Mon.Word.

Generalizable All Variables.

(* * * Every 幺半群 coequalizer free monoids （已译） *)

(*
 nLab:   https://ncatlab.org/nlab/show/monadic+functor
 nLab:   https://ncatlab.org/nlab/show/split+coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonPresentation.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).
Local Notation UMonOS :=
  (@Mon_Forget@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

(* Awodey's ε : T²M → TM, "using multiplication TM": counit at
 free 幺半群 TM, concatenates word words. （已译） *)
Definition Mon_flatten@{+} (M : MonOS) :
  FreeMonSets (UMonOS (FreeMonSets (UMonOS M)))
    ~{MonOS}~> FreeMonSets (UMonOS M) :=
  @counit _ _ _ _ free_mon_sets_adjunction_hom (FreeMonSets (UMonOS M)).

(* 相关说明。 （已译） *)
Definition Mon_free_evaluate@{+} (M : MonOS) :
  FreeMonSets (UMonOS (FreeMonSets (UMonOS M)))
    ~{MonOS}~> FreeMonSets (UMonOS M) :=
  fmap[FreeMonSets]
    (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M)).

(* Awodey's π : TM → M, the evaluation (x₁, …, xₙ) ↦ x₁ ⋯ xₙ. *)
Definition Mon_evaluate@{+} (M : MonOS) :
  FreeMonSets (UMonOS M) ~{MonOS}~> M :=
  @counit _ _ _ _ free_mon_sets_adjunction_hom M.

(* π coforks pair: 自然性 counit, Monad/Monadicity/
 Crude.v's [crude_unit_cofork] states it any 伴随. （已译） *)
Lemma Mon_canonical_cofork@{+} (M : MonOS) :
  Mon_evaluate M ∘ Mon_flatten M ≈ Mon_evaluate M ∘ Mon_free_evaluate M.
Proof. exact (crude_unit_cofork free_mon_sets_adjunction_hom M). Qed.

(* Two 幺半群 maps out free 幺半群 agree letters agree. （已译） *)
Lemma Mon_free_hom_ext@{+} {X : obj[Sets@{o so}]} {L : MonOS}
  (g1 g2 : FreeMonSets X ~{MonOS}~> L) :
  (∀ a : X, mon_fun g1 (word1 a) ≈ mon_fun g2 (word1 a)) → g1 ≈ g2.
Proof.
  intros Hg l.
  transitivity (free_mon_extend (L := L) (fun a => mon_fun g2 (word1 a)) l).
  - exact (free_mon_extend_unique _ g1 Hg l).
  - symmetry.
    apply (free_mon_extend_unique _ g2).
    intro a; reflexivity.
Qed.

(* 相关说明。 （已译） *)

Section Descent.

Context (M : MonOS) {c : MonOS}.
Context (k : FreeMonSets (UMonOS M) ~{MonOS}~> c).
Context (Hk : k ∘ Mon_flatten M ≈ k ∘ Mon_free_evaluate M).

(* 相关说明。 （已译） *)
Lemma Mon_canonical_desc_mul@{+} (x y : mon_ob M) :
  mon_fun k (word1 (mon_mul M x y))
    ≈ mon_mul c (mon_fun k (word1 x)) (mon_fun k (word1 y)).
Proof using Hk.
  transitivity (mon_fun k (word1 (mon_mul M x (mon_mul M y (mon_one M))))).
  { apply (mon_fun_resp k).
    refine (we_cons _ _ _ _ _ we_nil).
    apply (mon_mul_resp M); [ reflexivity |].
    symmetry; apply mon_one_r. }
  transitivity (mon_fun k
                  (mon_fun (Mon_free_evaluate M) (word1 (word2 x y)))).
  { apply (mon_fun_resp k).
    symmetry.
    exact (free_mon_fmap_is_wmap
             (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M))
             (word1 (word2 x y))). }
  transitivity (mon_fun k (mon_fun (Mon_flatten M) (word1 (word2 x y)))).
  { symmetry; exact (Hk (word1 (word2 x y))). }
  exact (mon_fun_mul k (word1 x) (word1 y)).
Qed.

(* The cofork read at [[]]: k⟨1⟩ ≈ k⟨⟩ ≈ 1. *)
Lemma Mon_canonical_desc_one@{+} :
  mon_fun k (word1 (mon_one M)) ≈ mon_one c.
Proof using Hk.
  transitivity (mon_fun k (mon_fun (Mon_free_evaluate M) (word1 word0))).
  { apply (mon_fun_resp k).
    symmetry.
    exact (free_mon_fmap_is_wmap
             (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M))
             (word1 word0)). }
  transitivity (mon_fun k (mon_fun (Mon_flatten M) (word1 word0))).
  { symmetry; exact (Hk (word1 word0)). }
  exact (mon_fun_one k).
Qed.

Definition Mon_canonical_desc@{+} : M ~{MonOS}~> c :=
  @mk_mon_hom M c (fun x => mon_fun k (word1 x))
    (fun x x' H => mon_fun_resp k _ _ (we_cons _ _ _ _ H we_nil))
    Mon_canonical_desc_mul Mon_canonical_desc_one.

Lemma Mon_canonical_desc_commutes@{+} :
  Mon_canonical_desc ∘ Mon_evaluate M ≈ k.
Proof using Hk.
  apply Mon_free_hom_ext; intro a.
  apply (mon_fun_resp k).
  exact (we_cons _ _ _ _ (mon_one_r M a) we_nil).
Qed.

Lemma Mon_canonical_desc_unique@{+} (v : M ~{MonOS}~> c) :
  v ∘ Mon_evaluate M ≈ k → Mon_canonical_desc ≈ v.
Proof.
  intros Hv x.
  transitivity (mon_fun v (mon_mul M x (mon_one M))).
  - symmetry; exact (Hv (word1 x)).
  - apply (mon_fun_resp v).
    apply mon_one_r.
Qed.

End Descent.

(** ** Awodey, Proposition 3.22 *)

Definition Mon_canonical_presentation@{+} (M : MonOS) :
  IsCoequalizer (Mon_flatten M) (Mon_free_evaluate M) M (Mon_evaluate M).
Proof.
  unshelve econstructor.
  - exact (Mon_canonical_cofork M).
  - intros c k Hk.
    exact {| unique_obj      := Mon_canonical_desc M k Hk;
             unique_property := Mon_canonical_desc_commutes M k Hk;
             uniqueness      := Mon_canonical_desc_unique M k Hk |}.
Defined.

(* "Thus M ≅ F(G)/(r₁ = r₂)": any coequalizer of the pair is M. *)
Definition Mon_presented_iso@{+} (M : MonOS) {q : MonOS}
  {e : FreeMonSets (UMonOS M) ~{MonOS}~> q}
  (E : IsCoequalizer (Mon_flatten M) (Mon_free_evaluate M) q e) :
  M ≅[MonOS] q :=
  coequalizer_unique _ _ (Mon_canonical_presentation M) E.

(* * ** Awodey, §3.5 Exercise 3: forgetful 函子 preserves it （已译） *)

(*
   本节说明 Presentation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Mon_canonical_split@{+} (M : MonOS) :
  SplitCoequalizer (fmap[UMonOS] (Mon_flatten M))
                   (fmap[UMonOS] (Mon_free_evaluate M)) :=
  @canonical_split Sets@{o so} W0F W0 (UMonOS M) (projT2 (fobj[Mon_K] M)).

Definition Mon_canonical_U_IsCoequalizer@{+} (M : MonOS) :
  IsCoequalizer (fmap[UMonOS] (Mon_flatten M))
    (fmap[UMonOS] (Mon_free_evaluate M)) (UMonOS M)
    (fmap[UMonOS] (Mon_evaluate M)) :=
  split_coequalizer_is_coequalizer _ _ (Mon_canonical_split M).

(* Indeed every functor out of Sets preserves it. *)
Definition Mon_canonical_U_AbsoluteCoequalizer@{xo xh +} (M : MonOS) :
  AbsoluteCoequalizer@{_ _ xo xh _} (fmap[UMonOS] (Mon_flatten M))
    (fmap[UMonOS] (Mon_free_evaluate M)) (UMonOS M)
    (fmap[UMonOS] (Mon_evaluate M)) :=
  split_coequalizer_absolute (Mon_canonical_split M).

(** ** Readbacks *)

Example Mon_flatten_fun@{+} (M : MonOS)
  (ww : list (list (mon_ob M))) :
  mon_fun (Mon_flatten M) ww = wconcat ww := eq_refl.

Example Mon_evaluate_fun@{+} (M : MonOS) (l : list (mon_ob M)) :
  mon_fun (Mon_evaluate M) l = free_mon_extend (fun x => x) l := eq_refl.

Example Mon_canonical_desc_fun@{+} (M : MonOS) {c : MonOS}
  (k : FreeMonSets (UMonOS M) ~{MonOS}~> c)
  (Hk : k ∘ Mon_flatten M ≈ k ∘ Mon_free_evaluate M) (x : mon_ob M) :
  mon_fun (unique_obj (coeq_desc (Mon_canonical_presentation M) k Hk)) x
    = mon_fun k (word1 x) := eq_refl.

Example Mon_canonical_split_obj@{+} (M : MonOS) :
  scoeq_obj (Mon_canonical_split M) = UMonOS M := eq_refl.

Example Mon_canonical_split_e@{+} (M : MonOS) :
  scoeq_e (Mon_canonical_split M) = fmap[UMonOS] (Mon_evaluate M) := eq_refl.

Example Mon_canonical_split_s@{+} (M : MonOS) :
  scoeq_s (Mon_canonical_split M) = free_mon_insert (UMonOS M) := eq_refl.

Example Mon_canonical_split_t@{+} (M : MonOS) :
  scoeq_t (Mon_canonical_split M)
    = free_mon_insert (UMonOS (FreeMonSets (UMonOS M))) := eq_refl.

End MonPresentation.
