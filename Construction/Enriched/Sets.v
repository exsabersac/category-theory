Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EnrichedSetsTransform.

Context {C D : Category}.
Context (F G : C ⟶ D).

(* The enriched 函子 corresponding ordinary 函子 F G, via
 [Category → Enriched] / [(C ⟶ D) → EnrichedFunctor] halves two
 companion equivalences. （已译） *)
Definition EF : EnrichedFunctor Sets
                  (snd Category_is_Enriched_over_Set C)
                  (snd Category_is_Enriched_over_Set D) :=
  snd (Functor_is_Enriched_over_Set C D) F.

Definition EG : EnrichedFunctor Sets
                  (snd Category_is_Enriched_over_Set C)
                  (snd Category_is_Enriched_over_Set D) :=
  snd (Functor_is_Enriched_over_Set C D) G.

Theorem EnrichedTransform_is_Transform :
  @EnrichedTransform Sets Sets_Product_Monoidal _ _ EF EG ↔ (F ⟹ G).
Proof.
  split; intros X.
  - (* Forward: read each enriched component at [ttt] ordinary component,
 derive ordinary 自然性 enriched 自然性. （已译） *)
    apply (Build_Transform' (fun x => @etransform _ _ _ _ EF EG X x ttt)).
    intros x y f.
    (* Enriched naturality at [x], [y], evaluated at [f], unfolds in Sets to the
       [naturality_sym] orientation; take its symmetry. *)
    symmetry.
    exact (@enaturality _ _ _ _ EF EG X x y f).
  - (* Backward: package each ordinary component 常值 setoid map out of
 singleton, derive enriched 自然性 ordinary 自然性. （已译） *)
    unshelve refine
      (@Build_EnrichedTransform
         Sets Sets_Product_Monoidal
         (snd Category_is_Enriched_over_Set C)
         (snd Category_is_Enriched_over_Set D)
         EF EG
         (fun x => {| morphism := fun _ => @transform _ _ F G X x |}) _).
    + proper.
    + intros x y f.
      (* The enriched 自然性 square Sets reduces pointwise the
 [naturality_sym] orientation ordinary 自然性 square. （已译） *)
      exact (@naturality_sym _ _ F G X x y f).
Defined.

End EnrichedSetsTransform.
