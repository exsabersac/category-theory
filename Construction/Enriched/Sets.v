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

(* The enriched functors corresponding to the ordinary functors F and G, via
   the [Category → Enriched] / [(C ⟶ D) → EnrichedFunctor] halves of the two
   companion equivalences. *)
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
  - (* Forward: read each enriched component at [ttt] as an ordinary component,
       and derive ordinary naturality from enriched naturality. *)
    apply (Build_Transform' (fun x => @etransform _ _ _ _ EF EG X x ttt)).
    intros x y f.
    (* Enriched naturality at [x], [y], evaluated at [f], unfolds in Sets to the
       [naturality_sym] orientation; take its symmetry. *)
    symmetry.
    exact (@enaturality _ _ _ _ EF EG X x y f).
  - (* Backward: package each ordinary component as a constant setoid map out of
       the singleton, and derive enriched naturality from ordinary naturality. *)
    unshelve refine
      (@Build_EnrichedTransform
         Sets Sets_Product_Monoidal
         (snd Category_is_Enriched_over_Set C)
         (snd Category_is_Enriched_over_Set D)
         EF EG
         (fun x => {| morphism := fun _ => @transform _ _ F G X x |}) _).
    + proper.
    + intros x y f.
      (* The enriched naturality square in Sets reduces pointwise to the
         [naturality_sym] orientation of the ordinary naturality square. *)
      exact (@naturality_sym _ _ F G X x y f).
Defined.

End EnrichedSetsTransform.
