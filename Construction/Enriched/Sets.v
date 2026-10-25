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
   * V = Sets recovers ordinary category theory, at the transformation level.

   The companion theorems [Category_is_Enriched_over_Set] and
   [Functor_is_Enriched_over_Set] (in Construction/Enriched.v) show that a
   Sets-enriched category is an ordinary category and that a Sets-enriched
   functor is an ordinary functor.  This file completes the picture for the
   third leg: a Sets-enriched natural transformation between the enriched
   functors [EF], [EG] corresponding to ordinary functors [F], [G] is the same
   data as an ordinary natural transformation [F ⟹ G].

   In Sets the tensor unit is the singleton [I = {| carrier := poly_unit |}],
   so an enriched component [etransform x : I ~{Sets}~> ehom D (F x) (G x)] is a
   setoid map [poly_unit → (F x ~> G x)]; its value at [ttt] is an ordinary
   component [F x ~> G x].  Unfolding the enriched naturality square in Sets and
   evaluating at [f : x ~> y] gives exactly the ordinary naturality equation
   [etransform y ttt ∘ fmap[F] f ≈ fmap[G] f ∘ etransform x ttt] (the
   [naturality_sym] orientation, up to the left/right unitor plumbing). 

   --------
   * V = 集合 恢复了普通范畴论，在变换层面。

   伴随定理 [Category_is_Enriched_over_Set] 和 [Functor_is_Enriched_over_Set]（在 Construction/Enriched.v 中）表明一个集合增强范畴是一个普通范畴，集合增强函子是一个普通函子。这个文件完成了第三个部分的图景：集合增强函子 [EF] 和 [EG] 之间的集合增强自然变换，对应于普通函子 [F] 和 [G]，与普通自然变换 [F ⟹ G] 的数据是相同的。在集合中，张量单位是单元素集 [I = {| carrier := poly_unit |}]，因此一个加丰富的分量 [etransform x : I ~{Sets}~> ehom D (F x) (G x)] 是一个集合等价映射 [poly_unit → (F x ~> G x)]；它在 [ttt] 处的值是一个普通分量 [F x ~> G x]。在集合中展开加丰富的自然性方格并在 [f : x ~> y] 处求值，恰好得到普通的自然性方程 [etransform y ttt ∘ fmap[F] f ≈ fmap [G] f ∘ etransform x ttt]（[naturality_sym] 的方向，至左/右单子连接器的调整）。
*)

Section EnrichedSetsTransform.

Context {C D : Category}.
Context (F G : C ⟶ D).

(*
 The enriched functors corresponding to the ordinary functors F and G, via
 the [Category → Enriched] / [(C ⟶ D) → EnrichedFunctor] halves of the two
 companion equivalences. 

 --------
 通过两个伴随等价的 [Category → Enriched] / [(C ⟶ D) → EnrichedFunctor] 半部分，对应于普通函子 F 和 G 的加强函子。
*)
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
  - (* Forward: read each enriched component at [ttt] as an ordinary component, and derive ordinary naturality from enriched naturality. / 前向：将 [ttt] 处的每个增强组件作为普通组件来阅读，并从增强自然性中导出普通自然性。 *)
    apply (Build_Transform' (fun x => @etransform _ _ _ _ EF EG X x ttt)).
    intros x y f.
    (*
 Enriched naturality at [x], [y], evaluated at [f], unfolds in Sets to the
 [naturality_sym] orientation; take its symmetry. 

 --------
 在 [x] 、 [y] 增强的自然性，在 [f] 处评估，在集合中展开为 [naturality_sym] 方向；取其对称性。
*)
    symmetry.
    exact (@enaturality _ _ _ _ EF EG X x y f).
  - (* Backward: package each ordinary component as a constant setoid map out of the singleton, and derive enriched naturality from ordinary naturality. / 反向：将每个普通组件打包为从单元素集合映射出的常数等价类，并从普通自然性导出增强的自然性。 *)
    unshelve refine
      (@Build_EnrichedTransform
         Sets Sets_Product_Monoidal
         (snd Category_is_Enriched_over_Set C)
         (snd Category_is_Enriched_over_Set D)
         EF EG
         (fun x => {| morphism := fun _ => @transform _ _ F G X x |}) _).
    + proper.
    + intros x y f.
      (*
 The enriched naturality square in Sets reduces pointwise to the
 [naturality_sym] orientation of the ordinary naturality square. 

 --------
 集合中的丰富自然性方形在点上约化为普通自然性方形的 [naturality_sym] 取向。
*)
      exact (@naturality_sym _ _ F G X x y f).
Defined.

End EnrichedSetsTransform.
