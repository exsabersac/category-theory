Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Traversable.
Require Import Category.Functor.Applicative.

Generalizable All Variables.

(** The pointwise product of traversable functors is traversable  / 可遍历函子的逐点乘积是可遍历的*)

(*
nLab:      https://ncatlab.org/nlab/show/distributive+law
   HaskellWiki: https://wiki.haskell.org/Foldable_and_Traversable
   Reference: Jaskelioff and Rypacek, "An Investigation of the Laws of
              Traversals", MSFP 2012 (https://arxiv.org/abs/1202.2919)

   Wikipedia: none-exists - there is no Wikipedia page for "traversable
   functor"; the closest published accounts are the HaskellWiki article and
   the arXiv reference above (see also Category.Functor.Traversable).

   Here [F :*: G] is the pointwise tensor product of two endofunctors, from
   Category.Functor.Product: [(F :*: G) x = F x ⨂ G x], where [⨂] is the
   monoidal tensor.  The monoidal structure in scope is [CC_Monoidal], the
   cartesian (internal-product) structure [⨂ = ×, I = 1] of the closed
   monoidal category [C].

   Lawful traversable endofunctors on [C] form a monoidal category under
   composition, with the identity functor as unit; this file records that the
   pointwise product also carries a traversal.  Given traversals [δ_F : F ◯ H
   ⟹ H ◯ F] and [δ_G : G ◯ H ⟹ H ◯ G], the composite traversal on [F :*: G]
   pairs the two component sequences and merges them through the applicative's
   tensor comparison [lax_ap[H] : H a ⨂ H b ~> H (a ⨂ b)]:

     δ_(F :*: G) X
       := lax_ap[H] ∘ bimap (transform[δ_F] X) (transform[δ_G] X)
                                : H (F X) ⨂ H (G X) ~> H (F X ⨂ G X).

   The naturality of this transformation is discharged below from the
   naturality of [ap_functor_nat] and of the two component sequences, axiom
   free.  The three Traversable coherence laws (naturality in the applicative,
   identity, and composition) are inherited from the components; assembling
   them into the full [Traversable (F :*: G)] instance remains in progress and
   is kept as commented scaffolding after the lemma below. 

--------
nLab：https://ncatlab.org/nlab/show/distributive+law
 HaskellWiki：https://wiki.haskell.org/Foldable_and_Traversable
 参考文献：Jaskelioff 和 Rypacek，“对法律的调查”
 遍历”，MSFP 2012 (https://arxiv.org/abs/1202.2919)

维基百科：不存在 - 没有“可遍历”的维基百科页面
 函子”； 最接近的已发布帐户是 HaskellWiki 文章和
 上面的 arXiv 参考（另请参阅 Category.Functor.Traversable）。

这里 [F :*: G] 是两个 endofunctor 的逐点张量积，来自
 Category.Functor.Product：[(F :*: G) x = F x ⨂ G x]，其中 [⨂] 是
 幺半群张量。 范围内的幺半群结构是 [CC_Monoidal]，
 封闭式笛卡尔（内积）结构 [⨂ = ×, I = 1]
 幺半群类别 [C]。

[C] 上的合法可遍历endofunctor 形成了一个幺半群范畴
 组合，以恒等函子为单位； 该文件记录了
 点乘积也带有遍历。 给定遍历 [δ_F : F ◯ H
 ⟹ H ◯ F]和[δ_G : G ◯ H ⟹ H ◯ G]，[F :*: G]上的复合遍历
 将两个组件序列配对并通过应用程序合并它们
 张量比较 [lax_ap[H] : H a ⨂ H b ~> H (a ⨂ b)]：

δ_(F:*:G) X
 := lax_ap[H] ∘ bimap (transform[δ_F] X) (transform[δ_G] X)
 : H (F X) ⨂ H (G X) ~> H (F X ⨂ G X)。

这种转变的自然性如下所示：
 [ap_functor_nat] 和两个组件序列的自然性，公理
 免费。 三个可遍历的连贯性法则（应用中的自然性，
 身份和组成）是从组件继承的； 组装
 它们进入完整的 [Traversable (F :*: G)] 实例仍在进行中，并且
 在下面的引理之后保留为注释脚手架。 
*)

Section ProductTraversable.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Existing Instance CC_Monoidal.

(*
The component of the composite traversal on [F :*: G], built from the two
   component sequences merged through [lax_ap[H]].  [transform] leaves three
   goals: the component map, then the [naturality] and [naturality_sym]
   conditions of a natural transformation (the latter two are dual, so the two
   proof blocks below are identical - this is the library's built-in-duality
   idiom, not duplication). 

--------
[F :*: G] 上复合遍历的组件，由两个构建
 通过 [lax_ap[H] 合并组件序列]。 [transform] 留下三个
 目标：组件图，然后是 [naturality] 和 [naturality_sym]
 自然变换的条件（后两者是对偶的，所以两者
 下面的证明块是相同的 - 这是库的内置对偶性
 习语，不重复）。 
*)
Lemma ProductFunctor_Traversable_ap_functor_nat :
  Traversable F → Traversable G
    → ∀ H : C ⟶ C, @Applicative _ _ H
    → (F :*: G) ◯ H ⟹ H ◯ (F :*: G).
Proof.
  intros O P ??.

  transform.
  - simpl.
    intro x.
    exact (lax_ap[H0] ∘ bimap (transform[@sequence _ _ _ O _ X] x)
                              (transform[@sequence _ _ _ P _ X] x)).
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X] _ _ f) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X] _ _ f) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X] _ _ f) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X] _ _ f) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
Defined.

(*
Work in progress: the full [Traversable (F :*: G)] instance.  The component
   above supplies [sequence]; what remains is to discharge the three coherence
   laws (sequence_naturality, sequence_Id, sequence_Compose) from those of the
   components.  [sequence_Id] is complete; the other two obligations still need
   the interaction of [lax_ap]/[ap_functor_nat] with the component sequences,
   so the definition is kept here as commented scaffolding rather than sealed
   with an unfinished proof.  Nothing in the library depends on it yet. 

--------
正在进行中的工作：完整的 [Traversable (F :*: G)] 实例。 组件
 以上供应 [sequence]； 剩下的就是释放三相干
 法则（sequence_naturality、sequence_Id、sequence_Compose）
 组件。 [sequence_Id] 已完成； 另外两项义务仍需
 [lax_ap]/[ap_functor_nat] 与组件序列的相互作用，
 因此定义保留在这里作为注释脚手架而不是密封的
 带着未完成的证明。 库中没有任何东西依赖于它。 
*)
(*
Program Definition ProductFunctor_Traversable :
  Traversable F → Traversable G
    → Traversable (F :*: G) := fun O P => {|
  sequence := ProductFunctor_Traversable_ap_functor_nat _ _;
  sequence_naturality  := _;
  sequence_Id  := _;
  sequence_Compose  := _
|}.
Next Obligation.
  pose proof (@sequence_naturality _ _ _ _ _ O G0 _ H3 _ _ f X) as X0.
  pose proof (@sequence_naturality _ _ _ _ _ P G0 _ H3 _ _ f X) as X1.
  repeat (unfold ap; simpl).
(*
  pose proof (naturality[@slm_transform _ _ _ _ _ _ _ _ f]).
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrites.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  (* This must be proven based on how slm_transform interacts with ap. *)
*)
Next Obligation.
  repeat (unfold ap; simpl).
  rewrite id_left.
  rewrite (@sequence_Id _ _ _ _ _ O), (@sequence_Id _ _ _ _ _ P).
  cat.
Qed.
(*
Next Obligation.
  repeat (unfold lax_ap; simpl).
  rewrite (@sequence_Compose _ _ _ _ _ O G0 H2 H3 H4 X),
          (@sequence_Compose _ _ _ _ _ P G0 H2 H3 H4 X).
  pose proof (naturality[@ap_functor_nat _ _ _ _ G0
                           (@is_lax_monoidal _ _ _ _ _ H2)]
                        (F (H3 X), G (H3 X))
                        (H3 (F X), H3 (G X))
                        (transform sequence X, transform sequence X)) as X3;
  simpl in *.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrites.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)
Next Obligation.
*)

End ProductTraversable.
