Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(** * Equivalences preserve, reflect, and create limits / * 等价关系保留、反映并创造界限 *)

(*
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/preserved+limit
   nLab: https://ncatlab.org/nlab/show/reflected+limit
   nLab: https://ncatlab.org/nlab/show/created+limit

   An equivalence of categories (Theory/Equivalence.v) interacts with
   limits in every way one could ask: it preserves them, reflects them,
   and carries any limit of a composite diagram F ◯ G back to a limit of
   G.  This file proves the three statements, and their colimit duals,
   packaged in the preservation vocabulary of
   Structure/Limit/Preservation.v.

   - Preservation ([equivalence_preserves_limits]) is adjoint continuity:
     refining E : EquivalenceOfCategories F to an adjoint equivalence
     (Theory/Equivalence/Adjoint.v) and swapping its two sides exhibits F
     as a right adjoint — quasi_inverse ⊣ F — so RAPL
     (Adjunction/Continuity.v) applies.  Dually, F is the left adjoint of
     F ⊣ quasi_inverse, so LAPC makes it preserve all colimits as well
     ([equivalence_preserves_colimits]).

   - Reflection ([equivalence_reflects_limits]) needs only that F is full
     and faithful, so it is proved in that generality first
     ([ff_reflects_limit]): when the image of a cone N under F underlies
     a limit of F ◯ G, the cone N itself is a limit of G.  "The image of
     N is a limit" is stated as an apex-pinned witness
     [IsALimit (F ◯ G) (F (vertex_obj[N]))] together with the family
     identifying its legs with the image legs [fmap[F] (cone_leg N x)]
     (an arbitrary witness at the image apex says nothing about the legs
     of N, so the family is part of the hypothesis).  The mediating
     morphism in C is the [prefmap]-preimage of the mediator in D, and
     both of its laws are recovered from faithfulness — apply [fmap_inj],
     push [fmap[F]] through with [fmap_sur], and conclude among the
     images — since [prefmap] itself carries no functoriality (the issue
     #118 note in Theory/Functor.v).  The same technique gives
     [ff_reflects_isos] and [equivalence_reflects_isos], witnesses for
     the conservative-functor class [ReflectsIsos] of
     Structure/Limit/Preservation.v.  Since #481 the colimit half for a
     functor that is only full and faithful is [ff_reflects_colimit],
     and both halves are stated at cone level as well
     ([ff_ReflectsLimitCone], [ff_ReflectsColimitCocone]): Riehl's Lemma
     3.4.5.

   - Creation ([equivalence_creates_limits]) takes any limit of F ◯ G to
     a limit of G itself: the quasi-inverse is a right adjoint
     (F ⊣ quasi_inverse), so RAPL gives a limit of
     quasi_inverse ◯ (F ◯ G), which the unit cell identifies with G —
     the composite natural isomorphism [equivalence_diagram_iso] — and
     naturally isomorphic diagrams have the same limits: the iso-of-cones
     transport [limit_transport], proved here in full generality
     ([isalimit_transport]/[limit_transport], with the cone conjugates
     [cone_transport]/[cone_transport_inv]).  This produces, for every
     limit in D of the composite diagram, an actual limit in C of the
     original diagram; combined with preservation and reflection it is
     the practical content of "equivalences create limits".

   The colimit statements ride the opposite category, never a second
   proof: a cocone is a cone over the opposite diagram, [IsAColimit] is
   [IsALimit] of the opposite diagram, and F^op is an equivalence
   whenever F is ([EquivalenceOfCategories_op], whose two cells are the
   pointwise opposites of the cells of E).  The only friction is that
   (F ◯ G)^op and F^op ◯ G^op are distinct functor records sharing their
   object and morphism maps, so apex-pinned witnesses are repackaged
   field by field ([isalimit_op_comp], following the precedent of
   [preserves_colimit] in Structure/Limit/Preservation.v).

   Following Theory/Equivalence.v, nothing in this file is registered
   for instance resolution: quasi-inverses, preservation witnesses and
   reflection witnesses are choices, always passed explicitly at use
   sites.

--------
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
nLab: https://ncatlab.org/nlab/show/preserved+limit
nLab: https://ncatlab.org/nlab/show/reflected+limit
nLab: https://ncatlab.org/nlab/show/created+limit

范畴的等价（Theory/Equivalence.v）与极限在各方面都有交互：它保留极限，反映极限，并将复合图 F ◯ G 的任意极限带回 G 的极限。该文件证明了这三个陈述及其余极对偶，并以 Structure/Limit/Preservation.v 的保留词汇进行打包。

- 保持性（[equivalence_preserves_limits]）是伴随连续性：  
     将 E: EquivalenceOfCategories F 精炼为伴随等价  
     （Theory/Equivalence/Adjoint.v），并交换它的两边显示 F  
     作为一个右伴随 —— quasi_inverse ⊣ F —— 因此 RAPL  
     （Adjunction/Continuity.v）适用。 对偶地，F 是  
     F ⊣ quasi_inverse 的左伴随，因此 LAPC 使它也保持所有余极限  
     （[equivalence_preserves_colimits]）。

- 反射 ([equivalence_reflects_limits]) 只需要 F 是满且忠实的，因此首先在这一普遍性下证明 ([ff_reflects_limit])：当一个锥 N 在 F 下的像是 F ◯ G 的极限时，锥 N 本身就是 G 的极限。‘N 的像是极限’被陈述为顶点固定的见证 [IsALimit (F ◯ G) (F (vertex_obj[N]))，并且还有将其腿与像的腿对应的族 [fmap[F] (cone_leg N x)]（在像顶点任意的见证对 N 的腿没有信息，因此该族是假设的一部分）。C 中的中介态射是 D 中中介态射的 [prefmap]-原像，并且它的两个规律都可以从忠实性中恢复 — 应用 [fmap_inj]，用 [fmap_sur] 推动 [fmap[F]] 并在像中得出结论 — 由于 [prefmap] 本身不具有函子性（参见 Theory/Functor.v 中的第 118 个问题注释）。
同样的技术给出了 [ff_reflects_isos] 和 [equivalence_reflects_isos]，它们是 Structure/Limit/Preservation.v 中保守函子类 [ReflectsIsos] 的证人。自 #481 起，对于一个仅满且忠实的函子，其余极半为 [ff_reflects_colimit]，并且在锥层面上也陈述了两半（[ff_ReflectsLimitCone], [ff_ReflectsColimitCocone]）：Riehl 的引理 3.4.5。

- 创建（[equivalence_creates_limits]）将 F ◯ G 的任何极限带到 G 本身的极限：拟逆是右伴随（F ⊣ 拟逆），因此 RAPL 给出拟逆 ◯ (F ◯ G) 的极限，单位单元将其识别为 G — 复合自然同构 [equivalence_diagram_iso] — 自然同构的图具有相同的极限：圆锥同构传递 [limit_transport]，这里在完全一般性下证明（[isalimit_transport]/[limit_transport]，带有圆锥共轭 [cone_transport]/[cone_transport_inv]）。这为复合图在 D 中的每个极限生成了原始图在 C 中的实际极限；结合保持性和反射性，它是“等价抽象生成极限”的实用内容。

余极限的陈述作用于对偶范畴，从不需要第二个证明：余锥是对偶图上的锥，[IsAColimit] 是对偶图的 [IsALimit]，并且每当 F 是等价时，F^op 也是等价的（[EquivalenceOfCategories_op]，其两个单元是 E 的单元的逐点对偶）。唯一的摩擦是 (F ◯ G)^op 和 F^op ◯ G^op 是不同的函子记录，但它们共享对象和态射映射，因此顶点固定的证据需要逐字段重新打包 ([isalimit_op_comp]，遵循 Structure/Limit/Preservation.v 中 [preserves_colimit] 的先例)。

根据 Theory/Equivalence.v，本文件中没有任何内容被注册用于实例解析：准逆、保持证明和反射证明都是选项，总是在使用时显式传递。
*)

(** ** Additions to the covariant accessor toolkit / ** 协变访问工具包的补充 *)

(*
Coherence of [cone_leg], the first-class leg accessor of
   Structure/Limit/Preservation.v (which provides the analogous
   [limit_leg_coherence] only for apex-pinned limit witnesses).

--------
[cone_leg] 的相干性，它是 Structure/Limit/Preservation.v 的一流腿部访问器（该文件仅为顶点固定的极限证人提供类似的 [limit_leg_coherence]）。
*)

Lemma cone_leg_coherence {J C : Category} {F : J ⟶ C} (N : Cone F)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

(*
Rebundling an apex-pinned limit witness as a bundled [Limit]: the
   converse of [limit_is_alimit].  Purely a repackaging; the cone is the
   witness's own leg family over its pinned apex.

--------
将一个顶点固定的极限见证重新捆绑为一个捆绑的 [Limit]：这是 [limit_is_alimit] 的反向操作。纯粹是重新打包；锥体是该见证自身在其固定顶点上的腿系列。
*)

Definition isalimit_to_limit {J C : Category} {G : J ⟶ C} {c : C}
  (H : IsALimit G c) : Limit G :=
  @Build_Limit J C G
    (@Build_Cone J C G c (@limit_acone _ _ _ _ H))
    (@ump_limit _ _ _ _ H).

(** ** Transport of limits along a natural isomorphism of diagrams / ** 沿着图的自然同构的极限传输 *)

(*
Naturally isomorphic diagrams have the same cones and the same limits.
   Given e : G ≈ G' (which, for [Functor_Setoid], is a bundled natural
   isomorphism), a cone over G becomes a cone over G' by composing each
   leg with the componentwise isomorphism, and conversely; an apex-pinned
   limit witness follows, with the same apex.  This is the iso-of-cones
   step of limit creation below, but it is stated in full generality
   because nothing about it is specific to equivalences.

--------
自然同构的图具有相同的锥和相同的极限。给定 e : G ≈ G'（对于 [Functor_Setoid]，这是一个捆绑的自然同构），通过将每条边与分量层面的同构组合，一个关于 G 的锥就变为关于 G' 的锥，反之亦然；一个以顶点固定的极限见证也随之而来，顶点不变。这是下文极限创建中的锥同构（iso-of-cones）步骤，但这里以完全一般的形式陈述，因为它与等价性没有特定关系。
*)

Section DiagramIso.

Context {J : Category}.
Context {C : Category}.
Context {G G' : J ⟶ C}.
Context (e : G ≈ G').

(*
Push a cone over G across e: compose each leg with the forward
   component of the isomorphism family.

--------
将圆锥沿 e 推过 G：将每条边与同构族的前向分量组合。
*)

Definition cone_transport_leg (N : Cone G) (x : J) :
  vertex_obj[N] ~{C}~> G' x :=
  to (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_coherence (N : Cone G) {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ cone_transport_leg N x ≈ cone_transport_leg N y.
Proof using e.
  unfold cone_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport (N : Cone G) : Cone G' :=
  @Build_Cone J C G' (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G' (cone_transport_leg N)
       (fun x y f => cone_transport_coherence N f)).

(*
Pull a cone over G' back across e: compose each leg with the inverse
   component of the isomorphism family.

--------
把一个圆锥拉到 G' 的背面穿过 e：将每条边与同构族的逆分量组合起来。
*)

Definition cone_transport_inv_leg (N : Cone G') (x : J) :
  vertex_obj[N] ~{C}~> G x :=
  from (`1 e x) ∘ cone_leg N x.

Lemma cone_transport_inv_coherence (N : Cone G') {x y : J}
  (f : x ~{J}~> y) :
  fmap[G] f ∘ cone_transport_inv_leg N x ≈ cone_transport_inv_leg N y.
Proof using e.
  unfold cone_transport_inv_leg.
  rewrite comp_assoc.
  rewrite (fun_equiv_fmap_from e x y f).
  rewrite <- comp_assoc.
  now rewrite (cone_leg_coherence N f).
Qed.

Definition cone_transport_inv (N : Cone G') : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (cone_transport_inv_leg N)
       (fun x y f => cone_transport_inv_coherence N f)).

(* The legs of the pulled-back cone, in rewriting-friendly form. / 向后的圆锥的边，用便于改写的形式。 *)

Lemma cone_transport_inv_leg_eq (N : Cone G') (x : J) :
  cone_leg (cone_transport_inv N) x ≈ from (`1 e x) ∘ cone_leg N x.
Proof. reflexivity. Qed.

(** *** Transporting an apex-pinned limit witness / *** 运输顶点固定的极限见证者 *)

Section TransportWitness.

Context {c : C}.
Context (HL : IsALimit G c).

Definition isalimit_transport_leg (x : J) : c ~{C}~> G' x :=
  to (`1 e x) ∘ limit_leg HL x.

Lemma isalimit_transport_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[G'] f ∘ isalimit_transport_leg x ≈ isalimit_transport_leg y.
Proof using e HL.
  unfold isalimit_transport_leg.
  rewrite comp_assoc.
  rewrite <- (fun_equiv_to_fmap e x y f).
  rewrite <- comp_assoc.
  now rewrite (limit_leg_coherence HL f).
Qed.

Definition isalimit_transport_acone : ACone c G' :=
  @Build_ACone J C c G' isalimit_transport_leg
    (fun x y f => isalimit_transport_coherence f).

(*
Mediate a competing cone over G' by pulling it back across e and
   mediating through the limit of G; the apexes are untouched, so the
   mediator needs no adjustment at all.

--------
通过将竞争圆锥沿 e 拖回 G' 来调解它，并通过 G 的极限进行调解；顶点保持不变，因此调解者不需要任何调整。
*)

Definition isalimit_transport_med (N : Cone G') :
  vertex_obj[N] ~{C}~> c :=
  limit_med HL (cone_transport_inv N).

Lemma isalimit_transport_med_commutes (N : Cone G') :
  ∀ x : J, isalimit_transport_leg x ∘ isalimit_transport_med N
             ≈ cone_leg N x.
Proof using e HL.
  intro x.
  unfold isalimit_transport_leg, isalimit_transport_med.
  rewrite <- comp_assoc.
  rewrite (limit_med_commutes HL (cone_transport_inv N) x).
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma isalimit_transport_med_unique (N : Cone G')
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, isalimit_transport_leg x ∘ v ≈ cone_leg N x) →
  isalimit_transport_med N ≈ v.
Proof using e HL.
  intro Hv.
  unfold isalimit_transport_med.
  apply (limit_med_unique HL (cone_transport_inv N) v).
  intro x.
  rewrite (cone_transport_inv_leg_eq N x).
  rewrite <- (Hv x).
  unfold isalimit_transport_leg.
  rewrite !comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Definition isalimit_transport_ump (N : Cone G') :
  ∃! u : vertex_obj[N] ~{C}~> c,
    ∀ x : J, isalimit_transport_leg x ∘ u ≈ cone_leg N x :=
  Build_Unique _ _ _ (isalimit_transport_med N)
    (isalimit_transport_med_commutes N)
    (isalimit_transport_med_unique N).

Definition isalimit_transport : IsALimit G' c :=
  @Build_IsALimit J C G' c isalimit_transport_acone isalimit_transport_ump.

End TransportWitness.

(*
The bundled form: naturally isomorphic diagrams have the same limits,
   with the same apex.

--------
捆绑形式：自然同构的图具有相同的极限，并且具有相同的顶点。
*)

Definition limit_transport (L : Limit G) : Limit G' :=
  isalimit_to_limit (isalimit_transport (limit_is_alimit L)).

End DiagramIso.

(** ** The image of a cone under a functor / ** 函子下的圆锥的图像 *)

(** ** Fully faithful functors reflect isomorphisms and limits / ** 全忠实函子反映同构和极限 *)

Section FullyFaithful.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{HF : @Full C D F}.
Context `{HfF : @Faithful C D F}.

(*
A full and faithful functor is conservative: the chosen inverse of f
   is the [prefmap]-preimage of the inverse of fmap[F] f, and its two
   inverse laws are recovered from faithfulness.

--------
一个满且忠实的函子是保守的：所选择的 f 的逆是 fmap f 的逆的 [prefmap]-原像，并且它的两个逆律是从忠实性中恢复的。
*)

Definition ff_iso_inverse {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) : y ~{C}~> x :=
  prefmap (@two_sided_inverse D _ _ _ I).

Lemma ff_iso_inverse_right {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  f ∘ ff_iso_inverse f I ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_right_inverse D _ _ _ I).
Qed.

Lemma ff_iso_inverse_left {x y : C} (f : x ~{C}~> y)
  (I : IsIsomorphism (fmap[F] f)) :
  ff_iso_inverse f I ∘ f ≈ id.
Proof using HF HfF.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_iso_inverse.
  rewrite fmap_sur, fmap_id.
  exact (@is_left_inverse D _ _ _ I).
Qed.

Definition ff_reflects_isos : ReflectsIsos F :=
  @Build_ReflectsIsos C D F
    (fun x y f I =>
       @Build_IsIsomorphism C x y f (ff_iso_inverse f I)
         (ff_iso_inverse_right f I)
         (ff_iso_inverse_left f I)).

(** *** Reflection of limits / *** 极限的反思 *)

Section ReflectLimit.

Context {J : Category}.
Context {G : J ⟶ C}.
Context (N : Cone G).
Context (HL : IsALimit (F ◯ G) (F (vertex_obj[N]))).
Context (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)).

(*
Mediate a competing cone M over G: take the image of M, mediate in D
   through the hypothesized limit, and choose an [fmap]-preimage of the
   mediator with [prefmap].

--------
在 G 上调解一个竞争的锥 M：取 M 的像，通过假设的极限在 D 中调解，并选择调解器的一个 [fmap] 原像，并使用 [prefmap]。
*)

Definition ff_reflect_med (M : Cone G) :
  vertex_obj[M] ~{C}~> vertex_obj[N] :=
  prefmap (limit_med HL (FCone F M)).

Lemma ff_reflect_med_commutes (M : Cone G) :
  ∀ x : J, cone_leg N x ∘ ff_reflect_med M ≈ cone_leg M x.
Proof using HF HfF HL Hlegs.
  intro x.
  apply fmap_inj.
  rewrite fmap_comp.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  rewrite <- (Hlegs x).
  rewrite (limit_med_commutes HL (FCone F M) x).
  exact (FCone_leg F M x).
Qed.

Lemma ff_reflect_med_unique (M : Cone G)
  (v : vertex_obj[M] ~{C}~> vertex_obj[N]) :
  (∀ x : J, cone_leg N x ∘ v ≈ cone_leg M x) →
  ff_reflect_med M ≈ v.
Proof using HF HfF HL Hlegs.
  intro Hv.
  apply fmap_inj.
  unfold ff_reflect_med.
  rewrite fmap_sur.
  apply (limit_med_unique HL (FCone F M) (fmap[F] v)).
  intro x.
  rewrite (FCone_leg F M x).
  rewrite (Hlegs x).
  rewrite <- (Hv x).
  rewrite fmap_comp.
  reflexivity.
Qed.

Definition ff_reflect_ump (M : Cone G) :
  ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x :=
  Build_Unique _ _ _ (ff_reflect_med M)
    (ff_reflect_med_commutes M)
    (ff_reflect_med_unique M).

(*
Full + faithful functors reflect limits: the cone N, with its own leg
   family, is a limit of G.

--------
完全且忠实的函子会反映极限：锥 N，带有它自己的边族，是 G 的一个极限。
*)

Definition ff_reflects_limit : IsALimit G (vertex_obj[N]) :=
  @Build_IsALimit J C G (vertex_obj[N]) (@coneFrom _ _ _ N) ff_reflect_ump.

End ReflectLimit.

End FullyFaithful.

(*
Riehl's Lemma 3.4.5 (#481): a full and faithful functor reflects the
   limits and the colimits present in its codomain.  In the cone-level
   vocabulary of Structure/Limit/Preservation.v the limit half is
   [ff_reflect_ump] with its leg side condition discharged by
   [reflexivity], the legs of [FCone] being the image legs: the term that
   Theory/Equivalence/Creation.v's [equivalence_ReflectsLimitCone],
   Construction/Subcategory/Creation.v's [sub_ReflectsLimitCone] and
   Construction/Reflective/Limit.v's [reflective_ReflectsLimitCone] each
   wrote out at its own functor, and which each now calls (a CORRECTION
   (#481) at each).  The colimit halves ride the opposite
   functor, full and faithful by Functor/Opposite.v's [Full_op] and
   [Faithful_op] (#266): [ff_reflects_colimit] in the apex-pinned form of
   [ff_reflects_limit], with the injections of the image colimit as the
   side condition, and [ff_ReflectsColimitCocone] at cone level, the image
   cocone over (F ◯ K)^op read over F^op ◯ K^op by Preservation.v's
   [islimitcone_op_comp].

--------
Riehl 的引理 3.4.5 (#481)：一个充满且忠实的函子会反映其余域中存在的极限和余极限。在 Structure/Limit/Preservation.v 的锥层词汇中，极限部分是 [ff_reflect_ump]，其顶点侧条件由 [reflexivity] 解除，[FCone] 的各条边是像边：Theory/Equivalence/Creation.v 的 [equivalence_ReflectsLimitCone]、Construction/Subcategory/Creation.v 的 [sub_ReflectsLimitCone] 和 Construction/Reflective/Limit.v 的 [reflective_ReflectsLimitCone] 每个都在各自的函子上写出该术语，每个现在都称之为（每个的修正 (#481)）。余极限部分沿着相对函子运行，根据 Functor/Opposite.v 的 [Full_op] 和 [Faithful_op] (#266) 是充满且忠实的：[ff_reflects_colimit] 以 [ff_reflects_limit] 的顶点固定形式出现，像余极限的嵌入作为边条件，以及锥层的 [ff_ReflectsColimitCocone]，是 Preservation.v 的 [islimitcone_op_comp] 所读的 F^op ◯ K^op 上 (F ◯ K)^op 的像余锥。
*)

Definition ff_ReflectsLimitCone {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} (K : J ⟶ C) :
  ReflectsLimitCone K F :=
  fun N H =>
    @ff_reflect_ump C D F HF HfF J K N (limitcone_isalimit H)
      (fun x => reflexivity _).

Definition ff_reflects_colimit {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} {G : J ⟶ C}
  (N : Cocone G)
  (HL : IsAColimit (F ◯ G) (F (vertex_obj[N])))
  (Hinjs : ∀ x : J, colimit_inj HL x ≈ fmap[F] (cocone_inj N x)) :
  IsAColimit G (vertex_obj[N]) :=
  @ff_reflects_limit (C^op) (D^op) (F^op) (Full_op HF) (Faithful_op HfF)
    (J^op) (G^op) N (isalimit_op_comp HL) (fun x => Hinjs x).

Definition ff_ReflectsColimitCocone {C D : Category} {F : C ⟶ D}
  `{HF : @Full C D F} `{HfF : @Faithful C D F} {J : Category} (K : J ⟶ C) :
  ReflectsColimitCocone K F :=
  fun N H =>
    @ff_ReflectsLimitCone (C^op) (D^op) (F^op) (Full_op HF) (Faithful_op HfF)
      (J^op) (K^op) N (islimitcone_op_comp H).

(** ** Equivalences and limits / ** 等价与极限 *)

Section EquivalenceLimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(** *** Preservation / *** 保存 *)

(*
Swapping the adjoint equivalence refined from E exhibits F as a right
   adjoint (quasi_inverse ⊣ F); RAPL concludes.

--------
将从 E 提炼出的伴随等价交换出来，展示 F 作为右伴随（quasi_inverse ⊣ F）；RAPL 得出结论。
*)

Definition equivalence_preserves_limits : PreservesAllLimits F :=
  right_adjoint_preserves_limits
    (AdjointEquivalence_swap_adjunction
       (Equivalence_to_AdjointEquivalence E)).

Definition equivalence_preserves_limit {J : Category} (G : J ⟶ C) :
  PreservesLimit G F :=
  equivalence_preserves_limits J G.

(* Dually, F is the left adjoint of F ⊣ quasi_inverse; LAPC concludes. / 同样地，F 是 F ⊣ quasi_inverse 的左伴随；LAPC 结束。 *)

Definition equivalence_preserves_colimits : PreservesAllColimits F :=
  left_adjoint_preserves_colimits (equiv_adjunction E).

Definition equivalence_preserves_colimit {J : Category} (G : J ⟶ C) :
  PreservesColimit G F :=
  equivalence_preserves_colimits J G.

(* Bundled forms of the preserved (co)limits. / 保留（共）极限的捆绑形式。 *)

Definition equivalence_preserved_limit {J : Category} (G : J ⟶ C)
  (L : Limit G) : Limit (F ◯ G) :=
  isalimit_to_limit
    (@preserves_limit J C G D F (equivalence_preserves_limit G) L).

Definition equivalence_preserved_colimit {J : Category} (G : J ⟶ C)
  (L : Colimit G) : Colimit (F ◯ G) :=
  isalimit_to_limit
    (preserves_colimit (equivalence_preserves_colimit G) L).

(** *** Reflection / *** 反思 *)

(*
Equivalences are full and faithful (Theory/Equivalence/FullFaithful.v),
   so the fully-faithful reflection results specialize.

--------
等价是完全且忠实的（Theory/Equivalence/FullFaithful.v），所以完全忠实反射结果是特化的。
*)

Definition equivalence_reflects_isos : ReflectsIsos F :=
  ff_reflects_isos
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E).

Definition equivalence_reflects_limits {J : Category} {G : J ⟶ C}
  (N : Cone G)
  (HL : IsALimit (F ◯ G) (F (vertex_obj[N])))
  (Hlegs : ∀ x : J, limit_leg HL x ≈ fmap[F] (cone_leg N x)) :
  IsALimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full E) (HfF := Equivalence_Faithful E)
    N HL Hlegs.

(** *** Creation / *** 创造 *)

(*
The composite natural isomorphism quasi_inverse ◯ (F ◯ G) ≈ G:
   reassociate and cancel the unit cell.

--------
复合自然同构 quasi_inverse ◯ (F ◯ G) ≈ G：重新结合并消去单位元。
*)

Definition equivalence_diagram_iso {J : Category} (G : J ⟶ C) :
  @quasi_inverse C D F E ◯ (F ◯ G) ≈ G.
Proof.
  rewrite (fun_equiv_comp_assoc (@quasi_inverse C D F E) F G).
  rewrite <- (@equivalence_unit C D F E).
  exact (fun_equiv_id_left G).
Defined.

(*
Any limit of F ◯ G is carried back to a limit of G: the quasi-inverse
   (a right adjoint) preserves it, and the diagram isomorphism above
   transports the result from quasi_inverse ◯ (F ◯ G) to G.

--------
F ◯ G 的任何极限都会被传回到 G 的极限：拟逆（一个右伴随）会保持它，并且上面的图同构将结果从拟逆 ◯ (F ◯ G) 传递到 G。
*)

Definition equivalence_creates_limits {J : Category} (G : J ⟶ C)
  (L : Limit (F ◯ G)) : Limit G :=
  limit_transport (equivalence_diagram_iso G)
    (rapl_limit (equiv_adjunction E) (F ◯ G) L).

End EquivalenceLimit.

(** ** The opposite of an equivalence of categories / ** 范畴等价的相反 *)

(*
F^op is an equivalence whenever F is: the two cells of E dualize
   pointwise, their isomorphism families running through
   [Isomorphism_Opposite] and their conjugation coherences being those of
   E read at the reversed morphism (composition in the opposite category
   unfolds to reversed composition, so only a reassociation separates the
   two statements).

--------
每当 F 是等价时，F^op 也是等价的：E 的两个单元在点上对偶，其同构族遍历 [Isomorphism_Opposite]，并且它们的共轭相干性是将 E 在反向态射下读出的相干性（在对偶范畴中的复合展开为反向复合，因此只需重新关联即可区分这两个陈述）。
*)

Definition equivalence_counit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  F^op ◯ (@quasi_inverse C D F E)^op ≈ Id[D^op].
Proof.
  exists (fun d =>
            Isomorphism_Opposite (`1 (@equivalence_counit C D F E) d)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_counit C D F E) y x f).
Defined.

Definition equivalence_unit_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  Id[C^op] ≈ (@quasi_inverse C D F E)^op ◯ F^op.
Proof.
  exists (fun x =>
            Isomorphism_Opposite (`1 (@equivalence_unit C D F E) x)).
  intros x y f; simpl.
  rewrite comp_assoc.
  exact (`2 (@equivalence_unit C D F E) y x f).
Defined.

Definition EquivalenceOfCategories_op {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) :
  @EquivalenceOfCategories (C^op) (D^op) (F^op) :=
  @Build_EquivalenceOfCategories (C^op) (D^op) (F^op)
    ((@quasi_inverse C D F E)^op)
    (equivalence_counit_op E)
    (equivalence_unit_op E).

(** ** Equivalences and colimits, by op / ** 等价和余极限，经 op *)

Section EquivalenceColimit.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(*
Reflection of colimits: a cocone over G is a cone over G^op, an
   [IsAColimit] witness is an [IsALimit] witness over the opposite
   composite, and F^op is full and faithful because it is an equivalence
   ([EquivalenceOfCategories_op]).  The injection families translate
   definitionally.

--------
余极限的反映：G 上的余锥是 G^op 上的锥，[IsAColimit] 证据是在相反复合上的 [IsALimit] 证据，并且 F^op 是满且忠实的，因为它是一个等价 ([EquivalenceOfCategories_op])。注入族在定义上是可转化的。
*)

Definition equivalence_reflects_colimits {J : Category} {G : J ⟶ C}
  (N : Cocone G)
  (HL : IsAColimit (F ◯ G) (F (vertex_obj[N])))
  (Hinjs : ∀ x : J, colimit_inj HL x ≈ fmap[F] (cocone_inj N x)) :
  IsAColimit G (vertex_obj[N]) :=
  ff_reflects_limit
    (HF := Equivalence_Full (EquivalenceOfCategories_op E))
    (HfF := Equivalence_Faithful (EquivalenceOfCategories_op E))
    N (isalimit_op_comp HL)
    (fun x => Hinjs x).

(*
Creation of colimits: repackage the given colimit as a limit of
   F^op ◯ G^op and create through the opposite equivalence.

--------
余极限的创建：将给定的余极限重新包装为 F^op ◯ G^op 的极限，并通过对偶等价来创建。
*)

Definition equivalence_creates_colimits {J : Category} (G : J ⟶ C)
  (L : Colimit (F ◯ G)) : Colimit G :=
  equivalence_creates_limits (EquivalenceOfCategories_op E) (G^op)
    (isalimit_to_limit (isalimit_op_comp (limit_is_alimit L))).

End EquivalenceColimit.
