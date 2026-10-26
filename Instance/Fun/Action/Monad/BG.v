(* * * Riehl's Set^BG: evaluation is monadic, by the monadicity theorem / * * Riehl 的 Set^BG：评估是单值的，根据单值性定理 *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Group.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Fun.Action.Monad.

Generalizable All Variables.

(*
 Book: Riehl, “Category Theory in Context”, 2nd ed., Exercise
 5.5.iv, printed p. 208 (PDF p. 228) — riehl:5.5:exiv; with her
 Theorem 5.5.1, printed p. 202 (PDF p. 222), and Definition
 5.3.1, printed p. 196 (PDF p. 216)
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.2, “Group actions”, printed p. 141
 (PDF p. 150) — maclane:VI.2:remark2; and §VI.2 Exercise 3,
 printed p. 142 (PDF p. 151)
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem
 nLab: https://ncatlab.org/nlab/show/action

 Riehl's Exercise 5.5.iv gives, “For any group G”, the forgetful functor
 U : Set^BG → Set a left adjoint “that sends a set X to the G-set G × X,
 with G acting on the left”, and asks: “Prove that this adjunction is
 monadic by appealing to the monadicity theorem.”  Her Set^BG is the
 functor category [BG, Set], BG the one-object category of G, and U is
 evaluation at the one object.  Instance/Fun/Action/Monad.v proves the
 exercise at Instance/Fun/Action.v's category [MSet M] of actions, which
 [MSet_Fun_equiv] identifies with [Deloop M, Sets] in Cat; no lemma in the
 tree carries [Monadic] across such an identification, so this file states
 the exercise literally, on the functor category itself.  Every statement
 is over a monoid M, as there, since nothing below uses inverses.  The
 group instances are those of Instance/Fun/Action/Monad.v:
 [GSet_BG_Monadic] at Construction/Deloop.v's [GrpObject],
 [GSet_BG_Monadic_Grp] at Instance/Grp.v's, through Instance/Grp/Free.v's
 [grp_deloop_monoid], and [GSet_BG_Monadic_GroupObject] at
 Structure/Group.v's [GroupObject] in (Sets, ×), through Instance/Grp.v's
 [GroupObject_GrpObject], which needs [PropEquiv] of the carrier.  Both
 files that declare a [GrpObject] are imported, and each use is written
 with its full path.

 THE FUNCTOR CATEGORY AND ITS FORGETFUL FUNCTOR.  [SetBG M] is
 [Deloop M, Sets] with its hom level written out (UNIVERSES, below).
 [U_BG M] is Instance/Fun/Eval.v's [Eval] at the one object [ttt], and
 [F_BG M] is Instance/Fun/Action.v's [MSet_from] after the free M-set
 functor [MSet_Free] of Instance/Fun/Action/Monad.v: a setoid X goes to
 the functor whose value is M × X, acted on in the left factor.
 Evaluation agrees with [MSet_to] followed by [MSet_Forget] in both data
 fields at [eq_refl] ([U_BG_obj], [U_BG_map]), but not as a functor.

 THE ADJUNCTION.  [BG_adj : F_BG M ⊣ U_BG M] is built on hom-setoids by
 Theory/Adjunction.v's [Build_Adjunction'].  A transformation φ out of
 F X restricts to x ↦ φ (u, x) ([BG_restrict]); a map ψ : X → P ttt
 extends to (g, x) ↦ g · ψ x by Instance/Fun/Action/Monad.v's
 [MSet_extend], carried into the functor category by [MSet_from] and
 Instance/Fun/Action.v's round trip [MSet_round_iso] ([BG_extend]).

 CREATION, BY TRANSPORT.  By conversion, a split coequalizer of the
 U_BG-images of a pair p, q IS one of the [MSet_Forget]-images of
 [MSet_to p] and [MSet_to q], because [action_of_functor P] has carrier
 P ttt and action fmap[P].  So the creation of Instance/Fun/Action/
 Monad.v is used as it stands.  The created functor is [MSet_from] of
 its [CreatedAct]; the coequalizing transformation [BGCreatedE] has
 component e, and its naturality is [CreatedE]'s equivariance; the two
 clauses of the class are [CreatedE_is_coeq] and [Reflected_is_coeq]
 read back.  The one new lemma is [MSet_to_reflects_coeq]: a cofork of
 transformations whose [MSet_to]-image is a coequalizer of M-sets is a
 coequalizer of functors, a transformation out of the one object being
 one equivariant map.  The existence clause also passes through Monad/
 Monadicity/Beck.v's [coequalizer_along_iso], at Instance/Fun/Action.v's
 [MSet_action_round_iso].  No absorption lemma is proved again.  The
 lift is on the nose: its value is the split quotient Z, its action is
 g · z = e (g · s z), its arrow is e and its comparison isomorphism is
 the identity ([bg_created_carrier], [bg_created_action],
 [bg_created_arrow], [bg_created_iso]).

 MONADICITY.  [BG_beck_equivalence] is Beck.v's [beck_monadicity] at
 [BG_adj] and [U_BG_creates]; Instance/Fun/Action/Monad.v is the first
 use of that theorem in the tree, and this file the second.
 [U_BG_Monadic] packages it as Monad/Comparison.v's [Monadic].
 [U_BG_reflects] is Beck.v's [creates_split_reflects_isos] here: a
 transformation whose component at the one object is invertible in
 Sets is invertible.  [BG_EM_iso] is the isomorphism in Cat between
 [SetBG M] and the algebras of the induced monad [BGMonad M] (an
 isomorphism in Cat, inverse up to natural isomorphism, hence an
 equivalence), and its [to] leg IS the comparison functor
 ([BG_EM_iso_to]).

 TWO MONADS.  [BGMonad M] is Monad/Comparison.v's
 [Adjunction_Induced_Monad] at [BG_adj]; [ActMonad M] of
 Instance/Fun/Action/Monad.v is the same construction at the adjunction on
 [MSet M].  Their functors have the same object and arrow maps, M × X and
 M × f ([BG_T_obj], [BG_T_map]), and their multiplications agree at every
 p ([BG_join_ActMonad]); the two multiplications have the same underlying
 function, and differ as setoid morphisms only in their properness proofs
 (the probe's control beside N15).  [BGMonad]'s μ is Mac Lane's formula at
 his triple ([BG_join]) and as a function ([BG_join_fun]), which is
 stronger, since Coq's [prod] has no eta; its η likewise ([BG_ret],
 [BG_ret_fun]).  Their units differ.  Mac Lane's printed unit,
 η x = ⟨u, x⟩ (§VI.2, p. 141), is [ActMonad]'s on the nose, while
 [BGMonad]'s is (u u, x) ([BG_ret]): the unit is the restriction of the
 identity of F X, and the identity of the functor category is
 Theory/Natural/Transformation.v's [nat_id], whose component is fmap[F X]
 id, the action of u.  The functors are ≈ with identity components
 ([BG_T_ActF]), and the units agree at ≈ ([BG_ret_ActMonad]).

 THE TIE.  This file's comparison functor lands in the algebras of
 [BGMonad M], that of Instance/Fun/Action/Monad.v in those of
 [ActMonad M].  Mac Lane's §VI.2 Exercise 3(b) (p. 142) turns a morphism θ
 of monads into “a functor θ* : X^T' → X^T” with G^T ∘ θ* = G^T'; here θ
 is the identity-component isomorphism [BG_T_ActF], and θ* is built for
 this instance alone, with no general record of monad morphisms.
 [BG_Act_alg] reads an algebra of [BGMonad M] as one of [ActMonad M] with
 the SAME structure map: the unit law moves along mon_op_unit_l, and the
 action law passes unchanged, since the two monads' arrow maps and
 multiplications agree by conversion.  [Act_BG_alg] is the same reading
 the other way; it is kept as a map on algebras and is not assembled into
 a functor, only θ*'s direction being built.  [BG_Act_EM] is θ*, the
 identity on carriers, structure maps and arrows ([BG_Act_EM_carrier],
 [BG_Act_EM_alg]), and Mac Lane's G^T ∘ θ* = G^T' holds on the nose in
 both data fields ([BG_Act_EM_forget_obj], [BG_Act_EM_forget_map]).  [tie]
 states that θ* after this file's comparison functor is ≈, with identity
 components, the [to] leg of Instance/Fun/Action/Monad.v's [Fun_EM_iso],
 which is [EM_MSet_iso] after [MSet_Fun_equiv], that is,
 [EM_Comparison (MSet_adj M) ◯ MSet_to M] on the nose (the probe's control
 beside N19).  On objects the two agree at [eq_refl] in the carrier
 ([tie_carrier]) and in the structure map at each (g, z) and as a function
 ([tie_alg], [tie_alg_fun]); the whole algebras differ in their proof
 fields [t_id] and [t_action] (N19), and in the properness proof of the
 structure map, whose function agrees ([tie_alg_fun]; N20), so [tie] holds
 at ≈ only.  So the literal comparison functor, carried along θ*, is the
 equivalence of that file, at Set^BG itself.

 CORRECTION (#468).  A general record now exists: Monad/Morphism.v's
 [MonadHom] with the category [Monads C], and Monad/Morphism/Algebra.v's
 θ* ([mh_EM]).  Instance/Fun/Action/Monad/BG/Morphism.v states the θ of
 this paragraph as a morphism of monads, [BG_theta] from [ActMonad M] to
 [BGMonad M] with identity components, gives its inverse and
 [BG_theta_iso] in [Monads Sets], relates [BG_Act_EM] to the general θ*
 ([BG_theta_EM], at Cat's ≈; carriers, structure maps as functions and
 arrows at [eq_refl]) and assembles [Act_BG_alg] into a functor as θ* of
 the inverse ([Act_BG_EM]).  This file is not rewired: [BG_Act_EM] stays
 the functor built by hand, and its readback [BG_Act_EM_alg] is refused
 for the general θ*, whose structure map is h ∘ id.
 CORRECTION (#1347): since Instance/Sets.v gives its identity's and
 composite's properness fields as terms, h ∘ id converts with h in
 [Sets], and that readback restated for θ* holds at [eq_refl]
 (Test/ProbeMonadMorphism468.v's R12, now a control).  This file is
 still not rewired.

 WHICH “MONADIC”.  Riehl's Definition 5.3.1 (p. 196) calls an
 adjunction monadic when the comparison functor “defines an equivalence
 of categories”: Monad/Comparison.v's [Monadic].  Her Theorem 5.5.1
 (p. 202) reads “A right adjoint functor U : D → C is monadic if and
 only if it creates coequalizers of U-split pairs”; its “if” half is
 Beck.v's [beck_monadicity], in that form.  The same page names the
 strict reading, K an isomorphism exactly when U “strictly creates”
 those coequalizers, and leaves its proof to her Exercise 5.5.i.  This
 file implements the equivalence reading.  The lift above is on the
 nose, but the class does not record uniqueness on the nose, and no
 isomorphism of categories on the nose is stated.

 STRENGTHS.  By [eq_refl]: evaluation's two data fields against
 [MSet_Forget ◯ MSet_to]; the created lift's value, action, arrow and
 isomorphism; the [to] leg of [BG_EM_iso]; the induced monad's object and
 arrow maps, its unit as (u u, x) at each x and as a function, and its
 multiplication at (g₁, (g₂, x)) and as a function; its multiplication
 against [ActMonad]'s at every p; θ* on carriers, structure maps and
 arrows, and G^T ∘ θ* against G^T' in both data fields; the tie on
 objects, in the carrier and in the structure map at each (g, z) and as a
 function.  At ≈ only: the two monads' functors ([BG_T_ActF]), their units
 ([BG_ret_ActMonad]), and θ* after the comparison functor against the [to]
 leg of [Fun_EM_iso] ([tie]).  Refused by conversion, each pinned in
 Test/ProbeGroupAction464.v (its N13-N16, N19 and N20) and stripped in a
 copy of the whole probe: the unit as (u, x); [U_BG M ◯ F_BG M] as
 [ActF M]; the two multiplications as one setoid morphism; [U_BG M] as
 [MSet_Forget M ◯ MSet_to M]; the tie on a whole object, and on the
 properness proof of its structure map.  The refusals are not opacity.  In
 a copy of this file's 111-file dependency closure, every [Qed] was turned
 into [Defined] and every [Unset Transparent Obligations] into [Set], with
 two exceptions.  Instance/Sets.v, Structure/Cartesian/Closed.v,
 Instance/Grp.v and Instance/Grp/Free.v keep their [Qed]s
 (Instance/Fun/Action/Monad.v's measurement keeps the first three).
 Instance/Grp/Free.v keeps them because the second builder kept every file
 the first had measured, although the first found that that file's flip
 alone builds.  The choice is harmless: copies of the two targets without
 the imports of Instance/Grp.v and Instance/Grp/Free.v and without the six
 group twins of the two files that use them compile and load neither file,
 so no refused or compared term depends on either.  One proof of
 Structure/Limit/Preservation.v, [preserves_colimit], had its bullets
 rewritten, since the added transparency leaves it one goal instead of
 two.  There the whole probe compiles, so all six refusals stand and every
 positive control holds, and each refusal stripped there prints the error
 of the unchanged tree.  Corelib's CMorphisms lemmas stay opaque in any
 such tree.  In the normal forms of N13-N16, each refused field differs at
 a neutral term of the variable data: M's unit, or the transitivity and
 symmetry of a variable setoid.  Unfolding those lemmas cannot close the
 gap.  N19's two algebras differ in both proof fields, [t_id] and
 [t_action], and in the properness proof of the structure map (N20), each
 refused alone there as well.

 UNIVERSES, read off [About].  Every constant binds [@{o so}], and the
 three that name Cat, [BG_EM_iso], [BG_EM_iso_to] and [tie], bind
 [@{o so c}]; M : MonObject@{o o o}.  The only strict bounds are o < so,
 first carried by Instance/Sets.v's [Sets], and o < c, so < c, first
 carried by Instance/Cat.v's [Cat@{c so so so o}].  There is no equation
 and no [Set].  The hom level of the functor category is not free, and
 [SetBG M] writes it out as [Fun@{o o so o so o so}], hom level o, the
 instance Instance/Fun/Action.v's [MSet_to] and [MSet_from] and
 Instance/Fun/Eval.v's [Eval] already use.  It is forced.
 Instance/Fun.v's block puts that level at or above the index category's
 hom level, o.  Theory/Functor.v's [Functor] block, h1 <= h2, puts it at
 or below the hom level of the target of any functor out of the category,
 so at or below o for U_BG.  Four more constants state the same
 identification in their own blocks:
 - [Compose], whose binder gives one hom universe to all three
 categories, so that the composite [F_BG] needs it on its own;
 - Theory/Adjunction.v's [Adjunction] (h1 = h2);
 - Beck.v's [beck_monadicity], which inherits it (u0 = u2);
 - Monad/Comparison.v's [Monadic], whose binder shares one hom
 universe.
 Measured in Test/ProbeGroupAction464.v (N17, N18) at the same category
 with hom level so: a functor type out of it into Sets is refused, and
 [MSet_from] into it is accepted while its composite with [MSet_Free]
 is refused (“Cannot enforce so = o because o < so”).  The stdlib caps
 are the donors':
 - compose and ID from [Sets];
 - prod_rect and projections from [MSet_Free]'s product carrier;
 - Logic_lemmas.equality and so <= projections from
 [Build_Adjunction'];
 - prod_rect in the creation from [coequalizer_along_iso];
 - Projections from [beck_monadicity] and, in the [bg_created_*]
 readbacks, from the projections their statements apply; in θ* and
 the tie, from [EilenbergMoore], whose objects are sigma types;
 - eq_ind and eq_ind_r, in [GSet_BG_Monadic_GroupObject] only, from
 Instance/Grp.v's [GroupObject_GrpObject].
 A [simpl] in two proof bullets of [BG_Act_EM] added the strict bound
 o < Projections.u0 (implied by o < so and so <= Projections.u0) to nine
 constants, θ* and the eight that mention it ([tie_alg_fun] among them;
 measured again by putting the [simpl]s back in a copy of this file); the
 [simpl]s were removed and the bound is gone.  The adjunction is
 [Adjunction@{so o o so o o o o so o so}] and the witness
 [Monadic@{so so so so so o so so}], as in Instance/Fun/Action/Monad.v.

 NOT DELIVERED.
 - No general monad-morphism record; θ* for this instance is
 [BG_Act_EM] (THE TIE, above).
 - Transport of [Monadic], or of creation, along an equivalence of
 categories.
 - Mac Lane's and Riehl's strict monadicity, an isomorphism of
 categories on the nose.
 - The converse half of Riehl's theorem at [U_BG]: Beck.v's
 [monadic_creates] is stated at [EM_Forget]. 

 --------
 书籍：Riehl，《上下文中的范畴论》，第二版，习题 5.5.iv，第 208 页（PDF 第 228 页）— riehl:5.5:exiv；参见她的定理 5.5.1，第 202 页（PDF 第 222 页），以及定义 5.3.1，第 196 页（PDF 第 216 页）
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第二版，Springer GTM 5，1998年，第 VI.2 节，“群作用”，第 141 页（PDF 第 150 页）— maclane:VI.2:remark2；以及第 VI.2 节习题 3，第 142 页（PDF 第 151 页）
 nLab: https://ncatlab.org/nlab/show/monadicity+theorem
 nLab: https://ncatlab.org/nlab/show/actionRiehl 的练习 5.5.iv 给出：“对于任意群 G”，忘记函子
 U : Set^BG → Set 有一个左伴随，“将集合 X 映射到 G 集合 G × X，
 且 G 在左侧作用”，并要求：“通过调用单纯函子定理证明此伴随是单纯的。”她的 Set^BG 是函子范畴 [BG, Set]，BG 是 G 的一个单对象范畴，U 是在该单对象上的取值。Instance/Fun/Action/Monad.v 在 Instance/Fun/Action.v 的作用范畴 [MSet M] 中证明了此练习，该范畴 [MSet_Fun_equiv] 与 Cat 中的 [Deloop M, Sets] 对应；在此树中没有引理能将 [Monadic] 通过此类对应传递，因此此文件字面上陈述了该练习，直接在函子范畴本身上。由于下面没有使用逆元素，每一条陈述都是在一个幺半群 M 上完成的。这些组实例是 Instance/Fun/Action/Monad.v 中的实例：
 [GSet_BG_Monadic] 位于 Construction/Deloop.v 的 [GrpObject]，
 [GSet_BG_Monadic_Grp] 位于 Instance/Grp.v 中，通过 Instance/Grp/Free.v 的 [grp_deloop_monoid]，以及 [GSet_BG_Monadic_GroupObject] 位于 Structure/Group.v 的 [GroupObject] 中（在 (Sets, ×) 中），通过 Instance/Grp.v 的 [GroupObject_GrpObject]，这需要 [PropEquiv] 的承载。声明 [GrpObject] 的两个文件都已被导入，每个使用都写有其完整路径。函子范畴及其遗忘函子。[SetBG M] 是 [Deloop M, Sets]，其同态层次已写出（宇宙，见下文）。[U_BG M] 是 Instance/Fun/Eval.v 中的 [Eval] 在单对象 [ttt] 的情形，[F_BG M] 是 Instance/Fun/Action.v 中的 [MSet_from] 在自由 M-集函子 [MSet_Free]（来自 Instance/Fun/Action/Monad.v）作用后：一个集合 X 对应的函子值为 M × X，在左因子上作用。在 [eq_refl]（[U_BG_obj], [U_BG_map]）两数据字段中，求值与先 [MSet_to] 后 [MSet_Forget] 相符，但作为函子则不然。伴随。[BG_adj : F_BG M ⊣ U_BG M] 基于同态集合，由 Theory/Adjunction.v 的 [Build_Adjunction'] 构建。从 F X 出发的变换 φ 限制为 x ↦ φ(u, x) ([BG_restrict])；映射 ψ : X → P ttt 扩展为 (g, x) ↦ g · ψ x，由 Instance/Fun/Action/Monad.v 的 [MSet_extend] 提供，并通过 [MSet_from] 以及 Instance/Fun/Action.v 的往返 [MSet_round_iso] ([BG_extend]) 带入函子范畴。创造，通过运输。通过转换，一对 p, q 的 U_BG 图像的分裂共等化器是 [MSet_to p] 和 [MSet_to q] 的 [MSet_Forget] 图像之一，因为 [action_of_functor P] 的载体是 P ttt，作用是 fmap [P]。所以 Instance/Fun/Action/Monad.v 的创建照常使用。创建的函子是 [MSet_from]，它的 [CreatedAct]；共等化变换 [BGCreatedE] 的分量是 e，其自然性是 [CreatedE] 的等变性；类的两个条款是 [CreatedE_is_coeq] 和 [Reflected_is_coeq] 被读回。唯一的新引理是 [MSet_to_reflects_coeq]：一个变换的共叉，其 [MSet_to] 图像是 M-集合的共等化器，是函子的共等化器，从该唯一对象引出的变换是一个等变映射。存在子句也通过 Monad/Monadicity/Beck.v 的 [coequalizer_along_iso] ，在 Instance/Fun/Action.v 的 [MSet_action_round_iso] 。没有再次证明吸收引理。提升是直接的：它的值是分裂商 Z，它的作用是 g · z = e (g · s z)，它的箭头是 e，比较同构是恒等映射 ([bg_created_carrier], [bg_created_action], [bg_created_arrow], [bg_created_iso])。单子性。[BG_beck_equivalence] 是 Beck.v 在 [BG_adj] 和 [U_BG_creates] 的 [beck_monadicity]；Instance/Fun/Action/Monad.v 是该定理在树中的第一次使用，而这个文件是第二次使用。[U_BG_Monadic] 将其打包为 Monad/Comparison.v 的 [Monadic]。[U_BG_reflects] 是 Beck.v 在这里的 [creates_split_reflects_isos]：一个在单对象处的分量在集合中是可逆的变换是可逆的。[BG_EM_iso] 是 Cat 中 [SetBG M] 与诱导单子 [BGMonad M] 的代数之间的同构（在 Cat 中的同构，逆在自然同构下，因此是等价的），其 [to] 分支是比较函子（[BG_EM_iso_to]）。两个单子。[BGMonad M] 是 Monad/Comparison.v 的 [Adjunction_Induced_Monad] 于 [BG_adj]；Instance/Fun/Action/Monad.v 的 [ActMonad M] 是在 [MSet M] 上的伴随中的相同构造。它们的函子有相同的对象和箭头映射，M × X 和 M × f ([BG_T_obj], [BG_T_map])，并且它们的乘法在每个 p ([BG_join_ActMonad]) 上都一致；两个乘法具有相同的基础函数，仅在它们的适当性证明中作为集合同构映射有所不同（探针控制在 N15 旁边）。[BGMonad] 的 μ 是 Mac Lane 在他三重对象 ([BG_join]) 上的公式，并且作为一个函数 ([BG_join_fun])，这更强，因为 Coq 的 [prod] 没有 eta；它的 η 同样如此 ([BG_ret], [BG_ret_fun])。它们的单位不同。Mac Lane 印刷的单位，η x = ⟨u, x⟩ (§VI.2, p.141)，[ActMonad] 是完全正确的，而 [BGMonad] 是 (u u, x) ([BG_ret])：该单位是 F X 身份映射的限制，函子范畴的身份映射是 Theory/Natural/Transformation.v 的 [nat_id]，其分量是 fmap [F X] id，即 u 的作用。函子在身份分量下是 ≈ ([BG_T_ActF])，并且单位在 ≈ 处一致 ([BG_ret_ActMonad])。联系。本文件的比较函子落在 [BGMonad M] 的代数中，而 Instance/Fun/Action/Monad.v 的落在 [ActMonad M] 的代数中。Mac Lane §VI.2 练习 3(b)（第 142 页）将一个单子 θ 的态射转化为“函子 θ* : X^T' → X^T”，使得 G^T ∘ θ* = G^T'；这里 θ 是恒等分量同构 [BG_T_ActF]，而 θ* 是专为此实例构建的，没有单子态射的一般记录。[BG_Act_alg] 将 [BGMonad M] 的一个代数读取为 [ActMonad M] 的代数，具有相同的结构映射：单元律通过 mon_op_unit_l 转移，而作用律保持不变，因为两个单子的箭头映射和乘法通过转换是相同的。[Act_BG_alg] 以相反的方式读取；它保持为代数上的一个映射，而不被组合成函子，仅构建 θ* 的方向。[BG_Act_EM] 是 θ*，在载体、结构映射和箭头上为同一映射（[BG_Act_EM_carrier], [BG_Act_EM_alg]），并且 Mac Lane 的 G^T ∘ θ* = G^T' 在两个数据域上严格成立（[BG_Act_EM_forget_obj], [BG_Act_EM_forget_map]）。[tie] 表示，在应用这个文件的比较函子之后，θ* 近似（≈），分量为同一映射，即 Instance/Fun/Action/Monad.v 的 [to] 分支（[Fun_EM_iso]），在 [MSet_Fun_equiv] 之后为 [EM_MSet_iso]，也就是说，[EM_Comparison (MSet_adj M) ◯ MSet_to M] 严格成立（探针控制位于 N19 旁）。在对象上，两者在载体的 [eq_refl]（[tie_carrier]）以及在结构图中每个 (g, z) 处以及作为函数（[tie_alg], [tie_alg_fun]）上是一致的；整个代数在它们的证明域 [t_id] 和 [t_action]（N19）以及结构图的适当性证明上有所不同，其函数是一致的（[tie_alg_fun]；N20），所以 [tie] 仅在 ≈ 上成立。因此，沿 θ* 携带的字面比较函子是该文件在 Set^BG 本身上的等价。更正 (#468)。现在存在一个一般记录：Monad/Morphism.v 的 [MonadHom] 及其类别 [Monads C]，以及 Monad/Morphism/Algebra.v 的 θ* ([mh_EM])。Instance/Fun/Action/Monad/BG/Morphism.v 将本段的 θ 称为 monad 的态射，[BG_theta] 从 [ActMonad M] 到 [BGMonad M] 并具有恒等分量，给出了它的逆以及 [BG_theta_iso] 在 [Monads Sets] 中，将 [BG_Act_EM] 与一般的 θ* ([BG_theta_EM]，在 Cat 的 ≈；承载体、作为函数的结构映射以及在 [eq_refl] 的箭头) 联系起来，并将 [Act_BG_alg] 组装成一个函子，作为逆的 θ* ([Act_BG_EM])。此文件未重新连接：[BG_Act_EM] 保持手工构建的函子，其回读 [BG_Act_EM_alg] 被一般 θ* 拒绝，其结构映射为 h ∘ id。更正 (#1347)：由于 Instance/Sets.v 将其恒等和复合的正确性字段作为项给出，h ∘ id 在 [Sets] 中与 h 一起转换，并且在 [eq_refl] 中 θ* 的重读也成立（Test/ProbeMonadMorphism468.v 的 R12，现在是一个控制）。该文件仍未重新连接。哪个“单体的”。Riehl 的定义 5.3.1（第 196 页）称一个伴随是单体的，当比较函子“定义了范畴的等价”：Monad/Comparison.v 的 [Monadic]。她的定理 5.5.1（第 202 页）写道“当且仅当右伴随函子 U : D → C 创建 U 分裂对的余等化子时，它是单体的”；其“如果”部分在 Beck.v 的 [beck_monadicity] 中以该形式存在。同一页提到了严格的解释，K 当且仅当 U “严格创建”那些余等化子时是同构的，并将其证明留给她的练习 5.5.i。此文件实现了等价的解释。上面的提升是正儿八经的，但类中没有记录正儿八经的唯一性，也没有声明范畴的正儿八经同构。优势。由 [eq_refl]：对 [MSet_Forget ◯ MSet_to] 的两个数据字段的评估；所创建提升的值、箭头和同构；[to] 对 [BG_EM_iso] 的分支；诱导的单子对象和箭头映射，其在每个 x 的单元 (u u, x) 以及作为函数的表示，以及在 (g₁, (g₂, x)) 的乘法及其作为函数的表示；其乘法在每个 p 对 [ActMonad] 的作用；载体、结构映射和箭头上的 θ*，以及 G^T ∘ θ* 与两个数据字段中的 G^T' 的作用；对象上的绑定，在载体和每个 (g, z) 的结构映射中以及作为函数的表示。仅在 ≈：两个单子的函子 ([BG_T_ActF])、它们的单元 ([BG_ret_ActMonad])，以及 θ* 在比较函子后，相对于 [Fun_EM_iso] 的 [to] 分支 ([tie])。由于转换被拒绝，每个在 Test/ProbeGroupAction464.v 中钉住（其 N13-N16, N19 和 N20）并在整个探针的副本中被剥离：单元作为 (u, x)；[U_BG M ◯ F_BG M] 作为 [ActF M]；两个乘法作为一个集合态射；[U_BG M] 作为 [MSet_Forget M ◯ MSet_to M]；整个对象上的绑定，以及其结构映射的适当性证明上的绑定。这些拒绝不是不透明的。在此文件的 111 文件依赖闭包副本中，每个 [Qed] 被转换为 [Defined]，每个 [Unset Transparent Obligations] 被转换为 [Set]，有两个例外。Instance/Sets.v、Structure/Cartesian/Closed.v、Instance/Grp.v 和 Instance/Grp/Free.v 保留其 [Qed]s（Instance/Fun/Action/Monad.v 的测量保留前三个）。Instance/Grp/Free.v 保留它们，因为第二个构建器保留了第一个构建器测量的每个文件，尽管第一个发现仅翻转该文件就能构建。这个选择是无害的：两个目标的副本在没有导入 Instance/Grp.v 和 Instance/Grp/Free.v 以及不包含使用它们的两个文件的六个群组副本的情况下进行编译和加载，并且不依赖于任意一个文件，所以没有被拒绝或比较的项依赖于它们。Structure/Limit/Preservation.v 的一个证明 [preserves_colimit]，其项目符号被重写，因为增加的透明度使其从两个目标变为一个。在那里整个探测编译，因此所有六次拒绝都有效，每个正控制都成立，并且那里的每个被剥离的拒绝都会打印未改变树的错误。Corelib 的 CMorphisms 引理在任何此类树中保持不透明。在 N13-N16 的正规形式中，每个拒绝的字段在变量数据的中性项上有所不同：M 的单位，或变量集合的传递性和对称性。展开这些引理无法弥合差距。N19 的两个代数在两个证明字段 [t_id] 和 [t_action] 以及结构映射的恰当性证明（N20）中都不同，每个在那里也单独被拒绝。UNIVERSES，读作 [About]。每个常量绑定 [@{o so}]，命名为 Cat 的三个常量 [BG_EM_iso]、[BG_EM_iso_to] 和 [tie] 绑定 [@{o so c}]；M : MonObject@{o o o}。唯一严格的界限是 o < so，首先由 Instance/Sets.v 的 [Sets] 提供，以及 o < c，so < c，首先由 Instance/Cat.v 的 [Cat@{c so so so o}] 提供。没有方程，也没有 [Set]。函子范畴的 hom 等级不是自由的，[SetBG M] 将其写出为 [Fun@{o o so o so o so}]，hom 等级 o，实例 Instance/Fun/Action.v 的 [MSet_to] 和 [MSet_from] 以及 Instance/Fun/Eval.v 的 [Eval] 已经使用。它是强制的。Instance/Fun.v 的块将该等级设置在索引范畴的 hom 等级之上或等于。Theory/Functor.v 的 [Functor] 块，h1 <= h2，使其处于或低于任何从该类别出的函子目标的同态层级，因此在 U_BG 中处于 o 或以下。还有四个常量在它们自己的块中声明了相同的识别：
 - [Compose]，其绑定器为所有三个类别提供一个同态宇宙，因此复合 [F_BG] 需要它自己使用它；
 - Theory/Adjunction.v 的 [Adjunction]（h1 = h2）；
 - Beck.v 的 [beck_monadicity]，它继承了它（u0 = u2）；
 - Monad/Comparison.v 的 [Monadic]，其绑定器共享一个同态宇宙。在 Test/ProbeGroupAction464.v（N17，N18）中，在同一类别和同态层级下测量：从它出的函子类型到 Sets 被拒绝，而 [MSet_from] 到它是被接受的，同时它与 [MSet_Free] 的复合被拒绝（“无法强制 so = o 因为 o < so”）。stdlib 的上限是捐赠者的：
 - 来自 [Sets] 的 compose 和 ID；
 - 来自 [MSet_Free] 的 product carrier 的 prod_rect 和 projections；
 - 来自 [Build_Adjunction'] 的 Logic_lemmas.equality 以及 <= projections；
 - 来自 [coequalizer_along_iso] 的创建中的 prod_rect；
 - 来自 [beck_monadicity] 的 Projections，并且在 [bg_created_*] 的 readbacks 中，来自 projections 其语句适用的部分；在 θ* 和 tie 中，来自 [EilenbergMoore]，其对象是 sigma 类型；
 - eq_ind 和 eq_ind_r，仅在 [GSet_BG_Monadic_GroupObject] 中，来自 Instance/Grp.v 的 [GroupObject_GrpObject]。在 [simpl] 的两个 [BG_Act_EM] 证明要点中，向九个常数（θ* 和提及它的八个常数，其中包括 [tie_alg_fun]）添加了严格界限 o < Projections.u0（由 o < so 和 so <= Projections.u0 推导）；通过将 [simpl] 重新放回该文件的副本中再次进行测量；[simpl] 已被移除，界限也消失了。该附加项是 [Adjunction@{so o o so o o o o so o so}]，证据是 [Monadic@{so so so so so o so so}]，如 Instance/Fun/Action/Monad.v 所示。未交付。
 - 没有一般的单子态射记录；此实例的 θ* 为 [BG_Act_EM]（上文的 THE TIE）。
 - 沿范畴等价对 [Monadic] 或创造的传输。
 - Mac Lane 和 Riehl 的严格单子性，范畴之间的完全同构。
 - Riehl 定理的逆半部分在 [U_BG]：Beck.v 的 [monadic_creates] 在 [EM_Forget] 陈述。
*)

(* * ** Riehl's Set^BG and its forgetful functor / * ** Riehl的Set^BG及其遗忘函子 *)

(* The functor category [Deloop M, Sets], hom level o (see UNIVERSES). / 函子范畴 [Deloop M, Sets]，Hom 层级 o（见 UNIVERSES）。 *)
Definition SetBG@{o so} (M : MonObject@{o o o}) : Category@{so o o} :=
  @Fun@{o o so o so o so} (Deloop@{o o} M) Sets@{o so}.

(* Riehl's U: evaluation at the one object of BM. / Riehl 的 U：在 BM 的一个对象上的评估。 *)
Definition U_BG@{o so} (M : MonObject@{o o o}) :
  SetBG@{o so} M ⟶ Sets@{o so} :=
  @Eval@{o o so o so so} (Deloop@{o o} M) Sets@{o so} ttt.

(*
 Riehl's left adjoint: X goes to the functor whose value is the free
 M-set M × X. 

 --------
 Riehl 的左伴随：X 对应到其值为自由 M-集 M × X 的函子。
*)
Definition F_BG@{o so} (M : MonObject@{o o o}) :
  Sets@{o so} ⟶ SetBG@{o so} M :=
  MSet_from@{so o o so o} M ◯ MSet_Free@{o so} M.

(*
 Evaluation is [MSet_to] followed by forgetting the action, in both data
 fields. 

 --------
 评估是 [MSet_to]，然后忘记动作，在两个数据字段中。
*)
Example U_BG_obj@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  fobj[U_BG@{o so} M] P = fobj[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] P :=
  eq_refl.

Example U_BG_map@{o so} (M : MonObject@{o o o}) (P Q : SetBG@{o so} M)
  (η : P ~{SetBG@{o so} M}~> Q) :
  fmap[U_BG@{o so} M] η = fmap[MSet_Forget@{o so} M ◯ MSet_to@{so o} M] η :=
  eq_refl.

(** ** The free/forgetful adjunction / ** 自由/遗忘的伴随 *)

(* A transformation φ : F X ⟹ P restricts to x ↦ φ (u, x). / 一个变换 φ : F X ⟹ P 限制为 x ↦ φ (u, x)。 *)
Definition BG_restrict@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (φ : fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P) :
  X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P.
Proof.
  unshelve refine
    (@Build_SetoidMorphism X _ (fobj[P] ttt) _
       (fun x => transform[φ] ttt (mon_unit, x)) _).
  intros x y Hxy. apply (proper_morphism (transform[φ] ttt)).
  split; [ reflexivity | exact Hxy ].
Defined.

(* A map ψ : X → P ttt extends to (g, x) ↦ g · ψ x: [MSet_extend] at the action read off P, carried back along the round trip. / 一个映射 ψ : X → P ttt 可以扩展为 (g, x) ↦ g · ψ x: [MSet_extend]，在从 P 读取的作用下，沿着往返路径带回。 *)
Definition BG_extend@{o so} {M : MonObject@{o o o}}
  {X : SetoidObject@{o o}} {P : SetBG@{o so} M}
  (ψ : X ~{Sets@{o so}}~> fobj[U_BG@{o so} M] P) :
  fobj[F_BG@{o so} M] X ~{SetBG@{o so} M}~> P :=
  to (MSet_round_iso@{so o o so o} P)
    ∘ fmap[MSet_from@{so o o so o} M]
        (@MSet_extend@{o so} M X (action_of_functor@{o o o so o} P) ψ).

Definition BG_adj_iso@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (P : SetBG@{o so} M) :
  @Isomorphism Sets@{o so}
    (@Build_SetoidObject
       (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
       (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
    (@Build_SetoidObject
       (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
       (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))).
Proof.
  unshelve refine
    (@Build_Isomorphism Sets@{o so}
       (@Build_SetoidObject
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P))
       (@Build_SetoidObject
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P)))
       (@Build_SetoidMorphism
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (fun φ => @BG_restrict M X P φ) _)
       (@Build_SetoidMorphism
          (@hom Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@homset Sets@{o so} X (fobj[U_BG@{o so} M] P))
          (@hom (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (@homset (SetBG@{o so} M) (fobj[F_BG@{o so} M] X) P)
          (fun ψ => @BG_extend M X P ψ) _) _ _).
  - intros φ φ' Hφ x. exact (Hφ ttt (mon_unit, x)).
  - intros ψ ψ' Hψ [] [g x]; simpl.
    apply (proper_morphism (@fmap _ _ P ttt ttt g)). exact (Hψ x).
  - intros ψ x; simpl. exact (@fmap_id _ _ P ttt (ψ x)).
  - intros φ [] [g x]; simpl.
    transitivity
      (transform[φ] ttt
         (@fmap _ _ (fobj[F_BG@{o so} M] X) ttt ttt g (mon_unit, x))).
    + exact (@naturality _ _ _ _ φ ttt ttt g (mon_unit, x)).
    + apply (proper_morphism (transform[φ] ttt)).
      split; [ exact (mon_op_unit_r g) | reflexivity ].
Defined.

(* Riehl's adjunction, literally: F ⊣ U on Set^BM. / Riehl 的伴随，字面意思：F ⊣ U 在 Set^BM 上。 *)
Definition BG_adj@{o so} (M : MonObject@{o o o}) :
  @Adjunction@{so o o so o o o o so o so} (SetBG@{o so} M) Sets@{o so}
    (F_BG@{o so} M) (U_BG@{o so} M).
Proof.
  unshelve refine
    (@Build_Adjunction' (SetBG@{o so} M) Sets@{o so}
       (F_BG@{o so} M) (U_BG@{o so} M) (fun X P => BG_adj_iso M X P) _ _).
  - intros X Y P f g x; simpl. reflexivity.
  - intros X P Q f g x; simpl. reflexivity.
Defined.

(* * ** Creation of U-split coequalizers, transported from M-sets / * ** 从 M-集传递的 U-分裂共等化器的创建 *)

(*
 A cofork of transformations whose [MSet_to]-image is a coequalizer of
 M-sets is a coequalizer of functors: the descended equivariant map is
 the one component of the descended transformation. 

 --------
 一个共轭变换的子分叉，其 [MSet_to]-像是 M-集的共等化器，是函子的一种共等化器：下降的等变映射是下降变换的一个分量。
*)
Definition MSet_to_reflects_coeq@{o so} {M : MonObject@{o o o}}
  {P Q R : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q) (e : Q ~{SetBG@{o so} M}~> R)
  (E : @IsCoequalizer (MSet@{so so o o o o o o} M) _ _
         (fmap[MSet_to@{so o} M] p) (fmap[MSet_to@{so o} M] q)
         (fobj[MSet_to@{so o} M] R) (fmap[MSet_to@{so o} M] e)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q R e.
Proof.
  unshelve refine (@Build_IsCoequalizer _ _ _ _ _ _ _ _ _).
  - intros [] y. exact (cofork E y).
  - intros W h Hh.
    pose (D := coeq_desc E (fmap[MSet_to@{so o} M] h) (fun y => Hh ttt y)).
    unshelve eapply Build_Unique.
    + unshelve refine (@Build_Transform _ _ _ _ _ _ _).
      * intros []. exact (equiv_map (unique_obj D)).
      * intros [] [] g z; simpl. symmetry. exact (equivar (unique_obj D) g z).
      * intros [] [] g z; simpl. exact (equivar (unique_obj D) g z).
    + intros [] y. exact (unique_property D y).
    + intros v Hv [] z.
      exact (uniqueness D (fmap[MSet_to@{so o} M] v) (fun y => Hv ttt y) z).
Defined.

(*
 The coequalizing transformation onto the created functor: component e,
 naturality the equivariance of Instance/Fun/Action/Monad.v's
 [CreatedE]. 

 --------
 对所创建函子的共等化变换：组件 e，自然性 Instance/Fun/Action/Monad.v 的等变性 [CreatedE]。
*)
Definition BGCreatedE@{o so} {M : MonObject@{o o o}} {P Q : SetBG@{o so} M}
  (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  Q ~{SetBG@{o so} M}~>
    fobj[MSet_from@{so o o so o} M]
      (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
         (fmap[MSet_to@{so o} M] q) S).
Proof.
  unshelve refine (@Build_Transform _ _ _ _ _ _ _).
  - intros []. exact (scoeq_e S).
  - intros [] [] g y; simpl. symmetry.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
  - intros [] [] g y; simpl.
    exact (equivar (CreatedE@{o so} (fmap[MSet_to@{so o} M] p)
                      (fmap[MSet_to@{so o} M] q) S) g y).
Defined.

(*
 [CreatedE_is_coeq], moved along [MSet_action_round_iso] and read back
 through [MSet_to]. 

 --------
 [CreatedE_is_coeq]，沿着 [MSet_action_round_iso] 移动并通过 [MSet_to] 回读。
*)
Definition BGCreatedE_is_coeq@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  @IsCoequalizer (SetBG@{o so} M) P Q p q
    (fobj[MSet_from@{so o o so o} M]
       (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
          (fmap[MSet_to@{so o} M] q) S))
    (BGCreatedE@{o so} p q S).
Proof.
  apply MSet_to_reflects_coeq.
  refine (coequalizer_along_iso _ _ _
            (CreatedE_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
               (fmap[MSet_to@{so o} M] q) S)
            (MSet_action_round_iso
               (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                  (fmap[MSet_to@{so o} M] q) S))
            (fmap[MSet_to@{so o} M] (BGCreatedE@{o so} p q S)) _).
  intros y. reflexivity.
Defined.

Definition U_BG_creates@{o so} (M : MonObject@{o o o}) :
  CreatesUSplitCoequalizers (U_BG@{o so} M).
Proof.
  unshelve refine (@Build_CreatesUSplitCoequalizers _ _ _ _ _).
  - intros P Q p q S.
    exists (fobj[MSet_from@{so o o so o} M]
              (CreatedAct@{o so} (fmap[MSet_to@{so o} M] p)
                 (fmap[MSet_to@{so o} M] q) S)).
    exists (BGCreatedE@{o so} p q S).
    split.
    + exact (BGCreatedE_is_coeq@{o so} p q S).
    + exists (@iso_id Sets@{o so} (scoeq_obj S)).
      intros y; simpl. reflexivity.
  - intros P Q p q S R e He i Hi.
    apply MSet_to_reflects_coeq.
    refine (Reflected_is_coeq@{o so} (fmap[MSet_to@{so o} M] p)
              (fmap[MSet_to@{so o} M] q) S (fobj[MSet_to@{so o} M] R)
              (fmap[MSet_to@{so o} M] e) _ i Hi).
    intros y. exact (He ttt y).
Defined.

(*
 The lift is on the nose: value Z, action e (g · s z), arrow e and the
 identity comparison isomorphism. 

 --------
 提升作用在鼻子上：值 Z，动作 e (g · s z)，箭头 e 以及同一性比较同构。
*)
Example bg_created_carrier@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  fobj[`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S)] ttt
  = scoeq_obj S := eq_refl.

Example bg_created_action@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q))
  (g : carrier M) (z : carrier (scoeq_obj S)) :
  @fmap _ _ (`1 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))
    ttt ttt g z
  = scoeq_e S (@fmap _ _ Q ttt ttt g (scoeq_s S z)) := eq_refl.

Example bg_created_arrow@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  transform[`1 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))]
    ttt
  = scoeq_e S := eq_refl.

Example bg_created_iso@{o so} {M : MonObject@{o o o}}
  {P Q : SetBG@{o so} M} (p q : P ~{SetBG@{o so} M}~> Q)
  (S : @SplitCoequalizer Sets@{o so} _ _
         (fmap[U_BG@{o so} M] p) (fmap[U_BG@{o so} M] q)) :
  `1 (snd (`2 (`2 (@create_coeq _ _ _ (U_BG_creates@{o so} M) P Q p q S))))
  = @iso_id Sets@{o so} (scoeq_obj S) := eq_refl.

(* * ** Riehl's Exercise 5.5.iv, literally, by the monadicity theorem / * ** Riehl 的练习 5.5.iv，字面意思，通过幺范畴性定理 *)

Definition BG_beck_equivalence@{o so} (M : MonObject@{o o o}) :
  EquivalenceOfCategories (EM_Comparison (BG_adj@{o so} M)) :=
  beck_monadicity (BG_adj@{o so} M) (U_BG_creates@{o so} M).

Definition U_BG_Monadic@{o so} (M : MonObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} M) Sets@{o so}
    (U_BG@{o so} M).
Proof.
  exists (F_BG@{o so} M).
  exists (BG_adj@{o so} M).
  exact (BG_beck_equivalence@{o so} M).
Defined.

(* A transformation invertible at the one object is invertible. / 在单个对象上可逆的变换是可逆的。 *)
Definition U_BG_reflects@{o so} (M : MonObject@{o o o}) :
  ReflectsIsos (U_BG@{o so} M) :=
  creates_split_reflects_isos _ (U_BG_creates@{o so} M).

(** ** The induced monad / ** 诱导幺半群 *)

Definition BGMonad@{o so} (M : MonObject@{o o o}) :
  @Monad Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M) :=
  Adjunction_Induced_Monad (BG_adj@{o so} M).

(*
 Set^BM is isomorphic in Cat to the algebras of its monad, by the
 comparison functor itself. 

 --------
 Set^BM 在 Cat 中通过比较函子自身同构于其单子的代数。
*)
Definition BG_EM_iso@{o so c} (M : MonObject@{o o o}) :
  @Isomorphism Cat@{c so so so o} (SetBG@{o so} M)
    (@EilenbergMoore@{so so so o} Sets@{o so}
       (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :=
  Equivalence_to_Cat_Iso (BG_beck_equivalence@{o so} M).

Example BG_EM_iso_to@{o so c} (M : MonObject@{o o o}) :
  to (BG_EM_iso@{o so c} M) = EM_Comparison (BG_adj@{o so} M) := eq_refl.

(*
 The monad read back: T X = M × X, T f = M × f, η x = (u u, x) and
 μ (g₁, (g₂, x)) = (g₁ g₂, x). 

 --------
 该单子读作：T X = M × X，T f = M × f，η x = (u u, x) 且 μ (g₁, (g₂, x)) = (g₁ g₂, x)。
*)
Example BG_T_obj@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  fobj[U_BG@{o so} M ◯ F_BG@{o so} M] X = act_prod M X := eq_refl.

Example BG_T_map@{o so} (M : MonObject@{o o o}) (X Y : SetoidObject@{o o})
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[U_BG@{o so} M ◯ F_BG@{o so} M] f = act_prod_map M f := eq_refl.

Example BG_ret@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x = (mon_op mon_unit mon_unit, x) :=
  eq_refl.

Example BG_join@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o})
  (g1 g2 : carrier M) (x : carrier X) :
  (@join _ _ (BGMonad@{o so} M) X) (g1, (g2, x)) = (mon_op g1 g2, x) :=
  eq_refl.

(*
 The same two readbacks as functions, which is stronger, since Coq's
 [prod] has no eta. 

 --------
 同样的两个回读作为函数，这更强，因为 Coq 的 [prod] 没有 eta。
*)
Example BG_ret_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun x : carrier X => (@ret _ _ (BGMonad@{o so} M) X) x)
  = (fun x => (mon_op mon_unit mon_unit, x)) := eq_refl.

Example BG_join_fun@{o so} (M : MonObject@{o o o}) (X : SetoidObject@{o o}) :
  (fun p => (@join _ _ (BGMonad@{o so} M) X) p)
  = (fun p : carrier M * (carrier M * carrier X) =>
       (mon_op (fst p) (fst (snd p)), snd (snd p))) := eq_refl.

(* * ** Against the monad of Instance/Fun/Action/Monad.v / * ** 针对 Instance/Fun/Action/Monad.v 的 monad *)

(* The two functors, with identity components. / 这两个函子，带有恒等分量。 *)
Definition BG_T_ActF@{o so} (M : MonObject@{o o o}) :
  U_BG@{o so} M ◯ F_BG@{o so} M ≈ ActF@{o so} M.
Proof.
  exists (fun X => @iso_id Sets@{o so} (act_prod M X)).
  intros X Y f p. simpl. split; reflexivity.
Defined.

(* The two units, by the unit law of M. / 根据 M 的单位法则，这两个单位。 *)
Definition BG_ret_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (x : carrier X) :
  (@ret _ _ (BGMonad@{o so} M) X) x ≈ (@ret _ _ (ActMonad@{o so} M) X) x.
Proof.
  split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
Defined.

(* The two multiplications, on the nose at every triple. / 这两次乘法，每次三倍点都非常准确。 *)
Example BG_join_ActMonad@{o so} (M : MonObject@{o o o})
  (X : SetoidObject@{o o}) (p : carrier M * (carrier M * carrier X)) :
  (@join _ _ (BGMonad@{o so} M) X) p = (@join _ _ (ActMonad@{o so} M) X) p :=
  eq_refl.

(* * ** The tie: θ* from the algebras of [BGMonad] to those of [ActMonad] / * ** 该联系：从 [BGMonad] 的代数到 [ActMonad] 的代数 的 θ* *)

(* An algebra of [BGMonad M] is one of [ActMonad M] with the same structure map; the unit law moves along mon_op_unit_l. / [BGMonad M] 的一个代数是具有相同结构映射的 [ActMonad M] 的一个代数；单位律沿 mon_op_unit_l 移动。 *)
Definition BG_Act_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
         (BGMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a
       (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_op mon_unit mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ symmetry; exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(* The same reading the other way; it is not assembled into a functor. / 相同的读法反过来也一样；它没有被组装成函子。 *)
Definition Act_BG_alg@{o so} (M : MonObject@{o o o}) (a : SetoidObject@{o o})
  (h : @TAlgebra Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M) a) :
  @TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M) a.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
       (BGMonad@{o so} M) a (@t_alg _ _ _ _ h) _ _).
  - intros x. simpl.
    transitivity (@t_alg _ _ _ _ h (mon_unit, x)).
    + apply (proper_morphism (@t_alg _ _ _ _ h)).
      split; [ exact (mon_op_unit_l mon_unit) | reflexivity ].
    + exact (@t_id _ _ _ _ h x).
  - intros p. exact (@t_action _ _ _ _ h p).
Defined.

(*
 Mac Lane's θ*, for the identity-component isomorphism [BG_T_ActF]:
 the identity on carriers, structure maps and arrows. 

 --------
 Mac Lane 的 θ*，对于恒等分量同构 [BG_T_ActF]：在承载体、结构映射和箭头上的恒等映射。
*)
Definition BG_Act_EM@{o so} (M : MonObject@{o o o}) :
  @EilenbergMoore@{so so so o} Sets@{o so} (U_BG@{o so} M ◯ F_BG@{o so} M)
    (BGMonad@{o so} M)
  ⟶ @EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
      (ActMonad@{o so} M).
Proof.
  unshelve refine
    (@Build_Functor
       (@EilenbergMoore@{so so so o} Sets@{o so}
          (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M))
       (fun x => (`1 x; BG_Act_alg M (`1 x) (`2 x)))
       (fun x y f =>
          @Build_TAlgebraHom Sets@{o so} (ActF@{o so} M) (ActMonad@{o so} M)
            (`1 x) (`1 y) (BG_Act_alg M (`1 x) (`2 x))
            (BG_Act_alg M (`1 y) (`2 y)) (@t_alg_hom _ _ _ _ _ _ _ f)
            (@t_alg_hom_commutes _ _ _ _ _ _ _ f)) _ _ _).
  - intros x y f g E. exact E.
  - intros x z. reflexivity.
  - intros x y z f g w. reflexivity.
Defined.

Example BG_Act_EM_carrier@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  `1 (fobj[BG_Act_EM@{o so} M] x) = `1 x := eq_refl.

Example BG_Act_EM_alg@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  @t_alg _ _ _ _ (`2 (fobj[BG_Act_EM@{o so} M] x)) = @t_alg _ _ _ _ (`2 x) :=
  eq_refl.

(* Mac Lane's G^T ∘ θ* = G^T', on the nose in both data fields. / Mac Lane 的 G^T ∘ θ* = G^T'，在两个数据域上完全一致。 *)
Example BG_Act_EM_forget_obj@{o so} (M : MonObject@{o o o})
  (x : @EilenbergMoore@{so so so o} Sets@{o so}
         (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M)) :
  fobj[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] x
  = fobj[@EM_Forget _ _ (BGMonad@{o so} M)] x := eq_refl.

Example BG_Act_EM_forget_map@{o so} (M : MonObject@{o o o})
  (x y : @EilenbergMoore@{so so so o} Sets@{o so}
           (U_BG@{o so} M ◯ F_BG@{o so} M) (BGMonad@{o so} M))
  (f : x ~> y) :
  fmap[@EM_Forget _ _ (ActMonad@{o so} M) ◯ BG_Act_EM@{o so} M] f
  = fmap[@EM_Forget _ _ (BGMonad@{o so} M)] f := eq_refl.

(*
 The tie on objects: θ* after this file's comparison functor, against
 the comparison functor of [MSet_adj] after [MSet_to], the [to] leg of
 [Fun_EM_iso]. 

 --------
 对象上的绑定：θ* 在此文件的比较函数之后，针对 [MSet_adj] 在 [MSet_to] 之后的比较函数，[to] 的 [Fun_EM_iso] 分支。
*)
Example tie_carrier@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  `1 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)
  = `1 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P) :=
  eq_refl.

Example tie_alg@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M)
  (g : carrier M) (z : carrier (fobj[P] ttt)) :
  @t_alg _ _ _ _
    (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P))
    (g, z)
  = @t_alg _ _ _ _
      (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
      (g, z) := eq_refl.

(* The same, as a function of the pair. / 相同，作为该对的函数。 *)
Example tie_alg_fun@{o so} (M : MonObject@{o o o}) (P : SetBG@{o so} M) :
  (fun p => @t_alg _ _ _ _
     (`2 (fobj[BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M)] P)) p)
  = (fun p => @t_alg _ _ _ _
       (`2 (fobj[EM_Comparison (MSet_adj@{o so} M) ◯ MSet_to@{so o} M] P))
       p) := eq_refl.

(* The tie as a functor, in Cat, with identity components. / 在 Cat 中，领结作为一个函子，具有身份分量。 *)
Definition tie@{o so c} (M : MonObject@{o o o}) :
  @equiv _
    (@homset Cat@{c so so so o} (SetBG@{o so} M)
       (@EilenbergMoore@{so so so o} Sets@{o so} (ActF@{o so} M)
          (ActMonad@{o so} M)))
    (BG_Act_EM@{o so} M ◯ EM_Comparison (BG_adj@{o so} M))
    (to (Fun_EM_iso@{o so c} M)).
Proof.
  unshelve eexists.
  - intros P.
    unshelve refine (@Build_Isomorphism _ _ _ _ _ _ _).
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + unshelve refine
        (@Build_TAlgebraHom _ _ _ _ _ _ _ (@id Sets@{o so} _) _).
      intros [g z]. simpl. reflexivity.
    + intros z. simpl. reflexivity.
    + intros z. simpl. reflexivity.
  - intros P Q f z. simpl. reflexivity.
Defined.

(** ** Groups *)

(* Riehl's statement for a group G, at Construction/Deloop.v's groups. / Riehl 在 Construction/Deloop.v 的群组中对群 G 的陈述。 *)
Definition GSet_BG_Monadic@{o so}
  (G : Category.Construction.Deloop.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so} (SetBG@{o so} G) Sets@{o so}
    (U_BG@{o so} G) :=
  U_BG_Monadic@{o so} G.

(*
 At Instance/Grp.v's groups, through Instance/Grp/Free.v's
 [grp_deloop_monoid]. 

 --------
 在 Instance/Grp.v 的组中，通过 Instance/Grp/Free.v 的 [grp_deloop_monoid]。
*)
Definition GSet_BG_Monadic_Grp@{o so}
  (G : Category.Instance.Grp.GrpObject@{o o o}) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so} (grp_deloop_monoid@{o o o} G)) Sets@{o so}
    (U_BG@{o so} (grp_deloop_monoid@{o o o} G)) :=
  U_BG_Monadic@{o so} (grp_deloop_monoid@{o o o} G).

(*
 At Structure/Group.v's groups internal to (Sets, ×), through
 Instance/Grp.v's [GroupObject_GrpObject], which asks that the
 carrier's ≈ be a proposition. 

 --------
 在 Structure/Group.v 中的 (Sets, ×) 内的群，通过 Instance/Grp.v 的 [GroupObject_GrpObject]，该文件要求载体的 ≈ 是一个命题。
*)
Definition GSet_BG_Monadic_GroupObject@{o so} (X : Sets@{o so})
  (PX : PropEquiv@{o o} X)
  (GO : @GroupObject@{so o so} Sets@{o so} Sets_CartesianMonoidal X) :
  @Monadic@{so so so so so o so so}
    (SetBG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)))
    Sets@{o so}
    (U_BG@{o so}
       (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO))) :=
  U_BG_Monadic@{o so}
    (grp_deloop_monoid@{o o o} (GroupObject_GrpObject X PX GO)).
