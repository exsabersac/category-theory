Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Isomorphism.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Functoriality of the comma construction. / 逗号构造的函子性。 *)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category
 nLab: https://ncatlab.org/nlab/show/comma+object
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Mac Lane's §II.6 Exercise 6 (2nd ed., book p. 48; catalog item
 [maclane:II.6:ex6]) asks, in paraphrase, for two things.  Part (a): with
 the three categories held fixed, the assignment sending a pair of functors
 to their comma category is the object function of a functor
 (C^E)^op ∏ C^D ⟶ Cat — contravariant in the first functor argument,
 covariant in the second.  Part (b): describe a similar functor when the
 categories themselves are also allowed to vary.  The exercise's
 cross-references (per the catalog, doc/plan/books/maclane/inventory/II.json)
 are maclane:II.6:def4, the definition of the comma category itself, and
 maclane:II.5:construction2, the functor-category exponential as a bifunctor
 Cat^op ∏ Cat ⟶ Cat — which is the exact template for the shape delivered
 here.

 This file delivers both, in the library's naming: for S : A ⟶ C and
 T : B ⟶ C the comma is [S ↓ T] (Construction/Comma.v), so part (a)'s
 domain is ([A, C])^op ∏ [B, C] and the bifunctor is [Comma_Bifunctor].

 The action on arrows.  A natural transformation σ : S' ⟹ S reindexes the
 mediating morphism by PREcomposition on the source side,

 Comma_map_left σ   : (S ↓ T) ⟶ (S' ↓ T),
 ((a, b); h : S a ~> T b)  ↦  ((a, b); h ∘ σ a : S' a ~> T b),

 which reverses direction — hence the contravariance — while a natural
 transformation τ : T ⟹ T' reindexes by POSTcomposition on the target side,

 Comma_map_right τ  : (S ↓ T) ⟶ (S ↓ T'),
 ((a, b); h)  ↦  ((a, b); τ b ∘ h),

 preserving direction.  Both are the identity on the underlying pair of
 morphisms; the commuting-square obligation is discharged by naturality of
 σ (resp. τ) pasted against the source square.  [Comma_map σ τ] performs
 both at once, sending h to (τ b ∘ h) ∘ σ a.

 Strengths achieved, stated precisely.  The two one-sided actions commute,
 and the measurement is finer than a bare equivalence:

 - [Comma_map_left_right] : Comma_map σ τ EQUALS
 Comma_map_left σ ◯ Comma_map_right τ as whole functor records, by
 [eq_refl] — stated so plainly because that composite is literally the
 definition of [Comma_map]; the content of the choice is that ONE of
 the two orders can be taken as the definition, and this is that one.
 - [Comma_map_exchange_pair] / [Comma_map_exchange_fmap] : the other
 order, Comma_map_right τ ◯ Comma_map_left σ, agrees with it on the
 underlying A ∏ B-component of every object and on every morphism, by
 [eq_refl] — so the two orders differ in one place only.
 - [Comma_map_exchange_med] : the two orders' mediating morphisms differ
 by exactly one application of associativity,
 τ b ∘ (h ∘ σ a) ≈ (τ b ∘ h) ∘ σ a.  The note beside that lemma is
 careful about what this does and does not establish.
 - [Comma_map_exchange] therefore states the exchange law at the level of
 Cat's hom-equivalence, ≈, whose witnessing natural isomorphism has
 identity-carrier components ((id, id) in both directions).

 Throughout, `≈` between functors is [Functor_Setoid] — natural isomorphism,
 which is exactly Cat's hom-equivalence (Instance/Cat.v) — so an
 isomorphism in Cat is an EQUIVALENCE of categories, not an isomorphism of
 categories.  Every functor-level `≈` proved below is witnessed by a natural
 isomorphism all of whose components are the comma morphism ((id, id); _)
 in both directions, supplied either by [comma_med_iso] — two comma objects
 over the same A ∏ B-pair whose mediating morphisms agree up to ≈ are
 isomorphic by the identity pair — or, where the two object maps are already
 convertible, by [iso_id].  Those two, with the componentwise discharge
 tactic [comma_id_carrier], carry every ≈-level proof in the file.

 Universes, measured.  [Comma_map_left], [Comma_map_right], [Comma_map] and
 [Comma_reindex] impose no identification among the hom universes of the
 categories involved — [Comma_reindex] in particular keeps all six of its
 categories' object and hom universes independent.  [Comma_Bifunctor] DOES
 force one identification, and it is [Fun]'s doing rather than this file's:
 [Fun] identifies the hom universe of its source with that of its target
 (the same effect Theory/Shapes.v records on its `_2` side), so writing
 [A, C] forces A's hom universe to agree with C's and [B, C] forces B's to
 agree with C's.  The three hom universes of A, B and C are therefore ONE
 universe in [Comma_Bifunctor]'s signature.  It is a free universe, not a
 pinned one: nothing constrains it relative to [Set], and
 [Comma_Bifunctor_above_Set] below instantiates the bifunctor at a hom
 universe declared strictly above [Set].  The three OBJECT universes stay
 independent.

 The two non-vacuity witnesses at the end of the file identify MORE, and
 for a different reason, so the paragraph above is about the five constants
 it names and not about the file: [Comma_postcompose] identifies four hom
 universes and [Comma_precompose] five.  That is [Compose]'s doing — its
 three categories share ONE hom universe — not [Fun]'s, and neither witness
 mentions a functor category.  Whether the pins are avoidable by phrasing
 those two through raw families instead of ◯ in their types is not
 investigated here.

 Relation to the iso-restricted precursor.  Construction/Comma/Isomorphism.v
 already had the action on natural ISOMORPHISMS: [Comma_Iso] is a [Proper]
 instance taking a pair of natural isomorphisms to an isomorphism of comma
 categories in Cat, assembled from four one-sided constructions.  As that
 file's own header observes, each of the four uses only one component of its
 isomorphism, so each generalizes directly to an arbitrary transformation —
 which is what the two maps above do.  The agreement is proved here at the
 sharpest available strength: eight [eq_refl] lemmas
 ([Comma_Iso_to_Left_fobj]/[_fmap] and the [from_Left], [to_Right],
 [from_Right] triples) show that each of the four constructions has the SAME
 object and morphism data as the corresponding one-sided map applied to the
 relevant isomorphism leg, with the four ≈-level restatements
 [Comma_Iso_to_Left_is_map_left] and siblings.  Note which leg, per those
 lemmas: [Comma_Iso_to_Left] consumes [from iso] and [Comma_Iso_from_Left]
 consumes [to iso], while on the covariant side [Comma_Iso_to_Right]
 consumes [to iso] and [Comma_Iso_from_Right] consumes [from iso] — the leg
 is determined by the direction of the construction as well as by the slot,
 not by the slot alone.

 One disclosure about that comparison.  [Comma_Iso] ITSELF is proved by
 [Qed] (Construction/Comma/Isomorphism.v), so its [to] and [from] legs
 are opaque and cannot be compared term-by-term with anything.  The
 comparison is therefore stated at the four transparent one-sided
 constructions it is assembled from, and the statement it proves is
 re-derived independently through the bifunctor as
 [Comma_Bifunctor_Iso] — a functor carries isomorphisms to isomorphisms, so
 part (a) subsumes the invariance result rather than merely agreeing with
 it.  No claim is made that the two isomorphisms coincide; two isomorphisms
 between the same pair of objects need not be equal, and nothing in the
 exercise asks that they be.

 Part (b), and the shape chosen for it.  The varying-categories version is
 [Comma_reindex]: given F : A ⟶ A', G : B ⟶ B', K : C ⟶ C' together with
 families filling the two squares,

 α a : S' (F a) ~> K (S a)     and     β b : K (T b) ~> T' (G b),

 each natural in its argument, one gets [Comma_reindex : (S ↓ T) ⟶ (S' ↓ T')]
 sending ((a, b); h) to ((F a, G b); β b ∘ K h ∘ α a).  The two squares are
 stated as RAW FAMILIES with their naturality equations written out, rather
 than as [Transform]s between composite functors, deliberately: S' ◯ F and
 K ◯ S are distinct functor records from the ones a specialization would
 need, so the [Transform] phrasing would force the padding-isomorphism
 bookkeeping that Instance/Cat/Bicategory/Conjugate.v pays for elsewhere
 (its [Cat_conj_padL] and siblings; Adjunction/Conjugate.v only points at
 them).  With raw
 families the specialization is immediate, and it is proved:
 [Comma_reindex_recovers_Comma_map] shows that at F = G = K = Id the
 reindexing functor IS [Comma_map σ τ] — on objects by Leibniz equality
 ([Comma_reindex_fobj_Comma_map]) after case analysis on the comma object,
 the case analysis being needed only because Coq's [prod] has no
 definitional eta, and at the level of ≈ as functors.

 What part (b) does NOT deliver, stated so the scope is not overread: the
 full 2-categorical statement — that the reindexing operation is itself
 functorial in the triple (F, G, K) with its squares, i.e. a pseudofunctor
 out of a category of such data — is not formalized, and no category of
 cells is defined.  The single reindexing functor is the useful core and is
 what is built; the identity and composition laws for it would require
 first choosing the category structure on triples-with-squares, which the
 exercise does not pin down.  [Comma_reindex_recovers_Comma_map] is the
 evidence that the chosen shape is the right generalization of part (a).

 Non-vacuity of part (b) is not left to that identity case.  Two witnesses
 move genuinely non-identity index functors through the construction, one
 per side: [Comma_postcompose K : (S ↓ T) ⟶ (K ◯ S ↓ K ◯ T)] varies the
 COMMON CODOMAIN C, carrying the mediating morphism along K
 ([Comma_postcompose_med]), and [Comma_precompose F G :
 (S ◯ F ↓ T ◯ G) ⟶ (S ↓ T)] varies the two DOMAINS A and B, moving the
 underlying pair by F and G and leaving the mediating morphism alone
 ([Comma_precompose_pair], [Comma_precompose_med]).  In both the filling
 families α and β are identities, so what the witnesses exercise is the
 naturality hypotheses and the index functors, not the coherence data.

 Siblings.  Construction/Comma/Diagram.v and Construction/Comma/Special.v
 develop the diagrammatic and special-case readings of the same
 construction; Construction/Comma/Isomorphism.v is the iso-restricted
 precursor discussed above; Construction/Comma/Limit.v and
 Construction/Comma/Creation.v supply the limit theory that GAFT consumes.
 Viewed 2-categorically the comma category is the comma OBJECT of a cospan
 in Cat (nLab, "comma object"), and part (b) is the shadow at the level of
 1-categories of that object's universal property being natural in the
 cospan; the 2-categorical development is not attempted here. 

 --------
 nLab：https://ncatlab.org/nlab/show/comma+category
 nLab：https://ncatlab.org/nlab/show/comma+object
 维基百科：https://en.wikipedia.org/wiki/Comma_categoryMac Lane §II.6 练习 6（第二版，第 48 页；目录项 [maclane:II.6:ex6]）大意请求两个内容。部分 (a)：在三类固定的情况下，将一对函子映射到它们的逗号范畴的赋值是一个函子 (C^E)^op ∏ C^D ⟶ Cat 的对象函数——在第一个函子参数上是逆变的，在第二个上是协变的。部分 (b)：在类别本身也允许变化时，描述一个类似的函子。该练习的交叉引用（根据目录，doc/plan/books/maclane/inventory/II.json）是 maclane:II.6:def4，即逗号范畴自身的定义，以及 maclane:II.5:construction2，即作为双函子的函子范畴指数 Cat^op ∏ Cat ⟶ Cat——这正是这里所给出的形状的模板。这个文件在库的命名中都提供了：对于 S : A ⟶ C 和 T : B ⟶ C，逗号是 [S ↓ T]（Construction/Comma.v），因此部分 (a) 的定义域是 ([A, C])^op ∏ [B, C]，双函子是 [Comma_Bifunctor]。

 箭头上的作用。自然变换 σ : S' ⟹ S 通过在源端进行前组合来重新索引中介态射，

 Comma_map_left σ   : (S ↓ T) ⟶ (S' ↓ T),
 ((a, b); h : S a ~> T b)  ↦  ((a, b); h ∘ σ a : S' a ~> T b),

 这会反转方向——因此是逆变的——而自然变换 τ : T ⟹ T' 则通过在目标端进行后组合来重新索引，

 Comma_map_right τ  : (S ↓ T) ⟶ (S ↓ T'),
 ((a, b); h)  ↦  ((a, b); τ b ∘ h),保持方向。两者在基础的映射对上都是恒等；交换方框的义务通过将 σ（分别是 τ）的自然性与源方框粘贴来完成。[Comma_map σ τ] 一次性执行两者，把 h 发送为 (τ b ∘ h) ∘ σ a。

 精确说明所达到的强度。两个单侧作用是可交换的，并且度量比单纯的等价更精细：-  [Comma_map_left_right]：Comma_map σ τ 等于 Comma_map_left σ ◯ Comma_map_right τ，作为整体函子记录，由 [eq_refl] — 之所以如此明确地说明，是因为该复合实际上就是 [Comma_map] 的定义；选择的内容是两种顺序中的一种可以作为定义，而这就是其中的一种。-  [Comma_map_exchange_pair] / [Comma_map_exchange_fmap]：另一种顺序，Comma_map_right τ ◯ Comma_map_left σ，在每个对象的底层 A ∏ B 分量以及每个态射上都与其一致，由 [eq_refl] — 因此这两种顺序只在一个地方不同。-  [Comma_map_exchange_med]：这两种顺序的中介态射只相差一次结合律的应用，τ b ∘ (h ∘ σ a) ≈ (τ b ∘ h) ∘ σ a。该引理旁的注释小心说明了这能建立和不能建立的内容。-  [Comma_map_exchange] 因此在 Cat 的同态等价（≈）层面陈述了交换律，其见证自然同构在两个方向上的载体分量都是恒等映射 ((id, id))。在整个过程中，函子之间的 `≈` 是 [Functor_Setoid] —— 自然同构，这正是 Cat 的同态等价（Instance/Cat.v）——因此，在 Cat 中的同构是范畴的等价，而不是范畴的同构。下面证明的每个函子级别的 `≈` 都由自然同构见证，其所有分量都是在两个方向上由逗号态射 ((id, id); _) 提供的，要么由 [comma_med_iso] 提供——两个在同一 A ∏ B 对上的逗号对象，其中介态射在 ≈ 下一致，通过恒等对是同构的——要么在两个对象映射已经可转换的情况下，由 [iso_id] 提供。这两者，加上按组件消解的策略 [comma_id_carrier]，涵盖了文件中每个 ≈ 级别的证明。宇宙，已测量。[Comma_map_left]、[Comma_map_right]、[Comma_map] 和 [Comma_reindex] 对所涉及类别的同态宇宙没有进行任何识别——尤其是 [Comma_reindex] 保持其六个类别的对象宇宙和同态宇宙相互独立。[Comma_Bifunctor] 确实强制进行了一次识别，这是 [Fun] 的操作，而非本文件的操作：[Fun] 将其源的同态宇宙与目标的同态宇宙识别（Theory/Shapes.v 在其 `_2` 端记录了同样的效果），因此写入 [A, C] 会强制 A 的同态宇宙与 C 的一致，而 [B, C] 会强制 B 的同态宇宙与 C 的一致。因此，在 [Comma_Bifunctor] 的签名中，A、B 和 C 的三个同态宇宙变为同一个宇宙。这是一个自由宇宙，而不是固定宇宙：相对于 [Set] 没有任何约束，并且下面的 [Comma_Bifunctor_above_Set] 在严格高于 [Set] 的同源宇宙中实例化了双函子。这三个 OBJECT 宇宙保持独立。

 文件末尾的两个非空性证据识别了 MORE，并且出于不同的原因，因此上面的段落是关于它所命名的五个常量，而不是关于文件：[Comma_postcompose] 识别四个同源宇宙，[Comma_precompose] 识别五个。这是 [Compose] 的操作——它的三个范畴共享一个同源宇宙——而不是 [Fun] 的操作，并且两个证据都没有提到函子范畴。通过在类型中使用原始族而不是 ◯ 来表述这两个是否可以避免固定，这里没有调查。与等距受限前体的关系。构造/逗号/同构.v 已经在自然同构上执行了操作：[Comma_Iso] 是一个 [Proper] 实例，它将一对自然同构映射到 Cat 中的逗号范畴的同构，由四个单边构造组成。正如该文件的标题所指出的，每一个构造只使用其同构的一个分量，因此每一个都可以直接推广到任意变换——这正是上面两个映射所做的。该协议以目前可得的最强形式得到证明：八个[eq_refl]引理（[Comma_Iso_to_Left_fobj] / [_fmap]和[from_Left]、[to_Right]、[from_Right]三元组）表明，每个四种结构与将相应的单边映射应用于相关同构边所得到的结果，在对象和态射数据上完全相同，并且有四个≈级别的改述[Comma_Iso_to_Left_is_map_left]及其同类。注意根据这些引理，每条边：[Comma_Iso_to_Left]使用[from iso]，而[Comma_Iso_from_Left]使用[to iso]，而在协变侧[Comma_Iso_to_Right]使用[to iso]，[Comma_Iso_from_Right]使用[from iso]——边由构造的方向以及位置决定，而不仅仅由位置决定。关于那个比较，有一点需要说明。[Comma_Iso] 本身是由 [Qed]（Construction/Comma/Isomorphism.v）证明的，因此它的 [to] 和 [from] 构件是不透明的，不能与任何东西进行逐项比较。因此，这个比较是在它所由其组装的四个透明单边构造上陈述的，而它所证明的命题是通过双函子独立重新推导出来的，成为 [Comma_Bifunctor_Iso]——一个函子将同构保持为同构，所以部分 (a) 包含的不变性结果，而不仅仅是与其一致。没有声称两个同构会重合；同一对象对之间的两个同构不需相等，并且练习中也没有要求它们必须相等。（b）部分，以及为其选择的形状。变化类别版本是
 [Comma_reindex] ：给定 F : A ⟶ A'，G : B ⟶ B'，K : C ⟶ C'，以及填充两个方格的族，

 α a : S' (F a) ~> K (S a)     和     β b : K (T b) ~> T' (G b),每一个在其论域上都是自然的，可以得到 [Comma_reindex : (S ↓ T) ⟶ (S' ↓ T')]，将 ((a, b); h) 发送到 ((F a, G b); β b ∘ K h ∘ α a)。这两个方框被表述为带有自然性方程的 RAW FAMILIES，而不是作为复合函子之间的 [Transform]，故意如此：S' ◯ F 和 K ◯ S 是与特化所需函子记录不同的，所以 [Transform] 表述会强制进行 Instance/Cat/Bicategory/Conjugate.v 在其他地方处理的填充同构簿记（其 [Cat_conj_padL] 及其同类；Adjunction/Conjugate.v 只指向它们）。对于原始家庭，专业化是即时的，并且已经被证明：[Comma_reindex_recovers_Comma_map] 表明在 F = G = K = Id 时，重索引函子是 [Comma_map σ τ] —— 在对象上通过莱布尼茨相等（[Comma_reindex_fobj_Comma_map]）在逗号对象上进行情况分析之后，仅因为 Coq 的 [prod] 没有定义性的 eta，并且在 ≈ 作为函子的层面上。（b）部分没有提供的内容，说明范围不被过度解读：完整的二范畴陈述——即重新索引操作本身在三元组 (F, G, K) 及其交换方格中具有函子性，即从此类数据的一个范畴中出的伪函子——没有被形式化，也没有定义单元格的范畴。单个重新索引函子是有用的核心，也是构建的对象；它的恒等和组合律需要首先选择含方格三元组的范畴结构，而该练习没有确定这一点。[Comma_reindex_recovers_Comma_map] 是所选形状是 (a) 部分正确推广的证据。部分 (b) 的非空性并不局限于该同一性情况。两个见证者通过构造真实地移动非同一性指标函子，每一侧一个：[Comma_postcompose K : (S ↓ T) ⟶ (K ◯ S ↓ K ◯ T)] 改变公共陪域 C，并沿 K 携带中介态射（[Comma_postcompose_med]），而 [Comma_precompose F G : (S ◯ F ↓ T ◯ G) ⟶ (S ↓ T)] 改变两个定义域 A 和 B，通过 F 和 G 移动底层对，并保持中介态射不变（[Comma_precompose_pair]，[Comma_precompose_med]）。在两个填充族 α 和 β 中都是恒等式，因此见证者执行的是自然性假设和指标函子，而不是相干数据。兄弟。Construction/Comma/Diagram.v 和 Construction/Comma/Special.v 发展了同一结构的图示和特例读法；Construction/Comma/Isomorphism.v 是上述讨论的同构限制前驱；Construction/Comma/Limit.v 和 Construction/Comma/Creation.v 提供了 GAFT 使用的极限理论。从二范畴的角度看，逗号范畴是在 Cat 中余跨度的逗号对象（nLab，“逗号对象”），而部分(b)是在对象的普适性质在余跨度下自然时其在一范畴层面的影子；此处未尝试二范畴的发展。
*)

Section CommaToolkit.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

(*
   * Two objects of a comma category over the SAME underlying A ∏ B-pair, whose
   mediating morphisms agree up to ≈, are isomorphic by the identity pair.
   This is the isomorphism of comma objects the file's natural isomorphisms
   are built from where the mediating morphisms genuinely differ; where the
   two objects are convertible, [iso_id] is used instead (five later
   proofs). 

   --------
   * 在同一基础 A ∏ B 对上的逗号范畴中，如果两个对象的中介态射在 ≈ 下相符，那么它们通过恒等对是同构的。这是文件中自然同构所建立的逗号对象同构，其中中介态射确实不同；当两个对象可互换时，使用 [iso_id]（在后面的五个证明中）。
*)

Program Definition comma_med_iso {S : A ⟶ C} {T : B ⟶ C} (X : S ↓ T)
        (k : S (fst ``X) ~{C}~> T (snd ``X)) (Heq : k ≈ `2 X) :
  @Isomorphism (S ↓ T) (``X; k) X := {|
  to   := ((id, id); _);
  from := ((id, id); _)
|}.
Next Obligation.
  rewrite !fmap_id, id_left, id_right.
  now symmetry.
Qed.
Next Obligation.
  rewrite !fmap_id, id_left, id_right.
  exact Heq.
Qed.
Next Obligation. split; simpl; apply id_left. Qed.
Next Obligation. split; simpl; apply id_left. Qed.

End CommaToolkit.

(*
   * Componentwise comparison of two functors into a comma category.  Every
   functor-level `≈` below is witnessed by a pointwise isomorphism whose two
   legs are the comma morphism ((id, id); _) — supplied either by
   [comma_med_iso] or, when the two object maps are already convertible, by
   [iso_id] — after which the [Functor_Setoid] obligation is componentwise
   `fst ``(fmap[F] f) ≈ (id ∘ fst ``(fmap[G] f)) ∘ id` and dually.  This
   tactic discharges that obligation.

   It is a tactic rather than a lemma for a typing reason worth recording:
   for arbitrary functors F and G into a comma category, the objects
   `1 (F x)` and `1 (G x)` of A ∏ B are rigid and distinct, so a hypothesis
   "the carrier of the isomorphism's leg is `id`" cannot even be STATED
   without a transport.  At each application below the two are convertible
   and the identities typecheck, which is exactly what the tactic exploits. 

   --------
   * 对进入逗号范畴的两个函子进行逐分量比较。下面的每个函子级别的 `≈` 都由一个逐点同构见证，其两条边是逗号态射 ((id, id); _) —— 由 [comma_med_iso] 提供，或者当两个对象映射已经可转换时，由 [iso_id] 提供 —— 之后 [Functor_Setoid] 的义务是逐分量的 `fst ` `(fmap [F]ZZ  f) ≈ (id ∘ fst ` `(fmap [G]ZZ  f)) ∘ id`，且对偶。该策略可以履行该义务。这是一种策略，而不是为了打字原因而值得记录的引理：
   对于任意函子 F 和 G 到逗号范畴，A ∏ B 中的对象
   `1 (F x)` 和 `1 (G x)` 是刚性的且不同的，因此一个假设
   “同构的分支的载体是 `id`” 甚至无法在没有迁移的情况下陈述。在下面的每次应用中，这两者都是可转换的，并且恒等式类型检查通过，这正是该策略所利用的。
*)

Ltac comma_id_carrier :=
  intros; simpl; split; rewrite id_left, id_right; reflexivity.

Section CommaOneSided.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

(*
   * The action on the first (source) functor argument, CONTRAVARIANT: a
   transformation σ : S' ⟹ S induces a functor (S ↓ T) ⟶ (S' ↓ T). 

   --------
   * 对第一个（源）函子参数的作用，逆变：一个变换 σ : S' ⟹ S 引起一个函子 (S ↓ T) ⟶ (S' ↓ T)。
*)

Program Definition Comma_map_left {S S' : A ⟶ C} {T : B ⟶ C} (σ : S' ⟹ S) :
  (S ↓ T) ⟶ (S' ↓ T) := {|
  fobj := fun X => (``X; `2 X ∘ transform[σ] (fst ``X));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite naturality_sym.
  rewrite comp_assoc.
  rewrite (`2 f).
  now rewrite <- comp_assoc.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

(*
   * The action on the second (target) functor argument, COVARIANT: a
   transformation τ : T ⟹ T' induces a functor (S ↓ T) ⟶ (S ↓ T'). 

   --------
   * 第二个（目标）函子参数上的作用，共变：一个变换 τ : T ⟹ T' 引出一个函子 (S ↓ T) ⟶ (S ↓ T')。
*)

Program Definition Comma_map_right {S : A ⟶ C} {T T' : B ⟶ C} (τ : T ⟹ T') :
  (S ↓ T) ⟶ (S ↓ T') := {|
  fobj := fun X => (``X; transform[τ] (snd ``X) ∘ `2 X);
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (`2 f).
  rewrite comp_assoc.
  rewrite naturality_sym.
  now rewrite <- comp_assoc.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

(*
   * Both actions at once — the arrow action of the bifunctor. It is DEFINED
   as one of the two one-sided composites, so that order of the exchange law
   holds by [eq_refl] on the whole functor record ([Comma_map_left_right]
   below), and its object action computes to

   ((a, b); h)  ↦  ((a, b); τ b ∘ h ∘ σ a). 

   --------
   * 两个动作同时进行——双函子（bifunctor）的箭头动作。它被定义为两个单边复合之一，因此交换律的顺序通过整个函子记录（如下的 [Comma_map_left_right]）成立，其对象动作计算为

   ((a, b); h)  ↦  ((a, b); τ b ∘ h ∘ σ a)。
*)

Definition Comma_map {S S' : A ⟶ C} {T T' : B ⟶ C}
           (σ : S' ⟹ S) (τ : T ⟹ T') : (S ↓ T) ⟶ (S' ↓ T') :=
  Comma_map_left σ ◯ Comma_map_right τ.

End CommaOneSided.

Section CommaMapLemmas.

Context {A B C : Category}.
Context {S S' : A ⟶ C}.
Context {T T' : B ⟶ C}.

#[local] Obligation Tactic := simpl; intros.

Lemma Comma_map_fobj (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  fobj[Comma_map σ τ] X
    = (``X; transform[τ] (snd ``X) ∘ `2 X ∘ transform[σ] (fst ``X)).
Proof. reflexivity. Qed.

Lemma Comma_map_fmap (σ : S' ⟹ S) (τ : T ⟹ T') (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_map σ τ] f) = ``f.
Proof. reflexivity. Qed.

(** [Comma_map] respects ≈ of both transformations. / [Comma_map] 尊重两种变换的 ≈。 *)

Program Definition comma_map_equiv_iso
        (σ σ' : S' ⟹ S) (τ τ' : T ⟹ T')
        (Hσ : ∀ a, transform[σ] a ≈ transform[σ'] a)
        (Hτ : ∀ b, transform[τ] b ≈ transform[τ'] b) (X : S ↓ T) :
  Comma_map σ τ X ≅ Comma_map σ' τ' X :=
  comma_med_iso (Comma_map σ' τ' X)
    (transform[τ] (snd ``X) ∘ `2 X ∘ transform[σ] (fst ``X)) _.
Next Obligation. now rewrite Hσ, Hτ. Qed.

Lemma Comma_map_respects (σ σ' : S' ⟹ S) (τ τ' : T ⟹ T')
      (Hσ : ∀ a, transform[σ] a ≈ transform[σ'] a)
      (Hτ : ∀ b, transform[τ] b ≈ transform[τ'] b) :
  Comma_map σ τ ≈ Comma_map σ' τ'.
Proof.
  exists (comma_map_equiv_iso σ σ' τ τ' Hσ Hτ); comma_id_carrier.
Qed.

(*
   * * The exchange law.

   [Comma_map σ τ] and the two one-sided composites agree.  One order is
   literally the same functor data, the other differs by exactly one
   associativity step. 

   --------
   * * 交换律。

   [Comma_map σ τ] 和两个单边复合一致。一个顺序字面上与函子数据相同，另一个仅在一个结合律步骤上不同。
*)

(*
   * One order is the definition: equality of the whole functor RECORDS, not
   merely of their object and morphism actions. 

   --------
   * 一阶是定义：整个函子 RECORDS 的等价，而不仅仅是它们的对象和态射作用的等价。
*)

Lemma Comma_map_left_right (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map σ τ = Comma_map_left σ ◯ Comma_map_right τ.
Proof. reflexivity. Qed.

(*
   * The other order agrees on the underlying pair of every object, and on
   every morphism, on the nose. 

   --------
   * 另一个顺序在每个对象的基本对以及每个态射上完全一致。
*)

Lemma Comma_map_exchange_pair (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  `1 (fobj[Comma_map_right τ ◯ Comma_map_left σ] X)
    = `1 (fobj[Comma_map_left σ ◯ Comma_map_right τ] X).
Proof. reflexivity. Qed.

Lemma Comma_map_exchange_fmap (σ : S' ⟹ S) (τ : T ⟹ T')
      (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_map_right τ ◯ Comma_map_left σ] f)
    = `1 (fmap[Comma_map_left σ ◯ Comma_map_right τ] f).
Proof. reflexivity. Qed.

(*
   * ...and their mediating morphisms differ by exactly one associativity. 

   --------
   * ...并且它们的中介态射仅在一个结合律上有所不同。
*)

Lemma Comma_map_exchange_med (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  `2 (fobj[Comma_map_right τ ◯ Comma_map_left σ] X)
    ≈ `2 (fobj[Comma_map_left σ ◯ Comma_map_right τ] X).
Proof. simpl; apply comp_assoc. Qed.

(*
   * Note what is and is not established here.  [Comma_map_exchange_pair] makes
   the corresponding LEIBNIZ statement well formed — its two sides have
   convertible types — and that statement is not closed by [eq_refl]: the two
   mediating morphisms are (τ b ∘ h) ∘ σ a and τ b ∘ (h ∘ σ a), and
   composition in an abstract category has no computation rule to bridge
   them.  A rejected-command guard would record that in the file, and is
   deliberately omitted because it would add hits to [make todo]; so the
   non-convertibility is an observation about the two displayed formulas, not
   a machine-checked claim.  What IS machine-checked is everything else in
   this block: the pair and morphism agreements by [eq_refl], and the ≈. 

   --------
   * 注意这里建立了什么和没有建立什么。[Comma_map_exchange_pair] 使相应的 LEIBNIZ 语句格式正确——它的两边具有可互换的类型——并且该语句并未被 [eq_refl] 闭合：两个中介态射是 (τ b ∘ h) ∘ σ a 和 τ b ∘ (h ∘ σ a)，而抽象范畴中的组合没有计算规则可以桥接它们。被拒绝的命令守护会将其记录在文件中，并故意省略，因为它会增加 [make todo] 的命中次数；所以不可互换性是关于两个显示公式的观察，而不是机器检验的断言。机器检验的是此块中的其他所有内容：[eq_refl] 给出的配对和态射一致性，以及 ≈。
*)

Program Definition comma_map_exchange_iso (σ : S' ⟹ S) (τ : T ⟹ T')
        (X : S ↓ T) :
  (Comma_map_right τ ◯ Comma_map_left σ) X ≅ Comma_map σ τ X :=
  comma_med_iso (Comma_map σ τ X)
    (transform[τ] (snd ``X) ∘ (`2 X ∘ transform[σ] (fst ``X))) _.
Next Obligation. apply comp_assoc. Qed.

Lemma Comma_map_right_left (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map_right τ ◯ Comma_map_left σ ≈ Comma_map σ τ.
Proof.
  exists (comma_map_exchange_iso σ τ); comma_id_carrier.
Qed.

(** The exchange law proper: the two one-sided actions commute. / 交换律本身：两个单边作用可交换。 *)

Theorem Comma_map_exchange (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_map_right τ ◯ Comma_map_left σ ≈ Comma_map_left σ ◯ Comma_map_right τ.
Proof.
  rewrite <- Comma_map_left_right.
  apply Comma_map_right_left.
Qed.

End CommaMapLemmas.

(* * * Identity and composition laws for the arrow action. / * * 箭头作用的单位元和组合律。 *)

Section CommaMapLaws.

Context {A B C : Category}.

#[local] Obligation Tactic := simpl; intros.

Program Definition comma_map_id_iso {S : A ⟶ C} {T : B ⟶ C} (X : S ↓ T) :
  Comma_map (@nat_id _ _ S) (@nat_id _ _ T) X ≅ Id X :=
  comma_med_iso X (fmap[T] (@id B (snd ``X)) ∘ `2 X ∘ fmap[S] (@id A (fst ``X)))
    _.
Next Obligation.
  rewrite !fmap_id, id_left.
  apply id_right.
Qed.

Lemma Comma_map_id {S : A ⟶ C} {T : B ⟶ C} :
  Comma_map (@nat_id _ _ S) (@nat_id _ _ T) ≈ @Id (S ↓ T).
Proof.
  exists comma_map_id_iso; comma_id_carrier.
Qed.

Program Definition comma_map_comp_iso
        {S1 S2 S3 : A ⟶ C} {T1 T2 T3 : B ⟶ C}
        (σ1 : S2 ⟹ S1) (σ2 : S3 ⟹ S2) (τ1 : T1 ⟹ T2) (τ2 : T2 ⟹ T3)
        (X : S1 ↓ T1) :
  Comma_map (nat_compose σ1 σ2) (nat_compose τ2 τ1) X
    ≅ (Comma_map σ2 τ2 ◯ Comma_map σ1 τ1) X :=
  comma_med_iso ((Comma_map σ2 τ2 ◯ Comma_map σ1 τ1) X)
    ((transform[τ2] (snd ``X) ∘ transform[τ1] (snd ``X)) ∘ `2 X
       ∘ (transform[σ1] (fst ``X) ∘ transform[σ2] (fst ``X))) _.
Next Obligation. now rewrite !comp_assoc. Qed.

Lemma Comma_map_comp {S1 S2 S3 : A ⟶ C} {T1 T2 T3 : B ⟶ C}
      (σ1 : S2 ⟹ S1) (σ2 : S3 ⟹ S2) (τ1 : T1 ⟹ T2) (τ2 : T2 ⟹ T3) :
  Comma_map (nat_compose σ1 σ2) (nat_compose τ2 τ1)
    ≈ Comma_map σ2 τ2 ◯ Comma_map σ1 τ1.
Proof.
  exists (comma_map_comp_iso σ1 σ2 τ1 τ2); comma_id_carrier.
Qed.

End CommaMapLaws.

(*
   * * Part (a): the bifunctor.

   For fixed A, B and C the comma construction is a functor
   ([A, C])^op ∏ [B, C] ⟶ Cat: contravariant in the source functor,
   covariant in the target functor. 

   --------
   * * 第（a）部分：双函子。

   对于固定的 A、B 和 C，逗号构造是一个函子
   ( [A, C] )^op ∏  [B, C]  ⟶ Cat：在源函子上是逆变的，
   在目标函子上是协变的。
*)

Section CommaBifunctor.

Context {A B C : Category}.

#[local] Obligation Tactic := idtac.

Program Definition Comma_Bifunctor : (([A, C])^op ∏ ([B, C])) ⟶ Cat := {|
  fobj := fun ST => (fst ST ↓ snd ST);
  fmap := fun _ _ στ => Comma_map (fst στ) (snd στ)
|}.
Next Obligation.
  intros ST ST' στ στ' Hst.
  apply Comma_map_respects; intros; [ sapply (fst Hst) | sapply (snd Hst) ].
Qed.
Next Obligation. intros; apply Comma_map_id. Qed.
Next Obligation. intros; apply Comma_map_comp. Qed.

(*
   * Acceptance: the bifunctor's two actions are the comma construction and
   [Comma_map] on the nose. 

   --------
   * 接受性：双函子的两个作用是逗号构造和 [Comma_map]，完全一致。
*)

Lemma Comma_Bifunctor_fobj (S : A ⟶ C) (T : B ⟶ C) :
  fobj[Comma_Bifunctor] (S, T) = (S ↓ T).
Proof. reflexivity. Qed.

Lemma Comma_Bifunctor_fmap (ST ST' : (([A, C])^op ∏ ([B, C]))%category)
      (στ : ST ~> ST') :
  fmap[Comma_Bifunctor] στ = Comma_map (fst στ) (snd στ).
Proof. reflexivity. Qed.

End CommaBifunctor.

(*
   * Universe acceptance: nothing above is pinned to [Set].  [Fun] identifies
   the hom universes of A, B and C (see the header), but the resulting single
   hom universe is free — here it is declared strictly above [Set] and the
   bifunctor is still formable. 

   --------
   * 宇宙接纳：上方没有任何内容固定在 [Set] 上。[Fun] 识别了 A、B 和 C 的同构宇宙（见标题），但最终生成的单一同构宇宙是自由的——在这里它被严格声明在 [Set] 之上，并且双函子仍然可以形成。
*)

Monomorphic Universe comma_bifun_hom.
Monomorphic Constraint Set < comma_bifun_hom.

Definition Comma_Bifunctor_above_Set
           (A B C : Category@{comma_bifun_hom comma_bifun_hom
                              comma_bifun_hom}) :=
  @Comma_Bifunctor A B C.

(*
   * * Restriction to natural isomorphisms.

   The four one-sided constructions of Construction/Comma/Isomorphism.v are
   exactly the one-sided maps above, applied to the appropriate leg of the
   given isomorphism.  Agreement holds on the nose for the functor data
   ([eq_refl] below); the ≈-level restatements follow. 

   --------
   * * 限制于自然同构。

   Construction/Comma/Isomorphism.v 的四个单边构造正好是上面的一边映射，应用于给定同构的适当部分。函子数据（下文的 [eq_refl]）在定义上完全一致；≈ 级别的重述随后给出。
*)

Section CommaIsoRestriction.

Context {A B C : Category}.

Lemma Comma_Iso_to_Left_fobj (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X : x ↓ z) :
  fobj[Comma_Iso_to_Left x y iso z] X
    = fobj[Comma_map_left (from iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Left_fmap (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X Y : x ↓ z) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_to_Left x y iso z] f)
    = `1 (fmap[Comma_map_left (from iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Left_fobj (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X : y ↓ z) :
  fobj[Comma_Iso_from_Left x y iso z] X
    = fobj[Comma_map_left (to iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Left_fmap (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C)
      (X Y : y ↓ z) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_from_Left x y iso z] f)
    = `1 (fmap[Comma_map_left (to iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Right_fobj (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X : z ↓ x) :
  fobj[Comma_Iso_to_Right x y iso z] X
    = fobj[Comma_map_right (to iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_to_Right_fmap (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X Y : z ↓ x) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_to_Right x y iso z] f)
    = `1 (fmap[Comma_map_right (to iso)] f).
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Right_fobj (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X : z ↓ y) :
  fobj[Comma_Iso_from_Right x y iso z] X
    = fobj[Comma_map_right (from iso)] X.
Proof. reflexivity. Qed.

Lemma Comma_Iso_from_Right_fmap (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C)
      (X Y : z ↓ y) (f : X ~> Y) :
  `1 (fmap[Comma_Iso_from_Right x y iso z] f)
    = `1 (fmap[Comma_map_right (from iso)] f).
Proof. reflexivity. Qed.

(*
   * The same four agreements restated at the level of Cat's hom-equivalence. 

   --------
   * 相同的四项协议在猫的同构等价层面上重新表述。
*)

Lemma Comma_Iso_to_Left_is_map_left
      (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  Comma_Iso_to_Left x y iso z ≈ Comma_map_left (from iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_from_Left_is_map_left
      (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  Comma_Iso_from_Left x y iso z ≈ Comma_map_left (to iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_to_Right_is_map_right
      (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  Comma_Iso_to_Right x y iso z ≈ Comma_map_right (to iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

Lemma Comma_Iso_from_Right_is_map_right
      (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  Comma_Iso_from_Right x y iso z ≈ Comma_map_right (from iso).
Proof.
  exists (fun _ => iso_id); comma_id_carrier.
Qed.

(*
   * The bifunctor subsumes the invariance result: a pair of natural
   isomorphisms is an isomorphism in the domain of [Comma_Bifunctor], hence
   is carried to an isomorphism of comma categories in Cat — the statement
   of [Comma_Iso], re-derived through part (a).  (No claim that the two
   isomorphisms coincide: [Comma_Iso] is [Qed]-opaque, and two isomorphisms
   between the same objects need not be equal.) 

   --------
   * 双函子包含不变性结果：一对自然同构是在  [Comma_Bifunctor]  的域中的同构，因此它被映射为 Cat 中逗号范畴的同构——这是  [Comma_Iso]  的陈述，通过部分 (a) 重新推导得到。（不声称这两个同构相同：  [Comma_Iso]  是  [Qed] -不透明的，且同一对象之间的两个同构不必相等。）
*)

#[local] Obligation Tactic := simpl; intros.

Program Definition Comma_Bifunctor_domain_iso
        {x x' : A ⟶ C} {y y' : B ⟶ C}
        (iso1 : x ≅[Fun] x') (iso2 : y ≅[Fun] y') :
  @Isomorphism (([A, C])^op ∏ ([B, C])) (x, y) (x', y') := {|
  to   := (from iso1, to iso2);
  from := (to iso1, from iso2)
|}.
Next Obligation.
  split; simpl.
  - apply (iso_to_from iso1).
  - apply (iso_to_from iso2).
Qed.
Next Obligation.
  split; simpl.
  - apply (iso_from_to iso1).
  - apply (iso_from_to iso2).
Qed.

Definition Comma_Bifunctor_Iso
        {x x' : A ⟶ C} {y y' : B ⟶ C}
        (iso1 : x ≅[Fun] x') (iso2 : y ≅[Fun] y') :
  (x ↓ y) ≅[Cat] (x' ↓ y') :=
  fobj_iso Comma_Bifunctor (x, y) (x', y')
           (Comma_Bifunctor_domain_iso iso1 iso2).

End CommaIsoRestriction.

(*
   * * Part (b): varying the categories.

   Given F : A ⟶ A', G : B ⟶ B', K : C ⟶ C' together with families filling
   the two squares — α a : S' (F a) ~> K (S a) and β b : K (T b) ~> T' (G b),
   each natural — one gets a functor (S ↓ T) ⟶ (S' ↓ T'). 

   --------
   * * 第(b)部分：改变范畴。

   已知 F : A ⟶ A'，G : B ⟶ B'，K : C ⟶ C'，以及填充两个方格的族——α a : S' (F a) ~> K (S a) 和 β b : K (T b) ~> T' (G b)，每个都是自然的——可以得到一个函子 (S ↓ T) ⟶ (S' ↓ T')。
*)

Section CommaReindex.

Context {A B C A' B' C' : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.
Context {S' : A' ⟶ C'} {T' : B' ⟶ C'}.

Context (F : A ⟶ A') (G : B ⟶ B') (K : C ⟶ C').

Context (α : ∀ a : A, S' (F a) ~{C'}~> K (S a)).
Context (α_natural : ∀ (a a' : A) (u : a ~> a'),
            α a' ∘ fmap[S'] (fmap[F] u) ≈ fmap[K] (fmap[S] u) ∘ α a).

Context (β : ∀ b : B, K (T b) ~{C'}~> T' (G b)).
Context (β_natural : ∀ (b b' : B) (v : b ~> b'),
            β b' ∘ fmap[K] (fmap[T] v) ≈ fmap[T'] (fmap[G] v) ∘ β b).

#[local] Obligation Tactic := simpl; intros.

Program Definition Comma_reindex : (S ↓ T) ⟶ (S' ↓ T') := {|
  fobj := fun X =>
    ((F (fst ``X), G (snd ``X));
     β (snd ``X) ∘ fmap[K] (`2 X) ∘ α (fst ``X));
  fmap := fun _ _ f => ((fmap[F] (fst ``f), fmap[G] (snd ``f)); _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite α_natural.
  rewrite comp_assoc.
  rewrite <- (comp_assoc (β _)).
  rewrite <- fmap_comp.
  rewrite (`2 f).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite β_natural.
  now rewrite <- !comp_assoc.
Qed.
Next Obligation.
  intros [[u v] pf] [[u' v'] pf'] [e0 e1]; simpl in *.
  split; simpl.
  - now rewrite e0.
  - now rewrite e1.
Qed.
Next Obligation. split; simpl; apply fmap_id. Qed.
Next Obligation. split; simpl; apply fmap_comp. Qed.

End CommaReindex.

Arguments Comma_reindex {A B C A' B' C' S T S' T'} F G K α α_natural β β_natural.

(*
   * [Comma_reindex] generalizes part (a): at identity index functors it IS
   [Comma_map]. The naturality hypotheses reduce to the naturality of σ and
   τ, and the two functors agree on objects by Leibniz equality — provable
   after case analysis on the comma object, which is required only because
   Coq's [prod] has no definitional eta. 

   --------
   * [Comma_reindex] 推广了部分 (a)：在恒等索引函子处，它是 [Comma_map]。自然性假设归结为 σ 和 τ 的自然性，并且通过莱布尼茨等式，可以证明两个函子在对象上是一致的 —— 在逗号对象上进行情况分析后可证明，这只是因为 Coq 的 [prod] 没有定义性的 eta。
*)

Section CommaReindexSpecializes.

Context {A B C : Category}.
Context {S S' : A ⟶ C}.
Context {T T' : B ⟶ C}.

Lemma comma_reindex_alpha (σ : S' ⟹ S) :
  ∀ (a a' : A) (u : a ~> a'),
    transform[σ] a' ∘ fmap[S'] (fmap[Id] u)
      ≈ fmap[Id] (fmap[S] u) ∘ transform[σ] a.
Proof. intros; simpl; apply naturality_sym. Qed.

Lemma comma_reindex_beta (τ : T ⟹ T') :
  ∀ (b b' : B) (v : b ~> b'),
    transform[τ] b' ∘ fmap[Id] (fmap[T] v)
      ≈ fmap[T'] (fmap[Id] v) ∘ transform[τ] b.
Proof. intros; simpl; apply naturality_sym. Qed.

Definition Comma_reindex_at_Id (σ : S' ⟹ S) (τ : T ⟹ T') :
  (S ↓ T) ⟶ (S' ↓ T') :=
  Comma_reindex Id Id Id
    (fun a => transform[σ] a) (comma_reindex_alpha σ)
    (fun b => transform[τ] b) (comma_reindex_beta τ).

Lemma Comma_reindex_fobj_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T') (X : S ↓ T) :
  fobj[Comma_reindex_at_Id σ τ] X = fobj[Comma_map σ τ] X.
Proof. destruct X as [[a b] h]; reflexivity. Qed.

Lemma Comma_reindex_fmap_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T')
      (X Y : S ↓ T) (f : X ~> Y) :
  `1 (fmap[Comma_reindex_at_Id σ τ] f) = `1 (fmap[Comma_map σ τ] f).
Proof. destruct f as [[u v] pf]; reflexivity. Qed.

Theorem Comma_reindex_recovers_Comma_map (σ : S' ⟹ S) (τ : T ⟹ T') :
  Comma_reindex_at_Id σ τ ≈ Comma_map σ τ.
Proof.
  unshelve eexists.
  - intro X.
    destruct X as [[a b] h].
    exact iso_id.
  - intros [[a b] h] [[a' b'] h'] [[u v] pf]; simpl.
    split; now rewrite id_left, id_right.
Qed.

End CommaReindexSpecializes.

(*
   * Two witnesses that [Comma_reindex] is not exercised only at identities.
   Together they move all three categories: the first varies the common
   codomain C, the second varies the two domains A and B.  In both the
   filling families are identities, so no coherence data has to be invented;
   what they demonstrate is that the naturality hypotheses are satisfiable
   with genuinely non-identity index functors. 

   --------
   * 两个证据表明 [Comma_reindex] 并非只在恒等映射下作用。  
   它们共同作用于所有三个类别：第一个变化公共陪域 C，第二个变化两个定义域 A 和 B。在这两种情况下，填充族都是恒等映射，因此无需发明任何相容性数据；它们所展示的是，自然性假设在真实的非恒等指标函子下是可满足的。
*)

Section CommaReindexPostcompose.

Context {A B C C' : Category}.
Context {S : A ⟶ C} {T : B ⟶ C}.

Lemma comma_post_alpha (K : C ⟶ C') :
  ∀ (a a' : A) (u : a ~> a'),
    id ∘ fmap[K ◯ S] (fmap[Id] u) ≈ fmap[K] (fmap[S] u) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

Lemma comma_post_beta (K : C ⟶ C') :
  ∀ (b b' : B) (v : b ~> b'),
    id ∘ fmap[K] (fmap[T] v) ≈ fmap[K ◯ T] (fmap[Id] v) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

(*
   * Post-composing both defining functors with K: the ambient category moves
   from C to C', and the mediating morphism is carried by K. 

   --------
   * 将两个定义函子都在 K 上后合成：环境范畴从 C 移动到 C'，并且中介态射由 K 携带。
*)

Definition Comma_postcompose (K : C ⟶ C') :
  (S ↓ T) ⟶ ((K ◯ S) ↓ (K ◯ T)) :=
  @Comma_reindex A B C A B C' S T (K ◯ S) (K ◯ T)
    Id Id K (fun _ => id) (comma_post_alpha K)
            (fun _ => id) (comma_post_beta K).

Lemma Comma_postcompose_med (K : C ⟶ C') (X : S ↓ T) :
  `2 (fobj[Comma_postcompose K] X) ≈ fmap[K] (`2 X).
Proof. simpl; rewrite id_left, id_right; reflexivity. Qed.

End CommaReindexPostcompose.

Section CommaReindexPrecompose.

Context {A B A' B' C : Category}.
Context {S : A' ⟶ C} {T : B' ⟶ C}.

Lemma comma_pre_alpha (F : A ⟶ A') :
  ∀ (a a' : A) (u : a ~> a'),
    id ∘ fmap[S] (fmap[F] u) ≈ fmap[Id] (fmap[S ◯ F] u) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

Lemma comma_pre_beta (G : B ⟶ B') :
  ∀ (b b' : B) (v : b ~> b'),
    id ∘ fmap[Id] (fmap[T ◯ G] v) ≈ fmap[T] (fmap[G] v) ∘ id.
Proof. intros; simpl; rewrite id_left, id_right; reflexivity. Qed.

(*
   * Pre-composing the defining functors with F and G: the two domains move
   from A, B to A', B', and the mediating morphism is untouched. 

   --------
   * 将定义函子与 F 和 G 预组合：两个范畴从 A、B 移动到 A'、B'，中介态射保持不变。
*)

Definition Comma_precompose (F : A ⟶ A') (G : B ⟶ B') :
  ((S ◯ F) ↓ (T ◯ G)) ⟶ (S ↓ T) :=
  @Comma_reindex A B C A' B' C (S ◯ F) (T ◯ G) S T
    F G Id (fun _ => id) (comma_pre_alpha F)
           (fun _ => id) (comma_pre_beta G).

Lemma Comma_precompose_pair (F : A ⟶ A') (G : B ⟶ B')
      (X : (S ◯ F) ↓ (T ◯ G)) :
  `1 (fobj[Comma_precompose F G] X) = (F (fst ``X), G (snd ``X)).
Proof. reflexivity. Qed.

Lemma Comma_precompose_med (F : A ⟶ A') (G : B ⟶ B')
      (X : (S ◯ F) ↓ (T ◯ G)) :
  `2 (fobj[Comma_precompose F G] X) ≈ `2 X.
Proof. simpl; rewrite id_left, id_right; reflexivity. Qed.

End CommaReindexPrecompose.
