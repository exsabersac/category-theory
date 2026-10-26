Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Map.

Generalizable All Variables.

(** * Adjoint squares (Kelly) and Palmquist's bijection  / * 伴随平方 (Kelly) 和 Palmquist 双射*)

(*
nLab: https://ncatlab.org/nlab/show/mate
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.7,
   book p. 103, Exercises 4 and 5, verbatim:

     “4. (Kelly.) An adjoint square is an array of categories, functors,
      adjunctions, and natural transformations ⟨F,G,φ⟩ : X ⇀ A,
      ⟨F',G',φ'⟩ : X' ⇀ A', H : X → X', K : A → A', σ : F'H ⇒ KF,
      τ : HG ⇒ G'K, such that the following diagram of hom-sets always
      commutes
          A(Fx,a) --K--> A'(KFx,Ka) --(σx)*--> A'(F'Hx,Ka)
            |φ                                      |φ'
          X(x,Ga) --H--> X'(Hx,HGa) --(τa)*--> X'(Hx,G'Ka).
      Express this last condition variously in terms of unit and counit of
      the adjunctions and prove that each of σ, τ determines the other.
      (The case H = K = identity functor is that treated in the text
      above.)

      5. (Palmquist.) Given H, K, and the two adjunctions as in Exercise 4,
      establish a bijection between natural transformations α : F'HG ⇒ K
      and natural transformations β : H ⇒ G'KF.”

   (The book sets the first hom-set arrow as a superscript star,
   precomposition with σx, and the second as a subscript star,
   postcomposition with τa; both are transcribed above as a plain star.
   The code has them the same way round: in [AdjointSquare] σ enters as
   [fmap[K] k ∘ sigma x] and τ as [tau a ∘ fmap[L] ⌊ k ⌋].)

   Riehl, “Category Theory in Context”, 2nd ed., §4.3, Exercise 4.3.v asks
   in addition that the mates correspondence commute with horizontal
   composition of the bounding functors and with vertical composition of
   the adjunctions.

   TREE VOCABULARY.  Mac Lane's X is D, his A is C, his G is U, his H is
   L, and his K is K; the two adjunctions are A : F ⊣ U with F : D ⟶ C
   and U : C ⟶ D, and A' : F' ⊣ U' with F' : D' ⟶ C' and U' : C' ⟶ D'.
   His σ is a [SqSigma], his τ a [SqTau], and his commuting square is
   [AdjointSquare].

   ** What is here

   (A) The condition [AdjointSquare], quantified over EVERY transposable
   arrow, with [AdjointSquareFrom] (the same square read through the
   inverse transposes) and Mac Lane's two unit/counit forms
   [AdjointSquareUnit] and [AdjointSquareCounit]; the two mate operators
   [sq_mate] and [sq_mate_inv], defined by the transpose exactly as
   Adjunction/Conjugate.v defines [conj_mate]/[conj_mate_inv];
   and the ledger of passages between the four forms, in which EVERY
   hypothesis is an explicit argument so that each type records what it
   consumes.  [adjoint_square_iff_mate] and [adjoint_square_iff_mate_inv]
   are “each of σ, τ determines the other”.

   (B) Five [eq_refl] identifications with Adjunction/Conjugate.v at
   K = L = Id and five with Adjunction/Map.v at invertible comparison
   families, so this file is an UPGRADE of those two rather than a
   parallel construction; neither donor is edited and neither is
   re-derived.

   (C) [Transform]-typed wrappers [SqMate]/[SqMateInv] and the bijection
   [square_bijection] : sq_dom ≅ sq_cod in Sets, packaged with
   Adjunction/Conjugate.v's inline [{| carrier := … |}] idiom.

   (D) Palmquist's bijection [palmquist_bijection], built DIRECTLY with
   both round trips, together with the two generic factor bijections
   ([precomp_bijection] along F ⊣ U, [postcomp_bijection] along F' ⊣ U')
   and two factorisations of it: [palm_to_via_mate] through the mate, and
   [palm_two_factor_agrees]/[palm_two_factor_spliced] through the two
   factors.

   (E) Riehl 4.3.v as two compatibility LAWS: [adjoint_square_paste_h] and
   [sq_mate_paste_h] for horizontal pasting, [adjoint_square_paste_v] and
   [sq_mate_paste_v] for vertical pasting over Adjunction/Compose.v's
   [Adjunction_Compose].  Both mate laws are proved BY UNIQUENESS
   ([SqMate_uniq]), not by a second chase.

   ** The design decision, and why (measured)

   The condition is stated over BARE COMPONENT FAMILIES rather than over
   [Transform]s, and that choice is forced twice over.

   First, it is what makes (B) hold at Leibniz equality of TYPES.  At
   K = L = Id a [Transform]-typed condition would speak of
   F' ◯ Id[D] ⟹ Id[C] ◯ F, which is not the type F' ⟹ F: the two functor
   records carry different [fmap_respects], [fmap_id] and [fmap_comp]
   fields, which are data here.  Over bare families the padding does not
   arise, because [Compose]'s object action is literal composition
   (Theory/Functor.v, inside the [Program Definition] for [Compose]), so a
   component already has the type the bare family wants.

   Second, it is what keeps the two adjunctions' hom universes APART.
   Measured with [About] under [Set Printing Universes] on this file:
   THIRTY-SEVEN constants — the whole of section (A), the ten engine
   constants [AdjointSquare], [SqSigma], [SqTau], [SigmaNat], [TauNat],
   [sq_mate], [sq_mate_inv], [adjoint_square_iff_mate],
   [adjoint_square_iff_mate_inv] and [sq_hom_iff_from] among them, plus
   the five Map.v readbacks — carry exactly the two block equations u0 = u2 and
   u6 = u8 — each adjunction's own two hom levels — and relate the two
   PAIRS by BOUNDS only, never by an equation: u0 <= u6 and u2 <= u8, with
   the redundant consequence u0 <= u8 or u2 <= u6 also printed on six of
   the ten engine constants.  Every [Transform]-typed constant in (C), and
   every four-category one in (D), instead carries u0 = u2, u0 = u6,
   u0 = u8 and u6 = u8: all four categories' hom-and-proof levels become
   one.  The two generic factor bijections of (D) bind THREE categories and
   carry u0 = u2 and u0 = u6 only; the pasting sections of (E) collapse
   differently and are described below.  The donor of the four-equation
   collapse is [Compose]: under a section declaring the two hom levels
   strictly apart, the whole body of the condition is formable — the two
   component families, [AdjointSquare] itself, [sq_mate] and
   [adjoint_square_iff_mate] are all accepted — while [F' ◯ L], [K ◯ F],
   [L ◯ U] and [U' ◯ K] are each refused with “universe inconsistency”.

   Adjunction/Map.v's four passages are NOT reusable by instantiation, and
   the obstruction is in the TYPE rather than in the proof terms:
   [MapAdjHom] demands a family of ISOMORPHISM records ∀ x, K (F x) ≅
   F' (L x), of which a bare family supplies one leg and cannot manufacture
   the other three fields.  The four legs are therefore rebuilt here, with
   Map.v's own proofs, [to (be _)]/[from (al _)] replaced by [tau _]/
   [sigma _] and [compare_left_nat_from Hal] by the bare [SigmaNat]
   hypothesis; no new argument appears anywhere.  Map.v is not weakened:
   it becomes the invertible-comparison instance, [square_is_map_adj_hom].

   The two naturality donors are consumed rather than copied:
   Adjunction/Conjugate.v's [conj_unit_nat] and its
   [conj_counit_nat] discharge with only one adjunction and are used as
   [conj_unit_nat A g] / [conj_counit_nat A f].

   ** The ledger, by what each passage consumes

   NO naturality at all: [sq_hom_to_unit], [sq_hom_to_counit],
   [sq_hom_to_mate], [sq_hom_to_mate_inv], and [sq_hom_iff_from] in BOTH
   directions.  Only [TauNat tau]: [sq_unit_to_hom], [sq_mate_inv_to_hom],
   [sq_hom_iff_unit], [adjoint_square_iff_mate_inv],
   [adjoint_square_sq_mate_inv], [sq_mate_mate_inv], [sq_mate_inv_nat].
   Only [SigmaNat sigma]: [sq_counit_to_hom], [sq_mate_to_hom],
   [sq_hom_iff_counit], [adjoint_square_iff_mate],
   [adjoint_square_sq_mate], [sq_mate_inv_mate], [sq_mate_nat].  Both:
   [sq_unit_iff_counit].  This mirrors Map.v's ledger; the ADDITION beyond
   it is [sq_hom_iff_from], which consumes neither and which Map.v does not
   state at all (its identity-bounding-functor case is
   Adjunction/Conjugate.v's [conjugate_iff_from]).

   ** Strengths, strict first

   TWENTY-SIX statements close by [eq_refl] (criterion: a declaration whose
   body is literally [eq_refl], counted over the whole file):
   [square_is_conjugate], [square_unit_is_conjugate_unit],
   [square_counit_is_conjugate_counit], [sq_mate_is_conj_mate],
   [sq_mate_inv_is_conj_mate_inv], [square_is_map_adj_hom],
   [square_unit_is_map_adj_unit], [square_counit_is_map_adj_counit],
   [tau_nat_is_compare_right], [sigma_nat_is_compare_left_from],
   [adjoint_square_T_is_bare], [SqMate_component], [SqMateInv_component],
   [sq_dom_setoid], [sq_cod_setoid], [bracket_fobj_left],
   [bracket_fmap_left], [comp_type_left], [comp_type_right],
   [bracket_transform_type_right], [palm_dom_setoid], [palm_cod_setoid],
   [sq_mate_is_post_of_pre], [sq_mate_inv_is_pre_of_post],
   [fun_comp_assoc_component] and [AB_to_strict].  One of the twenty-six,
   [bracket_transform_type_right], is an [X = X] after parsing: [◯]
   associates to the left, so [L ⟹ U' ◯ K ◯ F] and
   [L ⟹ (U' ◯ K) ◯ F] elaborate to the same term, and the Example records
   the parser's convention rather than a bracketing fact.  The bracketing
   content sits in [bracket_fobj_left] and [bracket_fmap_left], which
   compare [F' ◯ L ◯ U] against [F' ◯ (L ◯ U)], two different records.

   Two of them carry the load in (D).  [sq_mate_is_post_of_pre] and
   [sq_mate_inv_is_pre_of_post] say that the mate ABSORBS one pre/post
   pair on the nose, which is exactly why the mate route through
   [palm_via_mate] lands every endpoint at the natural left-associated
   bracketing and needs no associator, while the two-factor route
   re-brackets its codomain and does.  [AB_to_strict] says the composite
   adjunction's transposes are definitional, which is why the vertical
   pasting goes entirely through the hom-set form and never touches the
   composite's unit or counit — the composite's unit agrees with the
   whiskered formula only up to ≈ ([AB_unit_upto], and the strict form is
   refuted).

   The identifications that hold only up to ≈, each with its cause:
   [palm_to_via_mate] (one naturality of α at ε (F x) plus
   [fmap_counit_unit]); [palm_two_factor_agrees] (one [to_adj_nat_l]);
   [palm_two_factor_spliced] (the same, plus the associator's component,
   which [fun_comp_assoc_component] pins as [fmap[U'] id] and NOT [id]);
   [sq_mate_pasting] and [sq_mate_inv_pasting] (one [to_adj_unit] resp.
   [from_adj_counit]).  Also refuted at [eq_refl], and not repaired here:
   the two bracketings (F' ◯ L) ◯ U and F' ◯ (L ◯ U) are different functor
   records although their object and arrow actions agree, so the whole-
   [Transform] statements are bracketing-sensitive where the componentwise
   ones are not; and at K = L = Id the RECORD-level comparisons with
   Adjunction/Conjugate.v ([sq_dom] against [conj_dom], [square_bijection]
   against [conjugate_bijection]) are refused, though the COMPONENT-level
   ones above are [eq_refl].

   ** Universes, off both binder and block

   Every constant that binds all four categories — 97 of the 156 — is over
   C : Category@{u u0 u0}, D : Category@{u1 u2 u2}, C' : Category@{u5 u6 u6},
   D' : Category@{u7 u8 u8}; and in EVERY [Category] binder of every
   constant in the file, the three-category factor bijections and the
   six-category pasting sections included, hom is identified with proof by
   reusing the level variable, with NO block equation saying so; a
   block-only reading reports no such identification.  One donor is
   [Adjunction]: under a section declaring ch < cp, the category, its
   hom-sets, its identities, functors in BOTH directions and a [Transform]
   between two of them are all accepted, and [Fu ⊣ Uu] is refused.
   [Compose] is a SECOND, independent donor: in the same section, with no
   adjunction in the command, [Uq ◯ Fq] is refused too, so [Adjunction] is
   sufficient but not necessary (Test/ProbeSquare398.v, N24).
   The identification of C's hom level with D's has a different and earlier
   donor, functors in both directions: [Functor] bounds source-hom by
   target-hom, so under ch < dh the type Cu ⟶ Du is accepted and Du ⟶ Cu
   is refused, before any adjunction is formed.  Neither is claimed
   unavoidable; both are inherited.

   The four OBJECT universes are free of one another throughout, and there
   is NO word-bounded [Set] in any binder or any block of the constants
   measured.  The pasting sections collapse more, and visibly: the
   horizontal one identifies the three columns' hom levels (u2 = u7,
   u2 = u10) and the vertical one identifies six categories' hom-and-proof
   levels to a single level.

   ** Pinned

   With three exceptions named at the end of this section, every
   refutation this header reports, and every universe donor it names, is
   pinned in Test/ProbeSquare398.v: 25 refutation commands = 1 instrument
   + 24 negatives (12 conversion, 3 typing, 9 formability), each stripped
   one at a time and compiled alone with its whole error read,
   rename-simulated 14/14 over the constants the negatives name.  The
   bridge Instance/Cat/Bicategory/Square.v's strict form is pinned in the
   same file.  The exceptions: of the five identifications listed above
   as holding only up to ≈, two are pinned (N1 and N2) and three are NOT
   — the strict [eq_refl] forms of [palm_two_factor_spliced],
   [sq_mate_pasting] and [sq_mate_inv_pasting] were each MEASURED to be
   refused, out of tree, and are guarded nowhere.

   ** Not delivered

   No category and no double category of adjunction squares: no identity
   square, no associativity or unit law for either pasting, no interchange
   between the two pastings, and no setoid on squares — so the mate is NOT
   exhibited AS A FUNCTOR, and Riehl 4.3.v is discharged here as the two
   compatibility LAWS in ordinary-category vocabulary: the Cat case of
   Riehl's bicategorical statement, though nothing here is formed in Cat.
   Theory/Bicategory/Mates.v's descope ledger 10, which is about an
   ARBITRARY bicategory, was left untouched by this file and that file was
   not edited by it; Instance/Adj/Bicategory.v (#399) later narrows that
   note — citing this file's two pasting laws alongside its own
   bifunctoriality result — without discharging the entry, whose
   arbitrary-bicategory and double-category content remains open.  No
   pasting for [sq_mate_inv]; nothing relates either pasting to
   Adjunction/Conjugate.v's [conjugate_compose]; no naturality of any
   of the identifications in the bounding functors; no concrete witness at
   a named pair of adjunctions; nothing is registered as an [Instance].
   The comparison with Theory/Bicategory/Mates.v's [mate] is NOT here: it
   is the sibling Instance/Cat/Bicategory/Square.v, kept separate because
   requiring Instance/Cat/Bicategory/Adjunction pulls in
   Adjunction/Natural/Transformation, whose [unit] and [counit] shadow
   Theory/Adjunction.v's.

   ** Three sentences of the issue that are stale

   Its “Missing for Exercise 4: the adjoint-square condition itself,
   quantified over all transposable arrows” is stale since #393:
   Adjunction/Map.v's [MapAdjHom] IS that square over every
   transposable arrow.  What was genuinely absent is only the BARE-FAMILY
   generality, and [square_is_map_adj_hom] measures exactly that gap by
   closing it at [eq_refl].  Its “the exercise's first ask … has exactly
   one in-tree expression” is stale twice over: Map.v states the
   unit and counit forms, with six passages between them, and at H = K = Id
   Adjunction/Conjugate.v's [conjugate_characterizations] gives four
   equivalent forms.  And its “nor the packaging as an isomorphism of
   setoids” overlooks the precedent this file copies,
   Adjunction/Conjugate.v's [conjugate_bijection].  Two further notes.
   The Riehl checkbox's command
   [rg 'mate_compose|mate_functorial|mate_hcomp|mate_vcomp'] is claimed to
   return no hits; as written, un-anchored, and run over the tree EXCLUDING
   this file (which quotes the command and so matches itself), it returns
   18 lines in 5 files — Adjunction/Choice.v, Adjunction/Parameter.v,
   Adjunction/Conjugate.v, Instance/Adj.v and Test/ProbeChoice397.v — and
   all 18 match [conj_mate_compose] as a substring.  The claim survives
   only under [rg -w], which returns none.  And the
   “associator bookkeeping lining up the two factors” turns out to be
   AVOIDABLE rather than merely unwritten: the mate route needs none, and
   where one is wanted the tree already supplies it as
   Theory/Natural/Transformation.v's [fun_comp_assoc]. 

--------
nLab：https://ncatlab.org/nlab/show/mate
 nLab：https://ncatlab.org/nlab/show/adjoint+functor

Mac Lane，“工作数学家的类别”，第二版，§IV.7，
 布克页。 103，练习 4 和 5，逐字记录：

“4.（凯利。）伴随方阵是一系列类别、函子、
 附加词和自然变换 ⟨F,G,φ⟩ : X ⇀ A,
 ⟨F',G',φ'⟩ : X' ⇀ A', H : X → X', K : A → A', σ : F'H ⇒ KF,
 τ : HG ⇒ G'K，使得下面的 hom 集图总是
 通勤
 A(Fx,a) --K--> A'(KFx,Ka) --(σx)*--> A'(F'Hx,Ka)
 |φ |φ'
 X(x,Ga) --H--> X'(Hx,HGa) --(τa)*--> X'(Hx,G'Ka)。 
用不同的单位和数量来表达最后一个条件
 附加词并证明 σ, τ 中的每一个都决定另一个。 
（H = K = 恒等函子的情况是在文本中处理的
 上面。）

5.（Palmquist。）给定 H、K 以及练习 4 中的两个附加词，
 在自然变换 α : F'HG ⇒ K 之间建立双射
 和自然变换 β : H ⇒ G'KF。“

（本书将第一个本集箭头设置为上标星，
 与 σx 预合成，第二个作为下标星，
 与 τa 进行后合成； 两者都在上面被转录为普通的星星。 
代码以相同的方式处理它们：在 [AdjointSquare] 中 σ 输入为
 [fmap[K] k ∘ sigma x] 和 τ 为 [tau a ∘ fmap[L] ⌊ k ⌋]。）

Riehl，“语境中的范畴论”，第二版，§4.3，练习 4.3.v 提出
 此外，伙伴通信以水平方式通勤
 边界函子的组成和垂直组成
 附加词。

树词汇。 Mac Lane 的 X 是 D，他的 A 是 C，他的 G 是 U，他的 H 是
 L，他的K为K； 这两个附加词是 A : F ⊣ U 和 F : D ⟶ C
 且 U : C ⟶ D，以及 A' : F' ⊣ U' 以及 F' : D' ⟶ C' 和 U' : C' ⟶ D'。 
他的 σ 是 [SqSigma]，他的 τ 是 [SqTau]，他的通勤平方是
 [AdjointSquare]。

** 这里有什么

(A) [AdjointSquare] 条件，对每个转座子进行量化
 箭头，使用 [AdjointSquareFrom]（相同的方块读取
 逆转置）和 Mac Lane 的两种单位/单位形式
 [AdjointSquareUnit] 和 [AdjointSquareCounit]； 两个配合操作员
 [sq_mate] 和 [sq_mate_inv]，由转置定义，完全相同
 Adjunction/Conjugate.v 定义 [conj_mate]/[conj_mate_inv]；
 以及四种形式之间的通道分类账，其中每个
 假设是一个明确的论点，因此每种类型都会记录它的内容
 消耗。 [adjoint_square_iff_mate] 和 [adjoint_square_iff_mate_inv]
 是“σ、τ 中的每一个决定另一个”。

(B) 五个 [eq_refl] 与 Adjunction/Conjugate.v 的识别
 K = L = Id 和 5 与 Adjunction/Map.v 进行可逆比较
 家庭，所以这个文件是这两个的升级而不是
 并行建设； 捐赠者都没有被编辑，也没有被编辑
 重新衍生。

(C) [Transform] 型包装器 [SqMate]/[SqMateInv] 和双射
 [square_bijection] : sq_dom ≅ sq_cod 套装，打包为
 Adjunction/Conjugate.v 的内联 [{| carrier := … |}] 习惯用法。

(D) Palmquist 的双射 [palmquist_bijection]，直接使用
 两次往返，以及两个通用因子双射
 （[precomp_bijection] 沿 F ⊣ U，[postcomp_bijection] 沿 F' ⊣ U'）
 以及它的两个因式分解：[palm_to_via_mate] 通过配合，以及
 [palm_two_factor_agrees]/[palm_two_factor_spliced] 通过两个
 因素。

(E) Riehl 4.3.v 作为两个兼容性法则：[adjoint_square_paste_h] 和
 [sq_mate_paste_h] 用于水平粘贴，[adjoint_square_paste_v] 和
 [sq_mate_paste_v] 用于在 Adjunction/Compose.v 上垂直粘贴
 [Adjunction_Compose]。 两条配合法则都被唯一性证明
 ([SqMate_uniq])，不是第二次追逐。

** 设计决策以及原因（测量）

该条件是在 BARE COMPONENT FAMILIES 上声明的，而不是在
 [Transform]s，这个选择被迫两次。

首先，它使得（B）在莱布尼茨类型等式上成立。 在
 K = L = Id [Transform] 类型的条件会谈到
 F' ◯ Id[D] ⟹ Id[C] ◯ F，不是类型 F' ⟹ F：两个函子
 记录携带不同的 [fmap_respects]、[fmap_id] 和 [fmap_comp]
 字段，这里是数据。 在裸露的家庭上，填充不
 出现，因为 [Compose] 的对象动作是字面组合
 （Theory/Functor.v，在 [Program Definition] 内部用于 [Compose]），所以
 组件已经具有裸家族想要的类型。

其次，它是使两个附属物的本位宇宙保持分开的原因。 在 [Set Printing Universes] 下使用 [About] 对此文件进行测量：
 三十七个常数 — (A) 部分的全部，十个引擎
 常量 [AdjointSquare]、[SqSigma]、[SqTau]、[SigmaNat]、[TauNat]、
 XPTECT51X、[sq_mate_inv]、[adjoint_square_iff_mate]、
 其中包括 [adjoint_square_iff_mate_inv] 和 [sq_hom_iff_from]，以及
 五个 Map.v 读回 — 恰好包含两个分块方程 u0 = u2 和
 u6 = u8——每个附加词自己的两个本位水平——并将两者联系起来
 仅按边界配对，从不按方程配对：u0 <= u6 且 u2 <= u8，其中
 冗余结果 u0 <= u8 或 u2 <= u6 也打印在六个上
 十个发动机常数。 (C) 中的每个 [Transform] 类型常数，以及
 (D) 中的每个四类一都带有 u0 = u2, u0 = u6,
 u0 = u8 和 u6 = u8：所有四个类别的 hom-andproof 级别变为
 一。
(D) 的两个通用因子双射绑定了三个类别并且
 仅进位 u0 = u2 和 u0 = u6； (E)折叠的粘贴部分
 有所不同，并在下面进行描述。 四方程的捐赠者
 折叠是 [Compose]：在声明两个 hom 级别的部分下
 严格分开，整个条件是可形成的——两者
 组件系列、[AdjointSquare] 本身、[sq_mate] 和
 [adjoint_square_iff_mate] 全部被接受 — 而 [F' ◯ L]、[K ◯ F]、
 [L ◯ U] 和 [U' ◯ K] 均因“宇宙不一致”而被拒绝。

Adjunction/Map.v 的四个段落不可通过实例化重用，并且
 障碍在于类型而不是证明条款：
 [MapAdjHom] 需要一系列同态记录 ∀ x, K (F x) ≅
 F' (L x)，其中一个裸家庭提供一条腿，无法制造
 其他三个字段。 因此，四条腿在这里重建，
 Map.v自己的证明，[to (be _)]/[from (al _)]替换为[tau _]/
 [sigma _] 和 [compare_left_nat_from Hal] 由裸机 [SigmaNat] 组成
 假设； 任何地方都没有出现新的论点。 Map.v 没有被削弱：
 它成为可逆比较实例 [square_is_map_adj_hom]。

这两个自然捐赠者被消耗而不是被复制：
 Adjunction/Conjugate.v 的 [conj_unit_nat] 及其
 [conj_counit_nat] 放电仅带有一个附件，用作
 [conj_unit_nat A g] / [conj_counit_nat A f]。

** 分类账，按每个通道消耗的内容

完全不自然：[sq_hom_to_unit]、[sq_hom_to_counit]、
 [sq_hom_to_mate]、[sq_hom_to_mate_inv] 和 [sq_hom_iff_from] 均包含在内
 方向。 仅 [TauNat tau]：[sq_unit_to_hom]、[sq_mate_inv_to_hom]、
 [sq_hom_iff_unit]、[adjoint_square_iff_mate_inv]、
 XPTECT87X、[sq_mate_mate_inv]、[sq_mate_inv_nat]。 
仅 [SigmaNat sigma]：[sq_counit_to_hom]、[sq_mate_to_hom]、
 [sq_hom_iff_counit]、[adjoint_square_iff_mate]、
 XPTECT95X、[sq_mate_inv_mate]、[sq_mate_nat]。 两者：
 XPTECT98X。 这反映了 Map.v 的账本； 超出的附加
 它是 [sq_hom_iff_from]，它既不消耗，也不消耗 Map.v
 完全状态（其身份边界函子情况是
 Adjunction/Conjugate.v 的 [conjugate_iff_from]）。

** 强项，严为先

26 个以 [eq_refl] 结尾的语句（标准：一个声明，其
 正文实际上是 [eq_refl]，计入整个文件）：
 [square_is_conjugate]、[square_unit_is_conjugate_unit]、
 [square_counit_is_conjugate_counit]、[sq_mate_is_conj_mate]、
 [sq_mate_inv_is_conj_mate_inv]、[square_is_map_adj_hom]、
 [square_unit_is_map_adj_unit]、[square_counit_is_map_adj_counit]、
 XPTECT111X、[sigma_nat_is_compare_left_from]、
 [adjoint_square_T_is_bare]、[SqMate_component]、[SqMateInv_component]、
 [sq_dom_setoid]、[sq_cod_setoid]、[bracket_fobj_left]、
 [bracket_fmap_left]、[comp_type_left]、[comp_type_right]、
 [bracket_transform_type_right]、[palm_dom_setoid]、[palm_cod_setoid]、
 [sq_mate_is_post_of_pre]、[sq_mate_inv_is_pre_of_post]、
 [fun_comp_assoc_component] 和 [AB_to_strict]。 二十六人之一，
 [bracket_transform_type_right]，解析后是[X = X]：[◯]
 关联到左侧，因此 [L ⟹ U' ◯ K ◯ F] 和
 [L ⟹ (U' ◯ K) ◯ F]对同一个术语进行了详细阐述，并有Example记录
 解析器的约定而不是括号事实。 包围
 内容位于 [bracket_fobj_left] 和 [bracket_fmap_left] 中，其中
 将 [F' ◯ L ◯ U] 与 [F' ◯ (L ◯ U)] 进行比较，这是两个不同的记录。

其中两个在 (D) 中承载负载。 [sq_mate_is_post_of_pre] 和
 [sq_mate_inv_is_pre_of_post] 表示伴侣吸收一前/后
 配对在鼻子上，这正是配偶穿过的原因
 [palm_via_mate] 将每个端点降落在自然左关联处
 包围并且不需要关联器，而二因素路线
 重新括号其密码域并执行此操作。 [AB_to_strict] 表示复合材料
 附加词的转置是定义性的，这就是为什么垂直
 粘贴完全通过 hom-set 形式进行，并且从未触及
 复合材料的单位或数量 — 复合材料的单位与
 晶须公式仅达到 ≈ ([AB_unit_upto]，严格形式为
 反驳）。

只支持 ≈ 的标识，每个标识都有其原因：
 [palm_to_via_mate]（α 在 ε (F x) 处的一种自然性加上
 [fmap_counit_unit]）； [palm_two_factor_agrees]（一台 [to_adj_nat_l]）；
 [palm_two_factor_spliced]（相同，加上关联器的组件，
 其中 [fun_comp_assoc_component] 引脚为 [fmap[U'] id]，而不是 [id]）；
 [sq_mate_pasting] 和 [sq_mate_inv_pasting]（分别为一个 [to_adj_unit]）
 [from_adj_counit]）。 在[eq_refl]也被驳斥了，这里没有修复：
 两个括号 (F' ◯ L) ◯ U 和 F' ◯ (L ◯ U) 是不同的函子
 记录虽然他们的目标和箭头动作一致，所以整个-
 [Transform] 语句对括号敏感，其中组件
 一些不是； 在 K = L = Id 处，记录级比较
 Adjunction/Conjugate.v（[sq_dom] 与 [conj_dom]、[square_bijection]
 针对 [conjugate_bijection]）被拒绝，尽管组件级别
 以上是[eq_refl]。

** 宇宙，脱离活页夹和块

绑定所有四个类别的每个常量（156 个类别中的 97 个）都结束了
 C : 类别@{u u0 u0}, D : 类别@{u1 u2 u2}, C' : 类别@{u5 u6 u6},
 D' : 类别@{u7 u8 u8}; 在每个 [Category] 活页夹中
 文件中的常数，三类因子双射和
 包括六类粘贴部分，通过以下证明可以识别 hom
 重用级别变量，没有块方程这么说； 一个
 仅块读取报告没有此类标识。 一名捐赠者是
 [Adjunction]：在声明 ch < cp 的部分下，类别，其
 hom-sets、它的恒等式、两个方向的函子以及 [Transform]
 其中两者之间全部接受，[Fu ⊣ Uu] 被拒绝。
[Compose] 是第二个独立捐赠者：在同一部分，没有
 命令中的附加，[Uq ◯ Fq] 也被拒绝，所以 [Adjunction] 是
 足够但不是必需的（Test/ProbeSquare398.v，N24）。 C的hom水平的鉴定与D的有不同且更早
 供体，双向函子：[Functor] 通过以下方式绑定源-hom
 target-hom，因此在 ch < dh 下，接受 Cu ⟶ Du 类型并且 Du ⟶ Cu
 在形成任何附加条件之前被拒绝。 两者都没有被声称
 不可避免的； 两者都是遗传的。

四个 OBJECT 宇宙自始至终都是相互独立的，并且
 在任何绑定器或任何常量块中都没有字限制的 [Set]
 测量。 粘贴部分塌陷得更多，并且明显可见：
 水平一标识三列的 hom 水平（u2 = u7，
 u2 = u10) 纵向的标识了六类的 hom-and-proof
 级别到单一级别。

** 固定

除了本节末尾列出的三个例外之外，每个
 反驳这个标题报告，以及它命名的每个宇宙捐赠者，是
 固定在 Test/ProbeSquare398.v 中：25 个反驳命令 = 1 个仪器
 + 24 个底片（12 个转换、3 个打字、9 个可成形性），每个都被剥离
 一次一个并单独编译并读取其整个错误，
 重命名模拟 14/14 超过常量的底片名称。 的
 桥 Instance/Cat/Bcategory/Square.v 的严格形式固定在
 相同的文件。 例外情况：上面列出的五个标识中
 因为仅保持到 ≈，所以两个被固定（N1 和 N2），三个未被固定
 — [palm_two_factor_spliced] 的严格 [eq_refl] 形式，
 [sq_mate_pasting] 和 [sq_mate_inv_pasting] 均经过测量
 拒绝了，就从树上掉下来，而且无人看守。

** 未交付

附属方格没有类别和双重类别：没有恒等性
 正方形，粘贴时没有结合性或单位定律，没有互换
 在两个粘贴之间，并且正方形上没有 setoid - 所以伴侣不是
 作为函数展示，Riehl 4.3.v 在这里作为两个
 普通类别词汇中的兼容性法则：Cat 的情况
 里尔的双范畴陈述，尽管这里没有在猫中形成。 Theory/Bcategory/Mates.v 的 descope ledger 10，大约是
 任意二类，该文件未受影响，该文件是
 未经其编辑； Instance/Adj/Bcategory.v (#399) 后来缩小了范围
 注意 - 引用该文件的两个粘贴规则以及它自己的规则
 双功能结果 - 不释放条目，其
 任意二类和双类内容仍然开放。
否
 [sq_mate_inv] 的粘贴； 与粘贴无关
 Adjunction/Conjugate.v 的 [conjugate_compose]； 没有任何自然性
 边界函子中的标识； 没有具体证人
 一对命名的附加词； 没有任何内容被注册为 [Instance]。 与 Theory/Bcategory/Mates.v 的 [mate] 的比较不在这里：它
 是同级 Instance/Cat/Bcategory/Square.v，保持独立，因为
 需要实例/Cat/Bcategory/Adjunction 拉入
 附加/自然/变换，其[unit]和[counit]的影子
 理论/附加.v's。

** 该问题的三句话已过时

它的“练习 4 缺失：伴随平方条件本身，
 对所有转座箭头进行量化”自 #393 以来已过时：
 Adjunction/Map.v 的 [MapAdjHom] 是每个的平方
 可转座箭头。 真正缺席的只是赤裸的家庭
 通用性，[square_is_map_adj_hom] 通过以下方式精确测量该差距
 在 [eq_refl] 处关闭它。 它的“练习的第一个问题……正好
 一个树内表达式”已过时两次：Map.v 指出
 单位和计数形式，它们之间有六段，并且 H = K = Id
 Adjunction/Conjugate.v 的 [conjugate_characterizations] 给出了四个
 等价形式。 它的“也不是作为同构的包装
 setoids”忽略了该文件复制的先例，
 Adjunction/Conjugate.v 的 [conjugate_bijection]。 还有两个注释。
Riehl 复选框的命令
 [rg 'mate_compose|mate_functorial|mate_hcomp|mate_vcomp'] 声称
 没有返回任何命中； 如所写，未锚定，并在树上运行，排除
 这个文件（它引用命令并因此匹配自身），它返回
 5 个文件中的 18 行 — Adjunction/Choice.v、Adjunction/Parameter.v、
 Adjunction/Conjugate.v、Instance/Adj.v 和 Test/ProbeChoice397.v — 以及
 所有 18 个都匹配 [conj_mate_compose] 作为子字符串。 索赔仍然有效
 仅在 [rg -w] 下，它不返回任何内容。 还有
 “关联簿记将两个因素联系起来”结果是
 可避免的而不是仅仅不成文：交配路线不需要，并且
 在需要的地方，树已经提供了它
 Theory/Natural/Transformation.v 的 [fun_comp_assoc]。 
*)

(* ====================================================================== *)
(* (A) The condition, over BARE component families.                        / (A) BARE 组件系列的条件。*)
(* ====================================================================== *)

Section AdjointSquareCompare.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).
Notation "'η²' x" := (@unit   _ _ _ _ A' x) (at level 9).
Notation "'ε²' a" := (@counit _ _ _ _ A' a) (at level 9).

(* The two comparison families of Mac Lane's array.  / Mac Lane 阵列的两个比较系列。*)

Definition SqSigma : Type := ∀ x : D, F' (L x) ~> K (F x).
Definition SqTau   : Type := ∀ a : C, L (U a) ~> U' (K a).

(*
Naturality, stated on the bare families.  Neither predicate mentions an
   adjunction, exactly as Map.v's [CompareLeftNat]/[CompareRightNat] do not. 

--------
自然性，就赤裸的家庭而言。 两个谓词都没有提到
 附加，正如 Map.v 的 [CompareLeftNat]/[CompareRightNat] 所没有的那样。 
*)

Definition SigmaNat (sigma : SqSigma) : Type :=
  ∀ (x y : D) (f : x ~> y),
    sigma y ∘ fmap[F'] (fmap[L] f) ≈ fmap[K] (fmap[F] f) ∘ sigma x.

Definition TauNat (tau : SqTau) : Type :=
  ∀ (a b : C) (f : a ~> b),
    tau b ∘ fmap[L] (fmap[U] f) ≈ fmap[U'] (fmap[K] f) ∘ tau a.

(*
Mac Lane's commuting square of hom-sets, quantified over every
   transposable arrow rather than evaluated at one distinguished argument. 

--------
麦克莱恩 (Mac Lane) 的通勤广场，对每个区域进行了量化
 转置箭头而不是在一个不同的参数上进行评估。 
*)

Definition AdjointSquare (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    ⌊ fmap[K] k ∘ sigma x ⌋² ≈ tau a ∘ fmap[L] ⌊ k ⌋.

(* The same square read through the inverse transposes.  / 同一个方块读取逆转置。*)

Definition AdjointSquareFrom (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (g : x ~> U a),
    ⌈ tau a ∘ fmap[L] g ⌉² ≈ fmap[K] ⌈ g ⌉ ∘ sigma x.

(*
Mac Lane's Lη = η'L and Kε = ε'K, with the comparison families split
   across the two sides in Map.v's orientation. 

--------
Mac Lane 的 Lη = η'L 和 Kε = ε'K，比较系列分开
 横跨 Map.v 方向的两侧。 
*)

Definition AdjointSquareUnit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ x : D, tau (F x) ∘ fmap[L] (η x) ≈ fmap[U'] (sigma x) ∘ η² (L x).

Definition AdjointSquareCounit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ a : C, fmap[K] (ε a) ∘ sigma (U a) ≈ ε² (K a) ∘ fmap[F'] (tau a).

(* ---- the two mate operators, defined BY THE TRANSPOSE ----  / ---- 两个配合运算符，由 TRANSPOSE 定义 ----*)

Definition sq_mate (sigma : SqSigma) : SqTau :=
  λ a, ⌊ fmap[K] (ε a) ∘ sigma (U a) ⌋².

Definition sq_mate_inv (tau : SqTau) : SqSigma :=
  λ x, ⌈ tau (F x) ∘ fmap[L] (η x) ⌉².

(* The whiskered pasting spellings, up to ≈.  / 胡须粘贴拼法，可达≈。*)

Lemma sq_mate_pasting (sigma : SqSigma) (a : C) :
  sq_mate sigma a
    ≈ fmap[U'] (fmap[K] (ε a) ∘ sigma (U a)) ∘ η² (L (U a)).
Proof. unfold sq_mate; now rewrite (to_adj_unit (H:=A')). Qed.

Lemma sq_mate_inv_pasting (tau : SqTau) (x : D) :
  sq_mate_inv tau x
    ≈ ε² (K (F x)) ∘ fmap[F'] (tau (F x) ∘ fmap[L] (η x)).
Proof. unfold sq_mate_inv; now rewrite (from_adj_counit (H:=A')). Qed.

(* ---- the ledger; every hypothesis is an explicit argument ----  / ---- 账本； 每个假设都是一个明确的论证----*)

Lemma sq_hom_to_unit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareUnit sigma tau.
Proof.
  intros H x.
  pose proof (H x (F x) id) as Hx.
  rewrite fmap_id, id_left in Hx.
  rewrite (to_adj_unit (H:=A')) in Hx.
  now rewrite <- Hx.
Qed.

Lemma sq_unit_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → AdjointSquareUnit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Ht H x a k.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite <- (H x : _ ≈ _).
  rewrite comp_assoc.
  rewrite <- (Ht (F x) a k).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now rewrite <- (to_adj_unit (H:=A)).
Qed.

Lemma sq_hom_to_counit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareCounit sigma tau.
Proof.
  intros H a.
  pose proof (H (U a) a (ε a)) as Ha.
  rewrite (to_adj_counit (H:=A)) in Ha.
  rewrite fmap_id, id_right in Ha.
  apply (snd (adj_univ (H:=A') _ _)) in Ha.
  rewrite Ha.
  now rewrite (from_adj_counit (H:=A')).
Qed.

Lemma sq_counit_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → AdjointSquareCounit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Hs H x a k.
  apply (fst (adj_univ (H:=A') _ _)).
  rewrite (from_adj_counit (H:=A')).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (H a : _ ≈ _).
  rewrite <- comp_assoc.
  rewrite (Hs _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Theorem sq_hom_iff_unit (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (AdjointSquare sigma tau ↔ AdjointSquareUnit sigma tau).
Proof.
  intros Ht; split; [ exact (sq_hom_to_unit sigma tau)
                    | exact (sq_unit_to_hom sigma tau Ht) ].
Qed.

Theorem sq_hom_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (AdjointSquare sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs; split; [ exact (sq_hom_to_counit sigma tau)
                    | exact (sq_counit_to_hom sigma tau Hs) ].
Qed.

Theorem sq_unit_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → TauNat tau →
  (AdjointSquareUnit sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs Ht; split; intro H.
  - exact (sq_hom_to_counit sigma tau (sq_unit_to_hom sigma tau Ht H)).
  - exact (sq_hom_to_unit sigma tau (sq_counit_to_hom sigma tau Hs H)).
Qed.

Theorem sq_hom_iff_from (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau ↔ AdjointSquareFrom sigma tau.
Proof.
  split.
  - intros H x a g.
    pose proof (H x a ⌈ g ⌉) as Hg.
    rewrite (from_adj_comp_law (H:=A)) in Hg.
    rewrite <- Hg.
    now rewrite (to_adj_comp_law (H:=A')).
  - intros H x a k.
    pose proof (H x a ⌊ k ⌋) as Hk.
    rewrite (to_adj_comp_law (H:=A)) in Hk.
    rewrite <- Hk.
    now rewrite (from_adj_comp_law (H:=A')).
Qed.

(* ---- each of sigma, tau determines the other ----  / ---- sigma、tau 各自决定另一个 ----*)

Theorem sq_hom_to_mate (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ a, tau a ≈ sq_mate sigma a.
Proof.
  intros H a.
  unfold sq_mate.
  rewrite (H (U a) a (ε a)).
  rewrite (to_adj_counit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem sq_mate_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (∀ a, tau a ≈ sq_mate sigma a) → AdjointSquare sigma tau.
Proof.
  intros Hs H.
  apply (sq_counit_to_hom sigma tau Hs).
  intros a.
  rewrite (H a).
  unfold sq_mate.
  rewrite <- (from_adj_counit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma →
  (AdjointSquare sigma tau ↔ (∀ a, tau a ≈ sq_mate sigma a)).
Proof.
  intros Hs; split; [ exact (sq_hom_to_mate sigma tau)
                    | exact (sq_mate_to_hom sigma tau Hs) ].
Qed.

Theorem sq_hom_to_mate_inv (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ x, sigma x ≈ sq_mate_inv tau x.
Proof.
  intros H x.
  unfold sq_mate_inv.
  rewrite (sq_hom_to_unit sigma tau H x).
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem sq_mate_inv_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (∀ x, sigma x ≈ sq_mate_inv tau x) → AdjointSquare sigma tau.
Proof.
  intros Ht H.
  apply (sq_unit_to_hom sigma tau Ht).
  intros x.
  rewrite (H x).
  unfold sq_mate_inv.
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate_inv (sigma : SqSigma) (tau : SqTau) :
  TauNat tau →
  (AdjointSquare sigma tau ↔ (∀ x, sigma x ≈ sq_mate_inv tau x)).
Proof.
  intros Ht; split; [ exact (sq_hom_to_mate_inv sigma tau)
                    | exact (sq_mate_inv_to_hom sigma tau Ht) ].
Qed.

(* ---- naturality of the two mates ----  / ---- 两个伴侣的自然性 ----*)

Lemma sq_mate_nat (sigma : SqSigma) : SigmaNat sigma → TauNat (sq_mate sigma).
Proof.
  intros Hs a b f.
  unfold sq_mate.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  apply (to_adj_respects (H:=A')).
  rewrite <- !comp_assoc.
  rewrite (Hs _ _ (fmap[U] f)).
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [| reflexivity ].
  apply fmap_respects.
  now rewrite (conj_counit_nat A f).
Qed.

Lemma sq_mate_inv_nat (tau : SqTau) : TauNat tau → SigmaNat (sq_mate_inv tau).
Proof.
  intros Ht x y f.
  unfold sq_mate_inv.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite <- (from_adj_nat_l (Adjunction:=A')).
  apply (from_adj_respects (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (conj_unit_nat A f).
  rewrite fmap_comp.
  rewrite !comp_assoc.
  now rewrite (Ht _ _ (fmap[F] f)).
Qed.

(* ---- existence, and the two round trips ----  / ---- 存在，以及两次往返 ----*)

Theorem adjoint_square_sq_mate (sigma : SqSigma) :
  SigmaNat sigma → AdjointSquare sigma (sq_mate sigma).
Proof.
  intros Hs; apply (sq_mate_to_hom sigma (sq_mate sigma) Hs).
  intro a; reflexivity.
Qed.

Theorem adjoint_square_sq_mate_inv (tau : SqTau) :
  TauNat tau → AdjointSquare (sq_mate_inv tau) tau.
Proof.
  intros Ht; apply (sq_mate_inv_to_hom (sq_mate_inv tau) tau Ht).
  intro x; reflexivity.
Qed.

Corollary sq_mate_inv_mate (sigma : SqSigma) :
  SigmaNat sigma → ∀ x, sq_mate_inv (sq_mate sigma) x ≈ sigma x.
Proof.
  intros Hs x; symmetry.
  exact (sq_hom_to_mate_inv sigma (sq_mate sigma)
           (adjoint_square_sq_mate sigma Hs) x).
Qed.

Corollary sq_mate_mate_inv (tau : SqTau) :
  TauNat tau → ∀ a, sq_mate (sq_mate_inv tau) a ≈ tau a.
Proof.
  intros Ht a; symmetry.
  exact (sq_hom_to_mate (sq_mate_inv tau) tau
           (adjoint_square_sq_mate_inv tau Ht) a).
Qed.

End AdjointSquareCompare.

(* ====================================================================== *)
(* (B) The condition SUBSUMES its two in-tree special cases, at Leibniz    / (B) 条件包含其两个树内特殊情况，在莱布尼茨*)
(*     equality of TYPES.                                                  / 类型的平等。*)
(* ====================================================================== *)

Section SquareIdCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A : F ⊣ U) (A' : F' ⊣ U').

Example square_is_conjugate (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquare A A' Id[C] Id[D] (transform[s]) (transform[t])
    = Conjugate A A' s t := eq_refl.

Example square_unit_is_conjugate_unit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareUnit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateUnit A A' s t := eq_refl.

Example square_counit_is_conjugate_counit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareCounit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateCounit A A' s t := eq_refl.

Example sq_mate_is_conj_mate (s : F' ⟹ F) (a : C) :
  sq_mate A A' Id[C] Id[D] (transform[s]) a = conj_mate A A' s a := eq_refl.

Example sq_mate_inv_is_conj_mate_inv (t : U ⟹ U') (x : D) :
  sq_mate_inv A A' Id[C] Id[D] (transform[t]) x
    = conj_mate_inv A A' t x := eq_refl.

End SquareIdCase.

Section SquareMapCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (al : ∀ x : D, K (F x) ≅ F' (L x)).
Context (be : ∀ a : C, L (U a) ≅ U' (K a)).

Example square_is_map_adj_hom :
  AdjointSquare A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjHom A A' K L al be := eq_refl.

Example square_unit_is_map_adj_unit :
  AdjointSquareUnit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjUnit A A' K L al be := eq_refl.

Example square_counit_is_map_adj_counit :
  AdjointSquareCounit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjCounit A A' K L al be := eq_refl.

Example tau_nat_is_compare_right :
  TauNat K L (fun a => to (be a)) = CompareRightNat K L be := eq_refl.

Example sigma_nat_is_compare_left_from :
  SigmaNat K L (fun x => from (al x))
    = (∀ (x y : D) (f : x ~> y),
         from (al y) ∘ fmap[F'] (fmap[L] f)
           ≈ fmap[K] (fmap[F] f) ∘ from (al x)) := eq_refl.

End SquareMapCase.

(* ====================================================================== *)
(* (C) Transform-typed wrappers and the bijection in Sets.                 / (C) 变换类型包装器和集合中的双射。*)
(* ====================================================================== *)

Section SquareBijection.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition AdjointSquareT
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) : Type :=
  AdjointSquare A A' K L (fun x => sg x) (fun a => ta a).

Example adjoint_square_T_is_bare
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta
    = AdjointSquare A A' K L (fun x => sg x) (fun a => ta a) := eq_refl.

(*
A component family of a Transform meets the bare engine with no
   transport, and [naturality_sym] IS the naturality predicate. 

--------
Transform 的组件系列满足裸机引擎的需求，无需
 传输，[naturality_sym] 是自然谓词。 
*)

Lemma transform_SigmaNat (s : F' ◯ L ⟹ K ◯ F) : SigmaNat K L (transform[s]).
Proof. intros x y f; exact (naturality_sym s x y f). Qed.

Lemma transform_TauNat (t : L ◯ U ⟹ U' ◯ K) : TauNat K L (transform[t]).
Proof. intros a b f; exact (naturality_sym t a b f). Qed.

Program Definition SqMate (sg : F' ◯ L ⟹ K ◯ F) : L ◯ U ⟹ U' ◯ K := {|
  transform := sq_mate A A' K L (transform[sg])
|}.
Next Obligation.
  symmetry; exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.

Program Definition SqMateInv (ta : L ◯ U ⟹ U' ◯ K) : F' ◯ L ⟹ K ◯ F := {|
  transform := sq_mate_inv A A' K L (transform[ta])
|}.
Next Obligation.
  symmetry; exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.

Example SqMate_component (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  SqMate sg a = sq_mate A A' K L (transform[sg]) a := eq_refl.

Example SqMateInv_component (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  SqMateInv ta x = sq_mate_inv A A' K L (transform[ta]) x := eq_refl.

Theorem AdjointSquareT_SqMate (sg : F' ◯ L ⟹ K ◯ F) :
  AdjointSquareT sg (SqMate sg).
Proof. exact (adjoint_square_sq_mate A A' K L _ (transform_SigmaNat sg)). Qed.

Theorem SqMate_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → ta ≈ SqMate sg.
Proof. intros H a; exact (sq_hom_to_mate A A' K L _ _ H a). Qed.

Theorem AdjointSquareT_SqMateInv (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT (SqMateInv ta) ta.
Proof.
  exact (adjoint_square_sq_mate_inv A A' K L _ (transform_TauNat ta)).
Qed.

Theorem SqMateInv_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → sg ≈ SqMateInv ta.
Proof. intros H x; exact (sq_hom_to_mate_inv A A' K L _ _ H x). Qed.

Definition sq_dom : SetoidObject := {| carrier := F' ◯ L ⟹ K ◯ F |}.
Definition sq_cod : SetoidObject := {| carrier := L ◯ U ⟹ U' ◯ K |}.

Example sq_dom_setoid :
  is_setoid sq_dom = @Transform_Setoid D C' (F' ◯ L) (K ◯ F) := eq_refl.
Example sq_cod_setoid :
  is_setoid sq_cod = @Transform_Setoid C D' (L ◯ U) (U' ◯ K) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition square_bijection : @Isomorphism Sets sq_dom sq_cod := {|
  to   := {| morphism := SqMate |};
  from := {| morphism := SqMateInv |}
|}.
Next Obligation.
  intros s s' Hs a; simpl; unfold sq_mate.
  now rewrite (Hs (U a)).
Qed.
Next Obligation.
  intros t t' Ht x; simpl; unfold sq_mate_inv.
  now rewrite (Ht (F x)).
Qed.
Next Obligation.
  intros t a; simpl.
  exact (sq_mate_mate_inv A A' K L (transform[t]) (transform_TauNat t) a).
Qed.
Next Obligation.
  intros s x; simpl.
  exact (sq_mate_inv_mate A A' K L (transform[s]) (transform_SigmaNat s) x).
Qed.

Definition square_nat_bijection :
  (F' ◯ L ⟹ K ◯ F) ≊ (L ◯ U ⟹ U' ◯ K) := square_bijection.

End SquareBijection.

(* ====================================================================== *)
(* (D) Palmquist's bijection, and its two factorisations.                  / (D) Palmquist 双射及其两个因式分解。*)
(* ====================================================================== *)

Section PrecompFactor.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {X : Category}.

Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

#[local] Obligation Tactic := idtac.

Program Definition pre_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z)
  : Y ⟹ Z ◯ F := {| transform := fun x => th (F x) ∘ fmap[Y] (η x) |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (fmap[F] g)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects; now rewrite (conj_unit_nat A g).
Qed.
Next Obligation. symmetry; now apply pre_to_obligation_1. Qed.

Program Definition pre_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F)
  : Y ◯ U ⟹ Z := {| transform := fun a => fmap[Z] (ε a) ∘ ps (U a) |}.
Next Obligation.
  intros Y Z ps a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ps _ _ (fmap[U] f)).
Qed.
Next Obligation. symmetry; now apply pre_from_obligation_1. Qed.

Theorem pre_from_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z) :
  pre_from (pre_to th) ≈ th.
Proof.
  intros a; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (ε a)); simpl.
  rewrite <- comp_assoc, <- fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem pre_to_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F) :
  pre_to (pre_from ps) ≈ ps.
Proof.
  intros x; simpl.
  rewrite <- comp_assoc.
  rewrite <- (naturality ps _ _ (η x)); simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite fmap_id, id_left.
Qed.

Lemma pre_to_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ◯ U ⟹ Z) :
  t ≈ t' → pre_to t ≈ pre_to t'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma pre_from_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ⟹ Z ◯ F) :
  t ≈ t' → pre_from t ≈ pre_from t'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition precomp_dom (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ◯ U ⟹ Z |}.
Definition precomp_cod (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ⟹ Z ◯ F |}.

Program Definition precomp_bijection (Y : D ⟶ X) (Z : C ⟶ X) :
  @Isomorphism Sets (precomp_dom Y Z) (precomp_cod Y Z) := {|
  to   := {| morphism := @pre_to Y Z |};
  from := {| morphism := @pre_from Y Z |}
|}.
Next Obligation. repeat intro; now apply pre_to_respects. Qed.
Next Obligation. repeat intro; now apply pre_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply pre_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply pre_from_to. Qed.

End PrecompFactor.

Section PostcompFactor.

Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context {X : Category}.

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).

#[local] Obligation Tactic := idtac.

Program Definition post_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z)
  : Y ⟹ U' ◯ Z := {| transform := fun x => ⌊ th x ⌋² |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality th _ _ g); simpl.
  now rewrite (to_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_to_obligation_1. Qed.

Program Definition post_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z)
  : F' ◯ Y ⟹ Z := {| transform := fun x => ⌈ ps x ⌉² |}.
Next Obligation.
  intros Y Z ps x y g; simpl.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality ps _ _ g); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_from_obligation_1. Qed.

Theorem post_from_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z) :
  post_from (post_to th) ≈ th.
Proof. intros x; simpl; apply (to_adj_comp_law (H:=A')). Qed.

Theorem post_to_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z) :
  post_to (post_from ps) ≈ ps.
Proof. intros x; simpl; apply (from_adj_comp_law (H:=A')). Qed.

Lemma post_to_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : F' ◯ Y ⟹ Z) :
  t ≈ t' → post_to t ≈ post_to t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Lemma post_from_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : Y ⟹ U' ◯ Z) :
  t ≈ t' → post_from t ≈ post_from t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Definition postcomp_dom (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := F' ◯ Y ⟹ Z |}.
Definition postcomp_cod (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := Y ⟹ U' ◯ Z |}.

Program Definition postcomp_bijection (Y : X ⟶ D') (Z : X ⟶ C') :
  @Isomorphism Sets (postcomp_dom Y Z) (postcomp_cod Y Z) := {|
  to   := {| morphism := @post_to Y Z |};
  from := {| morphism := @post_from Y Z |}
|}.
Next Obligation. repeat intro; now apply post_to_respects. Qed.
Next Obligation. repeat intro; now apply post_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply post_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply post_from_to. Qed.

End PostcompFactor.

Section Palmquist.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

(*
[◯] is left associative, so [F' ◯ L ◯ U] is [(F' ◯ L) ◯ U].  The two
   bracketings agree on objects and arrows but not as functor records. 

--------
[◯] 是左关联的，因此 [F' ◯ L ◯ U] 是 [(F' ◯ L) ◯ U]。 两人
 括号在对象和箭头上一致，但与函子记录不同。 
*)

Example bracket_fobj_left (a : C) :
  fobj[F' ◯ L ◯ U] a = fobj[F' ◯ (L ◯ U)] a := eq_refl.

Example bracket_fmap_left (a b : C) (f : a ~> b) :
  fmap[F' ◯ L ◯ U] f = fmap[F' ◯ (L ◯ U)] f := eq_refl.

Example comp_type_left (a : C) :
  (fobj[F' ◯ L ◯ U] a ~> fobj[K] a) = (F' (L (U a)) ~> K a) := eq_refl.

Example comp_type_right (x : D) :
  (fobj[L] x ~> fobj[U' ◯ K ◯ F] x) = (L x ~> U' (K (F x))) := eq_refl.

Example bracket_transform_type_right :
  (L ⟹ U' ◯ K ◯ F) = (L ⟹ (U' ◯ K) ◯ F) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition palm_to (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F := {|
  transform := fun x => ⌊ al (F x) ⌋² ∘ fmap[L] (η x)
|}.
Next Obligation.
  intros al x y f; simpl.
  rewrite comp_assoc.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality al _ _ (fmap[F] f)); simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (conj_unit_nat A f).
Qed.
Next Obligation. symmetry; now apply palm_to_obligation_1. Qed.

Program Definition palm_from (be : L ⟹ U' ◯ K ◯ F) : F' ◯ L ◯ U ⟹ K := {|
  transform := fun a => fmap[K] (ε a) ∘ ⌈ be (U a) ⌉²
|}.
Next Obligation.
  intros be a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality be _ _ (fmap[U] f)); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply palm_from_obligation_1. Qed.

Theorem palm_from_to (al : F' ◯ L ◯ U ⟹ K) : palm_from (palm_to al) ≈ al.
Proof.
  intros a; simpl.
  rewrite (from_adj_nat_l (Adjunction:=A')).
  rewrite (to_adj_comp_law (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε a)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

Theorem palm_to_from (be : L ⟹ U' ◯ K ◯ F) : palm_to (palm_from be) ≈ be.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (from_adj_comp_law (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- (naturality be _ _ (η x)); simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite !fmap_id, id_left.
Qed.

Lemma palm_to_respects (al al' : F' ◯ L ◯ U ⟹ K) :
  al ≈ al' → palm_to al ≈ palm_to al'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma palm_from_respects (be be' : L ⟹ U' ◯ K ◯ F) :
  be ≈ be' → palm_from be ≈ palm_from be'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition palm_dom : SetoidObject := {| carrier := F' ◯ L ◯ U ⟹ K |}.
Definition palm_cod : SetoidObject := {| carrier := L ⟹ U' ◯ K ◯ F |}.

Example palm_dom_setoid :
  is_setoid palm_dom = @Transform_Setoid C C' (F' ◯ L ◯ U) K := eq_refl.
Example palm_cod_setoid :
  is_setoid palm_cod = @Transform_Setoid D D' L (U' ◯ K ◯ F) := eq_refl.

Program Definition palmquist_bijection :
  @Isomorphism Sets palm_dom palm_cod := {|
  to   := {| morphism := palm_to |};
  from := {| morphism := palm_from |}
|}.
Next Obligation. exact palm_to_respects. Qed.
Next Obligation. exact palm_from_respects. Qed.
Next Obligation. exact palm_to_from. Qed.
Next Obligation. exact palm_from_to. Qed.

Definition palmquist_nat_bijection :
  (F' ◯ L ◯ U ⟹ K) ≊ (L ⟹ U' ◯ K ◯ F) := palmquist_bijection.

(* ---- the mate absorbs one pre/post pair ON THE NOSE ----  / ---- 配偶在鼻子上吸收一对前/后 ----*)

Example sq_mate_is_post_of_pre (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  sq_mate A A' K L (transform[sg]) a
    = ⌊ pre_from A (Y:=F' ◯ L) (Z:=K) sg a ⌋² := eq_refl.

Example sq_mate_inv_is_pre_of_post (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  sq_mate_inv A A' K L (transform[ta]) x
    = ⌈ pre_to A (Y:=L) (Z:=U' ◯ K) ta x ⌉² := eq_refl.

(* ---- Palmquist factors through the mate, with NO associator ----  / ---- Palmquist 因素通过配偶，没有关联者 ----*)

Definition palm_via_mate (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F :=
  pre_to A (Y:=L) (Z:=U' ◯ K)
    (SqMate A A' K L (pre_to A (Y:=F' ◯ L) (Z:=K) al)).

Theorem palm_to_via_mate (al : F' ◯ L ◯ U ⟹ K) :
  palm_via_mate al ≈ palm_to al.
Proof.
  intros x; simpl.
  apply compose_respects; [ | reflexivity ].
  apply (to_adj_respects (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε (F x))); simpl.
  rewrite <- comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

(* ---- the two-factor route, which DOES meet the associator ----  / ---- 双因素路由，满足关联者 ----*)

Definition palm_two_factor (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ (K ◯ F) :=
  post_to A' (Y:=L) (Z:=K ◯ F) (pre_to A (Y:=F' ◯ L) (Z:=K) al).

Theorem palm_two_factor_agrees (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  palm_to al x ≈ palm_two_factor al x.
Proof.
  simpl.
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  reflexivity.
Qed.

Theorem palm_two_factor_spliced (al : F' ◯ L ◯ U ⟹ K) :
  palm_to al ≈ fun_comp_assoc (F:=U') (G:=K) (H:=F) ∙ palm_two_factor al.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite fmap_id, id_left.
  reflexivity.
Qed.

Example fun_comp_assoc_component (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x = fmap[U'] id := eq_refl.

Theorem fun_comp_assoc_is_id (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x ≈ id.
Proof. simpl; now rewrite !fmap_id. Qed.

End Palmquist.

(* ====================================================================== *)
(* (E) Riehl 4.3.v: horizontal and vertical pasting.                       / (E) Riehl 4.3.v：水平和垂直粘贴。*)
(* ====================================================================== *)

Section HorizontalPaste.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}.
Context (A'' : F'' ⊣ U'').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (K' : C' ⟶ C'') (L' : D' ⟶ D'').

#[local] Obligation Tactic := idtac.

Program Definition paste_h_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F')
  : F'' ◯ (L' ◯ L) ⟹ (K' ◯ K) ◯ F :=
  {| transform := fun x => fmap[K'] (sg1 x) ∘ sg2 (L x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality sg1 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality sg2 _ _ (fmap[L] f)).
Qed.
Next Obligation. symmetry; now apply paste_h_sigma_obligation_1. Qed.

Program Definition paste_h_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : L' ◯ U' ⟹ U'' ◯ K')
  : (L' ◯ L) ◯ U ⟹ U'' ◯ (K' ◯ K) :=
  {| transform := fun a => ta2 (K a) ∘ fmap[L'] (ta1 a) |}.
Next Obligation.
  intros ta1 ta2 a b f; simpl.
  rewrite comp_assoc.
  rewrite (naturality ta2 _ _ (fmap[K] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality ta1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_h_tau_obligation_1. Qed.

Theorem adjoint_square_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : F'' ◯ L' ⟹ K' ◯ F') (ta2 : L' ◯ U' ⟹ U'' ◯ K') :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT A' A'' K' L' sg2 ta2 →
  AdjointSquareT A A'' (K' ◯ K) (L' ◯ L)
    (paste_h_sigma sg1 sg2) (paste_h_tau ta1 ta2).
Proof.
  intros H1 H2 x a k; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (H2 (L x) (K a) (fmap[K] k ∘ sg1 x)).
  rewrite (H1 x a k).
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F') :
  SqMate A A'' (K' ◯ K) (L' ◯ L) (paste_h_sigma sg1 sg2)
    ≈ paste_h_tau (SqMate A A' K L sg1) (SqMate A' A'' K' L' sg2).
Proof.
  symmetry.
  apply (SqMate_uniq A A'').
  apply adjoint_square_paste_h; apply AdjointSquareT_SqMate.
Qed.

End HorizontalPaste.

Section VerticalPaste.

Context {D C E : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (B : G ⊣ V).
Context {D' C' E' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {G' : C' ⟶ E'} {V' : E' ⟶ C'} (B' : G' ⊣ V').
Context (L : D ⟶ D') (K : C ⟶ C') (M : E ⟶ E').

#[local] Obligation Tactic := idtac.

Program Definition paste_v_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G)
  : (G' ◯ F') ◯ L ⟹ M ◯ (G ◯ F) :=
  {| transform := fun x => sg2 (F x) ∘ fmap[G'] (sg1 x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc.
  rewrite (naturality sg2 _ _ (fmap[F] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality sg1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_v_sigma_obligation_1. Qed.

Program Definition paste_v_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : K ◯ V ⟹ V' ◯ M)
  : L ◯ (U ◯ V) ⟹ (U' ◯ V') ◯ M :=
  {| transform := fun e => fmap[U'] (ta2 e) ∘ ta1 (V e) |}.
Next Obligation.
  intros ta1 ta2 e e2 f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality ta2 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ta1 _ _ (fmap[V] f)).
Qed.
Next Obligation. symmetry; now apply paste_v_tau_obligation_1. Qed.

Definition AB  : (G ◯ F) ⊣ (U ◯ V)     := Adjunction_Compose A B.
Definition AB' : (G' ◯ F') ⊣ (U' ◯ V') := Adjunction_Compose A' B'.

(* The composite's transposes are definitional; its unit is not.  / 复合体的转置是定义性的； 它的单位不是。*)

Example AB_to_strict (x : D) (e : E) (k : G (F x) ~> e) :
  to (@adj _ _ _ _ AB x e) k
    = to (@adj _ _ _ _ A x (V e)) (to (@adj _ _ _ _ B (F x) e) k) := eq_refl.

Theorem AB_unit_upto (x : D) :
  @unit _ _ _ _ AB x
    ≈ fmap[U] (@unit _ _ _ _ B (F x)) ∘ @unit _ _ _ _ A x.
Proof. apply Adjunction_Compose_unit. Qed.

Theorem adjoint_square_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : G' ◯ K ⟹ M ◯ G) (ta2 : K ◯ V ⟹ V' ◯ M) :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT B B' M K sg2 ta2 →
  AdjointSquareT AB AB' M L (paste_v_sigma sg1 sg2) (paste_v_tau ta1 ta2).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite (to_adj_nat_l (Adjunction:=B')).
  rewrite (H2 (F x) e k).
  rewrite <- (comp_assoc (ta2 e)
                (fmap[K] (to (@adj _ _ _ _ B (F x) e) k)) (sg1 x)).
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (H1 x (V e) (to (@adj _ _ _ _ B (F x) e) k)).
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G) :
  SqMate AB AB' M L (paste_v_sigma sg1 sg2)
    ≈ paste_v_tau (SqMate A A' K L sg1) (SqMate B B' M K sg2).
Proof.
  symmetry.
  apply (SqMate_uniq AB AB').
  apply adjoint_square_paste_v; apply AdjointSquareT_SqMate.
Qed.

End VerticalPaste.
