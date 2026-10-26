(* * * Complete semilattices: the free ones, [Prop], and the chain 0 < 1 / * * 完全半格：自由完全半格，[Prop]，以及链 0 < 1 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.SupLat.
Require Import Category.Instance.SupLat.Free.

Generalizable All Variables.

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.2, Exercise 1(c), printed p. 142
 (PDF p. 151) — maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/suplattice
 nLab: https://ncatlab.org/nlab/show/weak+excluded+middle

 Mac Lane's part (c) reads, from the page image: “Prove conversely that
 every (small) complete semi-lattice is a 𝒫-algebra in this way”, and
 the exercise opens by recalling that “a complete semi-lattice is a
 partial order Q in which every subset S ⊂ Q has a supremum (least upper
 bound) in Q”.  Instance/SupLat.v proves (b) for every 𝒫-algebra, and
 (c) and (d) for every [SupLatObject]; a statement about every member of
 a class says nothing until the class has members, and this file
 supplies them, together with the measured reason why the smallest
 classical example, the chain false < true on bool, whose equality is
 decidable, is not one of them ([Prop], classically a two-element chain
 too, is one with no hypothesis, [Prop_SupLat]).

 P X, THE FREE ONE.  Instance/SupLat/Free.v's [FreeSL X] is the power set
 of X ordered by inclusion with union as its supremum, read back at
 [eq_refl] ([FreeSL_set], [FreeSL_le], [FreeSL_sup]).  Part (c) at P X
 has the carrier and the structure map of the free algebra (P X, μ_X) of
 Monad/Eilenberg/Moore/Adjunction.v's [EM_Free] at [eq_refl] (the
 structure maps in [FreeSL_alg], the carriers in the probe); as a whole
 algebra, and as a whole object of the Eilenberg–Moore category, it is
 refused (E3, E3b of Test/ProbeSupLat466.v), its proof fields [t_id] and
 [t_action] each differing from the free algebra's (each refused at
 [eq_refl] in a scratch copy of the probe).  Part (b) at the free
 algebra orders P X by S ∪ T ≈ T, which is inclusion
 ([FreeSL_talg_le_iff]) logically but not definitionally; since the
 order reads only the structure map, which is (c)'s at [FreeSL X] by
 conversion, that lemma is Instance/SupLat.v's [sl_talg_le_iff] at
 [FreeSL X], reused.  The
 object that (b) builds from the free algebra has the carrier and the
 supremum of [FreeSL X] at [eq_refl], and as a whole object, and in its
 order field, it is refused (E1, E1b of Test/ProbeSupLat466.v).  The
 universal property of the free complete semilattice is read off the
 adjunction's bijection elementwise: a map ψ into a complete semilattice
 extends along the singletons ([FreeSL_extend_singleton]), and every
 sup-preserving map that agrees with ψ on singletons is that extension
 ([FreeSL_extend_unique]).

 PROP, WHICH IS P 1.  [Prop_SupLat] is [Prop] ordered by implication,
 with sup S := ∃ Q ∈ S, Q ([Prop_SupLat_le], [Prop_SupLat_sup], at
 [eq_refl]); its carrier is Instance/Sets/Powerset.v's truth-value object
 [Powerset_Prop_truth], compared by mutual implication.  [Prop_P1_iso]
 is an isomorphism in [SupLat] between it and P 1, the free complete
 semilattice on Instance/Sets.v's one-point setoid [unit_setoid_object]:
 Q goes to the constant subset Q ([Prop_to_P1]), a subset T to T ttt
 ([P1_to_Prop]).  The round trip on Prop holds at [eq_refl]
 ([Prop_P1_round_trip]); on P 1 it holds at [eq_refl] at the point ttt
 and is refused as a whole subset (E2: λ _, T ttt is not T).  False ≤ True
 and True ≉ False ([Prop_SupLat_nontrivial]), so Prop is not the
 one-point lattice.

 THE CHAIN false < true ON bool IS A COMPLETE SEMILATTICE ONLY UNDER
 INFORMATIVE WEAK EXCLUDED MIDDLE.  In Instance/SupLat.v a subset is
 every ≈-respecting [Prop] predicate, so “every subset has a supremum”
 quantifies over all propositions.  [suplat_two_points_WLEM]: a complete
 semilattice with a decidable ≈ and two distinct comparable points,
 bot ≤ top with top ≉ bot, decides ¬Q or ¬¬Q for every proposition Q,
 informatively, (~ Q) + (~ ~ Q), the form of
 Instance/Mod/Cogenerator.v's [QZ_injective_WLEM].  The sup of the
 subset { x | Q ∧ x ≈ top } ([two_points_probe]) is compared with top:
 when it is top, Q cannot be refuted, since a refutation empties the
 subset and puts its sup at or below bot; when it is not, Q cannot hold,
 since then the subset is {top}.  The conclusion is informative, a sum
 and not a disjunction in [Prop], because the supremum is an operation,
 the record's setoid map [sl_sup], and not a mere existence: the proof
 decides the equality of that sup with top by the decidability of ≈,
 and from a supremum that only existed in [Prop] the same argument would
 reach only the proposition ¬Q ∨ ¬¬Q, an existence in [Prop] being
 eliminable only into a proposition.  [bool_SupLat_WLEM] instantiates
 the theorem at Instance/Sets.v's two-element setoid [bool_setoid_object]
 ordered false ≤ true ([bool_chain_le]), whose equality is decidable:
 any supremum operator for that order gives informative weak excluded
 middle.  [bool_SupLat] is the converse at that chain, not for the
 theorem in general: given wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q), it is a
 [SupLatObject] on [bool_setoid_object] ordered by [bool_chain_le], with
 sup S = true exactly when ¬¬(true ∈ S).  Both
 build the chain with [bool_chain_SupLat], which proves its four order
 axioms once.  So the chain false < true on bool is a complete
 semilattice in this library exactly under the informative weak excluded
 middle ∀ Q, (~ Q) + (~ ~ Q), which [bool_SupLat] consumes and
 [bool_SupLat_WLEM] produces, and the witnesses of non-vacuity are P X
 and Prop, which the theorem does not reach: Prop meets every hypothesis
 of the theorem but the decidability of ≈, and a decidable ≈ on it would
 give informative weak excluded middle outright
 ([Prop_SupLat_decidable_WLEM]).
 Instance/Two.v is the walking arrow, a category rather than a lattice,
 and is not used.

 STRENGTHS.  By [eq_refl]: the readbacks of [FreeSL] and [Prop_SupLat],
 [FreeSL_alg], [Prop_to_P1_at] and [Prop_P1_round_trip]; in the probe,
 also the carrier and supremum of (b) at the free algebra against
 [FreeSL X], and the P 1 round trip at ttt.  Logically ([iff]): the order
 of (b) at the free algebra against inclusion.  At ≈: the universal
 property, and [Prop_P1_iso].  Refused, each by a comparison with a
 different term or a variable that no transparency changes, and each
 standing in the probe's flip, where every [Qed] of its dependency
 closure but those it names is turned into [Defined], and again in the
 copy with Instance/Sets.v's two properness fields written as terms
 (Test/ProbeSupLat466.v records both, and Instance/SupLat/Free.v the
 second): E1, E1b, E2, E3 and E3b above.

 UNIVERSES, read off [About].  The readbacks of [FreeSL], [Prop_sup],
 [Prop_SupLat] with its readbacks, [Prop_SupLat_nontrivial],
 [two_points_probe], [suplat_two_points_WLEM] and
 [Prop_SupLat_decidable_WLEM] bind [@{o}] with the one bound [Set < o].
 The constants on P 1 add o <= Logic_lemmas.equality.u0, first carried
 by Lib/Setoid.v's [eq_equivalence] through [unit_setoid], and the
 constants on the chain the same through Instance/Sets.v's
 [bool_setoid_object]; [bool_chain_le] binds no universe ([@{}]).
 [FreeSL_extend_singleton], [FreeSL_extend_unique] and [Prop_P1_iso]
 bind [@{o so}] with the block of [SupLat@{o so}] (and [Prop_P1_iso]
 the equality cap above);
 [FreeSL_alg] and [FreeSL_talg_le_iff] add the sigma projections of
 [EilenbergMoore], o <= Projections.u1 and so <= Projections.u0.  An
 [exfalso] in the chain's proofs added o <= False_rect.u0; it was
 replaced by case analysis on the absurd hypothesis and the cap is gone.
 There is no equation and no strict bound beyond [Set < o] and [o < so].

 NOT DELIVERED.  No finite chain beyond 0 < 1 is examined; the theorem
 covers any complete semilattice with a decidable ≈ and two distinct
 comparable points.  No classical witness is given, and none is needed:
 under informative weak excluded middle [bool_SupLat] is one.  Frames
 and complete lattices of open sets are not built. 

 --------
 书籍：Mac Lane，《供数学工作者使用的范畴论》，第2版，Springer GTM 5，1998年，第VI.2节，练习题1(c)，印刷页142（PDF页151）—— maclane:VI.2:ex1
 nLab：https://ncatlab.org/nlab/show/suplattice
 nLab：https://ncatlab.org/nlab/show/weak+excluded+middleMac Lane 的第 (c) 部分从页面图像中写道：“反过来证明，每一个（小的）完备半格都是以这种方式的 𝒫-代数”，并且练习开始时回顾道“完备半格是一个偏序 Q，其中每个子集 S ⊂ Q 都有在 Q 中的上确界（最小上界）”。Instance/SupLat.v 对每个 𝒫-代数证明了 (b)，对每个 [SupLatObject] 证明了 (c) 和 (d)；关于一个类的每个成员的陈述在该类有成员之前是没有意义的，而这个文件提供了它们，以及为什么最小的经典例子——布尔上的链 false < true，其等式是可判定的——不是其中之一的理由（[Prop]，经典上也是一个两元素链，是没有假设的情况，[Prop_SupLat]）。P X，自由的。Instance/SupLat/Free.v 的 [FreeSL X] 是 X 的幂集，按包含关系排序，且并集作为其上确界，在 [eq_refl]（[FreeSL_set]、[FreeSL_le]、[FreeSL_sup]）处读取。P X 的部分 (c) 拥有自由代数 (P X, μ_X)（来自 Monad/Eilenberg/Moore/Adjunction.v 的 [EM_Free] 在 [eq_refl] 处）的载体和结构映射（结构映射在 [FreeSL_alg] 中，载体在探针中）；作为整体代数，以及作为 Eilenberg–Moore 范畴的整体对象，它被拒绝（Test/ProbeSupLat466.v 的 E3，E3b），其证明字段 [t_id] 和 [t_action] 每个都与自由代数的不同（在探针的临时副本 [eq_refl] 处每个都被拒绝）。在自由代数中，部分 (b) 将 P X 按照 S ∪ T ≈ T 排序，这在逻辑上是包含关系（[FreeSL_talg_le_iff]），但在定义上不是；因为该顺序仅读取结构映射，而该映射在 [FreeSL X] 由 (c) 通过转换得到，因此该引理是 Instance/SupLat.v 中 [sl_talg_le_iff] 在 [FreeSL X] 的重用对象。(b) 从自由代数构建的对象具有 [FreeSL X] 在 [eq_refl] 的承载体和上确界，并且作为整体对象，在其顺序域中，它被拒绝（Test/ProbeSupLat466.v 的 E1, E1b）。自由完全半格的普遍性质是通过伴随的逐元素双射读取的：进入完整半格的映射 ψ 沿单元素集（[FreeSL_extend_singleton]）扩展，并且与 ψ 在单元素集上一致的每个保持上确界的映射都是该扩展（[FreeSL_extend_unique]）。命题 PROP，它是 P1。[Prop_SupLat] 是由含意顺序的 [Prop]，具有上确界 S := ∃ Q ∈ S, Q([Prop_SupLat_le], [Prop_SupLat_sup], 在 [eq_refl])；它的承载体是 Instance/Sets/Powerset.v 的真值对象 [Powerset_Prop_truth]，通过相互含意进行比较。[Prop_P1_iso] 是 [SupLat] 中它与 P1 之间的同构，P1 是 Instance/Sets.v 的单点集体 [unit_setoid_object] 上的自由完备半格：Q 映射到常量子集 Q([Prop_to_P1])，一个子集 T 映射到 T ttt([P1_to_Prop])。命题上的往返操作成立在 [eq_refl] ([Prop_P1_round_trip])；在 P1 上，它在点 ttt 的 [eq_refl] 处成立，并且作为整个子集被拒绝 (E2: λ _, T ttt 不是 T)。False ≤ True 并且 True ≉ False ([Prop_SupLat_nontrivial])，所以命题 Prop 不是单点格。只有在信息性弱排中律下，链 false < true 在布尔上是一个完全半格。在 Instance/SupLat.v 中，一个子集是每个 ≈-尊重的 [Prop] 谓词，所以“每个子集都有上确界”是对所有命题进行量化。[suplat_two_points_WLEM]：一个具有可判定 ≈ 和两个不同可比较点的完全半格，bot ≤ top 且 top ≉ bot，对每个命题 Q 信息性地决定 ¬Q 或 ¬¬Q，即 (~ Q) + (~ ~ Q)，这是 Instance/Mod/Cogenerator.v 的 [QZ_injective_WLEM] 的形式。子集 { x | Q ∧ x ≈ top } ([two_points_probe]) 的上确界与 top 进行比较：当它是 top 时，Q 无法被驳斥，因为驳斥会使子集变空并将其上确界置于 bot 或以下；当它不是 top 时，Q 无法成立，因为此时子集为 {top}。结论是信息性的，是一个和，而不是在 [Prop] 中的析取，因为上确界是一种运算，记录的集合等价映射是 [sl_sup]，而不仅仅是存在：证明通过 ≈ 的可判定性来决定该上确界与 top 的相等性，而如果只是存在于 [Prop] 中的上确界，相同的论证只能得出命题 ¬Q ∨ ¬¬Q，[Prop] 中的存在只能消去为命题。[bool_SupLat_WLEM] 在 Instance/Sets.v 的两个元素集合等价 [bool_setoid_object] 上实例化了定理，该集合等价按 false ≤ true 排序（[bool_chain_le]），其相等性是可判定的：对于该顺序的任何上确界运算符都给出信息性弱排中律。[bool_SupLat] 是该链的逆命题，而不是定理的一般情况：给定 wlem : ∀ Q : 命题, (~ Q) + (~ ~ Q)，它是在 [bool_setoid_object] 上由 [bool_chain_le] 排序的 [SupLatObject]，当且仅当 ¬¬(true ∈ S) 时，sup S = true。两者都使用 [bool_chain_SupLat] 构建链，这一次证明其四个序关系公理。因此，bool 上的链 false < true 在这个库中恰好是一个完备半格，正好在信息性弱排中值律 ∀ Q, (~ Q) + (~ ~ Q) 下，它由 [bool_SupLat] 消耗并由 [bool_SupLat_WLEM] 生成，而非空性的证据是 P X 和 Prop，定理无法触及：Prop 满足定理的每个假设，但 ≈ 的可判定性不是，而它上的可判定 ≈ 将直接给出信息性弱排中值律 ( [Prop_SupLat_decidable_WLEM] )。Instance/Two.v 是行进箭头，是一种范畴而不是格，并且未被使用。优势。由 [eq_refl] 提供：[FreeSL] 和 [Prop_SupLat] 的回读，[FreeSL_alg]、[Prop_to_P1_at] 和 [Prop_P1_round_trip]；在探针中，还包括自由代数中 (b) 的载体和上确界，以对抗 [FreeSL X]，以及 ttt 时的 P1 往返。逻辑上 ([iff])：自由代数中 (b) 对包含的阶。约为 ≈：其普适性，以及 [Prop_P1_iso]。每个都被拒绝，通过与不同项或不改变透明性的变量进行比较，每个都位于探针的翻转中，其中依赖闭包中的每个 [Qed]（除了它所命名的那些）都被转换为 [Defined]，并且在带有 Instance/Sets.v 的两个适当性字段作为项写入的副本中再次出现（Test/ProbeSupLat466.v 记录两者，而 Instance/SupLat/Free.v 记录第二个）：E1、E1b、E2、E3 和上文 E3b。宇宙，读出 [About]。[FreeSL]、[Prop_sup]、[Prop_SupLat] 及其读回、[Prop_SupLat_nontrivial]、[two_points_probe]、[suplat_two_points_WLEM] 和 [Prop_SupLat_decidable_WLEM] 将 [@{o}] 与已绑定的 [Set < o] 绑定。在 P1 上的常量增加 o <= Logic_lemmas.equality.u0，最初通过 Lib/Setoid.v 的 [eq_equivalence] 传递到 [unit_setoid]，并且链上的常量在 Instance/Sets.v 的 [bool_setoid_object] 中相同；[bool_chain_le] 不绑定任何宇宙（[@{}]）。[FreeSL_extend_singleton]、[FreeSL_extend_unique] 和 [Prop_P1_iso] 将 [@{o so}] 与 [SupLat@{o so}] 的区块绑定（以及 [Prop_P1_iso] 上方的等式帽）；[FreeSL_alg] 和 [FreeSL_talg_le_iff] 增加 [EilenbergMoore] 的 sigma 投影，o <= Projections.u1 并且 so <= Projections.u0。在链的证明中，[exfalso] 添加了 o <= False_rect.u0；它被通过对荒谬假设的情况分析所替代，cap 消失了。没有方程，也没有严格的界限，除了 [Set < o] 和 [o < so]。

 未交付。没有检验 0 < 1 以外的有限链；该定理适用于任何具有可判定 ≈ 和两个不同可比较点的完全半格。没有给出经典的证据，也不需要：在信息性弱排中律下，[bool_SupLat] 是一个。框架和开集的完全格没有构建。
*)

(* ------------------------------------------------------------------------ *)
(* * ** P X, the free complete semilattice / * ** P X，自由完全半格 *)

Example FreeSL_set@{o} (X : SetoidObject@{o o}) :
  sl_set (FreeSL@{o} X) = Powerset_Prop_obj@{o} X := eq_refl.

Example FreeSL_le@{o} (X : SetoidObject@{o o})
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  sl_le (FreeSL@{o} X) S T = (∀ z, S z → T z) := eq_refl.

Example FreeSL_sup@{o} (X : SetoidObject@{o o}) :
  sl_sup (FreeSL@{o} X) = @Powerset_union@{o} X := eq_refl.

(* (c) at P X has the structure map of the free algebra (P X, μ_X); as a whole algebra it is refused (E3 of Test/ProbeSupLat466.v). / (c) 在 P X 处具有自由代数 (P X, μ_X) 的结构映射；作为一个整体代数，它被拒绝（Test/ProbeSupLat466.v 的 E3）。 *)
Example FreeSL_alg@{o so} (X : SetoidObject@{o o}) :
  t_alg[projT2 (fobj[SupLat_to_EM@{o so}] (FreeSL@{o} X))]
    = t_alg[projT2 (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                          Powerset_Monad@{o so}] X)] := eq_refl.

(*
 (b) at the free algebra: Mac Lane's order S ∪ T ≈ T is inclusion.  The
 free algebra's structure map is (c)'s at [FreeSL X] by conversion
 ([FreeSL_alg]) and the order reads only that map, so this is
 Instance/SupLat.v's [sl_talg_le_iff] there. 

 --------
 (b) 在自由代数上：Mac Lane 的顺序 S ∪ T ≈ T 是包含关系。自由代数的结构映射是通过转换 ([FreeSL_alg]) 在 [FreeSL X] 上的 (c) 的映射，并且顺序只读取该映射，所以这是 Instance/SupLat.v 的 [sl_talg_le_iff] 在那里。
*)
Lemma FreeSL_talg_le_iff@{o so} (X : SetoidObject@{o o})
  (S T : carrier (Powerset_Prop_obj@{o} X)) :
  iff (sl_le (fobj[EM_to_SupLat@{o so}]
                (fobj[@EM_Free Sets@{o so} Powerset_Prop@{o so}
                        Powerset_Monad@{o so}] X)) S T)
      (sl_le (FreeSL@{o} X) S T).
Proof. exact (sl_talg_le_iff@{o so} (FreeSL@{o} X) S T). Qed.

(*
 The universal property of P X, elementwise: a map ψ into a complete
 semilattice extends along the singletons, and uniquely so. 

 --------
 P X 的普遍性质，按元素：映射 ψ 到一个完全半格沿单元集合扩展，并且是唯一的。
*)
Lemma FreeSL_extend_singleton@{o so} {X : SetoidObject@{o o}}
  {A : SupLatObject@{o}} (ψ : X ~{Sets@{o so}}~> sl_set A) (x : carrier X) :
  @equiv _ (is_setoid (sl_set A))
    (slh_map (SL_extend@{o so} ψ) (Powerset_Prop_singleton_pred@{o} x)) (ψ x).
Proof. exact (@iso_to_from _ _ _ (SL_adj_iso@{o so} X A) ψ x). Qed.

Lemma FreeSL_extend_unique@{o so} {X : SetoidObject@{o o}}
  {A : SupLatObject@{o}} (φ : SupLatHom@{o} (FreeSL@{o} X) A)
  (ψ : X ~{Sets@{o so}}~> sl_set A)
  (H : ∀ x, @equiv _ (is_setoid (sl_set A))
              (slh_map φ (Powerset_Prop_singleton_pred@{o} x)) (ψ x))
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  @equiv _ (is_setoid (sl_set A)) (slh_map φ S)
    (slh_map (SL_extend@{o so} ψ) S).
Proof.
  transitivity (slh_map (SL_extend@{o so} (SL_restrict@{o so} φ)) S).
  - symmetry. exact (@iso_from_to _ _ _ (SL_adj_iso@{o so} X A) φ S).
  - exact (@proper_morphism _ _ _ _
             (@from _ _ _ (SL_adj_iso@{o so} X A))
             (SL_restrict@{o so} φ) ψ H S).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Prop, which is P 1 / ** 属性， 即 P 1 *)

(* sup S := ∃ Q ∈ S, Q. *)
Definition Prop_sup@{o} :
  SetoidMorphism@{o o o}
    (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}) Powerset_Prop_truth@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}))
       (is_setoid (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o}))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (λ S, ex (fun Q : Prop => S Q /\ Q)) _).
  intros S T E; split; intros [Q [HQ q]]; exists Q; split; try exact q.
  - exact (proj1 (E Q) HQ).
  - exact (proj2 (E Q) HQ).
Defined.

(* Prop under implication, the complete semilattice of truth values. / 在蕴含下的命题，真值的完整半格。 *)
Definition Prop_SupLat@{o} : SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} Powerset_Prop_truth@{o}
       (λ P Q : Prop, P → Q) _ _ _ _ Prop_sup@{o} _ _).
  - intros P p; exact p.
  - intros P Q R f g p; exact (g (f p)).
  - intros P P' Q Q' EP EQ f p. exact (proj1 EQ (f (proj2 EP p))).
  - intros P Q f g; split; assumption.
  - intros S P HP p. exists P; split; assumption.
  - intros S Q H [P [HP p]]. exact (H P HP p).
Defined.

Example Prop_SupLat_le@{o} (P Q : Prop) :
  sl_le Prop_SupLat@{o} P Q = (P → Q) := eq_refl.

Example Prop_SupLat_sup@{o}
  (S : carrier (Powerset_Prop_obj@{o} Powerset_Prop_truth@{o})) :
  sl_sup Prop_SupLat@{o} S = ex (fun Q : Prop => S Q /\ Q) := eq_refl.

(* Two comparable points that are not equal: False ≤ True. / 两个可比较但不相等的点：False ≤ True。 *)
Lemma Prop_SupLat_nontrivial@{o} :
  sl_le Prop_SupLat@{o} False True
  * (@equiv _ (is_setoid (sl_set Prop_SupLat@{o})) True False → False).
Proof.
  split.
  - intros f; destruct f.
  - intros [H _]. exact (H I).
Qed.

(* The one-point set, and the constant subsets on it. / 单点集，以及其上的常数子集。 *)
Definition Prop_to_P1_pred@{o} (Q : Prop) :
  carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} poly_unit@{o} unit_setoid@{o o}
       Prop (is_setoid Powerset_Prop_truth@{o}) (λ _, Q) _).
  intros u v _; split; intro q; exact q.
Defined.

Definition Prop_to_P1@{o} :
  SupLatHom@{o} Prop_SupLat@{o} (FreeSL@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} Prop_SupLat@{o}
       (FreeSL@{o} unit_setoid_object@{o o})
       (@Build_SetoidMorphism@{o o o} Prop (is_setoid Powerset_Prop_truth@{o})
          (carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          (is_setoid (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          Prop_to_P1_pred@{o} _) _).
  - intros P Q E u. exact E.
  - intros S u; split.
    + intros [Q [HQ q]]. exists (Prop_to_P1_pred@{o} Q); split; [ | exact q ].
      apply Powerset_squash_intro. exists Q; split; [ exact HQ | ].
      intro v; split; intro r; exact r.
    + intros [T [HT t]]. apply HT; intros [Q [HQ E]].
      exists Q; split; [ exact HQ | exact (proj2 (E u) t) ].
Defined.

Definition P1_to_Prop@{o} :
  SupLatHom@{o} (FreeSL@{o} unit_setoid_object@{o o}) Prop_SupLat@{o}.
Proof.
  unshelve refine
    (@Build_SupLatHom@{o} (FreeSL@{o} unit_setoid_object@{o o})
       Prop_SupLat@{o}
       (@Build_SetoidMorphism@{o o o}
          (carrier (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          (is_setoid (Powerset_Prop_obj@{o} unit_setoid_object@{o o}))
          Prop (is_setoid Powerset_Prop_truth@{o})
          (λ T, T ttt) _) _).
  - intros S T E. exact (E ttt).
  - intros SS; split.
    + intros [T [HT t]]. exists (T ttt); split; [ | exact t ].
      apply Powerset_squash_intro. exists T; split; [ exact HT | ].
      split; intro r; exact r.
    + intros [Q [HQ q]]. apply HQ; intros [T [HT E]].
      exists T; split; [ exact HT | exact (proj2 E q) ].
Defined.

(* Prop = P 1, as an isomorphism of complete semilattices. / Prop = P 1，作为完全半格的同构。 *)
Definition Prop_P1_iso@{o so} :
  @Isomorphism SupLat@{o so} Prop_SupLat@{o}
    (FreeSL@{o} unit_setoid_object@{o o}).
Proof.
  unshelve refine
    (@Build_Isomorphism SupLat@{o so} Prop_SupLat@{o}
       (FreeSL@{o} unit_setoid_object@{o o}) Prop_to_P1@{o} P1_to_Prop@{o}
       _ _).
  - intros T u. destruct u.
    split; intro r; exact r.
  - intros Q. split; intro r; exact r.
Defined.

(* Q goes to the constant subset Q, and back to Q itself. / Q 前往常数子集 Q，然后返回到 Q 本身。 *)
Example Prop_to_P1_at@{o} (Q : Prop) (u : poly_unit@{o}) :
  slh_map Prop_to_P1@{o} Q u = Q := eq_refl.

Example Prop_P1_round_trip@{o} (Q : Prop) :
  slh_map P1_to_Prop@{o} (slh_map Prop_to_P1@{o} Q) = Q := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Two comparable points decide ¬Q or ¬¬Q / * ** 两个可比的点决定 ¬Q 或 ¬¬Q *)

(* The subset { x | Q ∧ x ≈ top }. / 子集 { x | Q ∧ x ≈ top }。 *)
Definition two_points_probe@{o} (A : SupLatObject@{o})
  (top : carrier (sl_set A)) (Q : Prop) :
  carrier (Powerset_Prop_obj@{o} (sl_set A)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (sl_set A)) (is_setoid (sl_set A)) Prop
       (is_setoid Powerset_Prop_truth@{o})
       (λ x, Q /\ Powerset_squash@{o} (@equiv _ (is_setoid (sl_set A)) top x))
       _).
  intros x y E; split; intros [q H]; split; try exact q;
    intros R k; apply H; intro e; apply k.
  - now transitivity x.
  - transitivity y; [ exact e | now symmetry ].
Defined.

(*
 A complete semilattice with a decidable ≈ and two points bot ≤ top that
 are not equal decides, for every proposition Q, ¬Q or ¬¬Q: sup of the
 probe is top when Q holds and bot-or-below when it does not. 

 --------
 一个具有可判定≈和两个不同点 bot ≤ top 的完全半格，对每个命题 Q 决定 ¬Q 或 ¬¬Q：当 Q 成立时，探针的上确界是 top，当 Q 不成立时，上确界是 bot 或以下。
*)
Theorem suplat_two_points_WLEM@{o} (A : SupLatObject@{o})
  (bot top : carrier (sl_set A)) (Hle : sl_le A bot top)
  (Hne : @equiv _ (is_setoid (sl_set A)) top bot → False)
  (Hdec : ∀ x y, @equiv _ (is_setoid (sl_set A)) x y
                 + (@equiv _ (is_setoid (sl_set A)) x y → False))
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  destruct (Hdec (sl_sup A (two_points_probe@{o} A top Q)) top) as [E|N].
  - right. intro nQ. apply Hne. apply sl_antisym; [ | exact Hle ].
    apply (sl_le_respects A (sl_sup A (two_points_probe@{o} A top Q)) top
             bot bot E (reflexivity bot)).
    apply sl_sup_least. intros x [q _]. contradiction.
  - left. intro q. apply N. apply sl_antisym.
    + apply sl_sup_least. intros x [_ H]. apply H; intro e.
      exact (sl_le_respects A top x top top e (reflexivity top)
               (sl_le_refl A top)).
    + apply sl_sup_ub. split; [ exact q | ].
      exact (Powerset_squash_intro (reflexivity top)).
Qed.

(*
 Prop satisfies every hypothesis but the decidability of ≈, and with it
 the theorem gives informative weak excluded middle. 

 --------
 命题满足每个假设，但不满足 ≈ 的可判定性，而有了它，定理给出了信息性的弱排中律。
*)
Corollary Prop_SupLat_decidable_WLEM@{o}
  (Hdec : ∀ P Q : Prop, @equiv _ (is_setoid (sl_set Prop_SupLat@{o})) P Q
                        + (@equiv _ (is_setoid (sl_set Prop_SupLat@{o})) P Q
                           → False))
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  destruct Prop_SupLat_nontrivial@{o} as [Hle Hne].
  exact (suplat_two_points_WLEM@{o} Prop_SupLat@{o} False True Hle Hne Hdec Q).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The chain false ≤ true on [bool] / * ** 链条 false ≤ true 在 [bool] *)

(*
 The carrier is Instance/Sets.v's two-element setoid [bool_setoid_object],
 compared by [eq]. 

 --------
 载体是 Instance/Sets.v 的二元集合 [bool_setoid_object]，通过 [eq] 进行比较。
*)
Definition bool_chain_le@{} (b c : bool) : Prop := b = true → c = true.

(* The chain with a given supremum operator: its four order axioms, proved once for the two uses below. / 具有给定上确界运算符的链：其四个序公理，已证明，用于下面的两种情况。 *)
Definition bool_chain_SupLat@{o}
  (sup : SetoidMorphism@{o o o}
           (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
           bool_setoid_object@{o o})
  (ub : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
          (x : bool), S x → bool_chain_le x (sup S))
  (least : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
             (y : bool),
             (∀ x : bool, S x → bool_chain_le x y) → bool_chain_le (sup S) y) :
  SupLatObject@{o}.
Proof.
  unshelve refine
    (@Build_SupLatObject@{o} bool_setoid_object@{o o} bool_chain_le
       _ _ _ _ sup ub least).
  - intros x H; exact H.
  - intros x y z H1 H2 H; exact (H2 (H1 H)).
  - intros x x' y y' Ex Ey H. destruct Ex, Ey. exact H.
  - intros [|] [|] H1 H2; try reflexivity.
    + exact (eq_sym (H1 eq_refl)).
    + exact (H2 eq_refl).
Defined.

(* Any sup operator for this order on bool gives informative weak excluded middle. / 对布尔上的此顺序的任何 supremum 运算符都给出信息性弱排中律。 *)
Theorem bool_SupLat_WLEM@{o}
  (sup : SetoidMorphism@{o o o}
           (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
           bool_setoid_object@{o o})
  (ub : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
          (x : bool), S x → bool_chain_le x (sup S))
  (least : ∀ (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
             (y : bool),
             (∀ x : bool, S x → bool_chain_le x y) → bool_chain_le (sup S) y)
  (Q : Prop) : (~ Q) + (~ ~ Q).
Proof.
  unshelve refine
    (suplat_two_points_WLEM@{o} (bool_chain_SupLat@{o} sup ub least)
       false true _ _ _ Q).
  - intro H; discriminate H.
  - intro H; discriminate H.
  - intros [|] [|]; (left; reflexivity) || (right; intro H; discriminate H).
Qed.

(* Conversely, under informative weak excluded middle the chain IS a complete semilattice, with sup S = true exactly when ¬¬(true ∈ S). / 相反，在信息性弱排中律下，该链是一个完备半格，当且仅当 ¬¬(true ∈ S) 时，sup S = true。 *)
Definition bool_chain_sup_fun@{o}
  (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) : bool :=
  match wlem (S true) with inl _ => false | inr _ => true end.

Lemma bool_chain_sup_true@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) :
  bool_chain_sup_fun@{o} wlem S = true → ~ ~ S true.
Proof.
  unfold bool_chain_sup_fun; destruct (wlem (S true)) as [n|n];
    [ intro H; discriminate H | intros _; exact n ].
Qed.

Lemma bool_chain_sup_false@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q))
  (S : carrier (Powerset_Prop_obj@{o} bool_setoid_object@{o o})) :
  bool_chain_sup_fun@{o} wlem S = false → ~ S true.
Proof.
  unfold bool_chain_sup_fun; destruct (wlem (S true)) as [n|n];
    [ intros _; exact n | intro H; discriminate H ].
Qed.

Definition bool_chain_sup@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q)) :
  SetoidMorphism@{o o o}
    (Powerset_Prop_obj@{o} bool_setoid_object@{o o})
    bool_setoid_object@{o o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} _
       (is_setoid (Powerset_Prop_obj@{o} bool_setoid_object@{o o}))
       bool (is_setoid bool_setoid_object@{o o})
       (bool_chain_sup_fun@{o} wlem) _).
  intros S T E.
  destruct (bool_chain_sup_fun@{o} wlem S) eqn:HS,
           (bool_chain_sup_fun@{o} wlem T) eqn:HT; try reflexivity.
  - destruct (bool_chain_sup_true@{o} wlem S HS
                (fun s =>
                   bool_chain_sup_false@{o} wlem T HT (proj1 (E true) s))).
  - destruct (bool_chain_sup_true@{o} wlem T HT
                (fun t =>
                   bool_chain_sup_false@{o} wlem S HS (proj2 (E true) t))).
Defined.

Definition bool_SupLat@{o} (wlem : ∀ Q : Prop, (~ Q) + (~ ~ Q)) :
  SupLatObject@{o}.
Proof.
  unshelve refine (bool_chain_SupLat@{o} (bool_chain_sup@{o} wlem) _ _).
  - intros S [|] Hx Ht; [ | discriminate Ht ].
    change (bool_chain_sup_fun@{o} wlem S = true).
    destruct (bool_chain_sup_fun@{o} wlem S) eqn:HS; [ reflexivity | ].
    destruct (bool_chain_sup_false@{o} wlem S HS Hx).
  - intros S [|] Hub H; [ reflexivity | ].
    destruct (bool_chain_sup_true@{o} wlem S H
                (fun s => ltac:(discriminate (Hub true s eq_refl)))).
Defined.
