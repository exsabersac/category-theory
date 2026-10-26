Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   * Huq's correspondence: natural transformations as sections of the comma
   projections. 

   --------
   * Huq的通信：将自然变换视为逗号投影的截面。
*)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Wikipedia: “If the domains of S, T are equal, then the diagram which
 defines morphisms in S↓T with α=β, α′=β′, g=h is identical to the diagram
 which defines a natural transformation S ⟹ T. The difference between the
 two notions is that a natural transformation is a particular collection of
 morphisms of type of the form S(α) → T(α), while objects of the comma
 category contains all morphisms of type of such form. A functor to the
 comma category selects that particular collection of morphisms. This is
 described succinctly by an observation by Huq that a natural transformation
 η : S → T, with S, T : A → C, corresponds to a functor A → (S↓T) which maps
 each object α to (α, α, η α) and maps each morphism g to (g, g). This is a
 bijective correspondence between natural transformations S ⟹ T and functors
 A ⟶ (S↓T) which are sections of both forgetful functors from S↓T.”

 This is also given in Mac Lane, page 47, exercise 4.

 The two definitions below realize the two directions of Huq's bijection for
 functors S T : D ⟶ C sharing the domain D (the “domains equal” case above).
 Comma_Functor sends a natural transformation F : S ⟹ T to the functor
 D ⟶ (S ↓ T) of the observation, X ↦ (X, X; F X) and f ↦ (f, f); it is a
 common section of comma_proj1 and comma_proj2 by construction. Comma_Transform
 is the inverse: from a functor F : D ⟶ (S ↓ T) together with witnesses that
 it is a section of both projections (comma_proj1 ◯ F ≈ Id and
 comma_proj2 ◯ F ≈ Id), it recovers a natural transformation S ⟹ T. 

 --------
 nLab: https://ncatlab.org/nlab/show/comma+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category维基百科：“如果 S 和 T 的定义域相等，那么定义 S↓T 中态射 α=β、α′=β′、g=h 的图，与定义自然变换 S ⟹ T 的图是相同的。两者的区别在于，自然变换是一组特定类型为 S(α) → T(α) 的态射，而逗号范畴中的对象包含所有该类型的态射。到逗号范畴的函子选择了那组特定的态射。这可以通过 Huq 的一个观察简明描述，即自然变换 η : S → T（其中 S, T : A → C）对应于一个函子 A → (S↓T)，它把每个对象 α 映射为 (α, α, η α)，并把每个态射 g 映射为 (g, g)。”这是一个自然变换 S ⟹ T 与函子 A ⟶ (S↓T) 之间的双射对应关系，这些函子是 S↓T 的两个遗忘函子的截面。

 这也在 Mac Lane 的第 47 页，第 4 题中给出。

 下面的两个定义实现了 Huq 双射的两个方向，适用于共享域 D 的函子 S, T : D ⟶ C（上述“域相等”情况）。
 Comma_Functor 将自然变换 F : S ⟹ T 发送到函子 D ⟶ (S ↓ T) 的观察，即 X ↦ (X, X; F X) 和 f ↦ (f, f)；根据构造，它是 comma_proj1 和 comma_proj2 的公共截面。Comma_Transform 是逆操作：从函子 F : D ⟶ (S ↓ T) 以及它是两个投影截面的证明（comma_proj1 ◯ F ≈ Id 和 comma_proj2 ◯ F ≈ Id），它恢复出自然变换 S ⟹ T。
*)

(*
 WHAT IS PROVED HERE, AND AT WHAT STRENGTH

 Mac Lane's exercise (catalog maclane:II.6:ex4, “natural transformations as
 sections of the comma projections (S. A. Huq)”) asks, for functors
 T, S : D ⟶ C, that a natural transformation τ : T ⟹ S be the same thing
 as a functor τ : D ⟶ (T ↓ S) with P τ = Q τ = id_D, where P and Q are the
 comma projections (phrasing per the catalog's statement_summary paraphrase,
 doc/plan/books/maclane/inventory/II.json, not the book's wording).  Both
 texts name the SOURCE of the transformation first in their own letters --
 his is T, this file's is S -- so his T and S are this file's S and T.
 Nothing else differs.

 THE SECTION EQUATIONS, AT TWO STRENGTHS.

 Mac Lane's “P τ = id_D” is an equality of functors, on the nose.
 [Comma_Functor_proj1_strict] and [Comma_Functor_proj2_strict] deliver
 exactly that, at [Functor_StrictEq_Setoid] — the hom-setoid of StrictCat,
 in which two functors are identified when their object maps are equal
 propositionally and their morphism maps agree after transport along that
 equality.  Both hold with [eq_refl] as the object witness, because
 [comma_proj1 ◯ Comma_Functor τ] has object map [fun X => fst (X, X)], which
 is [fun X => X] by iota, and likewise on morphisms; every transport in the
 coherence condition therefore vanishes and the condition is [f ≈ f].  This
 is the strongest sense in which this library can say “on the nose”: Coq's
 own equality of the two functor RECORDS is not available, since they carry
 proof fields that nothing identifies.

 [Comma_Functor_proj1] and [Comma_Functor_proj2] are the same two facts at
 [Functor_Setoid], the hom-setoid of Cat, in which “equal” means naturally
 isomorphic — so ≈[Cat] and ≅[Cat] read as EQUIVALENCE, not isomorphism, of
 categories.  Those are the witnesses [Comma_Transform] consumes, which is
 why the backward direction proved here GENERALIZES the book's: it accepts a
 functor that sections the projections only up to natural isomorphism, of
 which a functor sectioning them on the nose is the special case.  (They are
 built directly, with [iso_id] components, rather than transported from the
 strict versions along [strict_equiv_implies_fun_equiv]; that bridge is
 Qed-opaque, so the components of the isomorphism it produces would not
 reduce, and the round trip below needs them to compute to [id].)

 WITNESS DEPENDENCE, AND WHY IT DECIDES THE PACKAGING.

 The generalization has a price, and it is not incidental.
 [Comma_Transform F p q] is a function of the WITNESSES p and q, not of F
 alone: [Comma_Transform_witness_shift] computes that replacing (p, q) by
 (p', q') conjugates every component,

 Comma_Transform F p' q' d
 ≈ fmap[T] (to (`1 q' d) ∘ from (`1 q d)) ∘ Comma_Transform F p q d
 ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d)),

 by automorphisms of d assembled from the two witness pairs;
 [Comma_Transform_witness_irrelevant] is the complementary reading, that
 only the [to] components of the witnesses matter, and only up to ≈.

 That conjugation is not merely a formal possibility, and the file does not
 ask the reader to take it on faith.  [huq_witness_separates], at the end,
 exhibits ONE section functor over B(Z/2) — the delooping of the two-element
 group, where every element is a natural automorphism of the identity
 because the group is abelian — carrying two witness pairs whose recovered
 transformations compute to [false] and to [true], with the two values
 pinned by [eq_refl] examples.  So a setoid of section functors whose
 equivalence compared the FUNCTOR alone, discarding the witnesses, provably
 could not support [Comma_Transform] as a map out of it: that one functor
 would have to be sent to two distinct transformations.  That is why
 [HuqSection] bundles the witnesses as data rather than asserting the
 section property.

 Retreating to on-the-nose witnesses would not remove the phenomenon, only
 relocate it: a strict witness is still data, a family of object equalities
 [∀ x, fst ``(F x) = x], and two such families differ by a family of loops
 in obj[D] that nothing here identifies.  Identifying them uniformly is a
 UIP hypothesis on the objects of D, which this development does not take.

 THE PACKAGING, AND THE EQUIVALENCE IT QUOTIENTS BY.

 [HuqSection] is a section functor packaged with its two witnesses.  Two of
 them are [HuqCompatible] when there is a natural isomorphism θ between the
 section functors — an inhabitant of [huq_functor X ≈[Cat] huq_functor Y],
 so θ carries its naturality, it is not merely a pointwise family — ALONG
 WHICH the witnesses correspond:

 to (`1 (huq_sec1 X) d) ≈ to (`1 (huq_sec1 Y) d) ∘ fst `1 (to (`1 θ d))

 and likewise for the second witness.  This is the geometric condition, “X
 and Y are isomorphic AS SECTIONS”; it is deliberately NOT defined as the
 kernel of the recovery map.  That it coincides with that kernel is the
 theorem [huq_compatible_iff]: X and Y are compatible if and only if
 [huq_transform X ≈ huq_transform Y].  The forward half is well-definedness
 of the recovery map on the quotient.  The backward half is the substantive
 one: from a bare equivalence of the two recovered transformations it builds
 the comparison isomorphism, whose components are forced to be
 [from (witness of Y) ∘ (witness of X)] — that is the opening step of
 [huq_compatible_transform] — and whose NATURALITY does not consume the
 hypothesis at all, [huq_compare_natural] using only the coherence fields of
 the four witnesses.  The hypothesis is spent exactly once, on the commuting
 square of the comparison, which the comma hom-setoid then ignores.

 So the equivalence is not a convenience chosen to make a round trip close:
 it is the coarsest relation for which the recovery map is injective, and it
 is exhibited independently as the relation of being isomorphic as sections.
 Nor is it so coarse as to collapse to “same underlying functor”:
 [huq_witness_sections_incompatible] separates two packaged sections whose
 functors are literally the same.

 [Huq_roundtrip] packages the correspondence as an isomorphism in Sets
 between [huq_dom], the natural transformations S ⟹ T under
 [Transform_Setoid], and [huq_cod], the packaged sections under
 [HuqCompatible] — the shape used by Adjunction/Conjugate.v's
 [conjugate_bijection] and Theory/Bicategory/Mates.v's [mate_iso].

 Both round trips are available unpackaged, and neither rests on the kernel
 characterization.  [Comma_Transform_Comma_Functor] is the transformation
 side: at the canonical witnesses the conjugation collapses to
 [fmap id ∘ τ X ∘ fmap id].  [Comma_Functor_Comma_Transform] is the section
 side at its honest strength — a natural isomorphism
 [Comma_Functor (Comma_Transform F p q) ≈[Cat] F] for ARBITRARY F, p and q,
 whose component at d is the comma isomorphism between ((d, d); the
 recovered arrow) and F d with legs the two witnesses at d.  It is not
 available on the nose from these hypotheses, and the reason is visible in
 the statement: F d is ((a, b); h) with a and b merely isomorphic to d, not
 equal to it.  [huq_section_compatible] reads that isomorphism back into the
 quotient, so the section-side round trip of [Huq_roundtrip] is discharged
 by the explicit comparison rather than by [huq_compatible_iff]. 

 --------
 这里证明的内容，以及其强度

 Mac Lane 的练习（目录 maclane:II.6:ex4，“自然变换作为逗号投影的截面 (S. A. Huq)”）要求，对于函子 T, S : D ⟶ C，自然变换 τ : T ⟹ S 与函子 τ : D ⟶ (T ↓ S) 是同一件事，且满足 P τ = Q τ = id_D，其中 P 和 Q 是逗号投影（表述依据目录的 statement_summary 概括，doc/plan/books/maclane/inventory/II.json，而非书本原文）。两份文本均先用各自的字母命名变换的来源——他的是 T，本文件的是 S——因此他的 T 和 S 就是本文件的 S 和 T。其他没有差异。

 截面方程，在两个强度下。Mac Lane 的 “P τ = id_D” 是函子之间的严格相等。
 [Comma_Functor_proj1_strict] 和 [Comma_Functor_proj2_strict] 在 [Functor_StrictEq_Setoid] —— StrictCat 的 Hom-集合——上正好给出了这一点，其中当两个函子的对象映射在命题上相等且其态射映射在沿该等式传递后也相同时，这两个函子被认定为相同。由于 [comma_proj1 ◯ Comma_Functor τ] 的对象映射是 [fun X => fst (X, X)]，而根据 iota 这就是 [fun X => X]，并且在态射上的情况类似，因此使用 [eq_refl] 作为对象证据时两者都成立；一致性条件中的每一次传递都会消失，因此条件是 [f ≈ f]。这是该库能够所说的“严格相等”的最强形式：Coq 对两个函子 RECORD 的自身相等并不可用，因为它们携带证明字段，而这些字段没有任何东西能将其识别。[Comma_Functor_proj1] 和 [Comma_Functor_proj2] 在 [Functor_Setoid]，也就是 Cat 的同态集合中，是相同的两个事实，其中“相等”意味着自然同构——因此 ≈ [Cat] 和 ≅ [Cat] 被解读为范畴的等价，而不是同构。这些是 [Comma_Transform] 使用的见证，这也是这里证明的逆向方向能够推广书中结果的原因：它接受一个函子，该函子仅在自然同构下截取投影，而精确截取投影的函子只是一个特例。（它们是直接构造的，使用 [iso_id] 组件，而不是沿 [strict_equiv_implies_fun_equiv] 从严格版本传递过来；这个桥是 Qed-不透明的，因此它生成的同构组件不会化简，而下面的往返需要它们计算为 [id]。）见证依赖，以及它为何决定了封装。

 泛化是有代价的，而且这代价并非偶然。
 [Comma_Transform F p q] 是见证 p 和 q 的函数，而不仅仅是 F 的函数：[Comma_Transform_witness_shift] 计算将 (p, q) 替换为 (p', q') 会共轭每个分量，

 Comma_Transform F p' q' d
 ≈ fmap [T] (to (`1 q' d) ∘ from (` 1 q d)) ∘ Comma_Transform F p q d
 ∘ fmap [S] (to (`1 p d) ∘ from (` 1 p' d))，

 通过由那两对见证组装的 d 的自身同构；
 [Comma_Transform_witness_irrelevant] 是补充性的理解，即只有见证的 [to] 分量才重要，并且只在 ≈ 范围内。该结合并不仅仅是一种形式上的可能性，文件也没有要求读者凭直觉相信它。[huq_witness_separates]在末尾展示了B(Z/2)——由两个元素组成群的去环化——上的一个截面函子，其中每个元素都是恒等函子的自然自同构，因为该群是阿贝尔群——携带两个见证对，其恢复的变换计算结果分别为[false]和[true]，并且这两个值由[eq_refl]示例固定。因此，如果一个截面函子的等价只比较函子本身而忽略见证，则可证明它不能支持[Comma_Transform]作为其出映射：因为那一个函子必须映射到两个不同的变换。这就是为什么[HuqSection]将见证作为数据捆绑，而不是断言截面性质。退回到恰如其分的见证者并不会消除该现象，只会将其重新定位：严格的见证仍然是数据，是对象等式的一个族 [∀ x, fst ``(F x) = x]，而两个这样的族通过 obj [D] 中的一个循环族而不同，而这里没有任何东西能识别它们。对它们进行一致的识别是对 D 的对象的 UIP 假设，而本发展中未采纳这一假设。

 打包及其所商的等价关系。

 [HuqSection] 是一个带有其两个见证者的截面函子。它们中的两个是 [HuqCompatible]，当截面函子之间存在自然同构 θ 时——是 [huq_functor X ≈[Cat] huq_functor Y 的一个元素——因此 θ 保持其自然性，它不仅仅是一个逐点族——沿着这个族，见证者对应于：

 (to (`1 (huq_sec1 X) d) ≈ to (` 1 (huq_sec1 Y) d) ∘ fst `1 (to (` 1 θ d))同样地，第二个证人也是如此。这是几何条件，“X 和 Y 作为截面是同构的”；它特意没有被定义为恢复映射的核。它与该核相吻合的事实就是定理 [huq_compatible_iff]：X 和 Y 兼容当且仅当 [huq_transform X ≈ huq_transform Y]。前半部分是恢复映射在商上的良定性。后半部分才是实质性的部分：从两个恢复的变换之间的纯粹等价性出发，它构建了比较同构，其组成部分被强制为 [from (witness of Y) ∘ (witness of X)]——即 [huq_compatible_transform] 的起步——其自然性完全不消耗假设，[huq_compare_natural] 仅使用四个证人的相干场。假设恰好使用一次，即在比较的交换方格上，然后逗号同态集合会忽略它。

 因此，这种等价并不是为了让往返转换便捷而选择的便利：它是使恢复映射可单射的最粗糙关系，并且它作为“作为截面同构”的关系独立地展示出来。它也不是粗到会简化为“相同的底层函子”：[huq_witness_sections_incompatible] 区分了两个封装的截面，即使它们的函子字面上相同。

 [Huq_roundtrip] 将对应关系封装为集合中的一个同构，在 [huq_dom] 与自然变换 S ⟹ T 在 [Transform_Setoid] 下，以及 [huq_cod] 中的封装截面在 [HuqCompatible] 下——这种形式被 Adjunction/Conjugate.v 的 [conjugate_bijection] 和 Theory/Bicategory/Mates.v 的 [mate_iso] 使用。两个往返行程都可以以非打包形式使用，并且都不依赖于核的刻画。[Comma_Transform_Comma_Functor] 是变换端：在典型证据下，共轭退化为 [fmap id ∘ τ X ∘ fmap id]。[Comma_Functor_Comma_Transform] 是截面端，以其真实强度——一个自然同构 [Comma_Functor (Comma_Transform F p q) ≈[Cat] F] 对任意 F、p 和 q 成立，其在 d 处的分量是((d, d); 恢复箭头) 与 F d 之间的逗号同构，两条边是 d 处的两个证据。根据这些假设，它无法直接使用，其原因在陈述中是显而易见的：F d 是 ((a, b); h)，其中 a 和 b 仅与 d 同构，而非等于 d。[huq_section_compatible] 将该同构映射回商，因此 [Huq_roundtrip] 的截面端往返行程是通过显式比较消解的，而非通过 [huq_compatible_iff]。
*)

(*
 natural transformation S ⟹ T  ↦  section functor D ⟶ (S ↓ T) 

 --------
 自然变换 S ⟹ T  ↦  截面函子 D ⟶ (S ↓ T)
*)
Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

#[local] Obligation Tactic := simpl; intros.

(*
 section functor D ⟶ (S ↓ T) of both projections  ↦  natural transformation
 S ⟹ T (the inverse direction of Huq's bijection) 

 --------
 截面函子 D ⟶ (S ↓ T) 的两个投影 ↦ 自然变换 S ⟹ T（Huq 双射的逆方向）
*)
Program Definition Comma_Transform {C D : Category} {S T : D ⟶ C}
        (F : D ⟶ (S ↓ T))
        (proj1 : comma_proj1 ◯ F ≈[Cat] Id)
        (proj2 : comma_proj2 ◯ F ≈[Cat] Id) : S ⟹ T := {|
  transform := fun X =>
    fmap (to (`1 proj2 X)) ∘ `2 (F X) ∘ fmap (from (`1 proj1 X))
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.

  spose (`2 proj1 _ _ f) as X0.
  spose (`2 proj2 _ _ f) as X1.

  rewrite <- (id_left f) at 1.
  rewrite <- (iso_to_from (`1 proj2 y)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f).
  rewrites.
  rewrite fmap_comp.
  comp_left.

  symmetry.
  rewrite <- (id_right f) at 1.
  rewrite <- (iso_to_from (`1 proj1 x)).
  rewrite !comp_assoc.
  rewrites.
  rewrite fmap_comp.
  comp_right.

  exact (`2 (fmap[F] f)).
Qed.
Next Obligation.
  symmetry.
  apply Comma_Transform_obligation_1.
Qed.

Section HuqBijection.

Context {C D : Category}.
Context {S T : D ⟶ C}.

(* * ** The canonical section witnesses / * ** 正典部分的证据 *)

(*
 [Comma_Functor tau] is a common section of the two projections on the nose:
 the object map of [comma_proj1 ◯ Comma_Functor tau] is
 [fun X => fst (X, X)], which is [fun X => X] by iota, and likewise for its
 morphism map, so the object witness required by [Functor_StrictEq_Setoid] is
 [eq_refl] and both transports vanish. This is the strict (on-the-nose)
 reading of the book's “sections of both forgetful functors”. 

 --------
 [Comma_Functor tau] 是鼻子上两个投影的常见截面：
 [comma_proj1 ◯ Comma_Functor tau] 的对象映射是
 [fun X => fst (X, X)]，它是通过 iota 得到的 [fun X => X]，映射同理，因此 [Functor_StrictEq_Setoid] 所需的对象见证是
 [eq_refl]，且两者的传输都消失。这是书中“两个遗忘函子截面”的严格（逐字）理解。
*)

Program Definition Comma_Functor_proj1_strict (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

Program Definition Comma_Functor_proj2_strict (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[StrictCat] Id := (fun _ => eq_refl; _).
Next Obligation. reflexivity. Qed.

(*
 The same two facts at the strength [Comma_Transform] consumes, namely in
 Cat's hom-setoid [Functor_Setoid], where equality of functors is natural
 isomorphism. These are built directly, with identity components, rather
 than routed through [strict_equiv_implies_fun_equiv] (Instance/StrictCat/
 ToCat.v): that bridge is [Qed]-opaque, so the components of the natural
 isomorphism it produces do not reduce, whereas the round trip below needs
 [to (`1 (Comma_Functor_proj2 tau) X)] to compute to [id]. 

 --------
 相同的两个事实在 [Comma_Transform] 的强度下被使用，即在 Cat 的同态集合 [Functor_Setoid] 中，其中函子相等是自然同构的。这些是直接构建的，带有恒等部分，而不是通过 [strict_equiv_implies_fun_equiv]（Instance/StrictCat/ToCat.v）处理：因为那个桥是 [Qed] 不透明的，所以它产生的自然同构组件不会化简，而下面的来回操作需要 [to (`1 (Comma_Functor_proj2 tau) X)] 计算到 [id]。
*)

Program Definition Comma_Functor_proj1 (tau : S ⟹ T) :
  comma_proj1 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

Program Definition Comma_Functor_proj2 (tau : S ⟹ T) :
  comma_proj2 ◯ Comma_Functor tau ≈[Cat] Id := (fun _ => iso_id; _).
Next Obligation. rewrite id_left, id_right; reflexivity. Qed.

(* * ** Round trip 1: recovering a natural transformation / * ** 往返行程1：恢复自然变换 *)

(*
 At the canonical witnesses the conjugation of [Comma_Transform] collapses:
 both isomorphism components are the identity, so the recovered component is
 [fmap id ∘ tau X ∘ fmap id]. 

 --------
 在典型的见证下，[Comma_Transform] 的共轭崩溃了：
 两个同构分量都是恒等的，因此恢复的分量是
 [fmap id ∘ tau X ∘ fmap id] 。
*)

Theorem Comma_Transform_Comma_Functor (tau : S ⟹ T) :
  Comma_Transform (Comma_Functor tau)
    (Comma_Functor_proj1 tau) (Comma_Functor_proj2 tau) ≈ tau.
Proof.
  intro X; simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** ** Witness dependence / ** 证人依赖 *)

(*
 [Comma_Transform] is a function of the section witnesses, not of the section
 functor alone. Replacing (p, q) by (p', q') conjugates every component by
 the automorphisms [to (`1 p d) ∘ from (`1 p' d)] of d and
 [to (`1 q' d) ∘ from (`1 q d)] of d. 

 --------
 [Comma_Transform] 是截面见证的函数，而不仅仅是截面函子。(p, q) 替换为 (p', q') 会将每个分量通过 d 的自同构 [to (`1 p d) ∘ from (`1 p' d)] 和 d 的自同构 [to (`1 q' d) ∘ from (`1 q d)] 共轭。
*)

Theorem Comma_Transform_witness_shift
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Transform F p' q' d
    ≈ fmap[T] (to (`1 q' d) ∘ from (`1 q d))
        ∘ Comma_Transform F p q d
        ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d)).
Proof.
  assert (Hq : fmap[T] (to (`1 q' d) ∘ from (`1 q d)) ∘ fmap[T] (to (`1 q d))
                 ≈ fmap[T] (to (`1 q' d))).
  { rewrite <- fmap_comp, <- comp_assoc, iso_from_to, id_right.
    reflexivity. }
  assert (Hp : fmap[S] (from (`1 p d)) ∘ fmap[S] (to (`1 p d) ∘ from (`1 p' d))
                 ≈ fmap[S] (from (`1 p' d))).
  { rewrite <- fmap_comp, comp_assoc, iso_from_to, id_left.
    reflexivity. }
  simpl.
  rewrite !comp_assoc, Hq.
  rewrite <- !comp_assoc, Hp.
  reflexivity.
Qed.

(*
 The dependence is exactly on the [to] components of the witnesses: two
 witness pairs with pointwise equivalent components give the same
 transformation. So nothing beyond those components can matter, and the
 conjugation of [Comma_Transform_witness_shift] is trivial precisely when
 they agree. 

 --------
 依赖性恰恰在于见证者的 [to] 组件：两对具有逐点等价组件的见证者会给出相同的变换。因此，超出这些组件的因素无关紧要，而 [Comma_Transform_witness_shift] 的共轭恰好在它们一致时是平凡的。
*)

Corollary Comma_Transform_witness_irrelevant
        (F : D ⟶ (S ↓ T))
        (p p' : comma_proj1 ◯ F ≈[Cat] Id)
        (q q' : comma_proj2 ◯ F ≈[Cat] Id) :
  (∀ d, to (`1 p d) ≈ to (`1 p' d)) →
  (∀ d, to (`1 q d) ≈ to (`1 q' d)) →
  Comma_Transform F p' q' ≈ Comma_Transform F p q.
Proof.
  intros Hp Hq d.
  rewrite (Comma_Transform_witness_shift F p p' q q' d).
  rewrite <- (Hq d), (Hp d), !iso_to_from, !fmap_id, id_left, id_right.
  reflexivity.
Qed.

(* * ** Round trip 2: recovering the section functor / * ** 往返行程 2：恢复截面函子 *)

(*
 The comparison isomorphism between [Comma_Functor (Comma_Transform F p q) d]
 — that is, ((d, d); the recovered component) — and [F d]; its legs are the
 two section witnesses at d. 

 --------
 [Comma_Functor (Comma_Transform F p q) d]——也就是 ((d, d); 恢复的分量)——与 [F d] 之间的比较同构；它的两条支线是 d 处的两个截面见证。
*)

Program Definition Comma_Functor_Comma_Transform_iso
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (d : D) :
  Comma_Functor (Comma_Transform F p q) d ≅ F d := {|
  to   := ((from (`1 p d), from (`1 q d)); _);
  from := ((to   (`1 p d), to   (`1 q d)); _)
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.
Next Obligation. split; apply iso_from_to. Qed.
Next Obligation. split; apply iso_to_from. Qed.

(*
 Naturality of that comparison. Note it uses only the coherence fields of
 the two witnesses; no property of [Comma_Transform] is needed. 

 --------
 这种比较的自然性。注意，它只使用了两个证人的相干场；不需要 [Comma_Transform] 的任何属性。
*)

Lemma Comma_Functor_Comma_Transform_natural
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) (x y : D) (f : x ~> y) :
  fmap[Comma_Functor (Comma_Transform F p q)] f
    ≈ from (Comma_Functor_Comma_Transform_iso F p q y)
        ∘ fmap[F] f
        ∘ to (Comma_Functor_Comma_Transform_iso F p q x).
Proof.
  spose (`2 p x y f) as Hp.
  spose (`2 q x y f) as Hq.
  split; simpl.
  - rewrite Hp.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
  - rewrite Hq.
    rewrite !comp_assoc, iso_to_from, id_left.
    rewrite <- comp_assoc, iso_to_from, id_right.
    reflexivity.
Qed.

(*
 Packaged transparently (not by [exists ...; Qed]) so that the components of
 the natural isomorphism remain observable downstream — [huq_section_
 compatible] below reads them. 

 --------
 以透明方式打包（不是由 [exists ...; Qed] 打包），以便自然同构的组件在下游仍然可观察 — [huq_section_compatible] 下面会读取它们。
*)

Definition Comma_Functor_Comma_Transform
        (F : D ⟶ (S ↓ T))
        (p : comma_proj1 ◯ F ≈[Cat] Id)
        (q : comma_proj2 ◯ F ≈[Cat] Id) :
  Comma_Functor (Comma_Transform F p q) ≈[Cat] F :=
  (Comma_Functor_Comma_Transform_iso F p q;
   Comma_Functor_Comma_Transform_natural F p q).

(** ** The bijection / ** 双射 *)

(*
 Two isomorphism-cancellation lemmas, used to compare two sections of the
 projections through their witnesses. 

 --------
 两个同构消去引理，用于通过它们的证据比较投影的两个截面。
*)

Lemma iso_conj_cancel {E : Category} {a b c : E} (i : a ≅ c) (j : b ≅ c) :
  (from j ∘ to i) ∘ (from i ∘ to j) ≈ id.
Proof.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to i)).
  rewrite iso_to_from, id_left.
  apply iso_from_to.
Qed.

Lemma iso_conj_recompose {E : Category} {p q m p' q' m' : E}
      (u : p ≅ m) (v : q ≅ m) (u' : p' ≅ m') (v' : q' ≅ m') (g : m' ~> m) :
  (from u ∘ to v) ∘ (from v ∘ g ∘ to v') ∘ (from v' ∘ to u')
    ≈ from u ∘ g ∘ to u'.
Proof.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from u) (to v) (from v)).
  rewrite iso_to_from, id_right.
  rewrite <- (comp_assoc (from u ∘ g) (to v') (from v')).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
 A section of both projections, packaged with its two witnesses. The
 witnesses are DATA, not a property: [Comma_Transform] genuinely depends on
 them ([Comma_Transform_witness_shift] above), so they cannot be discarded. 

 --------
 两种预测的一个部分，连同其两个见证一起打包。见证是数据，而不是属性：[Comma_Transform] 确实依赖于它们（如上面的 [Comma_Transform_witness_shift]），所以它们不能被丢弃。
*)

Record HuqSection : Type := {
  huq_functor : D ⟶ (S ↓ T);
  huq_sec1    : comma_proj1 ◯ huq_functor ≈[Cat] Id;
  huq_sec2    : comma_proj2 ◯ huq_functor ≈[Cat] Id
}.

Definition huq_transform (X : HuqSection) : S ⟹ T :=
  Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X).

Definition huq_section (tau : S ⟹ T) : HuqSection :=
  {| huq_functor := Comma_Functor tau;
     huq_sec1    := Comma_Functor_proj1 tau;
     huq_sec2    := Comma_Functor_proj2 tau |}.

Lemma huq_transform_apply (X : HuqSection) (d : D) :
  huq_transform X d
    ≈ fmap[T] (to (`1 (huq_sec2 X) d))
        ∘ `2 (huq_functor X d)
        ∘ fmap[S] (from (`1 (huq_sec1 X) d)).
Proof. reflexivity. Qed.

Theorem huq_transform_section (tau : S ⟹ T) : huq_transform (huq_section tau) ≈ tau.
Proof. apply Comma_Transform_Comma_Functor. Qed.

(*
 Two packaged sections are compatible when there is a natural isomorphism
 between the section functors ALONG WHICH the two pairs of witnesses
 correspond: the triangles below say that the witness of X factors through
 the witness of Y across the comparison. 

 --------
 当存在一个自然同构使沿着它两对见证相对应的截面函子之间成立时，两个封装的截面是兼容的：下列三角形表示 X 的见证通过比较在 Y 的见证中分解。
*)

Definition HuqCompatible (X Y : HuqSection) : Type :=
  ∃ theta : huq_functor X ≈[Cat] huq_functor Y,
      (∀ d, to (`1 (huq_sec1 X) d)
              ≈ to (`1 (huq_sec1 Y) d) ∘ fst `1 (to (`1 theta d)))
    * (∀ d, to (`1 (huq_sec2 X) d)
              ≈ to (`1 (huq_sec2 Y) d) ∘ snd `1 (to (`1 theta d))).

(* Well-definedness of the backward map on the quotient. / 商上的反向映射的良定义性。 *)

Theorem huq_compatible_transform (X Y : HuqSection) :
  HuqCompatible X Y → huq_transform X ≈ huq_transform Y.
Proof.
  intros [theta [H1 H2]] d.
  spose (`2 (to (`1 theta d))) as Hsq.
  assert (Hu0 : fst `1 (to (`1 theta d))
                  ≈ from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d)).
  { rewrite (H1 d), comp_assoc, iso_from_to, id_left; reflexivity. }
  assert (Hu : fst `1 (to (`1 theta d)) ∘ from (`1 (huq_sec1 X) d)
                 ≈ from (`1 (huq_sec1 Y) d)).
  { rewrite Hu0, <- comp_assoc, iso_to_from, id_right; reflexivity. }
  unfold huq_transform; simpl.
  rewrite <- Hu, (H2 d), !fmap_comp.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  comp_left.
  symmetry; exact Hsq.
Qed.

(*
 The converse: the compatible-witness relation is exactly the kernel of the
 backward map, so the equivalence above is not an arbitrary choice but the
 coarsest one that makes [huq_transform] injective. The comparison
 isomorphism is forced — its components are [from (witness of Y) ∘
 (witness of X)] — and its NATURALITY is automatic, using only the coherence
 fields of the four witnesses; the hypothesis is spent only on the comma
 square. 

 --------
 相反情况：兼容-证人关系正好是后向映射的核，因此上述等价不是任意选择，而是使 [huq_transform] 可注入的最粗等价。比较同构是强制的——它的组成部分是 [来自 Y 的证人 ∘ X 的证人]——并且它的自然性是自动的，仅使用四个证人的相干场；假设仅用于逗号平方。
*)

(*
 Undoing the conjugation on the [S] side: the recovered transformation,
 precomposed with the first witness, is the comma component of F d
 postcomposed with the second. 

 --------
 撤销 [S] 侧的共轭：恢复的变换与第一个见证预组合，是 F d 的逗号分量，与第二个后组合。
*)
Lemma huq_transform_unconj (X : HuqSection) (d : D) :
  huq_transform X d ∘ fmap[S] (to (`1 (huq_sec1 X) d))
    ≈ fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d).
Proof.
  rewrite (huq_transform_apply X d).
  rewrite <- (comp_assoc (fmap[T] (to (`1 (huq_sec2 X) d))
                            ∘ `2 (huq_functor X d))).
  rewrite <- fmap_comp, iso_from_to, fmap_id, id_right.
  reflexivity.
Qed.

(*
 The two recovered transformations agree, so the [X]-side conjugation of
 the comma component of [F X] equals the [Y]-side one, up to the two
 witnesses at d. This is the whole use made of the hypothesis. 

 --------
 两次恢复的变换是一致的，所以  [X] 侧对 [F X] 的逗号部分的共轭等于 [Y] 侧的共轭，最多差两个位于 d 的证明。这就是对该假设的全部使用。
*)
Lemma huq_transform_shift (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (d : D) :
  fmap[T] (to (`1 (huq_sec2 X) d)) ∘ `2 (huq_functor X d)
    ≈ fmap[T] (to (`1 (huq_sec2 Y) d)) ∘ `2 (huq_functor Y d)
        ∘ fmap[S] (from (`1 (huq_sec1 Y) d))
        ∘ fmap[S] (to (`1 (huq_sec1 X) d)).
Proof.
  rewrite <- (huq_transform_apply Y d).
  rewrite <- (H d).
  symmetry; apply huq_transform_unconj.
Qed.

Program Definition huq_compare (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ~{S ↓ T}~> huq_functor Y d :=
  ((from (`1 (huq_sec1 Y) d) ∘ to (`1 (huq_sec1 X) d),
    from (`1 (huq_sec2 Y) d) ∘ to (`1 (huq_sec2 X) d)); _).
Next Obligation.
  rewrite !fmap_comp.
  rewrite <- (comp_assoc (fmap[T] (from (`1 (huq_sec2 Y) d)))).
  rewrite (huq_transform_shift X Y H d).
  rewrite !comp_assoc, <- fmap_comp, iso_from_to, fmap_id, id_left.
  reflexivity.
Qed.

Program Definition huq_compare_iso (X Y : HuqSection)
        (H : huq_transform X ≈ huq_transform Y) (d : D) :
  huq_functor X d ≅ huq_functor Y d := {|
  to   := huq_compare X Y H d;
  from := huq_compare Y X (symmetry H) d
|}.
Next Obligation. split; apply iso_conj_cancel. Qed.
Next Obligation. split; apply iso_conj_cancel. Qed.

Lemma huq_compare_natural (X Y : HuqSection)
      (H : huq_transform X ≈ huq_transform Y) (x y : D) (f : x ~> y) :
  fmap[huq_functor X] f
    ≈ from (huq_compare_iso X Y H y)
        ∘ fmap[huq_functor Y] f
        ∘ to (huq_compare_iso X Y H x).
Proof.
  spose (`2 (huq_sec1 X) x y f) as H1X.
  spose (`2 (huq_sec1 Y) x y f) as H1Y.
  spose (`2 (huq_sec2 X) x y f) as H2X.
  spose (`2 (huq_sec2 Y) x y f) as H2Y.
  split; simpl.
  - rewrite H1X, H1Y.
    symmetry; apply iso_conj_recompose.
  - rewrite H2X, H2Y.
    symmetry; apply iso_conj_recompose.
Qed.

Definition huq_compare_equiv (X Y : HuqSection)
           (H : huq_transform X ≈ huq_transform Y) :
  huq_functor X ≈[Cat] huq_functor Y :=
  (huq_compare_iso X Y H; huq_compare_natural X Y H).

Theorem huq_transform_compatible (X Y : HuqSection) :
  huq_transform X ≈ huq_transform Y → HuqCompatible X Y.
Proof.
  intro H.
  exists (huq_compare_equiv X Y H).
  split; intro d; simpl;
  rewrite comp_assoc, iso_to_from, id_left; reflexivity.
Qed.

Theorem huq_compatible_iff (X Y : HuqSection) :
  HuqCompatible X Y ↔ huq_transform X ≈ huq_transform Y.
Proof.
  split.
  - apply huq_compatible_transform.
  - apply huq_transform_compatible.
Qed.

(*
 The section-side round trip, at the level of the quotient. This LEMMA is
 proved directly from the comparison isomorphism of
 [Comma_Functor_Comma_Transform] — it does not go through
 [huq_transform_compatible] — so the round trip itself does not rest on the
 kernel characterisation.  (The packaged [Huq_roundtrip] as a whole still
 does, elsewhere: the forward map's respectfulness consumes
 [huq_transform_compatible], and [HuqSection_Setoid]'s Equivalence
 obligation routes through the kernel reading — the latter stylistically,
 reflexivity at least having a direct geometric proof.) 

 --------
 在商的层面上，截面侧的往返。这个引理直接从 [Comma_Functor_Comma_Transform] 的比较同构中证明——它并没有通过 [huq_transform_compatible]——所以往返本身并不依赖于核的刻画。（整体打包的 [Huq_roundtrip] 仍然在其他地方依赖：前向映射的尊重性消耗了 [huq_transform_compatible]，而 [HuqSection_Setoid] 的等价性义务通过核的解读传递——后者在风格上至少具有直接的几何证明的自反性。）
*)

Theorem huq_section_compatible (X : HuqSection) :
  HuqCompatible (huq_section (huq_transform X)) X.
Proof.
  exists (Comma_Functor_Comma_Transform (huq_functor X) (huq_sec1 X) (huq_sec2 X)).
  split; intro d; simpl; symmetry; apply iso_to_from.
Qed.

Program Definition HuqSection_Setoid : Setoid HuqSection := {|
  equiv := HuqCompatible
|}.
Next Obligation.
  constructor.
  - intro X.
    apply huq_transform_compatible; reflexivity.
  - intros X Y HXY.
    apply huq_transform_compatible.
    symmetry; now apply huq_compatible_transform.
  - intros X Y Z HXY HYZ.
    apply huq_transform_compatible.
    transitivity (huq_transform Y); now apply huq_compatible_transform.
Qed.

Definition huq_dom : SetoidObject := {| carrier := S ⟹ T |}.
Definition huq_cod : SetoidObject :=
  {| carrier := HuqSection; is_setoid := HuqSection_Setoid |}.

Program Definition Huq_roundtrip : @Isomorphism Sets huq_dom huq_cod := {|
  to   := {| morphism := huq_section |};
  from := {| morphism := huq_transform |}
|}.
Next Obligation.
  proper.
  apply huq_transform_compatible.
  rewrite !huq_transform_section.
  assumption.
Qed.
Next Obligation.
  proper.
  now apply huq_compatible_transform.
Qed.
Next Obligation. apply huq_section_compatible. Qed.
Next Obligation. apply huq_transform_section. Qed.

End HuqBijection.

(* * ** Witness dependence is not merely formal / * ** 证人依赖不仅仅是形式上的 *)

(*
 The conjugation of [Comma_Transform_witness_shift] can be non-trivial, and
 the witness B(Z/2) shows it. In the delooping of the two-element group
 composition is [xorb] and the identity arrow is [false]; the group is
 abelian, so EVERY element is a natural automorphism of the identity functor
 (naturality of a family over a one-object category is exactly commutativity
 with each arrow). Hence [true] gives a second witness that
 [comma_proj1 ◯ Comma_Functor nat_id] is the identity, inequivalent to the
 canonical one, and the two transformations recovered from THE SAME section
 functor are [false] and [true].

 So the ill-definedness that motivates [HuqSection]'s bundling of witnesses
 is exhibited, not assumed: no map out of a setoid of section functors that
 discarded the witnesses could agree with [Comma_Transform], since one and
 the same functor would have to be sent to two distinct transformations.

 UNIVERSES: everything above this section is fully polymorphic with no
 [Set] anywhere.  The separation witness alone is pinned -- [Bool_Xor]'s
 carrier is [bool : Set], so [BZ2 : Category@{u Set Set}] has its hom and
 proof levels at [Set] -- the expected price of a concrete witness (the
 Instance/Grp/Center.v S3 precedent), and a counterexample needs only one
 instance. 

 --------
 [Comma_Transform_witness_shift] 的结合可以是非平凡的，见证 B(Z/2) 就说明了这一点。在二元素群的去环化中，组合是 [xorb]，恒等箭头是 [false]；该群是阿贝尔群，因此每个元素都是恒等函子的一种自然自同构（一个一对象范畴上函子族的自然性恰好是与每条箭头的可交换性）。因此 [true] 提供了第二个证明，表明 [comma_proj1 ◯ Comma_Functor nat_id] 是恒等元素，并且与标准的不同，从同一个截面函子恢复的两个变换是 [false] 和 [true]。因此，促使 [HuqSection] 将见证捆绑在一起的不明确性是表现出来的，而不是假设的：没有任何从剔除见证的截函子集合体映射的映射能够与 [Comma_Transform] 一致，因为同一个函子必须被送到两个不同的变换上。

 宇宙：本节以上的所有内容都是完全多态的，且没有任何 [Set]。唯一固定的是分离见证——[Bool_Xor] 的承载体是 [bool : Set]，因此 [BZ2 : Category@{u Set Set}] 的同态和证明层次在 [Set] ——这是一个具体见证的预期代价（参考 Instance/Grp/Center.v 中 S3 的先例），而一个反例只需要一个实例。
*)

Local Notation BZ2 := (Deloop Bool_Xor).

Definition huq_sep_tau : Id[BZ2] ⟹ Id[BZ2] := nat_id.

Definition huq_sep_F : BZ2 ⟶ (Id[BZ2] ↓ Id[BZ2]) := Comma_Functor huq_sep_tau.

(*
 The twisted witness: the component is [true], self-inverse in Z/2, and the
 coherence condition holds because conjugating by [true] on both sides is the
 identity. 

 --------
 扭曲的见证：该分量是 [true]，在 Z/2 中自反，并且一致性条件成立，因为在两边用 [true] 共轭是恒等映射。
*)
Program Definition huq_sep_twist :
  comma_proj1 ◯ huq_sep_F ≈[Cat] Id := (fun _ => {| to := true; from := true |}; _).
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. now destruct f. Qed.

Definition huq_sep_canonical : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := Comma_Functor_proj1 huq_sep_tau;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Definition huq_sep_twisted : HuqSection :=
  {| huq_functor := huq_sep_F;
     huq_sec1    := huq_sep_twist;
     huq_sec2    := Comma_Functor_proj2 huq_sep_tau |}.

Example huq_sep_canonical_value : huq_transform huq_sep_canonical ttt = false :=
  eq_refl.

Example huq_sep_twisted_value : huq_transform huq_sep_twisted ttt = true :=
  eq_refl.

Theorem huq_witness_separates :
  huq_transform huq_sep_canonical ≈ huq_transform huq_sep_twisted → False.
Proof.
  intro H.
  specialize (H ttt).
  discriminate.
Qed.

(*
 The quotient of [Huq_roundtrip] therefore distinguishes two packaged
 sections with the SAME underlying functor: [HuqCompatible] is strictly
 finer than equality of section functors. 

 --------
 因此，[Huq_roundtrip] 的商将两个具有相同底层函子的封装部分区分开来：[HuqCompatible] 比部分函子的相等严格得多。
*)

Corollary huq_witness_sections_incompatible :
  HuqCompatible huq_sep_canonical huq_sep_twisted → False.
Proof.
  intro HC.
  now apply huq_witness_separates, huq_compatible_transform.
Qed.
