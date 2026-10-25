Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(*
   * * The universal property of [C[C⁻¹]] at [Functor_Setoid] strength

   nLab:      https://ncatlab.org/nlab/show/localization
   nLab:      https://ncatlab.org/nlab/show/calculus+of+fractions
   Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
   printed p. 137 — the inclusion of groupoids into categories has a
   left adjoint, the category of fractions
   Book: Gabriel, Zisman, Calculus of Fractions and Homotopy Theory,
   Ergebnisse 35, Springer 1967, §I.1

   WHAT THIS FILE IS FOR.  [Construction/Fractions.v] proves the universal
   property of the zig-zag localization at STRICT strength: its
   [Fractions_UMP] and [Fractions_UMP_groupoid] are [Unique] records over
   [Functor_StrictEq_Setoid], i.e. Leibniz equality on objects together
   with `≈` on morphisms conjugated by [hom_cast].  That is the strength
   [Construction/Quotient.v] and [Construction/Free/Groupoid.v] state their
   own uniqueness clauses at, and it is the wrong strength for
   [Theory/Universal/Arrow.v]'s [universal_arrow_from_UMP], which reads the
   `∃!` at the AMBIENT category's hom-setoid.  The ambient here is [Cat],
   whose hom-setoid is [Functor_Setoid] — natural isomorphism.  The header
   of [Construction/Fractions.v] records the resulting mismatch and quotes
   the refusal in full.

   This file removes the mismatch by REPROVING the uniqueness clause
   against natural isomorphism.  Existence needed no work: it transfers
   along [Instance/StrictCat/ToCat.v]'s [strict_equiv_implies_fun_equiv],
   which is exactly the statement that strict equality of functors refines
   natural isomorphism.  Uniqueness does not transfer in that direction —
   a functor that factors [F] only up to natural isomorphism need not
   factor it up to object equality, so the strict statement says nothing
   about it — and it is reproved here from the beginning.

   WHY THE ARGUMENT WORKS.  Three facts about [Fractions C] make it go
   through, and all three are conversions, not lemmas: [Fractions C] has
   exactly the objects of [C] ([ZQuiver]'s [nodes] is [@obj C], and neither
   [FreeOnQuiver] nor [QuotientCong] disturbs the object type),
   [FractionsProj C] is the identity on objects, and a hom of
   [Fractions C] IS a [Lib/TList.v] word in the glued quiver, the quotient
   coarsening only the setoid.  So a natural isomorphism between the two
   restrictions [G1 ◯ FractionsProj C] and [G2 ◯ FractionsProj C] already
   supplies its component at every object of [Fractions C]; only naturality
   has to be extended, from the generators to all words.

   That extension is the induction [Fractions_weak_word], and it has the
   same shape as [Construction/Fractions.v]'s [ZigZagLift_unique] — the
   word is peeled with [tlist_app_cons], the tail handled by the induction
   hypothesis and the head letter by a separate lemma — with the
   [hom_cast] of the strict argument replaced throughout by conjugation
   with the components of the isomorphism.  The head letter splits the same
   way too: a forward letter is a generator and is given, while a backward
   letter is pinned because both [G1] and [G2] carry the two cancellation
   equations of [Construction/Fractions.v] to two-sided inverses
   ([zbwd_zfwd_functor], [zfwd_zbwd_functor], which hold for ANY functor out
   of the localization), and a two-sided inverse is determined up to `≈`.
   [iso_conj_inverse] is the replacement for [hom_cast_inverse]: it says
   that if [a] and [a'] correspond under conjugation by two isomorphisms,
   then so do their inverses.

   NO GROUPOID HYPOTHESIS ON THE TARGET, for the uniqueness half.
   [Fractions_weak_word] and [Fractions_proj_epic_weak] hold for an
   arbitrary target category [D]; the invertibility they use is that of the
   IMAGES of the generators, which the localization already forces.  Only
   existence needs [IsGroupoid D], and only to produce the [Finv] argument
   of [FractionsLift].

   WHAT IS PROVED, AND WHAT IS NOT.  [Fractions_UMP_weak] is the same
   [Unique] record as [Fractions_UMP_groupoid] with [Functor_StrictEq_Setoid]
   replaced by [Functor_Setoid] in both positions.  It is genuinely WEAKER
   than the strict one, and deliberately so: the two are not
   interchangeable, and [Test/ProbeFractionsAdjunction972.v] pins the
   direction by refusing the strict statement where only the weak one has
   been proved.  Nothing here says the strict version is subsumed, and
   [Construction/Fractions.v] keeps it — [Fractions_proj_epic] and
   [frac_restrict_recovers] still read at the strict setoid. 

   --------
   * * [C[C⁻¹] 在 [Functor_Setoid] 强度下的普遍性质

   nLab:       https://ncatlab.org/nlab/show/localization 
   nLab:       https://ncatlab.org/nlab/show/calculus+of+fractions 
   书籍: Riehl，《Category Theory in Context》，第2版，§4.1，例4.1.15，
   印刷第137页——群族到范畴的包含有一个左伴随，即分数范畴
   书籍: Gabriel, Zisman，《Calculus of Fractions and Homotopy Theory》，
   Ergebnisse 35, Springer 1967, §I.1这个文件的用途。[Construction/Fractions.v] 证明了在 STRICT 强度下锯齿局部化的普遍性：它的 [Fractions_UMP] 和 [Fractions_UMP_groupoid] 是 [Unique] 关于 [Functor_StrictEq_Setoid] 的记录，即对象上的莱布尼茨等式以及通过 [hom_cast] 共轭的态射上的 `≈`。也就是说，[Construction/Quotient.v] 和 [Construction/Free/Groupoid.v] 在其自身处状态其唯一性条款，而它对于 [Theory/Universal/Arrow.v] 的 [universal_arrow_from_UMP] 是错误的强度，后者在 AMBIENT 范畴的 hom-setoid 上读取 `∃!`。这里的环境是 [Cat]，其 hom-setoid 是 [Functor_Setoid]——自然同构。[Construction/Fractions.v] 的标题记录了由此产生的不匹配并完整引用了拒绝内容。此文件通过针对自然同构重新证明唯一性条款来消除不匹配。存在性不需要工作：它沿着  [Instance/StrictCat/ToCat.v] 的  [strict_equiv_implies_fun_equiv] 转移，这正是函子严格相等细化自然同构的陈述。唯一性在那个方向上不传递——一个仅在自然同构下分解 [F] 的函子不必在对象相等的意义下分解它，因此严格的陈述对此没有任何说明——并且它在这里从头重新证明。论证为何成立。关于 [Fractions C] 有三个事实使它成立，这三者都是变换(conversions)，而不是引理(lemmas)：[Fractions C] 恰好包含 [C] 的对象（[ZQuiver] 的 [nodes] 是 [@obj C]，并且 [FreeOnQuiver] 和 [QuotientCong] 都不改变对象类型），[FractionsProj C] 在对象上是恒等的，并且 [Fractions C] 的同态(hom) 在粘接箭图(glued quiver)中是 [Lib/TList.v] 单词，商集仅使同类集粗化。因此，两个限制 [G1 ◯ FractionsProj C] 和 [G2 ◯ FractionsProj C] 之间的自然同构已经在 [Fractions C] 的每个对象上提供了其分量；只需要将自然性从生成元扩展到所有单词。该扩展是诱导 [Fractions_weak_word]，它与 [Construction/Fractions.v] 的 [ZigZagLift_unique] 具有相同的形状——单词通过 [tlist_app_cons] 被剥离，尾部由诱导假设处理，而首字母由一个单独的引理处理——严格参数的 [hom_cast] 在整个过程中被同构的分量共轭所取代。首字母的分解方式也相同：前向字母是一个生成元并且是已知的，而后向字母被固定，因为 [G1] 和 [G2] 将 [Construction/Fractions.v] 的两个消去方程带到双边逆 ([zbwd_zfwd_functor], [zfwd_zbwd_functor]，这在定位化的任何函子中都成立)，并且双边逆在 `≈` 下唯一确定。[iso_conj_inverse] 是 [hom_cast_inverse] 的替代方案：它表示如果 [a] 和 [a'] 在两个同构的共轭下对应，那么它们的逆也对应。

   对于唯一性部分，目标上不需要群类假设。[Fractions_weak_word] 和 [Fractions_proj_epic_weak] 对任意目标范畴 [D] 都成立；它们使用的可逆性是生成元的像的可逆性，而这一点在局部化中已经被强制。只有存在性需要 [IsGroupoid D]，而且仅仅是为了生成 [FractionsLift] 的 [Finv] 论证。什么是已证明的，什么是未证明的。  [Fractions_UMP_weak] 与 [Unique] 记录相同为 [Fractions_UMP_groupoid] ，只是将 [Functor_StrictEq_Setoid] 替换为 [Functor_Setoid] ，在两个位置上都是如此。 它确实比严格版本弱，并且是故意如此：两者不可互换，[Test/ProbeFractionsAdjunction972.v] 通过拒绝仅弱版本已被证明的严格表述来固定方向。 这里没有说严格版本被包含，[Construction/Fractions.v] 保持它——[Fractions_proj_epic] 和 [frac_restrict_recovers] 仍然以严格集合读取。
*)

(*
   * ** Conjugating a two-sided inverse

   The weak counterpart of [Construction/Fractions.v]'s [hom_cast_inverse].
   There the correspondence between [a] and [a'] was transport along
   equalities of the endpoints; here it is conjugation by isomorphisms of
   the endpoints, which is the shape [Functor_Setoid] states naturality in
   ([fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x)]). 

   --------
   * ** 共轭双边逆

   [Construction/Fractions.v] 的 [hom_cast_inverse] 的弱对应。
   在那里，[a] 和 [a'] 之间的对应是沿端点的等式传递的；在这里，它是通过端点的同构进行共轭，这就是 [Functor_Setoid] 在 ([fmap[F] f ≈ from (iso y) ∘ fmap [G] f ∘ to (iso x)) 中表达自然性的方式。
*)

Lemma iso_conj_inverse {D : Category} {X1 Y1 X2 Y2 : D}
  (p : X1 ≅ X2) (q : Y1 ≅ Y2)
  (a : X1 ~> Y1) (b : Y1 ~> X1) (a' : X2 ~> Y2) (b' : Y2 ~> X2)
  (Hba : b ∘ a ≈ id) (Ha'b' : a' ∘ b' ≈ id)
  (Ha : a ≈ from q ∘ a' ∘ to p) :
  b ≈ from p ∘ b' ∘ to q.
Proof.
  assert (Hac : a ∘ (from p ∘ b' ∘ to q) ≈ id).
  { rewrite Ha.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to p) (from p)).
    rewrite iso_to_from, id_left.
    rewrite (comp_assoc a' b').
    rewrite Ha'b', id_left.
    apply iso_from_to. }
  rewrite <- (id_left (from p ∘ b' ∘ to q)).
  rewrite <- Hba.
  rewrite <- comp_assoc.
  rewrite Hac.
  now rewrite id_right.
Qed.

(*
   * ** Naturality spreads from the generators to every zig-zag word 

   --------
   * ** 自然性从生成器传播到每个之字形词
*)

Section FractionsWeak.

Context {C D : Category}.

(*
 A single letter of a zig-zag word.  The forward letter IS a generator —
 [tlist_singleton (inl f)] is [zfwd f], which is [fmap[FractionsProj C] f]
 by conversion — so it is the hypothesis read back.  The backward letter is
 the content: it is inverse to the forward letter under both functors, and
 a conjugate of an inverse is the inverse of the conjugate. 

 --------
 之字形单词的单个字母。正向字母是生成器——
 [tlist_singleton (inl f)] 变为 [zfwd f]，再变为 [fmap[FractionsProj C]，通过转换——所以它是读回的假设。反向字母是内容：在两个函子下它与正向字母相反，逆元的共轭是共轭的逆元。
*)

Lemma Fractions_weak_edge
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x))
  {x y : C} (e : ZEdge (WAll C) x y) :
  fmap[G1] (tlist_singleton e)
    ≈ from (iso y) ∘ fmap[G2] (tlist_singleton e) ∘ to (iso x).
Proof.
  destruct e as [f | [g w]].
  - exact (Hgen x y f).
  - exact (iso_conj_inverse (iso y) (iso x)
             (fmap[G1] (zfwd (WAll C) g)) (fmap[G1] (zbwd (WAll C) g w))
             (fmap[G2] (zfwd (WAll C) g)) (fmap[G2] (zbwd (WAll C) g w))
             (zbwd_zfwd_functor (WAll C) G1 g w)
             (zfwd_zbwd_functor (WAll C) G2 g w)
             (Hgen y x g)).
Qed.

(*
 The induction on words, in the shape of [ZigZagLift_unique]: the empty
 word is the identity and the isomorphism cancels, and [e ::: rest] is
 [rest ∘ (e)], where the two conjugations meet at the middle object and
 the inner [to (iso b) ∘ from (iso b)] collapses. 

 --------
 在字的归纳中，以 [ZigZagLift_unique] 的形式：空字是恒等式，且同构可以抵消，而 [e ::: rest] 是 [rest ∘ (e)]，其中两个共轭在中间对象相遇，且内部的 [to (iso b) ∘ from (iso b)] 坍塌。
*)

Lemma Fractions_weak_word
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x)) :
  ∀ (x y : C) (u : x ~{Fractions C}~> y),
    fmap[G1] u ≈ from (iso y) ∘ fmap[G2] u ∘ to (iso x).
Proof.
  intros x y u.
  induction u as [| a b e rest IH].
  - rewrite !fmap_id, id_right.
    now rewrite iso_from_to.
  - assert (Hu : (e ::: rest)
                 = @compose (Fractions C) a b y rest (tlist_singleton e))
      by apply tlist_app_cons.
    rewrite Hu, !fmap_comp.
    rewrite IH, (Fractions_weak_edge G1 G2 iso Hgen e).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite !comp_assoc.
    apply compose_respects; [ | reflexivity ].
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite comp_assoc.
    now rewrite iso_to_from, id_left.
Qed.

End FractionsWeak.

(*
   * ** Precomposition with the projection is injective, at [Functor_Setoid]

   The weak counterpart of [Construction/Fractions.v]'s
   [Fractions_proj_epic], and unlike that one it needs NO hypothesis on the
   target: the whole content is [Fractions_weak_word], and the isomorphism
   family is carried over unchanged because the objects of [Fractions C]
   are the objects of [C]. 

   --------
   * ** 与投影的预组合是单射，在 [Functor_Setoid]  

   [Construction/Fractions.v] 的弱对应 [Fractions_proj_epic] ，与其不同的是它对目标没有任何假设：整个内容是 [Fractions_weak_word] ，并且同构族保持不变，因为 [Fractions C] 的对象就是 [C] 的对象。
*)

Theorem Fractions_proj_epic_weak {C D : Category} (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) L L'.
Proof.
  destruct E as [iso Hn].
  exists iso.
  exact (Fractions_weak_word L L' iso Hn).
Qed.

(*
   * ** The universal property, at [Functor_Setoid] strength 

   --------
   * ** 在 [Functor_Setoid] 强度下的普遍性
*)

Section FractionsUMPWeak.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

Let Finv := fun (x y : C) (f : x ~> y) => Dg (F x) (F y) (fmap[F] f).

(*
 Existence is free: the strict factorization of [Construction/Fractions.v]
 pushed forward along [strict_equiv_implies_fun_equiv]. 

 --------
 存在是自由的：[Construction/Fractions.v] 的严格分解沿着 [strict_equiv_implies_fun_equiv] 推进。
*)

Lemma FractionsLift_factors_weak :
  @equiv _ (@Functor_Setoid C D) F (FractionsLift F Finv ◯ FractionsProj C).
Proof.
  symmetry.
  apply strict_equiv_implies_fun_equiv.
  exact (FractionsLift_factors F Finv).
Qed.

Lemma FractionsLift_unique_weak (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) (FractionsLift F Finv) L.
Proof.
  apply Fractions_proj_epic_weak.
  transitivity F.
  - symmetry; exact FractionsLift_factors_weak.
  - exact E.
Qed.

(*
 Riehl 4.1.15, left half, in the shape [universal_arrow_from_UMP] consumes:
 the same [Unique] record as [Fractions_UMP_groupoid], over
 [Functor_Setoid] in both positions instead of [Functor_StrictEq_Setoid]. 

 --------
 Riehl 4.1.15，左半部分，在形状 [universal_arrow_from_UMP] 中消耗：同样的 [Unique] 记录作为 [Fractions_UMP_groupoid]，在两个位置上使用 [Functor_Setoid] 而不是 [Functor_StrictEq_Setoid]。
*)

Definition Fractions_UMP_weak :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  @Build_Unique _ (@Functor_Setoid (Fractions C) D) _
    (FractionsLift F Finv)
    FractionsLift_factors_weak
    FractionsLift_unique_weak.

End FractionsUMPWeak.
