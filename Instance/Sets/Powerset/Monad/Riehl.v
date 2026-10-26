(* * * Riehl's route to the naturality of the union / * * 里尔关于联盟自然性的路径 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Monad.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(*
 Book: Riehl, “Category Theory in Context”, 2nd ed., §5.1, Example
 5.1.5(i), printed p. 185 (PDF p. 205) — riehl:5.1:example5; with
 her Corollary 4.6.3, printed p. 167, and Example 4.1.8, printed
 p. 134
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.2, Exercise 1(a), printed p. 142
 (PDF p. 151) — maclane:VI.2:ex1
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/adjoint+functor

 Riehl's Example 5.1.5(i) presents the covariant power set monad under
 “Monads also arise in nature” and says how its two naturality squares
 are proved: “Naturality of the unit with respect to a function f : A → B
 makes use of the fact that f_* : PA → PB is the direct image (rather
 than inverse image) function.  Naturality of the multiplication maps
 makes use of Corollary 4.6.3; the direct image function, as a left
 adjoint, preserves unions.”  Corollary 4.6.3 reads: “For any function
 f : A → B, the inverse image f^{-1} : PB → PA, a function between the
 power sets of A and B, preserves both unions and intersections, while
 the direct image f_* : PA → PB only preserves unions”, and its proof
 cites the adjunction f_* ⊣ f^{-1} of Example 4.1.8 between the posets of
 subsets and observes that “Unions are colimits and intersections are
 limits in the poset category PA”: left adjoints preserve colimits.

 Instance/Sets/Powerset/Monad.v proves the naturality of μ directly, by
 opening the squashed direct image ([Powerset_union_natural]).  This
 satellite takes Riehl's route, twice, through Instance/Powerset.v
 (#382), which has her Example 4.1.8 as [image_preimage_adjunction] and
 the direct-image half of Corollary 4.6.3 in two forms:
 [direct_image_preserves_joins], proved directly at an arbitrary least
 upper bound, and [direct_image_preserves_joins_via_LAPC], read off
 Adjunction/Continuity.v's [left_adjoint_preserves_colimit] at the
 adjunction, which is the corollary's own proof.  The naturality of η is
 #227's [Powerset_Prop_Singleton], whose naturality square is #227's
 [Powerset_Prop_image_singleton], the direct image of a singleton being
 the singleton of the image (Riehl's point that f_* is the direct
 image), and is not revisited.

 THE UNION AS A LEAST UPPER BOUND.  ⋃ SS is the least upper bound,
 under #382's inclusion [subset_le], of the family of its members,
 indexed by the members themselves, the sigma { S & S ∈ SS }
 ([Powerset_union_IsLUB], in Instance/Proset/Limit.v's [IsLUB]); and it
 is ≈ #382's canonical union [subset_union] of that family
 ([Powerset_union_family]).

 THE TWO ROUTES.  [join_natural_via_image]: the direct image of that
 least upper bound is the least upper bound of the images f S, S ∈ SS,
 by [direct_image_preserves_joins]; ⋃ (P (P f) SS) is the least upper
 bound of its own members, which are those images up to ≈; two least
 upper bounds of families with the same upper bounds are equal by the
 antisymmetry of inclusion.  [join_natural_via_LAPC] does the same with
 [direct_image_preserves_joins_via_LAPC] at the family of members,
 moving between #382's canonical union and the monad's by
 [Powerset_union_family].  Preservation of unions does not give the
 square for free: identifying ⋃ (P (P f) SS) with the least upper bound
 of the images still opens the squashed direct image that the direct
 proof opens, in both routes.

 THE ROUTES PROVE THE MONAD'S FIELD.  [Powerset_join_natural_statement f]
 is the type of [Powerset_Monad]'s naturality field [join_fmap_fmap] at
 f.  [join_natural_routes_agree] pairs the field itself with the direct
 lemma and both routes at that one type: it type-checks, so each route
 proves the field's statement as stated, by conversion.  The proofs are
 different terms of a proposition and are not compared.

 COST, measured.  The dependency closure is thirty-two files for
 Instance/Sets/Powerset/Monad.v, eighty-nine for that file with
 Instance/Powerset.v, and ninety for this satellite (the transitive
 closure of the Category.* [Require] lines, each file counted once, the
 root included; Instance/Powerset.v alone reaches eighty-eight), which
 is why the monad keeps the direct proof.  In universes, read off
 [About]: [join_natural_via_image] adds to the block of
 [Powerset_Monad] the caps o <= Relation_Definition.u0,
 first carried by Instance/Proset/Limit.v's [IsLUB] over the standard
 library's [relation], and o <= Projections.u0, the sigma projection of
 the index, first carried by [Powerset_union_IsLUB].
 [join_natural_via_LAPC] adds the strict bounds o < projections.u0 and
 o < projections.u1 (the pair projections), with Set < projections.u0,
 Set < projections.u1 and JMeq.u0 <= JMeq.u1, and the caps
 o <= RelationClasses.Defs.u0, Relation_Definition.u0, eq.u0,
 Logic_lemmas.equality.u0 and Projections.u0.  All are
 [direct_image_preserves_joins_via_LAPC]'s own: the two strict bounds
 and the caps eq.u0 and Logic_lemmas.equality.u0 at its index universe,
 which the family of members puts at o; the caps
 RelationClasses.Defs.u0, Relation_Definition.u0 and Projections.u0 at
 its setoid level o; and the bounds on Set and JMeq unconditionally.
 [join_natural_routes_agree] carries the union of the two.
 [Powerset_union_IsLUB] states [IsLUB] at [IsLUB@{o o Set Set Set}]:
 the bound is a pair of propositions, and with its level at o instead,
 [join_natural_via_image] gained o <= projections.u0 (measured).
 Every constant binds [@{o}] or [@{o so}]; there is no equation.

 STRENGTHS.  The four proofs of the square are at ≈, which is what the
 field states; that their statements are the field's is by conversion
 ([join_natural_routes_agree]).  Nothing here is refused, and no probe
 item pins this file.

 NOT DELIVERED.  No monad is built with Riehl's proof in its naturality
 field; one would differ from [Powerset_Monad] only in that proof.  The
 inverse-image half of Corollary 4.6.3 is #382's. 

 --------
 书籍：Riehl，《Category Theory in Context》，第2版，第5.1节，例5.1.5(i)，印刷版第185页（PDF第205页）— riehl:5.1:example5；及其推论4.6.3，印刷版第167页，以及例4.1.8，印刷版第134页
 书籍：Mac Lane，《Categories for the Working Mathematician》，第2版，Springer GTM 5，1998，第VI.2节，练习1(a)，印刷版第142页（PDF第151页）— maclane:VI.2:ex1
 nLab：https://ncatlab.org/nlab/show/power+set
 nLab：https://ncatlab.org/nlab/show/adjoint+functorRiehl 的例 5.1.5(i) 在“单子也出现在自然界中”下展示了协变幂集单子，并说明了它的两个自然性方格是如何证明的：“单位在函数 f : A → B 下的自然性利用了 f_* : PA → PB 是直像函数（而不是逆像函数）的事实。”乘法映射的自然性利用了推论 4.6.3；作为左伴随的直接像函数保持并集。推论 4.6.3 记作：“对于任何函数 f : A → B，其逆像 f^{-1} : PB → PA（A 和 B 的幂集之间的函数）既保持并集又保持交集，而直接像 f_* : PA → PB 仅保持并集”，其证明引用了示例 4.1.8 中子集偏序集之间的伴随关系 f_* ⊣ f^{-1}，并指出：“在偏序集范畴 PA 中，并集是余极限，交集是极限”：左伴随保持余极限。Instance/Sets/Powerset/Monad.v 直接证明了 μ 的自然性，通过打开压缩的直接象 ([Powerset_union_natural])。这个卫星模块采用了 Riehl 的方法，通过 Instance/Powerset.v（#382）两次，其中包含她的示例 4.1.8 作为 [image_preimage_adjunction]，以及推论 4.6.3 的直接象部分的两种形式：[direct_image_preserves_joins]，在任意最小上界处直接证明，以及 [direct_image_preserves_joins_via_LAPC]，从 Adjunction/Continuity.v 的 [left_adjoint_preserves_colimit] 在伴随关系处读取，这是该推论自身的证明。η 的自然性是 #227 的 [Powerset_Prop_Singleton]，其自然性方形是 #227 的 [Powerset_Prop_image_singleton]，单集的直接象即为像的单集（Riehl 提出的 f_* 是直接象的观点），并未重新讨论。并集作为最小上界。⋃ SS 是其成员族在 #382 的包含关系 [subset_le] 下的最小上界，该族按其自身成员索引，是 σ { S & S ∈ SS }（在 Instance/Proset/Limit.v 中的 [IsLUB]）；并且它是 #382 的该族的典型并集 [subset_union]（[Powerset_union_family]）。两条路线。[join_natural_via_image]：那个上确界的直接像是图像的上确界 f S，其中 S ∈ SS，由 [direct_image_preserves_joins] 得出；⋃ (P (P f) SS) 是它自身成员的上确界，这些成员是直到 ≈ 的那些图像；两个具有相同上界的族的上确界，根据包含的反对称性是相等的。[join_natural_via_LAPC] 对成员族使用 [direct_image_preserves_joins_via_LAPC] 做同样的事情，在 [Powerset_union_family] 的作用下，在 #382 的典型并和幺元之间移动。并集的保持并不会使方形自动成立：将 ⋃ (P (P f) SS) 与图像的上确界等同，仍然打开了直接证明所打开的压缩直接像，在这两条路线中都是如此。路线证明了单子（Monad）的域。[Powerset_join_natural_statement f] 是 [Powerset_Monad] 的自然性域 [join_fmap_fmap] 在 f 处的类型。[join_natural_routes_agree] 将该域本身与直接引理以及该类型的两条路线配对：它进行类型检查，因此每条路线通过转换证明了该域的陈述。证明是命题的不同项，并不进行比较。成本，可衡量。依赖闭包对于 Instance/Sets/Powerset/Monad.v 是三十二个文件，对于包含 Instance/Powerset.v 的该文件是八十九个，对于这个卫星文件是九十个（Category.* [Require] 行的传递闭包，每个文件只算一次，包括根；仅 Instance/Powerset.v 就达到了八十八个），这也是为什么 monad 保留直接证明。在宇宙中，读出 [About]：[join_natural_via_image] 将 [Powerset_Monad] 的块加入到 caps o <= Relation_Definition.u0，最初由 Instance/Proset/Limit.v 的 [IsLUB] 承载于标准库的 [relation] 上，并且 o <= Projections.u0，即索引的 sigma 投影，最初由 [Powerset_union_IsLUB] 承载。[join_natural_via_LAPC] 添加了严格界 o < projections.u0 和 o < projections.u1（成对投影），以及 Set < projections.u0、Set < projections.u1 和 JMeq.u0 <= JMeq.u1，还有上界 o <= RelationClasses.Defs.u0、Relation_Definition.u0、eq.u0、Logic_lemmas.equality.u0 和 Projections.u0。所有这些都是 [direct_image_preserves_joins_via_LAPC] 自己的：两个严格界，以及其索引类型宇宙处的上界 eq.u0 和 Logic_lemmas.equality.u0，这些由成员族置于 o；RelationClasses.Defs.u0、Relation_Definition.u0 和 Projections.u0 的上界处于其集合等价类层 o；而对 Set 和 JMeq 的界是无条件的。[join_natural_routes_agree] 承载了这两者的并集。[Powerset_union_IsLUB] 在 [IsLUB@{o o Set Set Set}] 表示 [IsLUB]：该界是一对命题，并且其层在 o 处时，[join_natural_via_image] 获得了 o <= projections.u0（经过测量）。每个常量绑定 [@{o}] 或 [@{o so}]；没有方程式。

 优势。平方的四个证明在 ≈，这就是该领域所陈述的；它们的陈述属于该领域是通过转换 ([join_natural_routes_agree]) 实现的。这里没有任何被拒绝的内容，也没有探针项目固定此文件。

 未交付。没有单子是在其自然性域中用 Riehl 的证明建立的；唯一的差异在于该证明中与 [Powerset_Monad] 的不同。推论 4.6.3 的逆像部分是 #382 的。
*)

(* ------------------------------------------------------------------------ *)
(* * ** The union as a least upper bound / * ** 并集作为最小上界 *)

(*
 ⋃ SS is the least upper bound, under inclusion, of the family of its
 members, indexed by the members themselves. 

 --------
 ⋃ SS 是其成员族在包含关系下的最小上界，该族的索引由其成员本身构成。
*)
Lemma Powerset_union_IsLUB@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  IsLUB@{o o Set Set Set} (@subset_le@{o} X)
    (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i)
    (Powerset_union_pred@{o} SS).
Proof.
  split.
  - intros [S HS] x Hx. exists S; split; assumption.
  - intros n Hn x [S [HS Hx]]. exact (Hn (S; HS) x Hx).
Qed.

(* The same union, as #382's canonical family union [subset_union]. / 同一个联合，如 #382 的规范家庭联合 [subset_union]。 *)
Lemma Powerset_union_family@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} SS
    ≈ subset_union@{o o o}
        (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } => projT1 i).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. exists (S; HS). exact Hx.
  - intros [[S HS] Hx]. exists S; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The naturality of μ, through the direct image as a left adjoint / * ** μ的自然性，通过作为左伴随的直接像 *)

(* Through #382's [direct_image_preserves_joins]: the image of a least upper bound is the least upper bound of the images. / 通过 #382 的 [direct_image_preserves_joins]：上确界的像是像的上确界。 *)
Lemma join_natural_via_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins f _ _ (Powerset_union_IsLUB SS))
    as Hf.
  pose proof (Powerset_union_IsLUB
                (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)) as Hu.
  destruct Hf as [Hf_ub Hf_least].
  destruct Hu as [Hu_ub Hu_least].
  intro y; split.
  - apply Hu_least. intros [T HT] z Hz.
    apply HT; intros [S [HS E]].
    exact (Hf_ub (S; HS) z (proj2 (E z) Hz)).
  - apply Hf_least. intros [S HS] z Hz.
    refine (Hu_ub (existT _ (Powerset_Prop_image@{o} f S) _) z Hz).
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(*
 Through #382's [direct_image_preserves_joins_via_LAPC]: Riehl's Corollary
 4.6.3 read off the left adjoint's preservation of colimits, at the
 canonical union of the members. 

 --------
 通过 #382 的 [direct_image_preserves_joins_via_LAPC]：Riehl 的推论 4.6.3，从左伴随保持余极限的性质中，在成员的典型并集上读取出来。
*)
Lemma join_natural_via_LAPC@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  pose proof (direct_image_preserves_joins_via_LAPC f
                (fun i : { S : carrier (Powerset_Prop_obj@{o} X) & SS S } =>
                   projT1 i)) as Hf.
  destruct Hf as [Hf_ub Hf_least].
  pose proof (@proper_morphism _ _ _ _ (Powerset_Prop_map@{o} f) _ _
                (Powerset_union_family SS)) as E.
  intro y; split.
  - intros [T [HT Hy]]. apply (proj2 (E y)).
    apply HT; intros [S [HS ES]].
    exact (Hf_ub (S; HS) y (proj2 (ES y) Hy)).
  - intro Hy.
    refine (Hf_least (Powerset_union_pred@{o}
                        (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS))
              _ y (proj1 (E y) Hy)).
    intros [S HS] z Hz. exists (Powerset_Prop_image@{o} f S); split;
      [ | exact Hz ].
    apply Powerset_squash_intro. exists S; split; [ exact HS | ].
    reflexivity.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The three proofs inhabit the monad's naturality field / * ** 三个证明存在于单子自然性领域 *)

(* The type of [Powerset_Monad]'s field [join_fmap_fmap] at f. / f 处 [Powerset_Monad] 的字段 [join_fmap_fmap] 的类型。 *)
Definition Powerset_join_natural_statement@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  @join _ _ Powerset_Monad@{o so} Y
    ∘ fmap[Powerset_Prop@{o so}] (fmap[Powerset_Prop@{o so}] f)
  ≈ fmap[Powerset_Prop@{o so}] f ∘ @join _ _ Powerset_Monad@{o so} X.

(*
 The field itself, the direct lemma, and both of Riehl's routes: the
 quadruple is well typed, so each route proves the field's statement. 

 --------
 该域本身、直接词条，以及Riehl的两条路线：这个四元组类型良好，因此每条路线都证明了该域的陈述。
*)
Definition join_natural_routes_agree@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f
  * Powerset_join_natural_statement@{o so} f :=
  (@join_fmap_fmap _ _ Powerset_Monad@{o so} X Y f,
   fun SS => Powerset_union_natural@{o} f SS,
   fun SS => join_natural_via_image f SS,
   fun SS => join_natural_via_LAPC f SS).
