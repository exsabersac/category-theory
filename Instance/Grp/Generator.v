Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(*
 The free group on one generator separates Grp

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/free+group

 Awodey, "Category Theory" (1st ed., Carnegie Mellon pre-print,
 September 2005), §7.2, printed p. 154 (PDF p. 163), gives the
 single-object generator and offers the free group on one generator as
 the generator of groups; Mac Lane, "Categories for the Working
 Mathematician", 2nd ed. (GTM 5), §V.7, book p. 127 (PDF p. 136),
 Definition 4 is the family form this instantiates, and Riehl,
 "Category Theory in Context", 2nd ed., Definition 4.7.7, printed
 p. 177 (PDF p. 197), is the same definition in her vocabulary.  This
 file supplies the [Grp] witness; the [Sets] witness is
 Instance/Sets/Generator.v and the [Ab] one Instance/Ab/Generator.v.

 THE ARGUMENT, AND WHERE ITS WORK LIVES.  Freeness does all of it.  For
 parallel homomorphisms f, g : G ~> K agreeing after every homomorphism
 out of the free group on one generator, and an element x of G, the
 constant map [grp_point x] sends the one generator to x; its extension
 [free_grp_extend] (Instance/Grp/Free.v) is a homomorphism out of
 the free group, so the hypothesis applies to it, and
 [free_grp_extend_generators] says the extension carries the
 inserted generator [fg_insert] to x.  Properness of f and g as
 setoid maps transports the agreement from the generator's image to x
 itself.  So the only structural input is the universal property, and
 the statement would read the same for any left adjoint to a forgetful
 functor whose unit at the singleton picks out an element.

 THE STRENGTH IS ≈, NOT CONVERSION, AND THAT IS FORCED BY THE DONOR.
 [free_grp_extend_generators] is stated at ≈, not at [eq_refl]: the
 extension's action is [fmap] of a functor built through
 Construction/Free/Groupoid.v's [FreeGroupoidFunctor], whose value on a
 one-letter word is reached by a [Qed]-opaque lemma rather than by
 computation.  So the two [rewrite]s below are not cosmetic — the proof
 cannot be the single [exact] that the [Ab] witness is, and the
 difference between the two files is exactly this.
 Instance/Ab/Generator.v records the contrast from the other side.

 WHAT "THE INTEGERS" ARE HERE.  Mac Lane's second example is the
 integers generating abelian groups, which belongs to
 Instance/Ab/Generator.v.  For [Grp] the corresponding object is the
 free group on one generator, which classically IS ℤ; this file does
 NOT prove that identification.  The tree DOES carry ℤ as a group
 object: Construction/Deloop/Functors.v's [Int_Plus_Grp : GrpObject]
 (the additive monoid [Int_Plus] of that file, with [grp_inv := Z.opp]), a
 built constant of the _CoqProject set.  What is left undone is the
 isomorphism [FreeGrpObject unit_setoid_object ≅ Int_Plus_Grp] in
 [Grp] -- the homomorphism out of the free group is
 [free_grp_extend] at the map sending the generator to 1%Z, the
 inverse needs the integer power of the generator in the free group,
 and the two inverse laws need induction on words and on integers --
 and nothing below depends on it.  On the abelian side the integers
 have five names, measured with grep -rnE
 '^Definition [A-Za-z_0-9]+ : AbObject := ring_ab Int_Ring\.$'
 --include='*.v' . (which reports 5): [ZAb] (Instance/Ab/Monoidal.v),
 [ab_Z] (Instance/Ab/Coproduct.v), [Zgroup]
 (Instance/Ab/Graded.v), [Ab_Z]
 (Structure/Kernel/Universal/Examples.v) and [ab_int]
 (Instance/Ab/Free.v); Instance/Ab/TorsionFree.v records the
 same count, and this is a re-measurement of it, not a citation.  An
 earlier revision of this paragraph said that NO ℤ group object existed
 in [Grp], from a sweep that saw only the tactic-mode
 [Definition … : GrpObject.] constants ([Grp_trivial], [Z2], [GalZ2],
 [GrpTwo]) and missed every [:= {| … |}] one; an audit found
 [Int_Plus_Grp], and the sentence is corrected here rather than
 removed.

 NOT DELIVERED.  No claim that the free group on one generator is the
 SMALLEST separator, nor that [Grp] has no smaller one; no statement
 about generating families of more than one object; no
 joint-faithfulness reading (Structure/Generator.v's [JointlyFaithful]),
 which is the theory half of #447; and no isomorphism with
 [Int_Plus_Grp], as above.  The two-generator non-degeneracy results of
 Instance/Grp/Free.v are not used and say nothing about
 separation. 

 --------
 一个生成元的自由群分离 Grp

 nLab: https://ncatlab.org/nlab/show/separator 
 nLab: https://ncatlab.org/nlab/show/free+group 

 Awodey，《范畴论》（第一版，卡耐基梅隆预印本，2005 年 9 月），§7.2，印刷页 154（PDF 页 163），给出了单对象生成元，并提供了一个生成元的自由群作为群的生成元；Mac Lane，《为工作数学家准备的范畴论》，第二版（GTM 5），§V.7，书本页 127（PDF 页 136），定义 4 是这个实例化的族形式，Riehl，《语境中的范畴论》，第二版，定义 4.7.7，印刷页 177（PDF 页 197），在她的术语中也是同样的定义。该文件提供了 [Grp] 的见证；[Sets] 的见证是 Instance/Sets/Generator.v，[Ab] 的见证是 Instance/Ab/Generator.v。论证，以及它的工作所在。自由性完成了所有这些。对于平行同态 f、g : G ~> K，它们在自由群上每一个生成元的同态之后都一致，并且对于 G 中的一个元素 x，常函数 [grp_point x] 将该生成元映射到 x；它的扩展 [free_grp_extend]（Instance/Grp/Free.v）是来自自由群的一个同态，因此假设适用于它，并且 [free_grp_extend_generators] 表明扩展将插入的生成元 [fg_insert] 映射到 x。作为集合等价映射的 f 和 g 的适当性将一致性从生成元的像传递到 x 本身。因此，唯一的结构性输入是泛性质，对于任何忘记函子的左伴随，其在单元素上的单位选择一个元素时，语句也将是相同的。强度是 ≈，而不是转换，这是由给定者强制的。
 [free_grp_extend_generators] 被表示为 ≈，而不是 [eq_refl] ：扩展的作用是通过 Construction/Free/Groupoid.v 的 [FreeGroupoidFunctor] 构建的函子 [fmap]，其在一个单字母词上的值是通过 [Qed] 不透明引理而不是计算获得的。因此，下面的两个 [rewrite] 并非装饰性——证明不能仅是 [exact]，[Ab] 见证就是，而两个文件之间的差异正是如此。
 Instance/Ab/Generator.v 从另一侧记录了对比。这里的“整数”是什么。麦克莱恩的第二个例子是生成阿贝尔群的整数，它属于 Instance/Ab/Generator.v。对于 [Grp]，对应的对象是一个生成元的自由群，传统上是 ℤ；这个文件并未证明该等同。该树确实将 ℤ 作为群对象承载：Construction/Deloop/Functors.v 的 [Int_Plus_Grp : GrpObject]（该文件的加法幺半群 [Int_Plus]，带有 [grp_inv := Z.opp]），这是 _CoqProject 集合的一个已构建常量。未完成的是同构 [FreeGrpObject unit_setoid_object ≅ Int_Plus_Grp] 在 [Grp] 中——从自由群出的同态是 [free_grp_extend]，映射将生成元送到 1%Z，逆向需要自由群中生成元的整数次幂，并且两个逆法则需要对字和整数进行归纳——下面的内容不依赖它。在阿贝尔方面，整数有五个名称，用命令 grep -rnE '^Definition  [A-Za-z_0-9] + : AbObject := ring_ab Int_Ring\.$' --include='*.v' . 测量（报告为 5 个）：[ZAb]（Instance/Ab/Monoidal.v）、[ab_Z]（Instance/Ab/Coproduct.v）、[Zgroup]（Instance/Ab/Graded.v）、[Ab_Z]（Structure/Kernel/Universal/Examples.v）和 [ab_int]（Instance/Ab/Free.v）；Instance/Ab/TorsionFree.v 记录了相同的数量，这只是对其的重新测量，而不是引用。该段的早期修订版本称在 [Grp] 中不存在 ℤ 群对象，这是因为一次扫描中只看到了战术模式 [Definition … : GrpObject.] 常量（[Grp_trivial]、[Z2]、[GalZ2]、[GrpTwo]），而遗漏了所有 [:= {| … |}]；审计发现了 [Int_Plus_Grp]，因此句子在此处已更正，而不是被删除。未交付。没有声称单生成元的自由群是最小分离子，也没有说 [Grp] 没有更小的分离子；没有关于生成两个或以上对象的族的说明；没有联合忠实性阅读（Structure/Generator.v 的 [JointlyFaithful]），这是 #447 的理论部分；也没有与 [Int_Plus_Grp] 的同构，如上所述。Instance/Grp/Free.v 的双生成元非退化结果未被使用，也没有关于分离的说明。
*)

(* * ** The element of a group as a map out of the singleton / * ** 群的元素作为从单元素集映射出的映射 *)

(*
 The constant map at [x], read into [Sets] through [Grp_Forget].  This
 is the transpose across the free/forgetful adjunction of the
 homomorphism that picks out [x].  Built by [refine] rather than as a
 [Program Definition] because under the universe annotation the
 respectfulness obligation is not discharged before the constant is
 registered, and the next proof's reference to it is then rejected with
 "The variable grp_point was not found in the current environment".
 It must also stay TRANSPARENT: closed with [Qed] instead, the
 separation proof stops at the [assert] of the generator equation,
 whose [exact (free_grp_extend_generators …)] is refused because the
 hypothesis has frozen as
 [f (grp_mul G (grp_unit G) (grp_point x ttt)) ≈ …] with nothing left
 to reduce (an earlier revision of this sentence placed the stop at the
 final [exact], which is never reached; measured on a full copy). 

 --------
 在 [x] 的常量映射，通过 [Grp_Forget] 读取到 [Sets]。这是自由/遗忘伴随下，取出 [x] 的同态的转置。由 [refine] 构建，而不是作为 [Program Definition]，因为在宇宙注释下，在注册常量之前，尊重性义务尚未解除，而下一次对它的证明引用则会被拒绝，并显示“当前环境中未找到变量 grp_point”。它还必须保持透明：如果改为用 [Qed] 关闭，分离证明将在生成器方程的 [assert] 停止，其 [exact (free_grp_extend_generators …)] 被拒绝，因为假设已经冻结为 [f (grp_mul G (grp_unit G) (grp_point x ttt)) ≈ …]，没有任何可缩减的内容（这个句子的早期修订版本将停止放在最后的 [exact]，但实际上从未到达；在完整副本上测量）。
*)
Definition grp_point@{o so+} {G : Grp@{so o}} (x : carrier G) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Grp_Forget G.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation / ** 分离 *)

Lemma Grp_free_one_separates@{o so+} :
  @IsSeparator Grp@{so o} (FreeGrpObject unit_setoid_object@{o o}).
Proof.
  intros G K f g Hk x.
  pose (e := @free_grp_extend unit_setoid_object@{o o} G (grp_point x)).
  pose proof (Hk e (fg_insert unit_setoid_object@{o o} ttt)) as E.
  simpl in E.
  assert (Ex : e (fg_insert unit_setoid_object@{o o} ttt) ≈ x)
    by exact (free_grp_extend_generators unit_setoid_object@{o o} G
                (grp_point x) ttt).
  rewrite <- (proper_morphism (grp_map f) _ _ Ex).
  rewrite <- (proper_morphism (grp_map g) _ _ Ex).
  exact E.
Qed.

(* Awodey's example as a one-object generating family. / 阿沃迪作为一个单对象生成族的例子。 *)
Definition Grp_Generator@{o so+} : Generator Grp@{so o} :=
  @Generator_of_separator Grp@{so o}
    (FreeGrpObject unit_setoid_object@{o o}) Grp_free_one_separates.
