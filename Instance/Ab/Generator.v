Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Structure.Generator.

Generalizable All Variables.

(*
 The free abelian group on one generator separates Ab

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/free+abelian+group

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.7, book p. 127 (PDF p. 136), Definition 4, gives two examples of a
 generating set: the one-point set for sets, and THE INTEGERS for
 abelian groups.  The second is this file's subject.  Awodey, “Category
 Theory” (1st ed., Carnegie Mellon pre-print, September 2005), §7.2,
 printed p. 154 (PDF p. 163), and Riehl, “Category Theory in Context”,
 2nd ed., Definition 4.7.7, printed p. 177 (PDF p. 197), are the
 single-object and family forms of the same definition.  The [Sets]
 witness is Instance/Sets/Generator.v and the [Grp] one
 Instance/Grp/Generator.v.

 WHAT IS PROVED, AND WHAT MAC LANE SAID.  Mac Lane's “the integers
 generate Ab” is, up to the standard isomorphism ℤ ≅ F_ab(1), the
 statement proved here: the free abelian group on a ONE-ELEMENT
 generating setoid separates [Ab].  The isomorphism itself is NOT in
 this tree and is not proved here, so the sentence “ℤ separates Ab” is
 not a theorem of this file.  The in-tree integers are
 [ab_int : AbObject] at Instance/Ab/Free.v (one of five names for
 [ring_ab Int_Ring]; Instance/Grp/Generator.v's header lists them with
 the measuring command), and that file's own measured negative
 records the related conversion fact — [FreeAbObject (Ab_Forget ab_int)]
 is not [ab_int] — while explicitly making no claim about isomorphism
 in either direction.  Supplying [FreeAbObject unit_setoid_object ≅
 ab_int] is left undone, and the reason is NOT a missing ℤ-action: the
 tree has [zsmul] (Instance/Ab/Monoidal.v), the ℤ-action on an
 arbitrary abelian group, with its additivity in the scalar
 [zsmul_add] and its compatibility with homomorphisms
 [zsmul_hom].  What is open is the isomorphism itself -- the
 map n ↦ n·(fa_gen ttt) out of [ab_int], the fold out of
 [FreeAbObject] sending the generator to 1, and the two inverse laws by
 induction on [FATerm] -- which is outside this issue's definition of
 done.  (An earlier revision of this paragraph said the tree had only
 the ℕ-scaled [nat_smul], which an audit refuted by reading
 the same file.)  So the honest reading of this file is: Mac Lane's
 example, with his ℤ replaced by the free-on-one-generator object that
 represents the same functor.

 THE PROOF IS ONE [exact], AND THE REASON IS A CONVERSION.  Compare
 Instance/Grp/Generator.v, which needs two [rewrite]s.  The difference
 is the strength at which the two donors state agreement on generators.
 Instance/Ab/Free.v's [free_ab_extend_generators] is an [Example]
 at Leibniz [=] — [cmon_map (free_ab_extend h) (fa_gen x) = h x
 := eq_refl] — because [free_ab_extend] is the fold [fa_eval]
 over the inductive [FATerm] and the generator clause IS the
 equation.  Instance/Grp/Free.v's [free_grp_extend_generators] is
 only at ≈, its extension being [fmap] of a functor whose value on a
 one-letter word comes from a [Qed]-opaque lemma.  Here, therefore, the
 hypothesis instantiated at [free_ab_extend (ab_point x)] and the
 generator [fa_gen ttt] IS the goal after conversion, with no transport
 by properness, and the [exact] closes it.

 NOT DELIVERED.  No claim that this object is the smallest separator of
 [Ab], nor that [Ab] has no other; no generating families of more than
 one object; no joint-faithfulness reading (Structure/Generator.v's
 [JointlyFaithful]), which is the theory half of #447; and no
 isomorphism with [ab_int], as above.  Nothing is said about [CMon],
 whose free objects Instance/Ab/Free.v does not build. 

 --------
 一个生成元上的自由阿贝尔群将 Ab 分开

 nLab: https://ncatlab.org/nlab/show/separator 
 nLab: https://ncatlab.org/nlab/show/free+abelian+group 

 Mac Lane，《为工作数学家准备的范畴论》，第二版（GTM 5），§V.7，书页127（PDF 页136），定义4，给出了两个生成集合的示例：集合的单点集，以及阿贝尔群的整数。第二个是本文件的主题。Awodey，《范畴论》（第一版，卡内基梅隆预印本，2005年9月），§7.2，印刷页154（PDF页163），以及 Riehl，《语境中的范畴论》，第二版，定义4.7.7，印刷页177（PDF页197），是同一定义的单对象和集合形式。[Sets] 的实例是 Instance/Sets/Generator.v，而 [Grp] 的实例是 Instance/Grp/Generator.v。什么是已证明的，以及麦克莱恩所说的。麦克莱恩的“整数生成 Ab”是，在标准同构 ℤ ≅ F_ab(1) 下，这里证明的陈述：一个单元素生成集合的自由阿贝尔群将 [Ab] 分离开来。同构本身不在这个树中，也未在此处证明，因此句子“ℤ 分离 Ab”不是该文件的定理。树中的整数是 Instance/Ab/Free.v 中的 [ab_int : AbObject]（[ring_ab Int_Ring] 的五个名字之一；Instance/Grp/Generator.v 的头部使用测量命令列出了它们），该文件自身测量的负记录了相关的转换事实——[FreeAbObject (Ab_Forget ab_int)] 不是 [ab_int]——同时明确不对任一方向的同构作出声明。提供 [FreeAbObject unit_setoid_object ≅ ab_int] 尚未完成，原因不是缺少 ℤ-作用：树中已有 [zsmul]（Instance/Ab/Monoidal.v）、任意阿贝尔群上的 ℤ-作用，以及其在标量 [zsmul_add] 上的可加性和与同态的兼容性 [zsmul_hom]。尚未完成的是同构本身——从 [ab_int] 映射 n ↦ n·(fa_gen ttt)，从 [FreeAbObject] 展开生成元映射到 1，以及通过对 [FATerm] 归纳证明的两个逆定律——这些都在该问题的完成定义之外。（这一段的早期修订版本说这棵树只有 ℕ 缩放的 [nat_smul]，而一次审计通过读取同一个文件否定了这一点。）所以对该文件的诚实解读是：Mac Lane 的例子，将他的 ℤ 替换为表示同一函子的单生成对象。证明是一个 [exact]，原因是一个转换。比较 Instance/Grp/Generator.v，它需要两个 [rewrite]。区别在于两个赋值在生成元上的一致性强度。Instance/Ab/Free.v 的 [free_ab_extend_generators] 是 Leibniz [=] 上的 [Example] — [cmon_map (free_ab_extend h) (fa_gen x) = h x := eq_refl] — 因为 [free_ab_extend] 是对归纳 [FATerm] 的 fold [fa_eval]，而生成元子句正是该方程。Instance/Grp/Free.v 的 [free_grp_extend_generators] 仅在 ≈ 上，其扩展是 [fmap]，这是一个函子的值，其对单字母词的取值来自一个 [Qed] 不透明引理。因此，这里在 [free_ab_extend (ab_point x)] 上实例化的假设和生成元 [fa_gen ttt] 在转换后就是目标，无需通过正当性传输，并且 [exact] 将其闭合。未送达。没有声称该对象是 [Ab] 的最小分隔器，也没有声称 [Ab] 没有其他对象；没有多于一个对象的生成族；没有联合忠实性解释（Structure/Generator.v 的 [JointlyFaithful]），这是 #447 的理论部分；也没有与上述 [ab_int] 的同构。未提及 [CMon]，其自由对象 Instance/Ab/Free.v 未构建。
*)

(* * ** The element of an abelian group as a map out of the singleton / * ** 阿贝尔群的元素作为从单元素集合到群的映射 *)

(*
 The constant map at [x], read into [Sets] through [Ab_Forget].  Built
 by [refine] for the same reason as Instance/Grp/Generator.v's
 [grp_point]: under the universe annotation the [Program] form does not
 register the constant before the obligation is met.  It must stay
 TRANSPARENT: closed with [Qed] the separation proof is refused with
 “The term ”Hk (free_ab_extend (ab_point x)) (fa_gen ttt)“ has type
 ”(f ∘ free_ab_extend (ab_point x)) (fa_gen ttt) ≈ …“ while it is
 expected to have type ”f x ≈ g x“”, a CONVERSION refusal. 

 --------
 在 [x] 的常量映射，通过 [Ab_Forget] 读入 [Sets]。由 [refine] 构建，原因与 Instance/Grp/Generator.v 的 [grp_point] 相同：在宇宙注解下，[Program] 形式在义务满足之前不会注册该常量。它必须保持 TRANSPARENT：使用 [Qed] 关闭，分离证明被拒绝，提示“项 'Hk (free_ab_extend (ab_point x)) (fa_gen ttt)' 的类型为 '(f ∘ free_ab_extend (ab_point x)) (fa_gen ttt) ≈ …'，而期望类型为 'f x ≈ g x'”，属于 CONVERSION 拒绝。
*)
Definition ab_point@{o so+} {A : Ab@{so o}} (x : carrier (cmon_setoid A)) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> Ab_Forget A.
Proof. unshelve refine {| morphism := fun _ => x |}; proper. Defined.

(** ** The separation / ** 分离 *)

Lemma Ab_free_one_separates@{o so+} :
  @IsSeparator Ab@{so o} (FreeAbObject unit_setoid_object@{o o}).
Proof.
  intros A B f g Hk x.
  exact (Hk (@free_ab_extend unit_setoid_object@{o o} A (ab_point x))
           (@fa_gen unit_setoid_object@{o o} ttt)).
Qed.

(* Mac Lane's second example as a one-object generating family. / Mac Lane 的第二个例子作为一个一对象生成族。 *)
Definition Ab_Generator@{o so+} : Generator Ab@{so o} :=
  @Generator_of_separator Ab@{so o}
    (FreeAbObject unit_setoid_object@{o o}) Ab_free_one_separates.
