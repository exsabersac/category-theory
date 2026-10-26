Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Kernel.Universal.
(* Last, matching Theory/Algebra/Rig.v's own placement of this import: after Category.Lib and after the [Sets]/[CMon] layer. / 最后，匹配 Theory/Algebra/Rig.v 自身对该导入的放置：在 Category.Lib 之后，以及在 [Sets] / [CMon] 层之后。 *)
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* * * Witnesses for kernels as universal elements / * * 作为普遍元素的内核的证据 *)

(*
 Companion to Structure/Kernel/Universal.v.  Two witnesses, one positive
 and one negative, and they are the two halves of the same point.

 POSITIVE.  [Instance/Ab.v] already builds the kernel of a homomorphism
 of abelian groups as a SUB-SETOID -- [AbKernel f], with its inclusion
 [ab_kernel_incl f] -- and uses it as the probe object for the monic
 half of Mac Lane's §I.7 proposition.  What it never states is that this
 object IS a kernel in the categorical sense, i.e. that it satisfies
 [Structure/Kernel.v]'s [IsKernel].  [ab_kernel_IsKernel] supplies that,
 and with it the whole apparatus of the companion file lands on a
 concrete algebraic category: the kill-f presheaf of a homomorphism of
 abelian groups is representable, and its representing object is the
 subgroup of elements killed by f.

 (This corrects the issue's own “Current state”, which says that none of
 the remark's concrete algebraic categories exists in tree to
 instantiate the result.  All four do -- Instance/Ab.v, Instance/Grp.v,
 Instance/Rng.v, Instance/Mod.v -- and Ab and RMod already carry
 concrete kernel OBJECTS.  What was genuinely missing is the universal
 property of those objects, which is supplied here.)

 The witness is proved non-degenerate rather than asserted to be so.
 [Ab_Z2] is Z/2 on [bool] under exclusive-or, [ab_parity] the parity
 homomorphism Z ⟶ Z/2, and its kernel is the even integers: a PROPER,
 NONTRIVIAL subgroup -- [ab_parity_kernel_has_two] exhibits two distinct
 elements of it and [ab_parity_kernel_proper] shows 1 is not one of
 them.  So neither the presheaf nor its representing object is a
 singleton, and the universal-element clause is not vacuously satisfied.
 The mediator computes: [ab_parity_med_computes] evaluates the unique
 factorization of the doubling map at 3 and gets 6, by [eq_refl].

 NEGATIVE.  [Rng_no_zero_morphisms] proves that Mac Lane's Rng -- unital
 rings, unit-preserving homomorphisms -- has NO zero-morphism family
 at all, hence no zero object, hence no kernels in the sense of
 Structure/Kernel.v.  The argument needs nothing about zero morphisms
 specifically: the terminal ring is the zero ring, in which 1 ≈ 0, and a
 homomorphism out of it into Z would carry that equation to 1 = 0 in Z.
 So the hom-set Rng(0-ring, Z) is EMPTY, and in particular contains no
 distinguished morphism.

 That is what makes the companion file's [ForkPresheaf] a necessity
 rather than a generalization for its own sake: over Rng the kill-f
 presheaf cannot even be written down, while the fork presheaf of a
 parallel pair can, and [equalizer_universal_element_iso] applies to it
 unchanged.  [Rng_fork_presheaf] records that the presheaf is formable
 at Rng, which is the whole content of the “survives without a zero
 object” clause.

 A UNIVERSE NOTE, since it dictates the shape of everything below.
 [Ab_Zero@{u}] carries ONE universe parameter where [Ab@{u u0}] carries
 two: it pins the second to [Set].  Inside a [Section], a
 [Context {A B : AbObject}] fixes that second universe rigidly before
 [Ab_Zero] is ever mentioned, and the later mention is then rejected
 (“Cannot enforce Set = ...”, measured).  Every definition below is
 therefore stated at TOP LEVEL with its own [{A B : AbObject} (f)]
 binders, so that the objects' universes and [Ab_Zero]'s are unified in
 one elaboration.  This is a restriction inherited from Instance/Ab.v,
 not one introduced here, and nothing below shows it unavoidable. 

 --------
 结构/核/通用.v的伴随。两个证人，一个是肯定的，一个是否定的，它们是同一点的两个部分。

 肯定的。[Instance/Ab.v] 已经将阿贝尔群同态的核构建为一个子子集（SUB-SETOID）——[AbKernel f]，以及它的包含 [ab_kernel_incl f]——并将其用作 Mac Lane §I.7 命题单射部分的探针对象。它从未声明的是，该对象在范畴意义上确实是一个核，即它满足 [Structure/Kernel.v] 的 [IsKernel]。[ab_kernel_IsKernel] 提供了这一点，并且借助它，伴随文件的整个装置落在了一个具体的代数范畴上：阿贝尔群同态的 kill-f 预层是可表示的，其表示对象是被 f 消掉的元素的子群。（这修正了问题自身的“当前状态”，它表示树中不存在任何可用于实例化结果的该备注的具体代数类别。实际上四个类别都存在——Instance/Ab.v、Instance/Grp.v、Instance/Rng.v、Instance/Mod.v——并且 Ab 和 RMod 已经包含具体的核对象。真正缺失的是这些对象的泛性质，而这里提供了这一点。）该证据被证明为非退化，而不是被声称为非退化。
 [Ab_Z2] 是 [bool] 上的 Z/2，运算为异或，[ab_parity] 是奇偶同态 Z ⟶ Z/2，其核为偶数：一个适当的、非平凡的子群——[ab_parity_kernel_has_two] 显示了其两个不同元素，而 [ab_parity_kernel_proper] 显示 1 不是其中之一。因此，无论是预层还是它的表示对象都不是单例，且普遍元素条款不是空洞地满足的。调解者计算：[ab_parity_med_computes] 在 3 处评估加倍映射的唯一分解并得到 6，依据 [eq_refl]。否定。[Rng_no_zero_morphisms] 证明了 Mac Lane 的 Rng——含单位环、保持单位的同态——完全没有零态射族，因此没有零对象，因此在 Structure/Kernel.v 的意义下没有核。这个论证并不特别依赖零态射：终环是零环，其中 1 ≈ 0，而从它到 Z 的同态会把这个等式映射为 Z 中的 1 = 0。所以同态集 Rng(0-环, Z) 是空的，特别是其中没有特殊的态射。这就是使伴随文件的 [ForkPresheaf] 成为必要而非为了自身泛化的原因：在 Rng 上，kill-f presheaf 甚至无法写出，而平行对的 fork presheaf 可以写出，并且 [equalizer_universal_element_iso] 对其不变地适用。[Rng_fork_presheaf] 记录了该 presheaf 可以在 Rng 上形成，这就是“在没有零对象的情况下依然存在”条款的全部内容。一个宇宙注释，因为它决定了下面一切的形状。
 [Ab_Zero@{u}] 携带一个宇宙参数，而 [Ab@{u u0}] 携带两个：它将第二个固定到 [Set]。在 [Section] 内部，[Context {A B : AbObject}] 在 [Ab_Zero] 被提到之前就刚性地固定了第二个宇宙，然后后来的提及会被拒绝（“无法强制执行 Set = ...”，已测量）。因此，下面的每个定义都是在顶层陈述的，并带有它自己 [{A B : AbObject} (f)] 的绑定器，以便对象的宇宙与 [Ab_Zero] 的统一在一个展开中完成。这是从 Instance/Ab.v 继承下来的限制，并不是这里引入的，下面没有任何内容显示它是不可避免的。
*)

(*
 WHAT IS DELIVERED

 * [ab_kernel_IsKernel] : [IsKernel f (ab_kernel_incl f)] for every
 homomorphism f of abelian groups -- new; Instance/Ab.v builds the
 object and the inclusion but proves no universal property of them.

 * [ab_kernel_aue], [ab_kernel_Representable], [ab_kernel_representation]:
 the companion file's constructions at [Ab], with the representing
 object and the universal element read back by [eq_refl].

 * [Ab_Z2], [ab_parity], and the non-degeneracy facts listed above.

 * [Rng_no_hom_zero_to_Z], [Rng_no_zero_morphisms], [Rng_no_zero_object],
 [Rng_fork_presheaf], [Rng_equalizer_aue] and [Rng_aue_equalizer].

 WHAT IS NOT DELIVERED

 * NO [HasKernels Ab] INSTANCE.  [ab_kernel_IsKernel] gives the kernel
 of each morphism separately, which is what [kernel_aue] consumes;
 bundling them into the class would add nothing to this file's point.

 * NO CLAIM ABOUT Grp, Rng or RMod BEYOND THE ABOVE.  Instance/Grp.v
 and Instance/Mod.v carry kernel objects too and the same proof shape
 would work there; it is not run here.

 * NO EQUALIZER WITNESS IN Rng.  [Rng_fork_presheaf] shows the presheaf
 is formable; whether Rng has equalizers is not addressed, and no
 universal element of that presheaf is exhibited.

 * NO CLAIM THAT [Ab_Z2] IS NEW.  Z/2 exists in tree several times over
 (Instance/Grp.v's [Z2], Construction/Deloop.v's [Bool_Xor_Grp]); none
 of them is an [AbObject], and converting would cost more than the
 six-line record below. 

 --------
 交付内容

 * [ab_kernel_IsKernel] : [IsKernel f (ab_kernel_incl f)] 对于每个阿贝尔群的同态 f -- 新增；Instance/Ab.v 构建了该对象和包含，但未证明它们的任何泛性质。

 * [ab_kernel_aue], [ab_kernel_Representable], [ab_kernel_representation] : 伴随文件在 [Ab] 的构造，具有由 [eq_refl] 读取的表示对象和泛元素。

 * [Ab_Z2], [ab_parity] 以及上述列出的非退化性事实。

 * [Rng_no_hom_zero_to_Z], [Rng_no_zero_morphisms], [Rng_no_zero_object], [Rng_fork_presheaf], [Rng_equalizer_aue] 和 [Rng_aue_equalizer]。

 未交付内容

 * 没有 [HasKernels Ab] 实例。[ab_kernel_IsKernel] 单独给出了每个态射的核，这是 [kernel_aue] 所使用的；将它们捆绑到类中不会为该文件增加任何内容。* 除了上述内容，关于 Grp、Rng 或 RMod 没有其他声明。Instance/Grp.v 和 Instance/Mod.v 也包含内核对象，相同的证明形式也适用；但这里并未运行。

 * 在 Rng 中没有等化器的证据。[Rng_fork_presheaf] 表明预层可以形成；是否 Rng 有等化器未被讨论，也未展示该预层的任何普遍元素。

 * 没有声明 [Ab_Z2] 是新的。在树中 Z/2 已经多次存在（Instance/Grp.v 的 [Z2]，Construction/Deloop.v 的 [Bool_Xor_Grp]）；它们都不是 [AbObject]，而转换会花费比下面六行记录更多的代价。
*)

(** ** Ab: [AbKernel] is a kernel / ** Ab: [AbKernel] 是一个内核 *)

(*
 The zero morphism of [Ab] evaluates to the zero element, by conversion:
 [Ab_Zero]'s coincidence isomorphism is [iso_id] (the chosen initial and
 terminal objects are literally the same term), so the tunnel through
 the zero object collapses with no rewriting. 

 --------
 [Ab] 的零态射通过转换求值为零元素：[Ab_Zero] 的重合同构是 [iso_id]（所选的初始对象和终端对象字面上是相同的项），因此通过零对象的通道在没有重写的情况下坍塌。
*)
Lemma ab_zero_mor_apply {X Y : AbObject} (a : carrier (cmon_setoid X)) :
  cmon_map (@zero_mor Ab Ab_Zero X Y) a = cmon_zero Y.
Proof. reflexivity. Qed.

(*
 The descent map: a homomorphism killed by f lands in the kernel, and
 the corestriction is a homomorphism because the kernel's zero and
 addition are those of A read on first projections.

 The hypothesis is stated ELEMENTWISE rather than as
 [f ∘ h ≈ zero_mor], for the universe reason in the header;
 [ab_kernel_IsKernel] feeds it from the [IsKernel] fork hypothesis,
 where the zero object is inferred once. 

 --------
 下降映射：被 f 消去的同态映射落在核中，而上核映射是同态映射，因为核为零，并且加法是 A 在第一投影上的加法。

 假设是按元素声明的，而不是以 [f ∘ h ≈ zero_mor] 形式，因为标题中的宇宙原因；[ab_kernel_IsKernel] 从 [IsKernel] 分支假设中提供它，其中零对象只推断一次。
*)
Program Definition ab_kernel_med {A B : AbObject} (f : A ~{Ab}~> B)
  {Z0 : AbObject} (h : Z0 ~{Ab}~> A)
  (Hh : ∀ a : carrier (cmon_setoid Z0), cmon_map f (cmon_map h a) ≈ cmon_zero B)
  : Z0 ~{Ab}~> AbKernel f :=
  {| cmon_map := {| morphism := fun a => (cmon_map h a; Hh a) |} |}.
Next Obligation. proper; simpl; now rewrite X. Qed.
Next Obligation. simpl; apply (cmon_map_zero h). Qed.
Next Obligation. simpl; apply (cmon_map_plus h). Qed.

(*
 [AbKernel f] with [ab_kernel_incl f] satisfies Structure/Kernel.v's
 [IsKernel].  The fork equation is the kernel elements' own defining
 property (the second projection); descent is [ab_kernel_med]; and
 uniqueness holds because the kernel's setoid compares first
 projections, which is exactly what the inclusion returns. 

 --------
 [AbKernel f] 与 [ab_kernel_incl f] 满足 Structure/Kernel.v 的 [IsKernel]。叉方程是核元素自身的定义性质（第二投影）；降下是 [ab_kernel_med]；并且唯一性成立，因为核的集合态比较第一投影，这正是包含所返回的。
*)
Definition ab_kernel_IsKernel {A B : AbObject} (f : A ~{Ab}~> B)
  : IsKernel f (ab_kernel_incl f).
Proof.
  unshelve econstructor.
  - (* f ∘ i ≈ zero_mor ∘ i, pointwise on kernel elements / f ∘ i ≈ zero_mor ∘ i，在核元素上逐点 *)
    intro p; simpl.
    exact (`2 p).
  - (* descent *)
    intros Z0 h Hh.
    unshelve econstructor.
    + exact (ab_kernel_med f h (fun a => Hh a)).
    + intro a; reflexivity.
    + intros v Hv a; simpl.
      symmetry; exact (Hv a).
Defined.

(* * ** ... hence a universal element of the kill-f presheaf / * ** ... 因此是 kill-f 预层的一个通用元 *)

Definition ab_kernel_aue {A B : AbObject} (f : A ~{Ab}~> B)
  : AUniversalElement
      (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
      (AbKernel f) :=
  kernel_universal_element f (ab_kernel_IsKernel f).

Definition ab_kernel_Representable {A B : AbObject} (f : A ~{Ab}~> B)
  : Representable (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
  := kernel_representable f (ab_kernel_IsKernel f).

Definition ab_kernel_representation {A B : AbObject} (f : A ~{Ab}~> B)
  : @Curried_Hom (Ab^op) (AbKernel f)
      ≅[[Ab^op, Sets]]
    (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
  := kernel_representation f (ab_kernel_IsKernel f).

(* The representing object is the kernel group, on the nose. / 所代表的对象是内核组，正中目标。 *)
Corollary ab_kernel_repr_obj {A B : AbObject} (f : A ~{Ab}~> B) :
  @repr_obj (Ab^op)
    (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
    (ab_kernel_Representable f)
  = AbKernel f.
Proof. reflexivity. Qed.

(* ... and the universal element is the inclusion, on the nose. / ... 而普遍的元素正是包含本身，恰到好处。 *)
Corollary ab_kernel_aue_elem {A B : AbObject} (f : A ~{Ab}~> B) :
  `1 (@aue_elem (Ab^op)
        (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
        (AbKernel f) (ab_kernel_aue f))
  = ab_kernel_incl f.
Proof. reflexivity. Qed.

(*
 The equivalence itself, in the universe-free form: the passage back, and
 the two round trips.  The bundled [kernel_universal_element_iso] is NOT
 available here -- [Ab] puts its objects strictly above its homs, which
 that packaging forbids (documented at its definition, pinned in
 Test/ProbeKernelUniversal.v) -- so these three, together with
 [ab_kernel_representation] above, are what “equivalent” means at [Ab]. 

 --------
 等价本身，在无宇宙形式下：返回的通道，以及两次往返。捆绑的 [kernel_universal_element_iso] 在这里不可用——[Ab] 将其对象严格置于其 Hom 之上，而该包装禁止这样做（在其定义中有记录，固定在 Test/ProbeKernelUniversal.v 中）——因此这三者，再加上上面的 [ab_kernel_representation]，就是在 [Ab] 中“等价”的含义。
*)
Definition ab_aue_kernel {A B : AbObject} (f : A ~{Ab}~> B)
  (U : AUniversalElement
         (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
         (AbKernel f))
  : @IsKernelOf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f (AbKernel f)
      (`1 (@aue_elem (Ab^op)
             (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
             (AbKernel f) U))
  := aue_kernel f U.

(*
 The round trip on the kernel side, at [Ab].  Stated by instantiation
 rather than by re-typing the conclusion: writing the [∃!] out by hand
 leaves the hom-setoid instance of [z ~{Ab}~> AbKernel f] unresolved
 (“expected to have type ∃! y, ?P y”, measured), while the general
 lemma's own statement carries it. 

 --------
 在内核端的往返，在 [Ab]。通过实例化而不是重新输入结论来说明：手动写出 [∃!] 会使 [z ~{Ab}~> AbKernel f] 的同构集合实例未解决（“预期类型为 ∃! y, ?P y”，已测量），而一般引理自身的陈述中包含了它。
*)
Definition ab_kernel_round {A B : AbObject} (f : A ~{Ab}~> B)
  {z : AbObject} (h : z ~{Ab}~> A)
  := kernel_round_mediator f (ab_kernel_IsKernel f) h.

(* ... and on the universal-element side. / ... 以及在通用元素方面。 *)
Definition ab_aue_kernel_round {A B : AbObject} (f : A ~{Ab}~> B)
  (U : AUniversalElement
         (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f)
         (AbKernel f))
  := aue_kernel_round_mediator f U.

(* * ** A non-degenerate instance: the even integers inside Z / * ** 非简并实例：Z 中的偶整数 *)

(*
 Z/2 as an abelian group on [bool] under exclusive-or.  Negation is the
 identity, since every element is its own inverse. 

 --------
 Z/2 作为一个在 [bool] 上按异或运算的阿贝尔群。取反是恒等运算，因为每个元素都是它本身的逆元。
*)
Definition Ab_Z2 : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := {| cmon_setoid := {| carrier := bool
                                  ; is_setoid := eq_Setoid bool |}
                ; cmon_zero := false
                ; cmon_plus := xorb
                (* the carrier's `≈` IS [eq], already a [Prop] / 运营商的 `≈` 是 [eq]，已经是 [Prop] *)
                ; cmon_prop := eq_PropEquiv bool |};
    ab_neg := fun b => b
  |}.
  - (* cmon_plus_respects / cmon_plus_respects *) repeat intro; simpl in *; subst; reflexivity.
  - (* cmon_plus_assoc / cmon_plus_assoc *)   intros a b c; now destruct a, b, c.
  - (* cmon_plus_comm / cmon_plus_comm *)    intros a b; now destruct a, b.
  - (* cmon_plus_zero_l / cmon_plus_zero_l *)  intros a; now destruct a.
  - (* ab_neg_respects / AB 阴性尊重 *)   repeat intro; simpl in *; subst; reflexivity.
  - (* ab_neg_left / AB阴性左 *)       intros a; now destruct a.
Defined.

(* Z as an abelian group, through the ring layer of Instance/Rng.v. / 作为阿贝尔群的 Z，通过 Instance/Rng.v 的环层。 *)
Definition Ab_Z : AbObject := ring_ab Int_Ring.

(* The parity homomorphism. Additivity is [Z.odd_add]. / 奇偶同态。可加性是 [Z.odd_add] 。 *)
Program Definition ab_parity : Ab_Z ~{Ab}~> Ab_Z2 :=
  {| cmon_map := {| morphism := Z.odd |} |}.
Next Obligation. apply Z.odd_add. Qed.

(* Its kernel is the even integers. Membership is decidable and computes: both witnesses below are [eq_refl] on the underlying booleans. / 它的核心是偶数。成员资格是可判定的，并计算：下面的两个证人都是在基础布尔值上的 [eq_refl]。 *)
Definition ab_even (n : Z) (H : Z.odd n = false)
  : carrier (cmon_setoid (AbKernel ab_parity)) := (n; H).

Definition ab_even_0 : carrier (cmon_setoid (AbKernel ab_parity)) :=
  ab_even 0%Z eq_refl.
Definition ab_even_2 : carrier (cmon_setoid (AbKernel ab_parity)) :=
  ab_even 2%Z eq_refl.

(*
 NONTRIVIAL: the kernel has at least two distinct elements, so it is not
 the zero group and the kill-f presheaf is not the constant singleton. 

 --------
 非平凡：核至少有两个不同的元素，所以它不是零群，并且 kill-f 预层不是常数单元素。
*)
Lemma ab_parity_kernel_has_two : (ab_even_0 ≈ ab_even_2) → False.
Proof. simpl; unfold Z_eqT; discriminate. Qed.

(*
 PROPER: 1 is not in it, so the kernel is not all of Z either and the
 inclusion is not an isomorphism. 

 --------
 正确：1不在其中，所以核也不是整个Z，并且包含不是同构。
*)
Lemma ab_parity_kernel_proper : Z.odd 1%Z = false → False.
Proof. discriminate. Qed.

(* Doubling, a map killed by parity, to exercise the descent clause. / 翻倍，由奇偶性终止的牌局，用于行使降级条款。 *)
Program Definition ab_double : Ab_Z ~{Ab}~> Ab_Z :=
  {| cmon_map := {| morphism := Z.mul 2 |} |}.
(*
 [change] first: the obligation tactic has already pushed [Z.mul 2]
 through [simpl] into its [match] form, which no [Z] lemma matches. 

 --------
 [change] 首先：义务策略已经将 [Z.mul 2] 通过 [simpl] 推入其 [match] 形式，没有 [Z] 引理与之匹配。
*)
Next Obligation.
  unfold Z_eqT.
  change ((2 * (a + b))%Z = (2 * a + 2 * b)%Z).
  apply Z.mul_add_distr_l.
Qed.

Lemma ab_double_killed :
  ab_parity ∘ ab_double ≈ @zero_mor Ab Ab_Zero Ab_Z Ab_Z2.
Proof.
  intro n; simpl.
  change (Z.odd (2 * n)%Z = false).
  now rewrite Z.odd_mul.
Qed.

(* THE MEDIATOR COMPUTES. The unique factorization of [ab_double] through the kernel of [ab_parity], evaluated at 3, is 6 -- by [eq_refl] on the underlying integer, with no reduction hint. / 调解者计算。[ab_double] 通过 [ab_parity] 的核的唯一分解，在 3 点处求值为 6 —— 对底层整数使用 [eq_refl]，没有简化提示。 *)
Definition ab_parity_med : Ab_Z ~{Ab}~> AbKernel ab_parity :=
  unique_obj (eq_desc (ab_kernel_IsKernel ab_parity) ab_double
                (fun n => ab_double_killed n)).

Example ab_parity_med_computes :
  `1 (cmon_map ab_parity_med 3%Z) = 6%Z.
Proof. reflexivity. Qed.

(*
 ... and it is the factorization: composing with the inclusion returns
 the doubling map. 

 --------
 ... 它是分解：与包含组合后返回倍增映射。
*)
Example ab_parity_med_factors :
  ab_kernel_incl ab_parity ∘ ab_parity_med ≈ ab_double.
Proof.
  exact (unique_property (eq_desc (ab_kernel_IsKernel ab_parity) ab_double
                            (fun n => ab_double_killed n))).
Qed.

(* The universal element of the kill-parity presheaf, named. / 杀宿预层的通用元素，已命名。 *)
Definition ab_parity_universal_element
  : AUniversalElement
      (@KillPresheaf Ab (ZeroMorphisms_of_ZeroObject Ab_Zero) Ab_Z Ab_Z2 ab_parity)
      (AbKernel ab_parity)
  := ab_kernel_aue ab_parity.

(** ** Rng: no zero morphisms at all / ** Rng：完全没有零态射 *)

(*
 A ring homomorphism preserves 1 and 0.  In the zero ring these coincide,
 so any homomorphism out of it into Z would give 1 = 0 there.  No appeal
 to zero morphisms is made: this shows the HOM-SET is empty. 

 --------
 环同态保持 1 和 0。在零环中，它们重合，因此从零环到整数环 Z 的任何同态都会使 1 = 0 成立。不涉及零态射：这表明同态集是空的。
*)
Lemma Rng_no_hom_zero_to_Z (u : Zero_Ring ~{Rng}~> Int_Ring) : False.
Proof.
  pose proof (rig_map_one u) as H1.
  pose proof (rig_map_zero u) as H0.
  (* [rig_one Zero_Ring] and [rig_zero Zero_Ring] are the same term [ttt], so the two conclusions are about the same integer. / [rig_one Zero_Ring] 和 [rig_zero Zero_Ring] 与 [ttt] 是相同的项，因此这两个结论是关于同一个整数的。 *)
  simpl in H1, H0.
  unfold Z_eqT in H1, H0.
  rewrite H1 in H0.
  discriminate.
Qed.

(*
 Hence Rng carries no zero-morphism family: one would in particular
 supply a morphism from the zero ring to Z. 

 --------
 因此，Rng 不包含零态射族：特别是，人们会提供一个从零环到 Z 的态射。
*)
Theorem Rng_no_zero_morphisms : ZeroMorphisms Rng → False.
Proof.
  intro ZM.
  exact (Rng_no_hom_zero_to_Z (@zmor Rng ZM Zero_Ring Int_Ring)).
Qed.

(* ... and a fortiori no zero object, since a zero object supplies one. / ... 更不必说零对象，因为零对象提供了一个。 *)
Theorem Rng_no_zero_object : @ZeroObject Rng → False.
Proof.
  intro Z.
  exact (Rng_no_zero_morphisms (ZeroMorphisms_of_ZeroObject Z)).
Qed.

(*
 What DOES survive: the fork presheaf of a parallel pair, which needs no
 structure on the category whatever.  This is the “survives in categories
 without a zero object” clause, exhibited at the category that motivates
 it. 

 --------
 真正存活的是：平行对的叉预层，它不需要范畴上的任何结构。这就是“在没有零对象的范畴中仍然存活”的条款，在启发它的范畴中体现出来。
*)
Definition Rng_fork_presheaf {R S : Rng} (u v : R ~{Rng}~> S)
  : Rng^op ⟶ Sets := ForkPresheaf u v.

(*
 ... and the passage: an equalizer in Rng is a universal element of it.
 The UNIVERSE-FREE form is used here deliberately -- the bundled
 [equalizer_universal_element_iso] does not instantiate at [Rng], for the
 reason documented at its definition and pinned in
 Test/ProbeKernelUniversal.v. 

 --------
 ... 和这一段：在 Rng 中的一个均衡器是它的一个通用元素。
 这里故意使用了无宇宙形式 —— 捆绑的
 [equalizer_universal_element_iso] 并未在 [Rng] 实例化，
 原因在其定义中已有记录，并在
 Test/ProbeKernelUniversal.v 中固定。
*)
Definition Rng_equalizer_aue {R S : Rng} (u v : R ~{Rng}~> S) {k : Rng}
  {i : k ~> R} (E : IsEqualizer u v k i)
  : AUniversalElement (ForkPresheaf u v) k
  := equalizer_aue u v E.

Definition Rng_aue_equalizer {R S : Rng} (u v : R ~{Rng}~> S) {k : Rng}
  (U : AUniversalElement (ForkPresheaf u v) k)
  : IsEqualizer u v k (`1 (@aue_elem (Rng^op) (ForkPresheaf u v) k U))
  := aue_equalizer u v U.
