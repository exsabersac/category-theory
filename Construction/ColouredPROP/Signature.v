Require Import Category.Lib.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Signatures over coloured PROPs / * 彩色道具上的签名 *)

(*
 nLab:      https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 A COLOURED SIGNATURE is the data of a many-sorted symmetric monoidal
 theory: a family of typed generators indexed by their input/output
 boundary.  Where a one-sorted PROP signature ([Construction/PROP/
 Signature.v]) indexes generators by a pair of natural numbers — how
 MANY wires enter and leave — a coloured signature over a set
 [Colour] of wire types indexes them by pairs of LISTS of colours:
 which wire types enter, in which order, and which leave.  It is a
 family of types indexed by pairs of colour words — an object of
 [Set^(W x W)] (here in [Type]) where [W := list Colour] is the free
 monoid of finite words over [Colour] — the underlying object of the
 free-coloured-PROP adjunction.

 Concretely [Sig cs ds] is the [Type] of generator names whose input
 boundary is the colour list [cs] and whose output boundary is [ds].
 In examples:

 - The empty signature [Empty_CSig] presents a coloured PROP with
 NO non-structural generators: its free coloured PROP has as
 morphisms exactly the structural rearrangements (identities,
 composites, tensors, braids), i.e. colour-preserving
 permutations of wires.
 - A typed circuit signature over [Colour := {wire; clk}] might
 have a generator in [Sig [wire; wire] [wire]] (a join that
 needs two data wires), one in [Sig [clk; wire] [wire]] (a
 latch), one in [Sig [] [clk]] (a clock source), etc.  The
 colour discipline makes ill-typed pluggings unrepresentable.

 The signature is the INPUT to the free construction: given [S],
 the free coloured PROP on [S] is the strict symmetric monoidal
 category whose morphisms are [S]-labelled typed string diagrams
 modulo the strict-SMC axioms.  This file defines the signatures,
 the raw [CTerm] syntax, and smart constructors; the equational
 theory lives in [Construction/ColouredPROP/TermEq.v] and the free
 category in [Construction/ColouredPROP/Free.v]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/PROP 
 维基百科：  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 彩色符号（COLOURED SIGNATURE）是一个多排序对称单体理论的数据：一族类型化生成元，由其输入/输出边界索引。当一个单排序的PROP符号（[Construction/PROP/Signature.v]）通过一对自然数索引生成元——有多少条线进入和离开——一个位于集合 [Colour] 上的彩色符号则通过颜色列表对索引它们：哪些线的类型进入，顺序如何，以及哪些离开。这是一族由颜色词对索引的类型——是 [Set^(W x W)] 的一个对象（此处在 [Type] 中），其中 [W := list Colour] 是 [Colour] 上有限词的自由单体——自由彩色PROP伴随的基础对象。具体来说，[Sig cs ds] 是生成器名称的 [Type]，其输入边界是颜色列表 [cs]，输出边界是 [ds]。
 在例子中：

 - 空签名 [Empty_CSig] 表示一个有色 PROP，没有非结构生成器：其自由有色 PROP 的态射正好是结构性重排（恒等、复合、张量、编织），即保持颜色的不变的线排列。
 - 在 [Colour := {wire; clk}] 上的类型电路签名可能有一个生成器在 [Sig [wire; wire] [wire]]（一个需要两条数据线的连接），一个在 [Sig [clk; wire] [wire]]（一个锁存器），一个在 [Sig [] [clk]]（一个时钟源），等等。颜色规则使得不正确类型的插入不可表示。签名是自由构造的输入：给定 [S]，自由着色 PROP 在 [S] 上是严格对称单体范畴，其态射是 [S] 标签的类型化字符串图，模严格-SMC 公理。此文件定义了签名、原始的 [CTerm] 语法以及智能构造器；等式理论存在于 [Construction/ColouredPROP/TermEq.v]，自由范畴存在于 [Construction/ColouredPROP/Free.v]。
*)

Section CSignature.

Context (Colour : Type).

Definition CSignature : Type := list Colour -> list Colour -> Type.

(** ** Examples / ** 示例 *)

(*
   * The empty signature.  Useful as a base case: the free coloured
   PROP on [Empty_CSig] is the coloured permutation category. 

   --------
   * 空签名。作为基础情况很有用：在 [Empty_CSig] 上的自由有色 PROP 是有色排列范畴。
*)
Definition Empty_CSig : CSignature :=
  fun _ _ => Empty_set.

(*
   * The signature of a single generator [g : ms -> ns] (with input
   boundary [ms] and output boundary [ns]), and no other generators.

   Deviation from the one-sorted donor: [Single_Sig] tested arities
   with [Nat.eqb], which presumes decidable equality.  Colour lists
   over an arbitrary [Colour : Type] have no such test, so the
   coloured form is PROOF-CARRYING instead: an inhabitant of
   [Single_CSig ms ns xs ys] is a pair of equality proofs, with
   canonical inhabitant [(eq_refl, eq_refl)] at boundary [(ms, ns)].
   This is decidability-free and definitionally empty nowhere — it
   is provably empty exactly off the diagonal. 

   --------
   * 单个生成元 [g : ms -> ns] 的签名（输入边界为 [ms]，输出边界为 [ns]），没有其他生成元。

   偏离单类型供体：[Single_Sig] 测试了 [Nat.eqb] 的元数，假设可判定的相等性。任意 [Colour : Type] 上的颜色列表没有这样的测试，因此彩色形式是 PROOF-CARRYING 的：[Single_CSig ms ns xs ys] 的一个元素是一个等式证明对，在边界 [(ms, ns)] 上的规范元素为 [(eq_refl, eq_refl)]。它不依赖可判定性，并且在定义上没有空值——它在对角线之外被证明为空。
*)
Definition Single_CSig (ms ns : list Colour) : CSignature :=
  fun xs ys => ((xs = ms) * (ys = ns))%type.

(*
   * ** Operations on signatures

   Sum (disjoint union) of two signatures: a generator is a generator
   of one or the other.  This builds complex signatures from smaller
   ones — e.g. a typed monoid-and-comonoid signature is the sum of
   the two single-generator families. 

   --------
   * ** 签名的操作

   两个签名的和（不相交并）：一个生成器是其中一个生成器。
   这从较小的签名构建复杂签名 — 例如，一个类型化的幺半群与余半群签名是两个单生成器族的和。
*)
Definition Sum_CSig (S T : CSignature) : CSignature :=
  fun cs ds => (S cs ds + T cs ds)%type.

(*
   * Sub-signature: a boundary-preserving family of generator
   relabellings into another signature — despite the name, no
   injectivity is required (generator collapses are allowed).
   Inhabited by [inl] / [inr] / nested projection chains. 

   --------
   * 子签名：一种保持边界的生成器重标记族，可映射到另一个签名 — 尽管名称如此，不要求单射性（生成器坍塌是允许的）。
   包含 [inl] / [inr] / 嵌套投影链。
*)
Definition CSubSig (Sub Sup : CSignature) : Type :=
  forall cs ds, Sub cs ds -> Sup cs ds.

(** The identity sub-signature. / 身份子签名。 *)
Definition CSubSig_id (S : CSignature) : CSubSig S S :=
  fun _ _ g => g.

(** Sub-signature composition. / 子签名组成。 *)
Definition CSubSig_compose {S T U : CSignature}
  (h2 : CSubSig T U) (h1 : CSubSig S T) : CSubSig S U :=
  fun cs ds g => h2 cs ds (h1 cs ds g).

End CSignature.

Arguments CSignature Colour : assert.
Arguments Empty_CSig {Colour} _ _.
Arguments Single_CSig {Colour} ms ns _ _.
Arguments Sum_CSig {Colour} S T _ _.
Arguments CSubSig {Colour} Sub Sup.
Arguments CSubSig_id {Colour} S.
Arguments CSubSig_compose {Colour S T U} h2 h1.

(*
   * * Raw terms over a coloured signature

   The syntactic representation of morphisms in the free coloured
   PROP on a signature [S].  A term of type [CTerm S cs ds] is a
   typed string-diagram expression whose input wires carry the
   colours [cs] (in order) and whose output wires carry [ds], built
   up from:

   - identity wires [CT_id cs]
   - braids [CT_braid cs ds] (the canonical “block braiding” that
   crosses a [cs]-typed bundle past a [ds]-typed bundle)
   - sequential composition [CT_comp]
   - parallel composition (tensor) [CT_tens]
   - signature-supplied generators [CT_gen]

   This defines just the SYNTAX — no equational theory.  Boundaries
   propagate through the constructors by list operations: tensor
   concatenates ([++] replacing the donor's [+] on [nat]), and the
   braid has boundary [(cs ++ ds, ds ++ cs)].

   The inductive lives in its own section, which closes here before
   any lemma about it; downstream files always state results as
   [CTerm S cs ds] with the signature [S] explicit. 

   --------
   * * 彩色标记上的原始项

   在签名 [S] 上的自由彩色 PROP 中，态射的句法表示。类型为 [CTerm S cs ds] 的项是一个带类型的字符串图表达式，其输入线携带颜色 [cs]（按顺序）而输出线携带 [ds]，由以下元素构建：

   - 恒等线 [CT_id cs]
   - 编织 [CT_braid cs ds]（将一个 [cs] 类型的束交叉通过一个 [ds] 类型的束的规范“块编织”）
   - 顺序组合 [CT_comp]
   - 并行组合（张量） [CT_tens]
   - 签名提供的生成元 [CT_gen]这仅定义了语法——没有方程理论。边界通过列表操作在构造子中传播：张量通过连接（[++] 替换捐赠者的 [+] 于 [nat]）进行，并且编织的边界是 [(cs ++ ds, ds ++ cs)]。

   归纳定义在其自己的部分中，在任何关于它的引理之前在此关闭；下游文件总是以 [CTerm S cs ds] 的形式陈述结果，并明确注明签名 [S]。
*)

Section CTerm.

Context {Colour : Type}.
Context (S : CSignature Colour).

Inductive CTerm : list Colour -> list Colour -> Type :=
  | CT_id (cs : list Colour) : CTerm cs cs
  | CT_braid (cs ds : list Colour) : CTerm (cs ++ ds) (ds ++ cs)
  | CT_comp {cs ds es} : CTerm ds es -> CTerm cs ds -> CTerm cs es
  | CT_tens {cs1 ds1 cs2 ds2} :
      CTerm cs1 ds1 -> CTerm cs2 ds2 -> CTerm (cs1 ++ cs2) (ds1 ++ ds2)
  | CT_gen {cs ds} : S cs ds -> CTerm cs ds.

End CTerm.

Arguments CT_id    {Colour S} cs.
Arguments CT_braid {Colour S} cs ds.
Arguments CT_comp  {Colour S cs ds es} _ _.
Arguments CT_tens  {Colour S cs1 ds1 cs2 ds2} _ _.
Arguments CT_gen   {Colour S cs ds} _.

Declare Scope cterm_scope.
Delimit Scope cterm_scope with cterm.

Notation "g ⊙c f" := (CT_comp g f)
  (at level 40, left associativity) : cterm_scope.
Notation "f ⊕c g" := (CT_tens f g)
  (at level 30, right associativity) : cterm_scope.

(** ** Smart constructors / ** 智能构造函数 *)

(*
   * The “swap” braid on two single typed wires.  Note that
   [[c] ++ [d]] is definitionally [[c; d]], so this term also
   inhabits [CTerm S [c; d] [d; c]] on the nose. 

   --------
   * 两根单类型线上的“交换”编织。请注意，[[c] ++ [d] ] 在定义上等于 [[c; d] ]，因此该项也恰好属于 [CTerm S [c; d] [d; c] ]。
*)
Definition CT_swap {Colour} {S : CSignature Colour} (c d : Colour) :
  CTerm S ([c] ++ [d]) ([d] ++ [c]) :=
  CT_braid [c] [d].

(*
   * Identity on a single typed wire.  Named [cwire] to steer clear of
   the [wire] projection of [Construction/ColouredPROP.v]'s supply
   vocabulary. 

   --------
   * 单类型线路上的身份。命名为 [cwire]，以避开 [Construction/ColouredPROP.v] 供应词汇的 [wire] 投影。
*)
Definition cwire {Colour} {S : CSignature Colour} (c : Colour) :
  CTerm S [c] [c] :=
  CT_id [c].

(*
   * The empty term: no input wires, no output wires — the monoidal
   unit's identity. 

   --------
   * 空术语：没有输入线，没有输出线 — 单位元的幺元。
*)
Definition CT_nothing {Colour} {S : CSignature Colour} : CTerm S [] [] :=
  CT_id [].

(*
 NOTE: there is deliberately no analogue of the donor's [T_inj]
 here.  Relabelling a term along a signature morphism is the
 computing fixpoint [CT_map] of [Construction/ColouredPROP/
 Relabel.v] from day one — in the one-sorted development [T_inj]
 was superseded by [T_map], and the coloured spine skips the
 intermediate step. 

 --------
 注意：这里故意没有对应捐赠者的 [T_inj]。在一个签名态射上重新标记一个项就是从一开始在 [Construction/ColouredPROP/Relabel.v] 中计算的不动点 [CT_map] —— 在单类型发展中 [T_inj] 已被 [T_map] 取代，而彩色脊跳过了中间步骤。
*)
