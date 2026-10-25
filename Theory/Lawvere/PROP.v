Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Theory.Lawvere.

Generalizable All Variables.

(** * Lawvere theories meet the PROP spine / * Lawvere理论遇到PROP主干 *)

(*
nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   A Lawvere theory is a CARTESIAN gadget (finite products, every object
   a power of the generator), while a PROP is a LINEAR one (a strict
   symmetric monoidal category on (ℕ, +, 0), with no built-in copying or
   discarding).  This file connects the two spines:

   1.  [Lawvere_Monoidal] / [Lawvere_Braided] / [Lawvere_Symmetric] —
       the cartesian symmetric monoidal structure on [law_cat T],
       instantiating the [CC_*] tower of
       [Structure/Monoidal/Internal/Product.v] (re-exported through
       [Structure/Monoidal/Cartesian.v]) at [law_cartesian] /
       [law_terminal]: tensor := ×, unit := 1, braid := swap = ⟨exr, exl⟩.

   2.  [Lawvere_PROP] / [Lawvere_PROP_interp] — interpretation of a free
       PROP on a signature [Σ] into [law_cat T].  The in-tree
       interpretation machinery ([Construction/PROP/Interp.v],
       [Construction/PROP/Universal.v]) is stated against a target that
       is itself a [PROP], i.e. carries a [StrictMonoidal] instance whose
       strictness equalities hold at ALL objects.  The cartesian monoidal
       structure of a general Lawvere theory is only WEAKLY monoidal —
       [(x × y) × z] and [x × (y × z)] are canonically isomorphic, not
       Leibniz-equal — so strictness is taken here as a hypothesis pack
       ([SM : StrictMonoidal (@law_cat T)] together with the coherence
       [coh : strict_is_monoidal SM = Lawvere_Monoidal T]).  On skeletal
       instances (where objects really are the natural numbers and
       products literally add) the pack is EXPECTED to be discharged with
       [coh := eq_refl] and the strictness object equalities by nat
       induction — associativity and the right unit are propositional on
       [nat], only the left unit computes — but no in-tree witness exists
       yet: the base [FinSet^op]'s own monoidal assembly is not built
       (see the note below), so that witness is deferred work, not a
       citation.  Under that
       pack, [Lawvere_PROP] assembles a bona-fide [PROP] on [law_cat T]
       — its [prop_of_nat] is [law_of_nat], its strictness equalities are
       [law_zero_terminal] / [law_plus_product] transported along [coh],
       and its symmetric structure is the cartesian braiding of (1) —
       and the induced interpretation functor
       [Lawvere_PROP_interp : FreeCat Σ ⟶ law_cat T] (the mediating
       functor out of [FreePROP Σ], whose underlying category is
       [FreeCat Σ]) is the in-tree [InterpF], with its strong / strict /
       braided / symmetric monoidal packaging instantiated verbatim.
       The braid-square requirement of [Interp.v] is met by the symmetry
       of (1), exactly as requested: [Lawvere_PROP_interp_Braided] lands
       in [symmetric_is_braided (Lawvere_Symmetric T)].

   3.  The Fox boundary.  Cartesian monoidal categories are exactly the
       symmetric monoidal categories in which every object carries a
       canonical commutative comonoid structure compatibly with the
       tensor — equivalently, the Markov categories all of whose
       morphisms are deterministic.  This is Fox's theorem, proven
       in-tree in [Structure/Monoidal/Markov/Fox.v]:
       [cartesian_all_deterministic] (in a cartesian Markov category
       every morphism commutes with copy/discard) and
       [all_deterministic_cartesian] (an all-deterministic Markov
       category is cartesian monoidal), with
       [markov_all_deterministic_iff_cartesian] the round trip.  The
       Lawvere (cartesian) spine and the PROP (linear) spine therefore
       meet at exactly the copy/discard boundary: a Lawvere theory is a
       PROP-like gadget in which every wire may be freely copied
       ([Δ = ⟨id, id⟩]) and discarded ([one]), naturally in the wire —
       whereas a bare PROP supplies neither.  [Instance/FinSet.v]'s
       header notes that its coproduct-induced monoidal assembly and the
       PROP instance riding on it are not yet built in-tree; the present
       file supplies the theory-level statement of the connection on the
       cartesian side ([Lawvere_PROP] + [Lawvere_PROP_interp]), so that
       once a skeletal instance provides the strictness pack, the free
       PROP on any signature interprets into it through this file.

--------
nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
nLab:      https://ncatlab.org/nlab/show/PROP
维基百科: https://en.wikipedia.org/wiki/Lawvere_theory

Lawvere 理论是一个笛卡尔装置（有限积，每个对象都是生成元的幂），而 PROP 是一个线性装置（在 (ℕ, +, 0) 上的严格对称单体范畴，没有内置的复制或丢弃）。这个文件连接了这两个主脊：

1. [Lawvere_Monoidal] / [Lawvere_Braided] / [Lawvere_Symmetric] —
       [law_cat T] 上的笛卡尔对称幺半群结构，
       在 [law_cartesian] / [law_terminal] 上实例化 [CC_*] 塔的 [Structure/Monoidal/Internal/Product.v]（通过 [Structure/Monoidal/Cartesian.v] 重新导出）：tensor := ×，unit := 1，braid := swap = ⟨exr, exl⟩。

2. [Lawvere_PROP] / [Lawvere_PROP_interp] — 将自由PROP在签名[Σ]上的解释转化为[law_cat T]。树内的解释机制（[Construction/PROP/Interp.v]，[Construction/PROP/Universal.v]）是针对自身为[PROP]的目标来陈述的，即携带其在所有对象上严格相等的[StrictMonoidal]实例。一般Lawvere理论的笛卡尔单体结构只是弱单体的——[(x × y) × z]和[x × (y × z)]在范畴上同构，而非Leibniz相等——因此严格性在此被作为一个假设包（[SM : StrictMonoidal (@law_cat T)]以及一致性[coh : strict_is_monoidal SM = Lawvere_Monoidal T]）。
在骨架实例上（对象确实是自然数，乘积实际上是加法）时，包预计使用 [coh := eq_refl] 释放，并通过自然数归纳处理严格的对象相等性——结合律和右单位律在 [nat] 上是命题性的，只有左单位律可以计算——但还不存在树内见证：基础 [FinSet^op] 自身的幺半群组装尚未构建（见下方注释），因此该见证是延迟工作，而不是引用。
在那个包下，[Lawvere_PROP] 在 [law_cat T] 上组装了一个真正的 [PROP]——它的 [prop_of_nat] 是 [law_of_nat]，其严格性等式沿着 [coh] 传输为 [law_zero_terminal] / [law_plus_product]，并且其对称结构是 (1) 的笛卡尔编织——并且诱导的解释函子 [Lawvere_PROP_interp : FreeCat Σ ⟶ law_cat T]（从 [FreePROP Σ] 出来的中介函子，其底层范畴是 [FreeCat Σ]）是 in-tree [InterpF]，其强/严格/编织/对称单体包装被逐字实例化。[Interp.v] 的编织方格要求由 (1) 的对称性满足，完全如要求：[Lawvere_PROP_interp_Braided] 落在 [symmetric_is_braided (Lawvere_Symmetric T)] 中。

3. 福克斯边界。笛卡尔单元范畴正是那些对称单元范畴，其中每个对象都带有一个与张量兼容的标准交换余单体结构——等价地说，就是所有态射都是确定性的马尔可夫范畴。这是福克斯定理，在 [Structure/Monoidal/Markov/Fox.v] 的树上证明：[cartesian_all_deterministic]（在笛卡尔马尔可夫范畴中，每个态射与复制/丢弃交换）和 [all_deterministic_cartesian]（一个全确定性的马尔可夫范畴是笛卡尔单元范畴），其中 [markov_all_deterministic_iff_cartesian] 为往返。
因此，Lawvere（笛卡尔）脊柱和PROP（线性）脊柱正好在复制/丢弃边界处相交：Lawvere理论是一个类似PROP的小工具，其中每根线都可以自由复制（[Δ = ⟨id, id⟩]）和丢弃（[one]），自然地在该线上——而一个纯PROP则两者都不提供。[Instance/FinSet.v]的标题指出，它的余积引出的单体组装以及在其上运行的PROP实例尚未在树中构建；当前文件提供了笛卡尔侧连接的理论级声明（[Lawvere_PROP] + [Lawvere_PROP_interp]），因此，一旦一个骨架实例提供了严格性包，任何签名上的自由PROP都可以通过此文件解释到其中。
*)

(** ** 1. The cartesian symmetric monoidal structure on a Lawvere theory / ** 1. Lawvere 理论上的笛卡尔对称幺半范畴结构 *)

Section LawvereMonoidal.

Context (T : LawvereTheory).

(** Tensor := ×, unit := 1, via [Cartesian_Monoidal] (= [CC_Monoidal]). / 张量 := ×，单位 := 1，通过 [Cartesian_Monoidal] (= [CC_Monoidal])。 *)
Definition Lawvere_Monoidal : @Monoidal (@law_cat T) :=
  @Cartesian_Monoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** The braiding is the product swap [⟨exr, exl⟩]. / 编织是产品交换 [⟨exr, exl⟩]。 *)
Definition Lawvere_Braided : @BraidedMonoidal (@law_cat T) :=
  @CC_BraidedMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(** Symmetry: [swap ∘ swap ≈ id]. / 对称性：[swap ∘ swap ≈ id]。 *)
Definition Lawvere_Symmetric : @SymmetricMonoidal (@law_cat T) :=
  @CC_SymmetricMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(**
The full cartesian-monoidal packaging (relevance + semicartesian),
    i.e. the Fox-side data: diagonal [⟨id, id⟩] and eliminate [one].

--------
完整的笛卡尔-幺半群打包（相关性 + 半笛卡尔），即 Fox 端数据：对角线 [⟨id, id⟩] 并消除 [one]。
*)
Definition Lawvere_CartesianMonoidal : @CartesianMonoidal (@law_cat T) :=
  @CC_CartesianMonoidal (@law_cat T) (@law_cartesian T) (@law_terminal T).

(**
Sanity, machine-checked: the monoidal structures underlying the
    braided/symmetric packagings are [Lawvere_Monoidal] itself, on the
    nose.  This definitional agreement is what lets the PROP coherence
    field below be a single equality hypothesis.

--------
理智，机器检查过的：支撑编织/对称封装的单体结构正是 [Lawvere_Monoidal] 本身。这一定义上的一致性正是使下面的 PROP 相干场成为单一等式假设的原因。
*)
Example Lawvere_Symmetric_monoidal_coherence :
  @braided_is_monoidal (@law_cat T)
    (@symmetric_is_braided (@law_cat T) Lawvere_Symmetric)
  = Lawvere_Monoidal := eq_refl.

End LawvereMonoidal.

(** ** 2. The PROP on a strict Lawvere theory, and interpretation / ** 2. 严格的 Lawvere 理论上的 PROP 及其解释 *)

Section LawverePROP.

Context (T : LawvereTheory).

(**
The strictness pack: the in-tree PROP/interpretation machinery
    requires a strict target, and a general Lawvere theory's cartesian
    monoidal structure is only weakly monoidal, so strictness is a
    hypothesis — expected to be satisfied on skeletal instances (objects
    literally the natural numbers) with [coh := eq_refl] and the
    strictness object equalities by nat induction; the in-tree witness
    awaits the base's monoidal assembly (header note).

--------
严格性包：树内PROP/解释机制要求一个严格的目标，而一般的Lawvere理论的笛卡尔幺半群结构只是弱幺半群，因此严格性是一个假设——预计在骨架实例（对象字面上为自然数）中通过[coh := eq_refl]以及通过自然数归纳的严格性对象等式得到满足；树内证据等待基底的幺半群组合（标题说明）。
*)
Context (SM : @StrictMonoidal (@law_cat T)).
Context (coh : @strict_is_monoidal (@law_cat T) SM = Lawvere_Monoidal T).

(**
The unit of the strict path is [law_of_nat 0]: transport
    [law_zero_terminal] along [coh].

--------
严格路径的单位是 [law_of_nat 0]：运输 [law_zero_terminal] 沿着 [coh]。
*)
Definition Lawvere_prop_unit_zero :
  @I (@law_cat T) (@strict_is_monoidal (@law_cat T) SM)
  = @law_of_nat T 0%nat :=
  eq_trans
    (f_equal (fun M : @Monoidal (@law_cat T) => @I (@law_cat T) M) coh)
    (eq_sym (@law_zero_terminal T)).

(**
Tensor on canonical objects is addition: transport
    [law_plus_product] along [coh].

--------
在典型对象上的张量是加法：沿 [coh] 传输 [law_plus_product]。
*)
Definition Lawvere_prop_tensor_plus (m n : nat) :
  (@law_of_nat T m ⨂[@strict_is_monoidal (@law_cat T) SM] @law_of_nat T n)%object
  = @law_of_nat T (m + n)%nat :=
  eq_trans
    (f_equal
       (fun M : @Monoidal (@law_cat T) =>
          (@law_of_nat T m ⨂[M] @law_of_nat T n)%object) coh)
    (@law_plus_product T m n).

(**
The PROP on [law_cat T]: strict path [SM], symmetric path the
    cartesian braiding of section 1, coherence the hypothesis [coh]
    (typechecking because [braided_is_monoidal (symmetric_is_braided
    (Lawvere_Symmetric T))] is definitionally [Lawvere_Monoidal T]),
    and object correspondence [law_of_nat].

--------
[law_cat T] 上的 PROP：严格路径 [SM]，对称路径第 1 节的笛卡尔编织，一致性假设 [coh]（类型检查因为 [braided_is_monoidal (symmetric_is_braided (Lawvere_Symmetric T))] 在定义上是 [Lawvere_Monoidal T]），以及对象对应 [law_of_nat]。
*)
Definition Lawvere_PROP : PROP := {|
  prop_cat := @law_cat T;
  prop_strict := SM;
  prop_symmetric := Lawvere_Symmetric T;
  prop_monoidal_coherence := coh;
  prop_of_nat := @law_of_nat T;
  prop_unit_zero := Lawvere_prop_unit_zero;
  prop_tensor_plus := Lawvere_prop_tensor_plus
|}.

(**
*** Interpretation of a free PROP in the Lawvere theory

    The side conditions are those of [Construction/PROP/Interp.v] /
    [Universal.v]: a [Prop] reflection of the hom equivalence and
    decidable object equality (powering the axiom-free UIP on objects).

--------
*** 在Lawvere理论中对自由PROP的解释

    边条件是[Construction/PROP/Interp.v] / [Universal.v]：同构等价的[Prop]反射以及可判定的对象相等性（为对象上的无公理UIP提供支持）。
*)

Context {HP : HomEqProp (@law_cat T)}.
Context {OD : @ObjDecEq (@law_cat T)}.

Context (Σ : Signature).

(**
A valuation of the generators of [Σ] in [law_cat T], along
    [law_of_nat] — definitionally a [Valuation (Lawvere_PROP) Σ].

--------
在 [law_cat T] 中对 [Σ] 的生成元进行估值，沿着 [law_of_nat] —— 从定义上是一个 [Valuation (Lawvere_PROP) Σ]。
*)
Context (v : ∀ m n : nat, Σ m n → (@law_of_nat T m ~{@law_cat T}~> @law_of_nat T n)).

Definition Lawvere_Valuation : Valuation Lawvere_PROP Σ := v.

(**
The induced interpretation functor out of the free PROP ([FreeCat Σ]
    is the underlying category of [FreePROP Σ]), instantiating the
    in-tree universal-property machinery at [Lawvere_PROP].

--------
由自由 PROP ([FreeCat Σ] 是 [FreePROP Σ] 的底层范畴) 引出的诱导解释函子，在 [Lawvere_PROP] 处实例化树内的通用性质机制。
*)
Definition Lawvere_PROP_interp : FreeCat Σ ⟶ @law_cat T :=
  @InterpF Σ Lawvere_PROP HP OD Lawvere_Valuation.

(**
Machine-checked: the interpretation extends the valuation — every
    generator is sent to its assigned [law_cat T]-morphism, on the nose.

--------
机器检查：该解释扩展了赋值——每个生成元都被精确地映射到其指定的 [law_cat T]-态射。
*)
Example Lawvere_PROP_interp_extends (m n : nat) (g : Σ m n) :
  fmap[Lawvere_PROP_interp] (T_gen g) ≈ v m n g.
Proof. reflexivity. Qed.

(** The strong monoidal packaging, over the strict path [SM]. / 经过严格的 [SM] 路径，坚固的单体包装。 *)
Definition Lawvere_PROP_interp_Monoidal :
  @MonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Monoidal Σ Lawvere_PROP HP OD Lawvere_Valuation.

(**
The strict monoidal packaging: the object comparisons are the
    transported [law_zero_terminal] / [law_plus_product], verbatim.

--------
严格的单体包装：对象比较是传输的 [law_zero_terminal] / [law_plus_product]，逐字对应。
*)
Definition Lawvere_PROP_interp_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Monoidal Σ)
    (@strict_is_monoidal (@law_cat T) SM) Lawvere_PROP_interp :=
  @InterpF_Strict Σ Lawvere_PROP HP OD Lawvere_Valuation.

(**
The braided packaging, landing in the cartesian braiding of
    section 1 — the braid-square requirement of [Interp.v] is met by
    the symmetry [swap = ⟨exr, exl⟩] of the Lawvere theory.

--------
编织包装，落在第1节的笛卡尔编织中——[Interp.v]的编织-平方要求由Lawvere理论的对称性[swap = ⟨exr, exl⟩]满足。
*)
Definition Lawvere_PROP_interp_Braided :
  @BraidedMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Braided Σ)
    (@symmetric_is_braided (@law_cat T) (Lawvere_Symmetric T))
    Lawvere_PROP_interp :=
  @InterpF_Braided Σ Lawvere_PROP HP OD Lawvere_Valuation.

(** The symmetric packaging, at [Lawvere_Symmetric]. / 在 [Lawvere_Symmetric] 的对称包装。 *)
Definition Lawvere_PROP_interp_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat Σ) (@law_cat T) (FreeCat_Symmetric Σ)
    (Lawvere_Symmetric T) Lawvere_PROP_interp :=
  @InterpF_Symmetric Σ Lawvere_PROP HP OD Lawvere_Valuation.

End LawverePROP.

