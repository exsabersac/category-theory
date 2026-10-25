Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.HypergraphFunctor.

Generalizable All Variables.

(**
* Bridge from symmetric monoidal functors to hypergraph functors

    This bridge lives in its own module — rather than in
    Functor/Structure/Monoidal/Braided.v, where the
    [BraidedMonoidalFunctor] / [SymmetricMonoidalFunctor] classes are
    defined — so that importers of the functor classes do not drag in the
    Frobenius/hypergraph chain (Monoid, Comonoid, Frobenius, SCFA,
    Hypergraph, HypergraphFunctor). 

--------
* 从对称幺半群函子到超图函子的桥梁

 这个桥存在于它自己的模块中——而不是在
 Functor/Structure/Monoidal/Braided.v，其中
 [BraidedMonoidalFunctor] / [SymmetricMonoidalFunctor] 类是
 已定义——这样函子类的导入器就不会拖入
 Frobenius/hypergraph 链（Monoid、Comonoid、Frobenius、SCFA、
 超图，超图函子）。 
*)

(*
Structure/Monoidal/HypergraphFunctor.v formalizes a deliberately weakened
   version of Fong–Spivak's hypergraph functors: raw comparison isomorphisms
   plus the four SCFA-preservation equations, WITHOUT the monoidal, unitor or
   braid coherences (see the "Known scoping limitation" caveat there — the
   weakened record is NOT in general a symmetric monoidal functor).  The
   coherence-complete literature notion is exactly: a strong symmetric
   monoidal functor — [SymmetricMonoidalFunctor] of
   Functor/Structure/Monoidal/Braided.v — whose comparison isomorphisms
   preserve the SCFA generators.

   The bridge below packages any such functor as a [HypergraphFunctor], with
   [pure_iso] and [ap_iso] as the comparison isomorphisms.  Only this
   forgetful direction is sound; the converse is false by that file's own
   caveat, since the record does not carry the coherences needed to
   reconstitute a monoidal functor.

   Be clear about how little is happening here: this is constructor
   repackaging and nothing more.  The four preservation hypotheses are
   literally the record's four hf_preserves_* fields, and the
   [HypergraphFunctor] record has no field that could receive [braid_compat]
   (nor the monoidal coherences), so the braided hypothesis [S] contributes
   no checked content to the constructed value — the definition would
   typecheck verbatim against a bare [MonoidalFunctor].  It is nevertheless
   stated against the symmetric hypothesis to name the literature notion the
   forgetting starts from.  In particular this bridge does NOT close
   HypergraphFunctor.v's coherence gap: forgetting into the record loses the
   coherences irrecoverably, and every consumer of the record remains
   subject to the caveat there. 

--------
Structure/Monoidal/HypergraphFunctor.v 形式化了故意弱化的
 Fong-Spivak 超图函子的版本：原始比较同构
 加上四个 SCFA 保存方程，没有幺半群、单位或
 编织一致性（请参阅“已知范围限制”警告 -
 弱化记录通常不是对称幺半群函子）。 的
 连贯完整的文学概念就是：强对称性
 幺半群函子 — [SymmetricMonoidalFunctor] 的
 Functor/Structure/Monoidal/Braided.v — 其比较同构
 保留 SCFA 发生器。

下面的桥将任何此类仿函数封装为 [HypergraphFunctor]，其中
 [pure_iso] 和 [ap_iso] 作为比较同构。 只有这个
 健忘的方向是正确的； 该文件自己的反之亦然
 需要注意的是，因为该记录不具备必要的连贯性
 重构一个幺半群函子。

清楚这里发生的事情有多么少：这是构造函数
 重新包装，仅此而已。 四种保存假设是
 从字面上看，记录的四个 hf_preserves_* 字段，以及
 [HypergraphFunctor] 记录没有可以接收 [braid_compat] 的字段
 （也不是幺半群相干性），因此编织假设 [S] 有助于
 没有检查构造值的内容 - 定义将
 针对裸 [MonoidalFunctor] 逐字检查。 尽管如此
 反对对称假设，将文献概念命名为
 遗忘是从开始的。 特别是这座桥不会关闭
 HypergraphFunctor.v 的连贯性差距：忘记记录会丢失
 不可恢复地连贯性，并且记录的每个消费者都保留
 须遵守那里的警告。 
*)

Section HypergraphBridge.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Context {D : Category}.
Context `{SD : @SymmetricMonoidal D}.
Context `{HG_D : @Hypergraph D SD}.

Context {F : C ⟶ D}.

(*
Over the symmetric bases SC and SD this hypothesis is precisely
   [SymmetricMonoidalFunctor F]. 

--------
在对称基 SC 和 SD 上，这个假设恰好成立
 [SymmetricMonoidalFunctor F]。 
*)
Context `{S : @BraidedMonoidalFunctor C D _ _ F}.

Program Definition SymmetricMonoidalFunctor_HypergraphFunctor
  (preserves_mu : ∀ X : C,
     fmap[F] (scfa_mu (scfa X)) ∘ to ap_iso ≈ scfa_mu (scfa (F X)))
  (preserves_eta : ∀ X : C,
     fmap[F] (scfa_eta (scfa X)) ∘ to pure_iso ≈ scfa_eta (scfa (F X)))
  (preserves_delta : ∀ X : C,
     from ap_iso ∘ fmap[F] (scfa_delta (scfa X)) ≈ scfa_delta (scfa (F X)))
  (preserves_epsilon : ∀ X : C,
     from pure_iso ∘ fmap[F] (scfa_epsilon (scfa X))
       ≈ scfa_epsilon (scfa (F X))) :
  HypergraphFunctor HG_C HG_D := {|
  hf_functor := F;
  hf_unit_iso := @pure_iso C D _ _ F _;
  hf_tensor_iso := fun X Y => @ap_iso C D _ _ F _ X Y
|}.

End HypergraphBridge.
