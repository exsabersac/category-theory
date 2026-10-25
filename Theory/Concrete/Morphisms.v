Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Concrete.

Generalizable All Variables.

(** * Underlying injections and surjections in a concrete category / * 具体范畴中的底层单射和满射 *)

(*
nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
              Exercise 1.6.iv, printed p. 47, and Definition 1.6.18,
              printed p. 45
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, Springer 1998, §I.5, Exercise 9, printed p. 21

   Riehl's Exercise 1.6.iv is that a faithful functor reflects monomorphisms
   and, dually, epimorphisms; that is [faithful_reflects_monic] and
   [faithful_reflects_epic] in Theory/Functor.v.  She then draws the corollary
   this file proves: in a CONCRETE category — one paired with a faithful
   functor to sets, Theory/Concrete.v's [Concrete] — a morphism whose
   underlying function is injective is a monomorphism, and one whose
   underlying function is surjective is an epimorphism.

   The two proofs are short and symmetric, and both run entirely through
   Theory/Concrete.v's [concrete_arrow_eq]: to make two arrows of `C`
   equivalent under `≈` it suffices that their underlying functions agree
   pointwise, and that is where the injectivity or surjectivity hypothesis is
   spent.  Note the direction of the corollary.  The converses are out of
   scope: nothing here says that a monic of a concrete category has injective
   underlying function, and no counterexample to that is exhibited either.

   Both hypotheses are Lib/Setoid.v's setoid-level classes, so they are stated
   up to `≈` and not up to `=`: [injective] reads `f a ≈ f b → a ≈ b` in the
   two underlying setoids, and [surjective] is the split form, carrying a
   chosen preimage.  The conclusions are Theory/Morphisms.v's [Monic] and
   [Epic], whose cancellation laws are likewise `≈` throughout; no statement
   in this file uses `=` on morphisms.

   Layering note: the general lemmas need only Theory/Concrete.v, but the
   second half of the file instantiates them at the roster of
   Instance/Concrete.v, so the file as a whole depends on the instance layer.
   Theory/Concrete.v itself already depends on Instance/Sets.v, since `Sets`
   is the codomain named in the definition of [Concrete].

--------
nLab：https://ncatlab.org/nlab/show/concrete+category
Wikipedia：https://en.wikipedia.org/wiki/Concrete_category
书籍：Riehl，《语境中的范畴论》，Dover 2016，第1.6节，练习1.6.iv，印刷第47页，以及定义1.6.18，印刷第45页
书籍：Mac Lane，《为工作数学家准备的范畴》，第2版，GTM 5，Springer 1998，第I.5节，练习9，印刷第21页

Riehl 的练习 1.6.iv 说明，一个忠实函子会反射单态射，并且对偶地会反射满射；也就是 Theory/Functor.v 中的 [faithful_reflects_monic] 和 [faithful_reflects_epic]。然后她得出了这个文件证明的推论：在一个具体范畴中——即与到集合的忠实函子配对的范畴，见 Theory/Concrete.v 的 [Concrete]——其底层函数是单射的态射是单态射，其底层函数是满射的态射是满态射。

这两个证明都很简短且对称，并且都完全通过 Theory/Concrete.v 的 [concrete_arrow_eq] 进行：为了使 `C` 的两个箭头在 `≈` 下等价，只需它们的底层函数在每一点上都相同，这正是单射性或满射性假设起作用的地方。注意推论的方向。逆命题不在讨论范围内：这里没有说明具体范畴中的单态箭头的底层函数一定是单射的，也没有展示任何反例。

两个假设都是 Lib/Setoid.v 中的集合等价类级别的类，所以它们是直到 `≈` 为止声明的，而不是直到 `=`：[injective] 在两个底层集合等价类中读取 `f a ≈ f b → a ≈ b`，[surjective] 是分裂形式，携带一个选定的原像。结论是 Theory/Morphisms.v 的 [Monic] 和 [Epic]，它们的抵消律同样在整个过程中都是 `≈`；本文件中没有任何语句在同态上使用 `=`。

分层说明：一般的引理只需要 Theory/Concrete.v，但文件的后半部分在 Instance/Concrete.v 的列表中实例化它们，因此整个文件依赖于实例层。Theory/Concrete.v 本身已经依赖于 Instance/Sets.v，因为 `Sets` 是在 [Concrete] 的定义中命名的值域。
*)

Section ConcreteMorphisms.

Context {C : Category}.
Context `{Con : @Concrete C}.

(*
Injective underlying function implies monic.  This IS a corollary of
   [faithful_reflects_monic]: the underlying functor is faithful by
   assumption, injectivity of the underlying function makes its image monic
   in [Sets] by [injectivity_is_monic], and reflection carries that back to
   `C`.  The first commit of this file proved it from scratch instead, and
   then described it as derived from the reflection lemma — an audit caught
   the discrepancy, so the proof now matches the description.

   NOTE THE ASYMMETRY with the epic direction below, which CANNOT take this
   route: Instance/Sets.v's [surjectivity_is_epic] terminates in an
   incomplete sketch and does not enter the environment, so there is no
   independent "surjective implies epic" in [Sets] to reflect through.  That
   direction is therefore proved directly here, and [Sets_surjective_epic]
   below is obtained FROM it rather than the other way round.

--------
注入的底层函数意味着单射。这是 [faithful_reflects_monic] 的推论：根据假设，底层函子是忠实的，底层函数的注入性使其在 [Sets] 中的像通过 [injectivity_is_monic] 成为单射，而反射则将其带回到 `C`。该文件的第一次提交是从零开始证明的，然后描述为从反射引理派生——审计发现了差异，因此现在的证明与描述一致。

注意以下满射方向的不对称性，它不能走这条路线：Instance/Sets.v 的 [surjectivity_is_epic] 以不完整的草稿结束，并未进入环境，因此 [Sets] 中不存在可以通过反射的独立“满射 implies epic”。因此，该方向在此直接证明，下面的 [Sets_surjective_epic] 是从它获得的，而不是相反。
*)
Lemma concrete_injective_monic {x y : C} (f : x ~> y) :
  injective (concrete_fun f) → Monic f.
Proof.
  intros Hinj.
  apply (faithful_reflects_monic underlying (H:=underlying_faithful) f).
  apply (fst (injectivity_is_monic (fmap[underlying] f))).
  intros a b Hab.
  exact (inj (injective:=Hinj) Hab).
Qed.

(*
Surjective underlying function implies epic: the mirror image.  A point of
   the underlying set of the TARGET is hit by some point `a` of the source, and
   the two composites agree at `a`; the underlying functions of `g1` and `g2`
   are setoid maps, so that agreement transports along the chosen preimage.

--------
满射的底层函数意味着支形：镜像。目标底层集合的某个点被源中的某个点 `a` 命中，并且两个复合在 `a` 处一致；`g1` 和 `g2` 的底层函数是集合同构映射，因此一致性沿着选择的原像传递。
*)
Lemma concrete_surjective_epic {x y : C} (f : x ~> y) :
  surjective (concrete_fun f) → Epic f.
Proof.
  intros Hsur.
  constructor; intros z g1 g2 Hg.
  apply concrete_arrow_eq; intro b.
  destruct (@surj _ _ _ _ Hsur b) as [a Ha].
  rewrite <- Ha.
  transitivity (concrete_fun (g1 ∘ f) a).
  { symmetry; exact (fmap_comp (Functor:=underlying) g1 f a). }
  transitivity (concrete_fun (g2 ∘ f) a).
  { exact (concrete_fun_respects _ _ Hg a). }
  exact (fmap_comp (Functor:=underlying) g2 f a).
Qed.

End ConcreteMorphisms.

(** ** The corollary at work: [Coq], via [Coq_Concrete] / ** 正在起作用的推论：[Coq]，通过 [Coq_Concrete] *)

(*
Non-vacuity of both lemmas at a real concrete category.  `Coq`
   (Instance/Coq.v) is concrete via [Coq_Concrete] (Instance/Concrete.v),
   whose underlying-set functor reads a type as a setoid under Leibniz
   equality.  So `injective` and `surjective` below are the ordinary
   element-level notions for the two functions chosen here, and the
   conclusions are genuine cancellation properties in `Coq` — genuine because
   `Coq`'s hom-setoids are not trivial, as Instance/Concrete.v's
   [Coq_two_arrows] records.

--------
在一个真实具体范畴上，两个引理都非空。`Coq`（Instance/Coq.v）通过 [Coq_Concrete]（Instance/Concrete.v）是具体的，其底层集合函子将类型作为勒布尼茨等价下的集合。因此，下面的 `injective` 和 `surjective` 是这里选择的两个函数的普通元素级概念，并且结论在 `Coq` 中是真正的消去性质——之所以真正，是因为 `Coq` 的同态集合并非平凡，如 Instance/Concrete.v 的 [Coq_two_arrows] 所记录的。
*)

Definition bool_to_nat (b : bool) : nat := if b then 1%nat else 0%nat.

(*
This one statement is `=` rather than `≈`, and deliberately so: it relates
   ELEMENTS of `bool` and `nat`, not morphisms.  Under [Coq_Underlying] those
   two carriers are setoids whose `≈` IS Leibniz equality, so this is already
   the `≈`-shaped premise [injective] asks for, and it is used as such
   directly below.

--------
这条语句是 `=` 而不是 `≈`，而且是故意的：它涉及 `bool` 和 `nat` 的元素，而不是同态。在 [Coq_Underlying] 下，这两个承载对象是等价类，其 `≈` 是 Leibniz 等式，因此这已经是 [injective] 所要求的 `≈` 形状的前提，并且在下面直接作为这样的前提使用。
*)
Lemma bool_to_nat_inj (a b : bool) : bool_to_nat a = bool_to_nat b → a = b.
Proof.
  destruct a, b; simpl; solve [ reflexivity | discriminate ].
Qed.

#[local] Instance bool_to_nat_injective :
  injective (concrete_fun (Con:=Coq_Concrete) (bool_to_nat : bool ~{Coq}~> nat)).
Proof.
  constructor; intros a b Hab.
  exact (bool_to_nat_inj a b Hab).
Qed.

(*
Predecessor is surjective: every `y` is `pred (S y)`.  It is not injective
   either (`pred 0` and `pred 1` are both `0`, both by computation), so the
   two halves above are exercised by two different arrows rather than by one
   arrow that happens to be bijective.

--------
前任是满射的：每个 `y` 都是 `pred (S y)`。它也不是单射的（`pred 0` 和 `pred 1` 都是 `0`，都是通过计算得出的），所以上面两部分是由两个不同的箭头操作的，而不是由一个碰巧是双射的箭头操作的。
*)
#[local] Instance Coq_pred_surjective :
  surjective (concrete_fun (Con:=Coq_Concrete) (Nat.pred : nat ~{Coq}~> nat)).
Proof.
  constructor; intro y.
  exists (S y); reflexivity.
Qed.

Definition Coq_bool_to_nat_Monic : Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  concrete_injective_monic (Con:=Coq_Concrete) bool_to_nat bool_to_nat_injective.

Definition Coq_pred_Epic : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  concrete_surjective_epic (Con:=Coq_Concrete) Nat.pred Coq_pred_surjective.

(** ** The same two conclusions through the reflection lemmas / ** 通过反射引理得出的相同两个结论 *)

(*
The corollary can also be reached by first establishing the property in
   `Sets` and then reflecting it along the faithful functor, which is what
   Riehl's exercise proper supplies.  Both routes are recorded because the
   second is a non-vacuity witness for [faithful_reflects_monic] and
   [faithful_reflects_epic] themselves: the hypothesis genuinely holds and the
   conclusion is a genuine monic (respectively epic) of `Coq`.

   No claim is made that the two routes produce the same proof term — they are
   different derivations of the same statement, and `Monic`/`Epic` are
   record types whose inhabitants are not compared here.

--------
该推论也可以通过先在 `Sets` 中建立该性质，然后沿着忠实函子反射来得到，这正是 Riehl 的练习所提供的。之所以记录这两条路径，是因为第二条路径是 [faithful_reflects_monic] 和 [faithful_reflects_epic] 本身的非空见证：假设确实成立，而结论则是 `Coq` 的一个真正的单态（分别是满态）。

并未声称这两条路径产生相同的证明项——它们是同一命题的不同推导，而 `Monic`/`Epic` 是记录类型，其元素在这里不作比较。
*)

Definition Coq_bool_to_nat_Monic_reflected :
  Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  faithful_reflects_monic Coq_Underlying bool_to_nat
    (fst (injectivity_is_monic (fmap[Coq_Underlying] bool_to_nat))
       (fun a b (Hab : bool_to_nat a = bool_to_nat b) => bool_to_nat_inj a b Hab)).

(*
For epis the `Sets`-side ingredient comes from this file's own
   [concrete_surjective_epic] at [Sets_Concrete] (Theory/Concrete.v),
   whose underlying-set functor is the identity: there `concrete_fun h` IS `h`,
   so the lemma reads "a surjective setoid map is epic in `Sets`".
   Instance/Sets.v states the corresponding biconditional as
   `surjectivity_is_epic`, but that proof is a sketch stopped before
   completion, so the name never enters the environment and cannot be used
   here; the header of Instance/Sets.v documents the size obstruction behind
   the missing direction.

--------
对于 epis，`Sets` 端的成分来自此文件自身的 [concrete_surjective_epic]，在 [Sets_Concrete] (Theory/Concrete.v)，其底层集合函子是恒等的：在那里 `concrete_fun h` 是 `h`，因此引理表述为“一个满射集合等价映射在 `Sets` 中是 epic”。Instance/Sets.v 将对应的等价条件陈述为 `surjectivity_is_epic`，但该证明只是一个在完成前就停止的草稿，因此名称从未进入环境，也不能在此处使用；Instance/Sets.v 的头部记录了导致缺失方向的规模障碍。
*)
Definition Sets_surjective_epic {X Y : SetoidObject} (h : X ~{Sets}~> Y) :
  surjective h → Epic h :=
  concrete_surjective_epic (Con:=Sets_Concrete) h.

Definition Coq_pred_Epic_reflected : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  faithful_reflects_epic Coq_Underlying Nat.pred
    (Sets_surjective_epic (fmap[Coq_Underlying] Nat.pred) Coq_pred_surjective).
