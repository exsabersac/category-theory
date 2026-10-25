Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.

Generalizable All Variables.

#[local] Obligation Tactic := intros.

(* * * The two forgetful functors off the category of adjunctions / * * 从伴随的范畴出发的两个遗忘函子 *)

(*
 nLab: https://ncatlab.org/nlab/show/2-category+of+adjunctions
 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7
 "Transformations of Adjoints", book p. 101, the display immediately
 after the paragraph naming A^(adj)X.

 Mac Lane: "Also there are two evident 'forgetful' functors to the
 ordinary functor categories, as follows:"

 A^X  ←  A^(adj)X ,     [A^(adj)X]^op  →  X^A

 and under that display he draws, for an arrow <sigma, tau> of
 A^(adj)X, the two legs

 F  ←--- <F, G, eta, eps> ---→  G
 |               |                 ^
 sigma          <sigma, tau>         tau
 v               v                 |
 F' ←-- <F', G', eta', eps'> --→  G'

 -- sigma pointing DOWN, from F to F', and tau pointing UP, from G' to G.
 The upward tau is exactly why the second functor is displayed on the
 OPPOSITE of the category of adjunctions.

 LETTERS.  His F : X ⟶ A is the left adjoint and G : A ⟶ X the right
 one, so his X is this file's D and his A is this file's C.  Then A^X,
 the functors X ⟶ A, is [D, C], the category the LEFT adjoints live in;
 and X^A, the functors A ⟶ X, is [C, D], where the RIGHT adjoints live.
 The two displayed functors are therefore

 AdjForgetLeft  C D :  Adj C D        ⟶ [D, C]
 AdjForgetRight C D : (Adj C D)^op    ⟶ [C, D]

 HOW THE CONTRAVARIANCE IS EXPRESSED.  Not by a bespoke notion of a
 contravariant functor, and not by any transport: the source is
 literally [(Adj C D)^op], Construction/Opposite.v's opposite category,
 which is what the book displays.  An arrow x ⟶ y of [(Adj C D)^op] IS
 an arrow y ⟶ x of [Adj C D], that is a [ConjPair y x], whose
 [conj_right] field already has type
 [adjobj_right x ⟹ adjobj_right y] -- the right adjoints of a conjugate
 pair run backward in [Adj C D], so they run forward out of its
 opposite.  So the arrow action of the second functor is the bare field
 projection [conj_right], with nothing inserted, and its two functor
 laws close by [reflexivity], as do the first functor's.

 BEYOND THE DISPLAY: BOTH FUNCTORS ARE FULL AND FAITHFUL.  Mac Lane does
 not say this on that page, and it is not needed for the display, but it
 is what makes the word "forgetful" precise here: neither functor loses
 information, because a conjugate pair is determined by either of its
 legs.  Faithfulness is Instance/Adj.v's [conj_pair_right_unique] and
 [conj_pair_left_unique]; fullness is Conjugate.v's
 [conjugate_conj_mate] and [conjugate_conj_mate_inv], which say that
 every transformation of left adjoints has [conj_mate] as a conjugate
 and every transformation of right adjoints has [conj_mate_inv].  Both
 [Full] instances therefore have a CHOSEN preimage, and it is the mate;
 [fmap_sur] holds by [reflexivity] in both.

 COST.  This file's transitive in-project closure is 21 modules
 excluding itself: Instance/Adj.v's own 19, plus Instance/Adj.vo itself,
 plus Instance/Fun.vo.  Construction/Opposite.vo was already inside that
 19, so the contravariant reading costs nothing extra.

 NOT DELIVERED.  Nothing here says either functor is essentially
 surjective, nor identifies the image of [AdjForgetLeft] with the left
 adjoints inside [D, C]; that would need "a functor with a right adjoint
 is in the image", which is not stated anywhere below.  No equivalence
 of [Adj C D] with any subcategory is claimed.  Nothing relates these to
 Instance/Adjoints.v, whose objects are categories rather than
 adjunctions between two fixed ones.  The 2-categorical structure on
 [Adj] now EXISTS -- Instance/Adj/Bicategory.v's [Adj_Bicategory], whose
 hom-categories are these very [Adj C D] -- and these two functors are
 still not related to it: neither is exhibited as a pseudofunctor, as a
 lax or oplax transformation, or as compatible with horizontal
 composition in any form, and Theory/Bicategory/Mates.v's picture is
 likewise untouched here.  No naturality of either functor in C or D
 is stated, and there is no concrete witness at a named pair of
 categories. 

 --------
 nLab：https://ncatlab.org/nlab/show/2-category+of+adjunctions
 Mac Lane，《为工作数学家而写的范畴论》，第二版，第IV.7节
 “伴随函子变换”，书中第101页，在命名 A^(adj)X 段落之后的显示。

 Mac Lane：“还有两个显而易见的‘遗忘’函子到普通函子范畴，如下：”

 A^X  ←  A^(adj)X ，      [A^(adj)X] ^op  →  X^A

 在该显示下，他为 A^(adj)X 的箭头 <sigma, tau> 画出了两条支线

 F  ←--- <F, G, eta, eps> ---→  G
 |               |                 ^
 sigma          <sigma, tau>         tau
 v               v                 |
 F' ←-- <F', G', eta', eps'> --→  G'-- σ 指向下，从 F 到 F'，而 τ 指向上，从 G' 到 G。向上的 τ 恰恰是第二个函子显示在伴随的范畴的相反上的原因。

 字母说明。他的 F : X ⟶ A 是左伴随，G : A ⟶ X 是右伴随，因此他的 X 是本文件的 D，他的 A 是本文件的 C。然后 A^X，即函子 X ⟶ A，是 [D, C]，左伴随所在的范畴；而 X^A，即函子 A ⟶ X，是 [C, D]，右伴随所在的范畴。因此显示的两个函子为

 AdjForgetLeft  C D :  Adj C D        ⟶  [D, C] 
 AdjForgetRight C D : (Adj C D)^op    ⟶  [C, D]逆变是如何表达的。不是通过对逆变函子量身定制的概念，也不是通过任何传输：源头实际上是 [(Adj C D)^op]，即 Construction/Opposite.v 的对立范畴，这正是书中展示的内容。[(Adj C D)^op] 的一个箭头 x ⟶ y 在 [Adj C D] 中是一个箭头 y ⟶ x，也就是一个 [ConjPair y x]，其 [conj_right] 字段已经具有类型 [adjobj_right x ⟹ adjobj_right y] ——共轭对的右伴随在 [Adj C D] 中向后运行，因此它们在其对立范畴中向前运行。因此，第二个函子的箭头作用就是简单字段投影 [conj_right]，不插入任何东西，并且其两个函子律通过 [reflexivity] 闭合，第一函子也是如此。超越显示：两个函子都是充满且忠实的。Mac Lane 在那一页并没有这样说，而且对于显示来说这也不是必须的，但这正是使这里“遗忘”一词精确的原因：两个函子都不会丢失信息，因为共轭对可以通过其任一支确定。忠实性在 Instance/Adj.v 的 [conj_pair_right_unique] 和 [conj_pair_left_unique] 中；充满性在 Conjugate.v 的 [conjugate_conj_mate] 和 [conjugate_conj_mate_inv] 中，它们说明每一个左伴随变换都有 [conj_mate] 作为共轭，每一个右伴随变换都有 [conj_mate_inv]。 因此，两个 [Full] 实例都有一个所选择的原像，它就是伴随；ZW22WZZ 由 [reflexivity] 在两者中成立。成本。这个文件的传递性项目内闭包是 21 个模块，不包括它自身：Instance/Adj.v 自身的 19 个模块，加上 Instance/Adj.vo 自身，再加上 Instance/Fun.vo。Construction/Opposite.vo 已经包含在那 19 个模块中，所以逆变读取不额外增加任何成本。未交付。这里没有任何内容表明任一函子本质上是满的，也没有将 [AdjForgetLeft] 的像与 [D, C] 内的左伴随函子对应；这需要“具有右伴随的函子在像中”，但在下文中并未说明。也没有声称 [Adj C D] 与任何子范畴等价。没有任何内容将这些与 Instance/Adjoints.v 关联起来，后者的对象是范畴，而不是两个固定范畴之间的伴随关系。[Adj] 上的二范畴结构现在存在——Instance/Adj/Bicategory.v 中的 [Adj_Bicategory]，其同态范畴正是这些 [Adj C D]——而这两个函子仍然与其无关：都没有被展示为伪函子、松或紧变换，也未以任何形式与水平复合兼容，Theory/Bicategory/Mates.v 中的图也在此未被触及。没有说明任一函子在 C 或 D 中的自然性，也没有在命名的范畴对上给出具体实例。
*)

(*
 The first forgetful functor: an adjunction to its left adjoint, a
 conjugate pair to its sigma. 

 --------
 第一个遗忘函子：它与左伴随函子的伴随关系，以及它与 sigma 的共轭对。
*)
Program Definition AdjForgetLeft (C D : Category) : Adj C D ⟶ [D, C] := {|
  fobj := fun x => adjobj_left x;
  fmap := fun _ _ f => conj_left f
|}.
Next Obligation. intros f g [Hl _]; exact Hl. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(*
 The second, on the OPPOSITE of the category of adjunctions: an
 adjunction to its right adjoint, a conjugate pair to its tau. 

 --------
 第二个，在与伴随范畴相反的方面：一个伴随到它的右伴随，一个共轭对到它的 τ。
*)
Program Definition AdjForgetRight (C D : Category) :
  (Adj C D)^op ⟶ [C, D] := {|
  fobj := fun x => adjobj_right x;
  fmap := fun _ _ f => conj_right f
|}.
Next Obligation. intros f g [_ Hr]; exact Hr. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the tau of a conjugate pair is determined by its sigma. / 忠诚的：共轭对的 tau 由其 sigma 决定。 *)
#[export]
Program Instance AdjForgetLeft_Faithful (C D : Category) :
  Faithful (AdjForgetLeft C D).
Next Obligation.
  split; [ exact X | now apply conj_pair_right_unique ].
Qed.

(* Full: every sigma has a conjugate, namely its mate. / 完整的：每个西格玛都有一个共轭，即它的配偶。 *)
#[export]
Program Instance AdjForgetLeft_Full (C D : Category) :
  Full (AdjForgetLeft C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := g
     ; conj_right := conj_mate (adjobj_adj y) (adjobj_adj x) g |}
|}.
Next Obligation. exact (conjugate_conj_mate _ _ g). Qed.
Next Obligation. reflexivity. Qed.

(* Faithful: the sigma of a conjugate pair is determined by its tau. / 忠诚的：共轭对的西格玛由它的塔决定。 *)
#[export]
Program Instance AdjForgetRight_Faithful (C D : Category) :
  Faithful (AdjForgetRight C D).
Next Obligation.
  split; [ now apply conj_pair_left_unique | exact X ].
Qed.

(* Full: every tau has a conjugate, namely its inverse mate. / 完整：每个 τ 都有一个共轭，即它的逆伴。 *)
#[export]
Program Instance AdjForgetRight_Full (C D : Category) :
  Full (AdjForgetRight C D) := {|
  prefmap := fun x y g =>
    {| conj_left  := conj_mate_inv (adjobj_adj x) (adjobj_adj y) g
     ; conj_right := g |}
|}.
Next Obligation. exact (conjugate_conj_mate_inv _ _ g). Qed.
Next Obligation. reflexivity. Qed.
