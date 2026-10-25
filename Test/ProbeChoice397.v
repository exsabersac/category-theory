Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Adj.Forgetful.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Two.
Require Import Category.Adjunction.Choice.

Generalizable All Variables.

(**
* Boundary probe for Adjunction/Choice.v (issue #397)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.7, book p. 102, Exercise 3: in the functor category A^X let S be
    the full subcategory of the functors that have a right adjoint, and
    make R a functor S^op -> X^A by choosing one RF for each F, with
    R(sigma) the conjugate of sigma.

    Adjunction/Choice.v carries ZERO [Fail] commands by design: the
    Definition-of-Done box forbids new [make todo] hits, and an in-file
    negative renames in lockstep with the constant it guards, so it
    cannot detect a rename at all.  This file is where every refutation
    that file's prose describes is pinned.

    METHOD.  The [Require] list above mirrors Adjunction/Choice.v's
    eighteen lines character for character, adding only the target
    module itself; measured, a [diff] of the two blocks reports exactly
    that one added line.  A probe with a short prefix can fail for a
    reason it never measured, which is a FALSE PASS, so nothing is
    dropped and nothing else is added.  Each negative below was
    STRIPPED (the [Fail] removed), written into its own scratch file
    with that same full prefix, compiled ALONE, and its WHOLE error
    read; the kind recorded beside it is read off that error text and
    not off an expectation:

      CONVERSION   the error ends in an explicit "cannot unify" between
                   two inhabitants of ONE type, with no universe clause;
      TYPING       a plain "has type ... while it is expected to have
                   type", with NO "cannot unify" and no universe clause;
      FORMABILITY  the error ends "universe inconsistency: Cannot
                   enforce ...".

    TALLY.  17 [Fail] commands = 1 instrument check + 16 negatives of
    THREE kinds, told apart by the error TEXT: 7 CONVERSION (negatives
    1-7), 1 TYPING (negative 8) and 8 FORMABILITY (negatives 9-16).
    The TYPING one is discriminating: the SAME term ascribed at the
    contravariant type is accepted immediately above it
    ([p397_raf_type_control]), so what is refused is the variance and
    not the term.

    THREE FALSE-PASS SHAPES ARE AVOIDED, and ONE of the three is
    MEASURED HERE rather than taken on trust.  (i) [Fail Program
    Definition] -- negative 8's statement, written with [Program],
    is ACCEPTED, so that spelling reports "The command has not failed!"
    and guards nothing; see negative 8's own note for the obligation it
    defers.  (ii) A bodyless [Fail Example], which fails for want of a
    proof rather than for the reason claimed: every [Fail Example] here
    carries the body [eq_refl].  (iii) An X = X tautology: negative 5
    compares [LeftAdjCat C D] with [Adj C D], two distinct constants
    both written APPLIED, so the command is refused at [eq_refl] and not
    at the statement, and negative 8 compares two different types.

    VERBATIM ERROR TAILS, as read from the sixteen stripped files:

      1.  (cannot unify "RAF_via C D" and "RightAdjointFunctor C D").
      2.  (cannot unify "LI_via C D" and
           "Incl ([D, C]) (LeftAdjSub C D)").
      3.  (cannot unify "fmap[SubToAdj C D ◯ AdjToSub C D] f" and "f").
      4.  (cannot unify "fmap[AdjToSub C D ◯ SubToAdj C D] f" and "f").
      5.  (cannot unify "LeftAdjCat C D" and "Adj C D").
      6.  (cannot unify "ch_obj (ch_canonical C D) x" and "x").
      7.  (cannot unify "conj_mate (adjobj_adj (F; q))
           (adjobj_adj (F; p)) nat_id ∙ conj_mate (adjobj_adj (F; p))
           (adjobj_adj (F; q)) nat_id" and "nat_id").
      8.  The term "RightAdjointFunctor C D" has type
          "(LeftAdjCat C D)^op ⟶ [C, D]" while it is expected to have
          type "LeftAdjCat C D ⟶ [C, D]".   [no "cannot unify" clause]
      9-13. (universe inconsistency: Cannot enforce cp = ch because
            ch < cp).
      14. (universe inconsistency: Cannot enforce ah = <fresh> because
          ah < bh <= <fresh>).
      15. (universe inconsistency: Cannot enforce bh = ah because
          ah < bh).
      16. (universe inconsistency: Cannot enforce ah = bh because
          ah < bh).

    RENAME SIMULATION.  Ten constants of Adjunction/Choice.v are named
    by a negative: [RAF_via], [RightAdjointFunctor], [LI_via],
    [LeftAdjSub], [SubToAdj], [AdjToSub], [LeftAdjCat], [ch_obj],
    [ch_canonical] and [HasRightAdjoint].  Each was renamed in a SCRATCH
    COPY of that file (never in place -- a whole-file rename is a no-op
    by construction and gives a false verdict), the copy recompiled
    under a scratch module name (rc=0 in all ten, so every rename was
    real), and this file recompiled against the copy.  10/10 broke it,
    EVERY ONE at a [Check] control line and NONE inside a
    [Fail].  Zero vacuous guards.  The DENOMINATOR is exactly the
    constants DECLARED IN THE TARGET that a negative names; the donors a
    negative also names -- [Opposite], [Subcategory], [Adj], [AdjObj],
    [Incl], [conj_mate], [adjobj_adj], [nat_id], and [Fun], which
    negatives 2, 11 and 15 reach through the [[_, _]] notation rather
    than by name -- are declared elsewhere and cannot be renamed in the
    target, so each is given a top-level [Check] guard instead.

    GUARD COVERAGE, measured rather than asserted.  Comment-stripping
    this file and splitting it into commands, the 17 [Fail] blocks
    mention 47 identifiers, of which 31 appear OUTSIDE every [Fail] --
    in the [Check] block below or in a control [Definition].  The
    sixteen that do not are exceptions by construction and nothing else:
    the two vernacular keywords [Fail] and [Example]; the four bound
    variables [F], [f], [p], [q]; the stdlib constructor [eq_refl]; the
    instrument's deliberately absent name; and the eight [Fail]
    command HEADS, which never enter the environment.

    MAKE TODO.  This file adds 36 hits to that target (1826 -> 1862,
    counted by leading "./path:"): the 17 refutation commands, plus 19
    lines of the prose above that name them.  That is the usual
    disclosed overshoot of a probe in this tree.  Adjunction/Choice.v
    itself contributes ZERO, measured with the target's own pattern
    anchored at that path.

--------
* (                                                                                                                                                 (                                                                                                             

重牢
,和,,和,和,和,和和,和,和,,和和,和和,和和,和 ,和 和 ,和 和 和和 ,和 和和和和和和和和  和和和 和 和和和 和 和和  和 和 和 和 和  和 和和 和 和   和   和      ,    和 和   和  和 和     和 和  和 和 和 和 和  和 和 和 和 和 和 和和 和   和 和 和 和  和  和 和 和    和      和和       和 和和 和和  和和 和 和    和 和 和           和 和  和        和   和    
业经 我知道了 拥有权利
两性平等  让 让  让 让 让  让  让 让 让 让  让 让 让  让 让 让 让 让 让 让 让 让 让 让 让 让 让 让 让 让  让 让 让 让 让 让  让 让 让 让 让 让  让  让 让 让 让 让 让 让 让 让 让 让 让 让  让 让 让 让 让 让 让 让 让  让  让  让 让 让 让 让 让 让 让 让  让 让 让 让 让 让 让  让 让  让  让 让 让 让 让 让  让 让 让 让 让  让 让 让 让 让 让 让 让 让  让 让 让 让 让  让 让 让 让  让 让 让 让 让 让  让 让 让 让  让 让 让 让 让 让 让  让 让    让  让 让 让 让     让  让 让  让 让 让 让 让  让   让 让 让 让 让 让 让 让 让 让 让 让   让  让   让   让 让 让   让 让 让 让  让   让 让   让  让 让  让 让 让    让    让   让  让   让     各自    每      通过        通过    通过          通过         通过     通过 通过 通过   通过  通过 通过  通过       通过    通过     通过   通过  通过   通过  通过      通过     通过  通过   通过  通过  通过   通过   通过   通过          通过      通过  通过  通过                                  通过         通过   通过         通过        通过 通过             通过                 通过         通过              通过      通过 
,      

以基于基于基于依据的基于基于基于基于基于基于依据的基于基于基于依据的基于基于基于基于基于基于基于基于基于基于基于基于基于依据的基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于基于
用它守护的恒定数重命名负数,所以
<\\\\\<\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ 其中的每个反驳
页机在轮机上

方法问题。而,,,,,,,,,,,,,,,,,,,,,,,, , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,  , , , , , , , , , , , , , , , ,  , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , 
用于字符的十八行字符, 只添加目标
你说什么实情是:
这条线 带短前缀的探测器会失败
其原因不曾衡量,这是FALSE PASS,所以,不是
員員, , , , , , , , , , , , ,  ,  ,                                                                                                                             ,                                                                                                 
... 她们SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS上SSSSSSSSSSSSSSSSSSSSSSSSS上SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS数SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS
证明了这一点, , , , , ), , , , , , ), , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ), , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,, , , , , , , , , , , , ,
和和和,和
暨

和工作人员 j 的 j 的 j 的 j 的 j 的 d 的 j 的 d 的 j 的 d 的 j 的 j 的 d 的 d 的 d 的 d 的 d 的 d 的 d  的 d 的 d 的 d 的 d       的  d     的 d 的 d                                                                                                                                             
( 的2个居民,没有宇宙条款;
(一一一一一,一一一一一一,一一一一一,一一一一一,一一一一一,一一一一,一一一一,一一一一,一一一一,一一一一,一一一一,一一一一,一一一,一一一,一一一,一一一,一一一,一一一,一一一,一一,一一一,一一,一一,一一,一一,一一,一一,一,一,一一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一,一
. . . . . . . . . . . . . . . . . . . . . .
,该错误结尾为“前后不一致:无法”
,,总共有,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,章,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,章,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,F,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,

17 [失效] 命令 = 1 仪器检查 + 16 底线
) 人) 。 。 。 。 。 。
水准
是一种是歧视:的术语
上 她们上都接受反式

以以以.以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以

哈三三三三三                                                   (                                                                                        (                                                                         (                                   
该,,,,,,,,,,,,,,,,,,,,.,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
并对其
微
不守什么,就看负8的本领
《 我们不能社会性别主流化《《公约》《公约》《公约》《公约》《公约《《公约》《公约》《《公约》《公约《公约》《《公约》《公约《公约》《公约《公约》《公约《公约《公约》《公约《公约《公约》《公约《 《公约《公约公约《公约《公约《公约《 《公约《公约《 《公约《公约《公约《公约《 《公约公约《 《公约《 《 《 《 《                                             鳌                                                                                                   
不良
限制因素                                                                                                                                                                                                                                                               
A. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .. . . ...........................................................................................................................................................................................
م者 她们者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者,者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者,者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者
10. 比较[左AdjCat C D]和[Adj C D],两个不同的常数
立
""""""""""""""""""""""""""""""""""""............................................................................................................................................................................................................................



(不能将"RAF via C D"和"右联拳C D"统一). 2. (不能统一“LI via C D”和
( ) ), ) ) , 输 输 输 呢 ), 输 输 呢 文 文 文 文 文 文 文 文 文 文 文 文 文, 其 文 文 文, 其 文 文 文, 其 文, 其 文 文, 其 文, 其   ,   其  ,   ,    ,    ,      ,   ,  ,   ,     ,   ,   ,   ,  ,   ,   ,  ,             , ,   ,            ,        ,                                              3. (不能将 "fmap [SubToAdj C D ◯ AdjToSub C D] f"和"f"合并).雌 ). ). ). ). ). ). f f f f f 5. (不能将"Left AdjCat C D"和"Adj C D"合并). 6. (不能将"ch obj(ch canonical C D) x"和"x"合并).。 。           
不同不同不同不同不同不同不同不同不同
طổ树(adjobj adj(F;p)) nat id * conj mate(adjobj adj(F;p))
体现了"nat-id"和"nat-id". 8. "RightAd UnitedFunctor C D"一词有以下类型:
“ص之间的平衡”
...,没有“不能统一”的条款]
专第收                                                                                              之  之                              之                         之                      之                             之                      之           之    之   之 
(单向不一致:无法执行 cp = ch 因为
,,, , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,  , ,  ,  ,  , , , , ,  , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,, , , , , , , , , , , , , , , , , , , 
者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者之者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于 , 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當于, 相當於 , 相當于, 相當于, 相當於, 相當于, , 相當於, , 相當於 , 相當于 , 相當於 , , 相當於 , 相當於 , 相當於 , 相當於 , 於 , , , 相當到到到來來來來來 , , , , 於 , , , 於 , , , , , 於是 , , , , 於 , , , , , 
16.(前后不一致:无法执行ah=bh,因为


全全全全全前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前的前前前前前前的前前前的前前前前前前前前前前前前前前前的前前前前前前前前的前前前前前前前的前前的前前前前的前前的的前的前的的的前的前前前前前前前前前前的前的前前前前前前前前前前的的的前前前前前前前前前的前前的前前的的的的的前前前前的前前前的的前前前前前前前前前的前前前前前前前的的的的的前的的前前前前前前前前前前前前的前前前前的前前的前前前前前前前的的的的前前前的 ,全全全全全全全全全全全全全全全全全全全全全前前前前前前前前前前前前前前前前前前的全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全全的全全全全全全全全全全全全全全全全全全全全前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前全前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前前的全前前前前前前前前前前前前前前前
[来宾:[RAF via]、[右联调 、[LI via],
各种各样增升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升升上上上上上上上上上上上上上上上上上上上上上上上上上上上下上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上上
[ [ch 和 和 [h 和
几句各项政策, 都用 , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,  , , , , , , , , , , , , , , 
由雌,,,,,,,,,,,,,,,,,,,,,,,由,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,由,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
一   资料                                                                                                                                                                                                                                                           
,的在在在在在的在在在的在在在的在在的在在在在的在在的在在在的在在的在在在的在在在在的在在在在的在在在在在在的在在在的在在在在在在在在在的在在在在在在在在在在在的在在在在在在在的在在在在在在在在在在的在在在在在在在在在在在在在的在在在在在在在在在在在的在在在在在在在在在在在的在在在在在在在在在在在在在在在的在在在在在在在在在在在在在在在在在在在在在在的在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在
3 333333333333333333333333333333333333333333333333333333333333333333333333333333 3333333333333333333333333333333333 33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333 33333333333333333333333333333333333333333333333333333333333333333333333333333333 33333333333333333333333333333333333333333333333333333333333333333333 333333333333333333333333333333333333333333333333333333333333333333
每个在[检查]控制线上,没有在a
的 [失败].  零空卫.
页
的就业情况; 捐助方a
负数 -- -- [对 [子类]、[Adj]、[AdjObj]、
t
倒数第2、第4和第4段;
、
, 。 。 。 。

,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,選,,,,,,,,,,,,,,,選,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,選,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,選,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,選,,,,,,,,選,,,,,,,,選,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,選,,,,,,,,,,,,,,,,,選,,,,,,,,,,,選,,,,,,選,,,,選選,,,選,,,,,,,,,,,選,,選,,,,,,,,,,選,,,,,,,,,,選,,,,,,選,,,,,,,,,,選,,,,,,,,,,,,,,選,,,,選,,,,,,,,,,,,選,,,,,,,,,選,選,,,選,,,選,,,,,選,,,,,,選,,,,選,,,選,選,,選,,,,,,,,,,,,,,,,,,
页文: 1
一类(,(,,,(,,,,,,,,(,,,,,(,,,,,,,,,,,,,,,,,,,,,,,(,,,,(,,,(,,,,,,,,,,,,,,,,(,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,(,,,,(,,,,,,,,(,,,,,(,,,,,,,(,,,,(,,,,,,,,(,,,,,,,,(,,,,,,,,,,,,(,,,(,,,,,,,,,,,,,,,,,(,,,,(,,,,(,,,,,,,(,,,,,,,,,,,,,,(,,,,,,,,(, 你应该,,,,,,,,,,,,,
实情对对和工作人员对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对中对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对
确认了
直接, --,,,,,, -- --, --,, -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --, -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --, -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
我想知道封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封 封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封封 封封封封封封封封
的的 的 的 的 的 的 的    的  的    的      的                   (         (              (         
乐器故意没有名称; 和 8 [虚 )  the  the八 F F F F ] ] ] ] ]  eight八  the ] ] ] ] ]  eight  eight  eight  eight  eight  eight  eight  eight  eight八  the  eight  eight  eight  eight  eight  eight  eight  eight  eight  eight8"  the  eight  eight8"下"下"下"下"下"下"下下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下"下""下"下"下"""""""""""""下""""""下"""下""""""""""""""""""下""""""""""""""""""""""
, , , , , , , , , , , , , ,  , , , , , , , , , , , , ,,, ,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,

,                                 ,                                  ,                                                                                                             
业经 .
报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告、报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告,报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告提交报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告报告
在这棵树上发现了一个探测器 附加/选择.v
则提供ZERO,
锚在这条路上。
*)

(**
** Instrument check

    The negatives below are only as good as the harness: a name that
    exists in no file of the tree must be refused.

--------
** 仪器检查

下面的否定项的有效性仅取决于线束：树中的任何文件中不存在的名称都必须被拒绝。
*)

Fail Check p397_no_such_constant_anywhere.

(**
** Guard coverage: every constant a negative names, outside a Fail

    Twenty-nine [Check]s.  Eighteen are DONORS declared elsewhere in the
    tree, which the rename simulation cannot reach, so the [Check] is
    their guard (nine of them are named by a negative).  The other
    eleven are target constants: the ten a negative names, which a
    rename of any of them breaks first, plus [RightAdjChoice].

--------
** 守卫覆盖：每个常量都是负名称，位于 Fail 之外

二十九个 [Check]。十八个是在树的其他地方声明的 DONORS，重命名模拟无法到达，所以 [Check] 是它们的守卫（其中九个被负名称命名）。另外十一个是目标常量：其中十个是负名称，对它们的任何重命名都会首先破坏它们，以及 [RightAdjChoice]。
*)

Check @RightAdjointFunctor.
Check @RAF_via.
Check @LI_via.
Check @LeftAdjSub.
Check @LeftAdjCat.
Check @SubToAdj.
Check @AdjToSub.
Check @ch_obj.
Check @ch_canonical.
Check @HasRightAdjoint.
Check @RightAdjChoice.
Check @Incl.
Check @Sub.
Check @Adj.
Check @AdjObj.
Check @Fun.
Check @Opposite.
Check @Opposite_Functor.
Check @Subcategory.
Check @conj_mate.
Check @adjobj_adj.
Check @adjobj_left.
Check @adjobj_right.
Check @nat_id.
Check @AdjForgetLeft.
Check @AdjForgetRight.
Check @fmap.
Check @Functor.
Check @Adjunction.

(**
** Section A: the seven CONVERSION boundaries, and the variance

    Every negative in this section sits beside the positive controls
    Adjunction/Choice.v already ships, so what each refutation locates
    is visible rather than asserted.

--------
** A部分：七个转换边界及其差异

    本部分的每一个负值都位于正控制旁边
    Adjunction/Choice.v 已经发布，因此每个反驳所定位的
    是可见的而非被声明的。
*)

Section Conversions.

Context (C D : Category).

(**
*** Negative 1 (CONVERSION): R is #395's forgetful functor
        transported, on both ACTIONS but not as a RECORD

    Both data fields agree at [eq_refl] -- the two controls immediately
    below are Adjunction/Choice.v's own [raf_obj_via] and [raf_map_via]
    -- so the difference is confined to the three [Functor] law fields,
    which [Compose] and [Program] rebuild as their own opaque proofs.
    Stripped, the error ends (cannot unify "RAF_via C D" and
    "RightAdjointFunctor C D").

--------
*** 负 1（转换）：R 是 #395 的遗忘函子，在两个操作上被传输，但不是作为记录

两个数据字段在 [eq_refl] 上一致——下面的两个控件是 Adjunction/Choice.v 自身的 [raf_obj_via] 和 [raf_map_via] ——所以差异限于三个 [Functor] 定律字段，[Compose] 和 [Program] 将其重建为自己的不透明证明。去掉后，错误终止（无法统一 "RAF_via C D" 和 "RightAdjointFunctor C D"）。
*)

Definition p397_raf_obj_control := raf_obj_via C D.
Definition p397_raf_map_control := raf_map_via C D.

Fail Example p397_raf_via_strict :
  RAF_via C D = RightAdjointFunctor C D := eq_refl.

(**
*** Negative 2 (CONVERSION): the same for the FIRST forgetful
        functor against the subcategory inclusion

    Again both actions agree at [eq_refl] ([incl_obj_via],
    [incl_map_via]).  Stripped, the error ends (cannot unify
    "LI_via C D" and "Incl ([D, C]) (LeftAdjSub C D)").

--------
*** 负二（转换）：对于针对子类别包含的第一个健忘函子也是相同的

同样，两种操作在 [eq_refl]（[incl_obj_via]，[incl_map_via]）处一致。剥离后，错误结束（无法统一“LI_via C D”和“Incl ([D, C]) (LeftAdjSub C D)”)。
*)

Definition p397_incl_obj_control := incl_obj_via C D.
Definition p397_incl_map_control := incl_map_via C D.

Fail Example p397_li_via_strict :
  LI_via C D = Incl ([D, C]) (LeftAdjSub C D) := eq_refl.

(**
*** Negative 3 (CONVERSION): the Adj-side round trip is not the
        identity on ARROWS

    The OBJECT round trip is [rt_adj_obj], at [eq_refl], which is what
    makes this statement well typed at all; the composite rebuilds
    [conj_right] as the mate of [conj_left], equal to the original only
    up to `≈`.  Stripped, the error ends (cannot unify
    "fmap[SubToAdj C D ◯ AdjToSub C D] f" and "f").

--------
*** 负 3（转换）：Adj 端的往返不是 ARROWS 上的恒等式

对象的往返是 [rt_adj_obj]，在 [eq_refl]，这正是使该语句完全类型正确的原因；复合函数将 [conj_right] 重建为 [conj_left] 的配对，仅在 `≈` 意义下等于原始值。简化后，错误结束（无法统一 "fmap[SubToAdj C D ◯ AdjToSub C D] f" 和 "f"）。
*)

Definition p397_rt_adj_obj_control := rt_adj_obj C D.

Fail Example p397_rt_adj_map_strict (x y : Adj C D) (f : x ~> y) :
  fmap[SubToAdj C D ◯ AdjToSub C D] f = f := eq_refl.

(**
*** Negative 4 (CONVERSION): nor is the S-side round trip

    Here the composite returns (`1 f; I) and stdlib [sigT] has no
    definitional eta (Lib/Foundation.v's [Set Primitive Projections]
    does not cover it), so this is not definitional even though [I] is
    the only inhabitant of [True].  Object round trip [rt_sub_obj] at
    [eq_refl] beside it.  Stripped, the error ends (cannot unify
    "fmap[AdjToSub C D ◯ SubToAdj C D] f" and "f").

--------
*** 负 4（转换）：S 侧的往返也不是如此

这里复合返回（`1 f; I`）和标准库 [sigT] 没有定义的 η（Lib/Foundation.v 的 [Set Primitive Projections] 并未覆盖它），因此即使 [I] 是 [True] 的唯一成员，这也不是定义性的。在 [eq_refl] 附近进行对象往返 [rt_sub_obj]。剥离后，错误结束（无法统一 "fmap[AdjToSub C D ◯ SubToAdj C D] f" 和 "f"）。
*)

Definition p397_rt_sub_obj_control := rt_sub_obj C D.

Fail Example p397_rt_sub_map_strict (x y : LeftAdjCat C D) (f : x ~> y) :
  fmap[AdjToSub C D ◯ SubToAdj C D] f = f := eq_refl.

(**
*** Negative 5 (CONVERSION): S and #395's Adj are DIFFERENT
        categories

    This is the negative that keeps [SubAdj_strict_iso] from being
    vacuous: it is an ISOMORPHISM OF CATEGORIES between two categories
    that are not the same term, S's hom being {sigma & True} and [Adj]'s
    the record [ConjPair].  The two controls beside it are the pivot
    [leftadj_obj] -- the OBJECT types DO agree, on the nose -- and the
    isomorphism itself.  Both sides are written applied, so the command
    is refused at [eq_refl] and not at the statement, and it is not an
    X = X tautology: the two heads are distinct constants.  Stripped,
    the error ends (cannot unify "LeftAdjCat C D" and "Adj C D").

--------
*** 负 5（转换）：S 和 #395 的 Adj 属于不同的类别

这是阻止 [SubAdj_strict_iso] 变得空洞的负数：它是两个类别之间的类别同构，它们不是相同的项，S 的 hom 是 {sigma & True}，[Adj] 的 hom 是记录 [ConjPair]。它旁边的两个控制是枢轴 [leftadj_obj]——对象类型确实完全一致——以及同构本身。两边都写为应用形式，所以命令在 [eq_refl] 被拒绝，而不是在语句处，而且它不是 X = X 的同义反复：两个头部是不同的常量。简化后，错误结束（无法统一“LeftAdjCat C D”和“Adj C D”）。
*)

Definition p397_leftadj_obj_control := leftadj_obj C D.
Definition p397_strict_iso_control := SubAdj_strict_iso C D.

Fail Example p397_cats_strict : LeftAdjCat C D = Adj C D := eq_refl.

(**
*** Negative 6 (CONVERSION): the canonical choice returns the same
        object only up to [sigT] eta

    All THREE projections return on the nose ([ch_canonical_left],
    [ch_canonical_right], [ch_canonical_adj]), so what is missing is
    exactly the eta rule for the stdlib pair, not any content.
    Stripped, the error ends (cannot unify
    "ch_obj (ch_canonical C D) x" and "x").

--------
*** 负 6（转换）：典型选择返回相同的对象，仅到 [sigT] eta 为止

所有三个投影都精确返回（[ch_canonical_left]、[ch_canonical_right]、[ch_canonical_adj]），所以缺失的正是 stdlib pair 的 eta 规则，而不是任何内容。去掉后，错误结束（无法统一 "ch_obj (ch_canonical C D) x" 和 "x"）。
*)

Definition p397_ch_left_control := ch_canonical_left C D.
Definition p397_ch_right_control := ch_canonical_right C D.
Definition p397_ch_adj_control := ch_canonical_adj C D.

Fail Example p397_ch_canonical_strict (x : LeftAdjCat C D) :
  ch_obj (ch_canonical C D) x = (x : AdjObj C D) := eq_refl.

(**
*** Negative 7 (CONVERSION): the inverse law of the membership
        isomorphism is `≈` and not [eq_refl]

    The composite of the two mates of the identity is [nat_id] only
    after [conj_mate_compose], one identity cancellation and
    [conj_mate_id]; the `≈` form is Adjunction/Choice.v's
    [raf_choice_inverse], the control below.  Stripped, the error ends
    (cannot unify "conj_mate (adjobj_adj (F; q)) (adjobj_adj (F; p))
    nat_id ∙ conj_mate (adjobj_adj (F; p)) (adjobj_adj (F; q)) nat_id"
    and "nat_id").

--------
*** 负 7（转换）：成员同构的逆定律是 `≈`，而不是 [eq_refl]

两个恒等的伴随复合在 [conj_mate_compose] 之后、一次恒等消去和 [conj_mate_id] 之后才是 [nat_id]；`≈` 形式是 Adjunction/Choice.v 的 [raf_choice_inverse]，控制在下方。去掉后，错误结束（无法统一 "conj_mate (adjobj_adj (F; q)) (adjobj_adj (F; p)) nat_id ∙ conj_mate (adjobj_adj (F; p)) (adjobj_adj (F; q)) nat_id" 和 "nat_id"）。
*)

Definition p397_inverse_weak_control := raf_choice_inverse C D.
Definition p397_choice_iso_control := choice_iso_in_Sub C D.
Definition p397_choice_to_control := raf_choice_iso_to C D.
Definition p397_choice_from_control := raf_choice_iso_from C D.

Fail Example p397_choice_inverse_strict
     (F : D ⟶ C) (p q : HasRightAdjoint F) :
  conj_mate (adjobj_adj ((F; q) : AdjObj C D))
            (adjobj_adj ((F; p) : AdjObj C D)) nat_id
    ∙ conj_mate (adjobj_adj ((F; p) : AdjObj C D))
                (adjobj_adj ((F; q) : AdjObj C D)) nat_id
  = nat_id := eq_refl.

(**
*** Negative 8 (TYPING): R is CONTRAVARIANT

    Mac Lane's R is a functor S^op -> X^A, and the delivered constant
    has exactly that type.  The control immediately below ascribes the
    SAME term at the contravariant type and is ACCEPTED, so the negative
    is discriminating and is not an X = X tautology.  Stripped, the
    error is a plain has-type mismatch with NO "cannot unify" clause and
    no universe clause.

    IT IS WRITTEN AS A [Fail Definition] AND NEVER AS A [Fail Program
    Definition], AND THAT IS MEASURED ON THIS EXACT STATEMENT rather
    than inferred: with [Program], the very same line is ACCEPTED, so
    [Fail Program Definition] reports "The command has not failed!" and
    pins nothing -- a FALSE PASS.  The mechanism was read off by
    stripping the [Fail] and asking [Obligations]: [Program] turns the
    variance mismatch into

      Obligation 1 of hazA: (((LeftAdjCat C D)^op)%category
                              = LeftAdjCat C D).

    a LEIBNIZ EQUALITY OF CATEGORIES, and the breakdown surfaces only at
    the section close, as "Unsolved obligations when closing section".

--------
*** 负 8（输入）：R 是逆变的

Mac Lane 的 R 是一个函子 S^op -> X^A，所传递的常量恰好具有该类型。下面的控制立即将相同的项标注为逆变类型并被接受，所以该负号是区分性的，而不是 X = X 的同义反复。简化后，错误只是一个普通的类型不匹配，没有“无法统一”条款，也没有宇宙条款。

它被写为 [Fail Definition]，而从不写为 [Fail Program Definition]，并且这是在这个确切声明上测量的，而不是推断的：使用 [Program]，相同的行被接受，所以 [Fail Program Definition] 报告“命令未失败！”并且没有固定任何内容——这是一个错误的通过。通过去掉 [Fail] 并询问 [Obligations]，可以读出该机制：[Program] 将方差不匹配转化为

hazA 的义务 1：(((LeftAdjCat C D)^op)%category = LeftAdjCat C D)。

类别的莱布尼茨等式，并且分解只在节关闭时出现，显示为“关闭节时的未解决义务”。
*)

Definition p397_raf_type_control : Opposite (LeftAdjCat C D) ⟶ [C, D] :=
  RightAdjointFunctor C D.

Fail Definition p397_raf_covariant :
  LeftAdjCat C D ⟶ [C, D] := RightAdjointFunctor C D.

(*
Two further controls this section names: the two variance readbacks
   that pin the arrow action's orientation, which no [Fail] can.

--------
本节还命名了两个进一步的控制：两个方差回读，它们固定箭头动作的方向，而没有 [Fail] 可以做到。
*)
Definition p397_variance_control := raf_fmap_variance C D.
Definition p397_id_control := raf_id_is_conj_mate_id C D.

End Conversions.

(**
** Section B: hom = proof, FOUR independent donors

    Every constant of Adjunction/Choice.v is over categories whose hom
    and proof universes coincide, expressed by REUSING the level
    variable in the BINDER while NOT ONE of the 79 constraint blocks
    carries such an equation.  That identification is INHERITED, and
    four donors are separated below, each sufficient ALONE and each with
    no constant of the target in its command.

    [Functor] is NOT a donor, and the controls prove it in BOTH
    directions: [Du ⟶ Cu] and [Cu ⟶ Du] are both ACCEPTED at the very
    levels where all five negatives are refused.  Negative 12 is the
    sharpest of the five for that reason -- its error is reported ON
    [Fq], displaying two [@Functor] instances, the one [Fq] has at
    @{co ch cp co ch cp} against the one [Adjunction] demands, whose hom
    and proof levels are the SAME variable -- so what is refused there
    is [Adjunction]'s own shape and not [Functor].

--------
** B部分：hom = 证明，四个独立供体

Adjunction/Choice.v 的每个常量都作用于同态和证明宇宙重合的范畴，通过在绑定器中重用级别变量来表达，而 79 个约束块中没有一个包含这样的方程。该识别是继承下来的，下面分离了四个捐赠者，每个单独足够，并且每个在其命令中都没有目标常量。

[Functor] 不是供体，且对照在两个方向上都证明了这一点：[Du ⟶ Cu] 和 [Cu ⟶ Du] 都在所有五个阴性样本被拒绝的同一水平上被接受。阴性样本 12 因此是五个中最尖锐的——其错误在 [Fq] 上报告，显示两个 [@Functor] 实例，其中一个 [Fq] 在 @{co ch cp co ch cp} 上对比另一个 [Adjunction] 所要求的，其 hom 和 proof 水平是同一个变量——所以在那里被拒绝的是 [Adjunction] 自身的形状，而不是 [Functor]。
*)

Section HomEqualsProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du : Category@{co ch cp}).
Context (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du).

(* CONTROLS at the declared levels. / 在申报水平的控制。 *)
Check Cu.
Check Du.
Check Fq.
Check Uq.
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (fun (x y : Cu) (g g' : x ~> y) => g ≈ g').
Check (Du ⟶ Cu).
Check (Cu ⟶ Du).

(**
*** Negative 9 (FORMABILITY): [Opposite] alone

    No subcategory, no functor category, no adjunction and no constant
    of the target in the command.  Stripped, the error ends "universe
    inconsistency: Cannot enforce cp = ch because ch < cp".

--------
*** 负 9（可形成性）：仅 [Opposite]

    在命令中目标没有子类别、没有函子类别、没有结合和没有常量。剥离后，错误结束为“宇宙不一致：无法强制 cp = ch 因为 ch < cp”。
*)

Fail Check (Opposite Cu).

(**
*** Negative 10 (FORMABILITY): [Subcategory] alone

    Stripped, same tail.

--------
*** 负10（成形性）：仅 [Subcategory]

    剥离，相同尾部。
*)

Fail Check (Subcategory Cu).

(**
*** Negative 11 (FORMABILITY): the functor CATEGORY alone

    [Du ⟶ Cu] is accepted above, so this is [Fun]'s own shape and not
    [Functor]'s.  Stripped, same tail, reported on [Du].

--------
*** 负11（可形成性）：仅函数范畴

    上述 [Du ⟶ Cu] 被接受，所以这是 [Fun] 本身的形态，而不是 [Functor] 的。去掉后，尾部相同，在 [Du] 上报告。
*)

Fail Check ([Du, Cu]).

(**
*** Negative 12 (FORMABILITY): [Adjunction] alone

    Both functors are formable at these levels ([Check Fq], [Check Uq]
    above), so what is refused is the adjunction.  Stripped, same tail,
    reported ON [Fq] with the two [@Functor] instances displayed.

--------
*** 负12（可形成性）：仅 [Adjunction]

    在这些水平上两个函子都是可形成的（[Check Fq]、[Check Uq] 以上），所以被拒绝的是附加。剥离后，相同的尾部，在 [Fq] 上报告，并显示两个 [@Functor] 实例。
*)

Fail Check (Fq ⊣ Uq).

(**
*** Negative 13 (FORMABILITY): the delivered functor inherits it

    This is the target's own rejection; it is NOT independent of the
    four above (its body contains all of them), and is pinned so that a
    change lifting the pin at any donor is visible here.  Stripped,
    same tail.

--------
*** 负13（可成形性）：传递的函子继承它

    这是目标自身的拒绝；它并不独立于上述四个（它的主体包含了所有这些），并且被固定，以便任何捐赠者处解除固定的变化在这里可见。剥离后，相同的尾部。
*)

Fail Check (RightAdjointFunctor Cu Du).

End HomEqualsProof.

(**
** Section C: where the two hom levels are identified

    Adjunction/Choice.v's profile is [C : Category@{o1 h h}] and
    [D : Category@{o2 h h}] -- ONE level variable in all FOUR
    hom-and-proof slots, with both OBJECT universes free.  The collapse
    of C's hom level with D's needs no adjunction and no record: the
    mere presence of functors in BOTH directions forces it, which is
    exactly the shape of an object of S (a left adjoint [D ⟶ C] paired
    with a right adjoint [C ⟶ D]), and the functor CATEGORY forces it
    independently.  The control shows the functor in the direction that
    IS formable.

--------
** C节：识别出两个同态层次的地方

Adjunction/Choice.v 的配置文件是 [C : Category@{o1 h h}] 和 [D : Category@{o2 h h}]——在所有四个同态与证明槽中都是一个层次变量，并且两个对象宇宙都是自由的。C 的同态层次与 D 的合并不需要附加，也不需要记录：仅仅两个方向上函子存在就强制了它，这正是 S 的一个对象的形状（一个左邻接 [D ⟶ C] 与一个右邻接 [C ⟶ D] 配对），而函子 CATEGORY 则独立地强制了它。控制显示了可以形成的方向上的函子。
*)

Section TwoHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* CONTROLS at the declared levels. / 在申报水平的控制。 *)
Check Au.
Check Bu.
Check (fun x y : Au => x ~{Au}~> y).
Check (fun x y : Bu => x ~{Bu}~> y).
Check (Au ⟶ Bu).

(**
*** Negative 14 (FORMABILITY): the reverse functor

    Stripped, the error ends "universe inconsistency: Cannot enforce
    ah = <fresh> because ah < bh <= <fresh>".

--------
*** 负 14（可成形性）：逆函子

剥离后，错误结束于“宇宙不一致：无法强制执行 ah = <fresh> 因为 ah < bh <= <fresh>”。
*)

Fail Check (Bu ⟶ Au).

(**
*** Negative 15 (FORMABILITY): the functor category, independently

    No functor pair in the command.  Stripped, the error ends "universe
    inconsistency: Cannot enforce bh = ah because ah < bh".

--------
*** 负 15（可塑性）：函子范畴，独立地

命令中没有函子对。删除后，错误结尾为“宇宙不一致：无法强制 bh = ah 因为 ah < bh”
*)

Fail Check ([Au, Bu]).

(**
*** Negative 16 (FORMABILITY): the delivered functor inherits it

    Not independent of 14 and 15; pinned so a change at either donor is
    visible here.  Stripped, the error ends "universe inconsistency:
    Cannot enforce ah = bh because ah < bh".

--------
*** 负16（可形成性）：传递的函子继承了它

    不独立于14和15；固定，因此在任一供体的更改在这里可见。剥离后，错误结束为“宇宙不一致：无法强制执行 ah = bh，因为 ah < bh”。
*)

Fail Check (RightAdjointFunctor Bu Au).

End TwoHomLevels.

(**
** Section D: the non-vacuity witness, named outside every Fail

    Adjunction/Choice.v's section (E) inhabits S at [C = D = _2] with a
    non-identity adjunction and shows the subcategory PROPER.  Nothing
    here is refuted; the block exists so that a rename of any of these
    breaks this file too, and so that the reader can see the witness is
    named rather than described.

--------
** D部分：非空证人，在每个Fail之外命名

    Adjunction/Choice.v的(E)部分在S的[C = D = _2]处存在，带有一个非同一的附加，并显示子类别PROPER。这里没有任何内容被驳斥；该块存在是为了使对其中任何一个的重命名也会破坏此文件，以及为了让读者看到证人是被命名而不是被描述的。
*)

Definition p397_two_object := two_left_adjoint_object.
Definition p397_two_value := two_raf_value.
Definition p397_two_proper := two_left_adjoint_proper.
Definition p397_two_differ := two_const_functors_differ.
Definition p397_two_not_id := two_left_adjoint_not_identity.
Definition p397_two_adj := two_const_adj.
Definition p397_independence := choice_independence.
Definition p397_equivalence := SubToAdj_Equivalence.
Definition p397_full := LeftAdjSub_Full.
