(**
* Probe: the measured boundaries of the two algebraic limit files
      Instance/Ab/Limit.v and Instance/Rng/Limit.v (issue #443)

    Sibling of Test/ProbeGrpLimit411.v, which pins the same ground for
    Instance/Grp/Limit.v — the group template both targets transpose.  Two
    things make a probe worth writing for the transpositions rather than
    letting the group one stand for all three.

    FIRST, THE HEADLINE SENTENCE IS "THE LIFTED STRUCTURE IS THE POINTWISE
    ONE", and at [Ab] and [Rng] that sentence has three and five operations
    in it against the group's three.  Both targets ship the positive halves
    as [Example]s of their own, so those guard themselves; what they cannot
    guard from inside is that the positive halves are SHARP.  Sections A and
    B restate each readback beside the obvious wrong statement — arguments
    swapped, one operation written where another belongs, negation written
    as the identity — so that the [eq_refl]s are known to be saying
    something.  The two swap refutations are the interesting pair: [Ab]'s
    addition IS commutative and [Rng]'s multiplication need not be, yet
    BOTH swaps are refused, which locates the readbacks at conversion and
    not at [≈].

    SECOND, [Ab] now carries TWO DISTINCT TERMS of type
    [ContinuousFunctor Ab_Forget] — Instance/Ab/FreeNotContinuous.v's
    [Ab_Forget_Continuous], which is RAPL applied to the free/forgetful
    adjunction, and the new [Ab_Forget_creates_continuous], which comes from
    limit creation.  Since they share a type, the sharp question is whether
    they share a TERM, and section F answers it: they do not (N15), the
    apex-only corollary descends from the creation one and not from the
    RAPL one (N16), and each is read back to the constant it is built from
    at [eq_refl].  That is what makes the new one worth declaring, and it is
    the whole reason the [Ab] file exists.

    KINDS, read off the messages actually produced rather than guessed, by
    the convention Test/ProbeGrpLimit411.v states in terms: a TYPE negative
    is a has-type mismatch with NO [cannot unify] clause, and a CONVERSION
    negative is the same mismatch CARRYING one.  Measured that way the
    twenty-five split NAME-ABSENCE (I1, N17, N18, N21) four, TYPE (I2, I3,
    N8) three, CONVERSION (N1–N7, N9–N16, N19, N20, N22) eighteen.  None of
    the twenty-five mentions a universe.

    ONE LABEL DISAGREES WITH A SIBLING PROBE, AND AN EARLIER REVISION OF
    THIS PARAGRAPH EXPLAINED THE DISAGREEMENT WRONGLY.
    Test/ProbeGrpFreeAFT442.v labels its N6 and N7 — the [Grp] forms of N11
    and N12 below — TYPE; stripped here, the [Ab] and [Rng] forms carry a
    [cannot unify] clause, so by 411's convention they are CONVERSION, and
    they are labelled so below.  That revision said "the commands differ
    from 442's only in the category".  They do not: 442's N6
    (Test/ProbeGrpFreeAFT442.v) passes FOUR arguments, including its
    solution set, while N11 and N12 below pass THREE and stop at the third.
    And the [cannot unify] clause is import-sensitive in any case (see
    section E), so its presence or absence is not a fact about the
    categories.  What is common to all of them, and is the whole content of
    the refutation, is the STABLE head: [ContinuousFunctor] does not ascribe
    where [PreservesImageLimit] is expected.

    Each was stripped ONE AT A TIME in a copy of this WHOLE file — not a
    preamble-plus-command scratch, which would drop the [Section]s'
    [Context] and the two locally built oracles and refuse for a reason
    unrelated to the claim — compiled alone, and its whole error read.  All
    twenty-five are refused, and each error lands inside the span of the
    command that was stripped.

    Every constant a refutation names also appears outside every refutation
    — section I is the guard block, and several appear in a control as well
    — so a rename breaks this file loudly instead of turning a refutation
    vacuously green.  Measured mechanically: 77 identifiers occur inside a
    refutation and 57 also occur outside every one, the twenty exceptions
    being exhaustively the keyword itself, the fifteen names a refutation
    DECLARES (which never enter the environment) and the four that are
    meant to be ABSENT — [p443_absent_name], [Ab_Forget_continuous],
    [Rng_Forget_Continuous] and [CMon_Complete].  Rename-simulated 6/6 over
    the load-bearing constants — [Ab_Complete],
    [Ab_Forget_creates_continuous], [Ab_Forget_reflects_limits],
    [Ab_Forget_Continuous], [Rng_Forget_continuous] and
    [Rng_Forget_creates_limits] — each rename breaking this file at a
    POSITIVE site and never inside a refutation, which is the property that
    matters.  Five break at a [Check] or an [Example]; the sixth,
    [Rng_Forget_creates_limits], breaks inside the [Definition]
    [Rng_ConeSet_Complete] (measured, not assumed — an earlier revision of
    this sentence said all six land at a [Check] or an [Example]).

    The import list is the union of the two targets' lists IN FULL, plus
    the two targets, plus five files the refutations and their controls
    need — Adjunction/GAFT.v and Construction/Comma/Creation.v for section
    E, and Adjunction/Continuity.v, Instance/Ab/Free.v and
    Instance/Ab/FreeNotContinuous.v for section F's second term — and one
    that nothing needs in order to typecheck, Theory/Adjunction.v:
    measured, this file compiles without it, and it is kept only so that
    section E's controls print [F ⊣ Ab_Forget] rather than
    [Adjunction.Adjunction F Ab_Forget].  Dropping Instance/Ab/Free.v, by
    contrast, was measured to leave [free_ab_adjunction] with no binding at
    section F's second readback.

    WHAT THIS PROBE DOES NOT PIN.  No universe boundary: unlike
    Test/ProbeGrpLimit411.v's N1 and N2, nothing here binds a shape below
    [Sets]' carrier universe, because that boundary belongs to
    [IsALimit] and to the generic [Sets] section, which both targets
    duplicate character-for-character from the group file and which 411
    already pins.  Nothing here measures the duplication itself.  No
    colimit, no cocompleteness, no monadicity, no comparison with
    Instance/Rng/Zp.v's [Zp_limit] — all four are on the targets' own
    NOT-DELIVERED lists and none acquires a probe here.  And no GAFT
    APPLICATION is built at either category: section E pins only that the
    hypothesis a consumer would reach for does not ascribe, which is the
    correction the [Ab] header already carries in prose.

--------
* 49 没事,, 你说什么,各式各式各式,和曲, 诠确实是,各式,以一种 太,各式各章,各式各章,各式各章,各式各章,各式各章,各章,各式各章,各式各章,各式各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,各章,,各章,各章,各章,各章,各章,各章, 让,各章,各章,各章,各,各章,各章,各章,各章,各章,各,,各章,,各章,,各竺,各章,各章,各章,各,各,,,各,委员会,cc,各,各,各,各,,各,各,各,,,,,各,,,,,,,,,,,,,,,,,各,,各,各,,,,,,,,,,
璞. (第443号案) 14月5月5月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月5月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月4月

的一份.... . .
、、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、  、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 两个
与政府                                                           ,                                                                                           
让三人一号代表三人

(一九九一年一月一日) (一九九九年一月一日)
, , ,, , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,                                                                                                                    
本 本 本                                                                                                                                                                           本             本                                                                      本 本                                                                                                                                                             
你肯定或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或或
通过谈判可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可可
保护他们中的的的的的的的的的的的的的的的的的的的的,的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的,的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的
的对他们的第第第第第第第第第第第第第第第第第第第第第第第第第和第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第九第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第九第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第第(第第第第第第第第第第第第第第第第第第第第
你还好吧
,的是,是是的的和和和是是是的的的,,,是是,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,的,,,,,,的,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
(
第

呐指号,指指号
mà ...

,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,2,2,2,2,2,3,2,2,2,3,2,2,2,2,2,2,2,2,2,2,2
从一开始就
也 也
绮,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,中,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
实情资料                                        
页
最高, 我爱的必然结果来自创造者 而不是来自创造者
. -          ,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,.,,,,,,,,,,,,,,,,,,,,,,,,,,,,,.,,,,,,,,,,,,,,.,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,.,,,,,,,,,,,,,,,,,,,,,,,.,,,,,,,,,,,,,,,,,,,,,,,,,,,.,,
备  备 
各种各样                                                                                                                                                                                                                                                               

时驴时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时

在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在在
的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的
你这样衡量

,景大,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,, 没有
实情 ,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,

م各方当事人                                                                         , ,          ,       ,         ,   ,                 ,            ,   ,          ,                          ,                 ,                               ,                      
本段对损失作了解释。 )
那就是限制,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,, ,,,,,,,,,,,,,,,,,, , , ,,,,,,,,, ,, ,,,,,,,,,,,, ,,,,, ,,,,, , ,,, ,  ,, ,, , , ,  ,  ,,,,,,,,,,,  ,,,,, ,  , , ,,,  ,  ,  ,, ,   ,              ,  , ,       ,    ,,,,        ,, ,    ,   ,  , ,    ,   ,  ,  ,  , 
各种各样
(国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国家国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国国
,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,包括,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
的的                                                              ,                                                                                                                ,                                                                              的,                                                                                        ,                                                          ,                                                                                                          
(Test/ ProbeGrpFreeAFT442.v)通过Four辩词,包括其
是是是是是.是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是,是是是是是是是是是,是是是是是是是是是,是是是是是是是是是是是是是是,是是是是是是是是是是,是是是是是是,是是是是是是是,是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是是,是是是是是是是是是,是是是是是是是是是是是是是是是是是是是,,是是是是是是是是,,是是是是是是 在任何情况下,[不能统一]条款都对进口敏感(见
E节),因此,它的存在或不存在并不是事实。

,
我们现在为女性   来                                                                                                                                                                                                                                                          
的.的的的的的的的的的的的的的的的的的的的的的的的的"的的的的""的""的""""的""""""""""""的"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

序言加命令划痕,从而减少[节]
,

三:从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从从 中 中 中 中经经经从从从从从从从从从从从从从从从 从从从从  从  这一 的从 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、 、、 、 、 、 、 、 、 、 、 、、、 、 、、、 、 、 、、 、 、 、、、、 、 、 、 、 、、 、、、、、、 、 、 、、、、、、 、、、、、
/确实是//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

甚为,,对对对对对对对对对对对对对对对对对对对,对对对对对对对对对对对对对对对对对对对对对对对对对,对对对对,对对对对对,对对对对对对,,对对对对对对,对对对对对对对对对对的,对对对对对对对对对,对对对对对对对对对对对对对对,,对对对对对对对对对对对对对对对对对对对对对对,对对对对对对对对对对对对对对对,对,对对对对对对对对对对,对对对对对对对对对对对对对对对对对对对对对对,对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对对,对对对对对对,对对,,对对,对对对对对对对对对对对对对

。 。 。
,                                                                                                                                   向                                   ,                                 向                                    ,     ,        , 
所
我们是人同人同人同人同人同人同人同人同人同人,二十人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同人同.
当然خ                                                                一个                                                                                                         一个                                                                                     
现在我们这几个人 , , , ,, , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,  , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , 
有望 上 上 .
[Rng forget continuive]和 [CMon complete] (英语).
重命名模拟 6/6 完毕
作为一种负载的常数,
),[Ab Forget creets Continents],[Ab Forget Reflects],[Ab Forget Reflects],[Ab Forget Reflects]],[Ab F],[Ab F],[Ab F],[Ab F],[Ab Forget Reflects]],[Ab F],[Ab F],[Ab F],[Ab F],[Ab F],[Ab F],[(Ab F],[Ab F],[Ab F],[Ab],[Ab],[Ab F],[Ab],[Ab],[A],[Ab],[Ab],[Ab],[Ab],[A],[Ab],[Ab],[A],[Ab]

之之之之之之者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者也者者者者者者者者者者者者者者者者者者者也者者者者者者者者者者者者者者者者者者者者者者者者者者者者者之者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者之者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者者
积极地点 永远不要在 反驳,这是财产

在[[查]或[例]时休息五次;第六,
按照联合国前..............................................................................................................................................................................................................................................................
你说什么. . , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , : , , , , , , , , , , , , , , , , , , , , , , , , , , : , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , : , , , , , , , , , , , , , , , , , , , , , , , , , ,
你说什么?

的的的的,的,,,,,,,,,,的,,,,的,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
ụ 兩兩兩兩兩兩兩 兩 兩 兩 兩 兩 兩  兩 兩 中  兩     中                                                                                                                 (                                                                                                          
安理会合..............................................................................................................................................................................................................................................................
、
本
我刚已已未需输入
. 页    
以 我们是以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以之以以以以以以以之以之以以以以以以以之以以以以以以以以以以之以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以以之以以以以以以以以以以以以以以以以以以以以以以以以以之以以以以以以以以以以以之以以以以以以之以以以以以以以以以以以以以以以以以以以以以以以以以以以之以以以以以以以以以以以以以以以以以之以之以以以之以之之以以之以之之以以以以以以之以以之以以以以之以以以以之以之以之以以以以以之以以以以以
进行再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再再的再再再再再的再再再的再再的再再的再再的再的再再的再再的再的再的再的的會的再的再的會的再的會的再的會的會的會的會的會的會的的的會的的會的會的會的會的的會的的會的的會的的會的的的會的的的的會的會的的會的的的的的的會的.的的的的的的的的的的會的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的.的的.的.的的的的的的.的的的的的的的的的.的.的.的.的的.的.的.的.的.的.的.的.的
Subject[标. maximum, Ab Forget] (英语).
,,,,,,,,,,,,,,,,,,,,,,, ,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,经验和,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,, ,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,, ,,,,,
真高兴制式
。。。 。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。

这证明什么不 pin。 无宇宙边界: 不同
的的N1和N2,这里没有绑定以下的形状
系系系系系系系系系系系系系系系
,((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((,((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((,((((((((((((((((((((
者,                                                                                                                        ,                          ,                                                                                                          
—[
没有

的  S S         蟑         小心                                                                               他会                          )                                                                                                                               
去,,,,,,,,的,,,,,的,,,,的,,的,的的放的,的放的,的放的的放的放的放的放的放放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放放的放的放的放的放的放的放的放的放的放放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放的放
没有GAFT
E节的标点符号仅指
的视情况م的发展的寄的的的的发展的的的的的的敬的的的的的的的的的的的的的的的的的的的的的的的的的的的发展的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的直播的 各位的的的的的的 希望的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的
校对:Portnoy
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Ab.FreeNotContinuous.

Generalizable All Variables.

(** ** Instruments / ** 乐器 *)

(*
I1 NAME-ABSENCE: the refutation keyword is live.  If the harness were
   reporting refusals as successes, or the reverse, this line would say
   so.

--------
I1 NAME-ABSENCE: 反驳关键字有效。如果测试工具将拒绝报告为成功，或者相反，这一行会说明。
*)

Fail Check p443_absent_name.

(*
I2 TYPE: elaboration is really happening.  This is the deliberately
   ill-typed variant of [ab_complete_leg], which DOES hold (the control
   sits beside it in section A): the leg of the created cone is a
   homomorphism of abelian groups, so comparing it with a map of setoids
   is a type error and not a conversion one.  [cmon_map] in the control is
   load-bearing.

--------
I2 类型：详细说明确实正在发生。这是 [ab_complete_leg] 的故意类型错误变体，它确实成立（控制在 A 节中与它相邻）：所创建圆锥的边是阿贝尔群的同态，因此将其与集合论映射进行比较是类型错误，而不是转换错误。控制中的 [cmon_map] 是承重的。
*)

Fail Example p443_i2 {J : Category} (K : J ⟶ Ab) (d : J) :
  cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(*
I3 TYPE: the same instrument on the other target, at the carrier rather
   than at a leg.  [rng_complete_carrier] holds with [rig_setoid] applied;
   without it the two sides are a ring and a setoid.

--------
I3 类型：相同的仪器在另一个目标上，位于载体而不是在一条腿上。[rng_complete_carrier] 在应用 [rig_setoid] 时成立；如果没有它，双方就是一个环和一个集合。
*)

Fail Example p443_i3 {J : Category} (K : J ⟶ Rng) :
  vertex_obj[Rng_Complete J K] = Sets_limit_obj (Rng_Forget ◯ K) := eq_refl.

(**
** A: at [Ab] the lifted structure is the pointwise one, and sharply

    Positive readbacks at an ARBITRARY shape and an ARBITRARY diagram, each
    beside the wrong statement it excludes.  The positives restate the
    target's own [ab_complete_*] [Example]s so that each refutation has its
    discriminating partner in view.

--------
** A：在 [Ab]，提升的结构是逐点的，而且非常

    在任意形状和任意图表上的正向回读，每一个都在其排除的错误陈述旁边。正向内容重述了目标自身的 [ab_complete_*] [Example]，以便每一个反驳都有其可辨认的对应物在视野中。
*)

Section AbPointwise.

Context {J : Category}.
Context (K : J ⟶ Ab).

(* control: the carrier / 控制：承运人 *)
Example p443_ab_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

(* control: the leg, with the coercion I2 removes / 控制：腿，被强制 I2 移除 *)
Example p443_ab_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(* control: the addition / 控制：增加 *)
Example p443_ab_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

(*
N1 CONVERSION: ...and the arguments are in that order on the nose.  The
   swapped statement is TRUE up to [≈] — [cmon_plus_comm] is a field of
   [CMonObject] and the target proves [alim_comm] for the lifted structure
   — so what this refutation locates is the LEVEL of the readback: the
   positive above holds by conversion, and commutativity does not.

--------
N1 转换：……而且参数正好按那个顺序排列。交换后的语句在 [≈] 之前为真——[cmon_plus_comm] 是 [CMonObject] 的一个字段，并且该目标为提升的结构证明了 [alim_comm]——因此这个反驳所定位的是回读的级别：上述正向通过转换成立，而交换律则不成立。
*)

Fail Example p443_n1
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the zero / 控制：零 *)
Example p443_ab_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

(*
N3 CONVERSION: the created zero is the coordinatewise zero and not its
   negation.  [ab_neg (K d) (cmon_zero (K d)) ≈ cmon_zero (K d)] is an
   ordinary consequence of [ab_neg_left]; it is not a conversion, so one
   operation cannot be read back as another even where they agree.

--------
N3 转换：创建的零是按坐标计算的零，而不是它的相反数。[ab_neg (K d) (cmon_zero (K d)) ≈ cmon_zero (K d)] 是 [ab_neg_left] 的普通推论；它不是一次转换，因此即使操作一致，也不能将一个操作解释为另一个操作。
*)

Fail Example p443_n3 (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d
    = ab_neg (K d) (cmon_zero (K d)) := eq_refl.

(* control: the negation / 控制：否定 *)
Example p443_ab_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

(*
N2 CONVERSION: the negation is a real operation and not the identity map
   on the apex.  At an arbitrary diagram neither side reduces to the other,
   so the readback above is saying something about which operation was
   lifted and not merely that some map was.

--------
N2 转换：否定是一个真实的操作，而不是顶点上的恒等映射。在任意图中，任一方都不会简化为另一方，因此上面的回读是在说明哪个操作被提升了，而不仅仅是某个映射被提升了。
*)

Fail Example p443_n2
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d = `1 a d := eq_refl.

End AbPointwise.

(** ** B: at [Rng] the same, over five operations / ** B：在 [Rng] 相同，超过五次操作 *)

Section RngPointwise.

Context {J : Category}.
Context (K : J ⟶ Rng).

(* control: the carrier, with the coercion I3 removes / 控制：承运人，使用强制 I3 移除 *)
Example p443_rng_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

(* control: the leg / 控制：腿 *)
Example p443_rng_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

(* control: the addition / 控制：增加 *)
Example p443_rng_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

(* control: the multiplication / 控制：乘法 *)
Example p443_rng_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(*
N4 CONVERSION: the two binary operations are lifted SEPARATELY, through
   two cones with the same apex [rlim_pair], and neither readback is the
   other's.  A single mediator reused for both would make this accepted.

--------
N4 转换：这两个二进制操作是分别通过两个具有相同顶点 [rlim_pair] 的锥体进行提升的，而且没有一个读回是另一个的。若为两者重复使用单一的中介者，则将被接受。
*)

Fail Example p443_n4
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(*
N6 CONVERSION: multiplication keeps its argument order.  The contrast
   with N1 is the point: [Ab]'s addition commutes up to [≈] and [Rng]'s
   multiplication need not commute at all, and BOTH swaps are refused
   alike, so the refusal is about conversion and carries no algebra.

--------
N6 转换：乘法保持其参数顺序。与 N1 的对比就是关键：[Ab] 的加法在 [≈] 层面上是可交换的，而 [Rng] 的乘法完全不必可交换，并且两种交换都被拒绝，所以这种拒绝与转换有关，而不涉及任何代数。
*)

Fail Example p443_n6
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the additive unit / 控制：添加单元 *)
Example p443_rng_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the multiplicative unit / 控制：乘法单位 *)
Example p443_rng_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

(*
N5 CONVERSION: the two units are lifted through two DIFFERENT cones out
   of the same apex [unit_setoid_object], and neither reduces to the other
   at an arbitrary diagram of rings.  One and zero coincide in a zero ring,
   but that is an [≈] and never a conversion, which is exactly what this
   refutation records.

--------
N5 转换：这两个单元通过两个不同的圆锥从同一个顶点 [unit_setoid_object] 提升出来，并且在任意环图中都不会化简为对方。 一和零在零环中重合，但那是一个 [≈]，绝不是转换，这正是这个反驳所记录的内容。
*)

Fail Example p443_n5 (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the negation / 控制：否定 *)
Example p443_rng_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

(*
N7 CONVERSION: and it is not the identity either.  [ring_neg] is the one
   operation whose coherence the target discharges by [RigHom_neg] rather
   than by a projection, since [RigHom] has no negation clause, so its
   readback is the one most worth keeping honest.

--------
N7 转换：它也不是恒等变换。[ring_neg] 是唯一一个操作，其一致性由 [RigHom_neg] 而不是投影来解除，因为 [RigHom] 没有否定子句，因此其回读是最值得保持准确的。
*)

Fail Example p443_n7
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d = `1 a d := eq_refl.

End RngPointwise.

(**
** C: strictness — the created cone lies over the given one on the nose

    Both targets record this inside their lifting sections, as
    [alim_over_obj] and [rlim_over_obj].  What is read back here is the
    packaged form a consumer meets: the [slift_eq] field of the
    [StrictLift] the class hands out IS [eq_refl], which is strictly more
    than "the two objects are equal" — it says the recorded proof is the
    trivial one, so [hom_rew] in the [slift_legs] clause transports along
    nothing.

--------
** C: 严格性——创建的圆锥位于给定的圆锥之上鼻子位置

两个目标都在它们的提升部分中记录了这一点，分别为 [alim_over_obj] 和 [rlim_over_obj]。在这里读回的是消费者遇到的打包形式：[StrictLift] 类提供的 [slift_eq] 字段是 [eq_refl]，它严格上比“两个对象相等”更多——它表明记录的证明是平凡的，因此 [slift_legs] 条款中的 [hom_rew] 不会传递任何东西。
*)

Example p443_ab_strict {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

Example p443_rng_strict {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Rng_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

(* control: what the lift IS — a cone of abelian groups / 控制：提升是什么——阿贝尔群的锥 *)
Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
         (slift_cone (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K)
                        N HN) : Cone K)).

(*
N8 TYPE: "on the nose" is an equation between IMAGES, and does not
   identify the two cones.  Reading the lifted cone as though it WERE the
   given one is a type error — [Cone K] against [Cone (Ab_Forget ◯ K)],
   with no [cannot unify] clause — which is what keeps strictness a
   statement about [Ab_Forget] rather than a collapse of the two
   categories.

--------
N8 类型：“一针见血”是图像之间的等式，并不识别两个圆锥。将被抬起的圆锥当作给定的圆锥来阅读是一种类型错误——[Cone K] 对 [Cone (Ab_Forget ◯ K)]，而没有 [cannot unify] 条款——这正是严格性成为关于 [Ab_Forget] 的陈述而不是将两类合并的原因。
*)

Fail Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
              (slift_cone (@screates _ _ _ _ _
                             (Ab_Forget_StrictlyCreatesLimit K) N HN)
                 : Cone (Ab_Forget ◯ K))).

(**
** D: the readbacks are about the limits [Sets_Complete] chooses

    Test/ProbeGrpLimit411.v's N4 at two more categories.  The created
    object depends DEFINITIONALLY on which limit oracle the creation
    theorem is fed; over Mac Lane's cone-set oracle the carrier is
    [cone_apex] and not [Sets_limit_obj], though the two are canonically
    isomorphic.  Built here and not in the library files: each is a second
    [Complete] for its category and must not become the one a consumer
    sees.

--------
** D：回读值大约是 [Sets_Complete] 所选择的限制。

在另外两个类别中测试/ProbeGrpLimit411.v 的 N4。所创建的对象在定义上依赖于创建定理所输入的限制预言机；在 Mac Lane 的锥集合预言机上，该载体是 [cone_apex] 而不是 [Sets_limit_obj]，尽管二者在范畴上同构。这里构建而不是在库文件中：每个都是其类别的第二个 [Complete]，并且不能成为用户看到的那个。
*)

Definition Ab_ConeSet_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget ConeSet_Complete Ab_Forget_creates_limits.

Definition Rng_ConeSet_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget ConeSet_Complete Rng_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (KA : J ⟶ Ab).
Context (KR : J ⟶ Rng).

(* control: over the cone-set oracle the carrier IS [cone_apex] / 控制：在锥形集合预言机上，承载者是 [cone_apex] *)
Example p443_ab_coneset :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = cone_apex (Ab_Forget ◯ KA) := eq_refl.

(* N9 CONVERSION *)
Fail Example p443_n9 :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = Sets_limit_obj (Ab_Forget ◯ KA) := eq_refl.

(* control *)
Example p443_rng_coneset :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = cone_apex (Rng_Forget ◯ KR) := eq_refl.

(* N10 CONVERSION *)
Fail Example p443_n10 :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = Sets_limit_obj (Rng_Forget ◯ KR) := eq_refl.

End Oracle.

(**
** E: which preservation hypothesis Freyd's theorem asks for

    Test/ProbeGrpFreeAFT442.v pins this as its N6 and N7 at [Grp]; the two
    targets make it apply at two more categories, and the [Ab] header
    records the refusal in prose as a correction to an earlier revision of
    itself.  [GAFT]'s THIRD argument is the cone-level
    [PreservesImageLimit], which takes a [Limit K] and then a cone over the
    image; neither [ContinuousFunctor], which takes a [Cone K] and then a
    proof that it is limiting, nor the apex-only [PreservesAllLimits]
    ascribes to it, so
    [Continuous_PreservesImageLimit] stands in the term.  NO GAFT
    application is built at either category — the controls stop at the
    partial application, which is exactly what the targets make
    available.

    THE PARENTHETICAL OF THIS REFUSAL IS IMPORT-SENSITIVE, AND AN EARLIER
    REVISION OF THIS COMMENT GOT THAT WRONG.  That revision recorded, as a
    measured CORRECTION to Instance/Ab/Limit.v, that the header's
    closing clause [cannot unify «Limit.Limit K» and «Cone.Cone K»] "does
    not reproduce" and should read
    [cannot unify «Cone (Ab_Forget ◯ K)» and «IsLimitCone N»].  That was
    wrong, and acting on it would have damaged correct prose.  BOTH texts
    are real; which one Coq prints depends on what is imported, because the
    parenthetical is rendered with the module short-names in scope.
    Measured, same command, varying one [Require Import]:

      base (+ Structure.Limit.Preservation)
                            cannot unify «Limit.Limit K» and «Cone.Cone K»
      + Structure.Limit     cannot unify «Cone.Cone (Ab_Forget ◯ K)»
                                     and «IsLimitCone N»
      + Structure.Cone      cannot unify «Limit.Limit K» and «Cone K»
      + Structure.Limit.Creation
                            cannot unify «Limit.Limit K» and «Cone.Cone K»

    The HEAD of the error is stable under all four and is what actually
    matters: [ContinuousFunctor] does not ascribe where
    [PreservesImageLimit] is expected.  Instance/Ab/Limit.v's quote is
    correct for its own environment; this file's strip produces a different
    parenthetical because this file imports more.  N11 and N12 below pin the
    refusal, not the wording.

--------
** E: 弗雷德定理所要求的哪种保持假设

Test/ProbeGrpFreeAFT442.v 将其标记为 [Grp] 的 N6 和 N7；这两个目标使其应用于两个更多的类别，并且 [Ab] 头记录了拒绝作为对其早期修订的修正的散文形式。[GAFT] 的第三个参数是锥层 [PreservesImageLimit]，它接受一个 [Limit K]，然后在图像上创建一个锥；无论是接受 [Cone K] 并随后证明其是限制的 [ContinuousFunctor]，还是仅顶点的 [PreservesAllLimits] 都没有归于它，因此 [Continuous_PreservesImageLimit] 在术语中占位。两个类别都没有建立 GAFT 应用——控件在部分应用处停止，这正是目标提供的。

这个拒绝的括号内容对导入敏感，而早期对这个评论的修改搞错了这一点。那个修改将 Instance/Ab/Limit.v 作为经过衡量的更正记录，下列标题的结束子句 [cannot unify «Limit.Limit K» and «Cone.Cone K»] “不会复制”，应该写成 [cannot unify «Cone (Ab_Forget ◯ K)» and «IsLimitCone N»]。那是错误的，依此操作会破坏正确的文本。两个文本都是真实的；Coq 打印哪一个取决于导入内容，因为括号内容是用作用域中的模块短名称呈现的。经过衡量，相同命令，改变一个 [Require Import]：

base (+ Structure.Limit.Preservation)
                            无法统一 «Limit.Limit K» 和 «Cone.Cone K»
      + Structure.Limit     无法统一 «Cone.Cone (Ab_Forget ◯ K)»
                                     和 «IsLimitCone N»
      + Structure.Cone      无法统一 «Limit.Limit K» 和 «Cone K»
      + Structure.Limit.Creation
                            无法统一 «Limit.Limit K» 和 «Cone.Cone K»

错误的头部在所有四个版本下都是稳定的，并且这才是实际重要的：[ContinuousFunctor] 并没有被指派到 [PreservesImageLimit] 所期望的位置。Instance/Ab/Limit.v 的引用对于其自身环境是正确的；此文件的剥离结果产生了不同的括号，因为此文件导入了更多内容。下面的 N11 和 N12 确定了拒绝，而不是措辞。
*)

(* controls: the bridged hypothesis is accepted at both / 控制：桥接假设在两者中都被接受 *)
Check (GAFT Ab_Forget Ab_Complete
            (Continuous_PreservesImageLimit Ab_Forget_creates_continuous)).
Check (GAFT Rng_Forget Rng_Complete
            (Continuous_PreservesImageLimit Rng_Forget_continuous)).

(*
N11 CONVERSION: measured, the pair the message reports is the two
   hypotheses' FOURTH binders — [PreservesImageLimit] asks next for a cone
   over the image where [ContinuousFunctor] asks for a proof that the cone
   it was already given is limiting.

--------
N11 转换：测量时，消息报告的这一对是两个假设的第四个绑定器——[PreservesImageLimit] 接下来要求对图像进行一个圆锥体，而 [ContinuousFunctor] 要求提供一个证明，证明已经给出的圆锥体是限制性的。
*)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous).

(*
N12 CONVERSION: nor the apex-only class, which the [Ab] target also
   supplies and which is the tempting wrong choice.  Its message prints
   [PreservesImageLimit]'s body in full, so the two are visibly different
   statements and not two spellings of one.

--------
N12 转换：也不是仅顶点类，[Ab] 目标也提供该类，而且这是一个诱人的错误选择。它的消息会完整打印 [PreservesImageLimit] 的主体，因此两者在视觉上是不同的语句，而不是同一个语句的两种拼写。
*)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_PreservesAllLimits).

(* N13 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_continuous).

(* N14 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_PreservesAllLimits).

(**
** F: two terms of type [ContinuousFunctor Ab_Forget], and they differ

    The reason the [Ab] file exists.  Instance/Ab/FreeNotContinuous.v
    already declares [Ab_Forget_Continuous] and proves it by RAPL
    applied to Instance/Ab/Free.v's [free_ab_adjunction]; the new
    [Ab_Forget_creates_continuous] comes from limit creation and
    presupposes only [Sets_Complete].  Both are read back to the constant
    they are built from, so the provenance claim is machine-checked and not
    asserted, and N15 settles the sharp question their shared type
    raises.

--------
** F：两个类型为 [ContinuousFunctor Ab_Forget] 的项，它们不同。

[Ab] 文件存在的原因。Instance/Ab/FreeNotContinuous.v 已经声明了 [Ab_Forget_Continuous] 并通过 RAPL 对 Instance/Ab/Free.v 的 [free_ab_adjunction] 进行了证明；新的 [Ab_Forget_creates_continuous] 来自极限创建，并且只假定 [Sets_Complete]。两者都被回读到它们构建的常量，因此来源声明经过机器检查而不是断言，N15 解决了它们共享类型引发的尖锐问题。
*)

(* controls: the same type, twice / 控制：相同类型，两次 *)
Check (Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget).
Check (Ab_Forget_Continuous : ContinuousFunctor Ab_Forget).

(* control: the new one IS creation applied, on the nose / 控制：新的就是创作的应用，正中要害 *)
Example p443_creates_continuous_term :
  Ab_Forget_creates_continuous
    = creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits
  := eq_refl.

(* control: the old one IS RAPL applied, on the nose / 控制：旧的那个是RAPL应用的，正中目标 *)
Example p443_rapl_continuous_term :
  Ab_Forget_Continuous = right_adjoint_Continuous free_ab_adjunction
  := eq_refl.

(*
N15 CONVERSION: so they are not the same term.  This is what makes the
   second declaration worth having: feeding Freyd's theorem a continuity
   witness built out of the very adjunction the theorem is asked to produce
   would establish nothing, and the two constants are now known to be
   distinct rather than assumed to be.

--------
N15 转换：所以它们不是同一个术语。这就是使第二个声明值得拥有的原因：给 Freyd 定理提供一个由定理要求产生的adjunction本身构建的连续性证据将无法证明任何事情，而这两个常量现在已知是不同的，而不是假定是相同的。
*)

Fail Example p443_n15 :
  Ab_Forget_creates_continuous = Ab_Forget_Continuous := eq_refl.

(* control: the apex-only corollary descends from the CREATION one / 控制：仅顶点的推论源自创世推论 *)
Example p443_ab_apex_descends :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_creates_continuous := eq_refl.

(*
N16 CONVERSION: and not from the RAPL one, which would have been
   available and is not what the target used.

--------
N16 转换：而不是来自 RAPL 的那个，它本可以使用，但不是目标使用的那个。
*)

Fail Example p443_n16 :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_Continuous := eq_refl.

(* control: at [Rng] there is only one, and it descends the same way / 控制：在 [Rng] 处只有一个，它以下降的相同方式下降 *)
Example p443_rng_apex_descends :
  Rng_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Rng_Forget_continuous := eq_refl.

(*
N17 NAME-ABSENCE: the two files' naming IS asymmetric, and a consumer
   reaching for the [Rng]-style name at [Ab] gets nothing.  An earlier
   revision of this comment gave a FALSE reason — that the name "could NOT
   be given" because [Ab_Forget_Continuous] was already taken.  Coq
   identifiers are case-sensitive, so [Ab_Forget_continuous] and
   [Ab_Forget_Continuous] would coexist perfectly well; the audit of this
   probe checked that by defining the former in an environment already
   holding the latter (rc=0).  The real reason is a CHOICE, made in
   Instance/Ab/Limit.v and stated in its header: two constants of the same
   type [ContinuousFunctor Ab_Forget], differing only in case, would be a
   trap, because one is RAPL applied to the free/forgetful adjunction and
   the other is derived from limit creation, and only the second is usable
   as a GAFT hypothesis without circularity.  So the new one is
   [Ab_Forget_creates_continuous], whose name says where it comes from.
   This refutation pins that the tempting name is absent.

--------
N17 NAME-ABSENCE: 这两个文件的命名是非对称的，消费者在 [Ab] 处尝试获取 [Rng] 风格的名称时会一无所获。该评论的早期修订给出了一个错误的原因——认为该名称“不能被使用”，因为 [Ab_Forget_Continuous] 已经被占用。Coq 标识符区分大小写，因此 [Ab_Forget_continuous] 和 [Ab_Forget_Continuous] 可以完美共存；对该探针的审计通过在已存在 [Ab_Forget_Continuous] 的环境中定义前者来验证了这一点（rc=0）。真正的原因是一个在 Instance/Ab/Limit.v 中做出的选择，并在其头部声明：两个类型相同但大小写不同的常量 [ContinuousFunctor Ab_Forget] 会是一个陷阱，因为一个是 RAPL 应用于自由/遗忘伴随，而另一个源自极限创建，并且只有第二个可以作为 GAFT 假设使用而不会产生循环。因此新的名称是 [Ab_Forget_creates_continuous]，其名称说明了它的来源。这一反驳指出了这个诱人的名称不存在。
*)

Fail Check Ab_Forget_continuous.

(*
N18 NAME-ABSENCE: the mirror.  There is no RAPL-style continuity
   constant at [Rng], and the [Rng] header's reason is measured there: no
   adjunction in tree has [Rng_Forget] as its right adjoint, so
   [right_adjoint_Continuous] does not reach it.

--------
N18 名称缺失：镜子。在 [Rng] 处没有 RAPL 风格的连续性常数，并且 [Rng] 头的原因在那里被测量：树中的任何附加结构都没有 [Rng_Forget] 作为其右附节点，因此 [right_adjoint_Continuous] 无法到达它。
*)

Fail Check Rng_Forget_Continuous.

(**
** G: reflection is not preservation, and the two creation classes are
        two types

--------
** G: 反映不是保存，两个创造类别是两种类型
*)

(* control: what the target delivers / 控制：目标所提供的内容 *)
Check (fun (J : Category) (K : J ⟶ Ab) =>
         (Ab_Forget_reflects_limits K : ReflectsLimitCone K Ab_Forget)).

(*
N22 CONVERSION: [ReflectsLimitCone] and [PreservesLimitCone] are converse
   implications between the same two propositions, so neither ascribes as
   the other.  This is the clause the [Ab] header says RAPL does not give
   at all, and it is a separate hypothesis from every continuity constant
   in section F.

--------
N22 转换：[ReflectsLimitCone] 和 [PreservesLimitCone] 是同两个命题之间的逆向蕴涵，因此彼此之间没有归属。这是 [Ab] 头文件所说的 RAPL 完全不提供的条款，并且它是与 F 节中每个连续性常数分开的假设。
*)

Fail Check (fun (J : Category) (K : J ⟶ Ab) =>
              (Ab_Forget_reflects_limits K : PreservesLimitCone K Ab_Forget)).

(* controls: each target ships an inhabitant of both creation classes / controls: each target ships an inhabitant of both creation classes / 控制：每个目标都会发送一个两种创造类别的居民 *)
Check (Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget).
Check (Ab_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Ab_Forget).
Check (Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget).
Check (Rng_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Rng_Forget).

(*
N19, N20 CONVERSION: neither is an ascription of the other — 411's N3 at
   the two new categories, and its message here too carries the [cannot
   unify] clause that 411 uses to tell the two kinds apart.

--------
N19，N20 转换：二者都不是对方的归属 — 411 在两个新类别上的 N3，以及它在这里的信息也带有 411 用来区分这两种类型的[不能统一]条款。
*)

Fail Definition p443_n19 : StrictlyCreatesLimits Ab_Forget :=
  Ab_Forget_creates_limits.

Fail Definition p443_n20 : StrictlyCreatesLimits Rng_Forget :=
  Rng_Forget_creates_limits.

(**
** H: one NOT-DELIVERED claim, pinned

    The [Ab] header says in terms that no [CMon] analogue is extracted,
    "No [CMon_Complete] exists either", though the engine transfers
    unchanged once [ab_neg] and its two laws are dropped.  Measured on the
    worktree this probe was written against, a whole-tree word-bounded grep
    of every [.v] file for that token returns exactly one hit,
    Instance/Ab/Limit.v, and that hit is the sentence itself; the
    refutation below is the same absence taken from the environment rather
    than from the text.

--------
** H: 有一个未交付的索赔，已固定

[Ab] 头文件明确表示没有提取 [CMon] 类似物，
“也不存在 [CMon_Complete]”，尽管引擎在丢弃 [ab_neg] 及其两条法律后保持不变。一旦在编写该探针时的工作树上测量，对每个 [.v] 文件进行整树单词边界的 grep 搜索该标记，恰好返回一次匹配，Instance/Ab/Limit.v，而该匹配就是这句话本身；下面的反驳则是从环境中而非文本中取得的同样缺失。
*)

(* N21 NAME-ABSENCE *)
Fail Check CMon_Complete.

(**
** I: guard block — every constant a refutation names, named outside
        every refutation

--------
** I：守卫块——每个常量都是反驳名称，在每个反驳之外命名
*)

Check @carrier.
Check @Cone.
Check @cone_leg.
Check @cone_apex.
Check @limit_cone.
Check @IsLimitCone.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_Complete.
Check @ConeSet_Complete.
Check @screates.
Check @slift_eq.
Check @slift_cone.
Check @CreatesAllLimits.
Check @StrictlyCreatesLimits.
Check @ReflectsLimitCone.
Check @PreservesLimitCone.
Check @ContinuousFunctor.
Check @Continuous_PreservesAllLimits.
Check @Continuous_PreservesImageLimit.
Check @creates_limits_Complete.
Check @creates_limits_continuous.
Check @right_adjoint_Continuous.
Check @GAFT.

Check @Ab.
Check @Ab_Forget.
Check @ab_cmon.
Check @ab_neg.
Check @cmon_setoid.
Check @cmon_map.
Check @cmon_plus.
Check @cmon_zero.
Check @Ab_Complete.
Check @Ab_ConeSet_Complete.
Check @Ab_Forget_StrictlyCreatesLimit.
Check @Ab_Forget_StrictlyCreatesLimits.
Check @Ab_Forget_creates_limits.
Check @Ab_Forget_creates_continuous.
Check @Ab_Forget_PreservesAllLimits.
Check @Ab_Forget_reflects_limits.
Check @Ab_Forget_Continuous.
Check @free_ab_adjunction.

Check @Rng.
Check @Rng_Forget.
Check @rig_setoid.
Check @rig_map.
Check @rig_add.
Check @rig_mul.
Check @rig_zero.
Check @rig_one.
Check @ring_neg.
Check @Rng_Complete.
Check @Rng_ConeSet_Complete.
Check @Rng_Forget_StrictlyCreatesLimit.
Check @Rng_Forget_StrictlyCreatesLimits.
Check @Rng_Forget_creates_limits.
Check @Rng_Forget_continuous.
Check @Rng_Forget_PreservesAllLimits.
Check @Rng_Forget_reflects_limits.
