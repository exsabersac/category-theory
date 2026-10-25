(**
* Boundary probes for the indexed coproduct of categories (issue #338)

    Mac Lane CWM 2nd ed. §III.5 Exercise 4, book p. 74; Riehl 2nd ed. §3.6.

    The two target files pin FOUR refutations of their own, and not all
    of one kind: three CONVERSION
    (`Construction/Coproduct/Indexed.v`,
    `Instance/Cat/Coproduct.v` and) and one FORMABILITY
    (`Instance/Cat/Coproduct.v`, the smallness measurement).  This
    file pins the THREE boundaries they cannot state -- two because
    stating them needs a section declaring universe levels strictly
    apart, which a target cannot carry without constraining itself.

    THREE NEGATIVES OF TWO KINDS, kept lexically apart, plus one compiled
    POSITIVE that turns a header argument into a fact:

      * Negatives 1 and 2 are FORMABILITY, and they carry the file's two
        universe claims.  Negative 1 is why `SigmaCat` is written with
        EXPLICIT universe binders: the same body written unannotated
        minimizes so as to IDENTIFY the summands' hom and proof universes,
        and is then rejected under `Constraint uh < up` where the
        annotated form is accepted.  A target cannot pin this, since
        stating it needs a section that declares levels strictly apart.
        Negative 2 localizes the ONE identification the UMP-level results
        do carry (`C : Category@{a b b}`) to its donor: `Functor_Setoid`
        is rejected at separated levels while the functor TYPE `C ⟶ D`
        and the underlying `Unique` over a hom-setoid both elaborate.
        `Functor_Setoid` (`Theory/Functor.v`) is an unannotated
        `Program Instance`, and since `≈` on functors IS that setoid, no
        statement of the UMP in this library's vocabulary avoids it.  It
        is not introduced by #338 and is NOT claimed unavoidable.

      * Negative 3 is CONVERSION: the indexed construction at
        `I := bool` is not Leibniz-equal to the binary `Coproduct` even
        in its OBJECT type -- which is exactly why
        `SigmaBool_strict_iso` is an isomorphism of categories and
        nothing stronger.

      An earlier revision of this file had a FOURTH negative, asserting
      that the elementary coproduct record is not the bundled
      `HasIndexedCoproducts` datum on the nose.  It was wrong twice over
      and is recorded here rather than quietly dropped: it fired for the
      WRONG REASON (an over-application typing error, since
      `Cat_HasIndexedCoproducts` is not a function of the index), and
      the statement it was reaching for is FALSE -- the packaging is
      definitional all the way through.  What replaced it is the three
      `eq_refl` identifications of section "The packaging is
      transparent" below, which are a stronger and truer result.

      * The POSITIVE, `probe_forall_encoding_inhabited`, compiles the
        first half of the header's refutation of encoding (c).  The
        header argues that reading the hom as `∀ e : i = j, …` is wrong
        MATHEMATICS because for provably distinct `i` and `j` that type is
        INHABITED by the vacuous function, so the reading would add a
        morphism between every cross-summand pair -- the indiscrete
        category on the summands rather than their disjoint union.  That
        half is a one-line construction, so it is compiled here rather
        than left as prose.  The header's SECOND half (no identity is
        definable) and its fourth-encoding argument remain arguments; the
        target says so and this file does not change that.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* 所提供的 

Mac Lane为女性 CWM 第2版 §III.5 演练 4,本书第74页; Riehl 第2版 §3.6.

two  two  two  files  files  files  files  files two  two  files  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two  two 
比的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的 的的的的的的的的的的的的的的的的的的的的 的的的的的的的的的的的的的的的的的的的
law؟(()),(())
" Instory/Cat/CoProperty.v)和(FORMABILYTY,第(I)段,第(i)段,第(i)段,第(i)段,第(i)段,第(i)段,第(i),第(i)段,第(i),第(i)段,第(i),第(i),第(i),第(i),第(ii),第(i),第(i),第(i),第(i),第(i),第(i),第(i),第(i),第((i),第(i),第(i),第(i),第(i),第(i),第(ii),第(i),第(第(ii),第(I),(第(I),第((I)),((I)),(第(第(I)),( '),( ')),((( '))),((((((
,內內內內 內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內(內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內(內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內內所有內內內內內內內內內內內內內內內內內內內內內內內內(內內內內內內內內內內內內內內內內
这位 , , , , , , , , , , , , , ,
被
业经
之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 之 , 之 之 之 之 之 之 之 , 之 之 , 之 之 之 , 之 之 之 , 之 之 , 之 之 , 之 , 之 , 之 之 , 之 之 , 之 , 之 之 , 之 , , 之 , 之 之 , , 之 , 之 之 , , 之 之 , 之 , , , 之 之 , 之 之 , , 之 之 之 , , 之

专门专门,专门专门,专门专门,专门专门,专门专门,专门,专门专门,专门专门,专门,专门专门,专门专门,专门专门,专门专门,专门专门专门,专门专门,专门专门专门专门,专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门特别专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门特别专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门专门
time 感知到将标题争论变成事实:

خ会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会会
联合国. 联合国. . . . . .
... P  P                                                   同时 同时 同时同时同时m同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时同时
đâyCC环CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC,CCCC,CC,C,C,C,C,C,C,C,C,C,C,C,C,,C,C,C,C,,,,,,,,,,,,,,,,,,,,,,,,,,C,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,
两个
的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的
目标不能对此负责,因为
要求它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它需要一个部分,它,需要一个部分,它,需要一个部分,需要一个部分,它,请一个区域,需要一个一个区域,请, :  负2将确定UMP一级结果的“一个”定位定位
,过、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、,、,,,,,,,,,,,,,、,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,、,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,、,,,,,,,,,,,,、,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,、,,,,,,,,,,,,,,
预期将
,
"""""""""""""" " " " " " " " " " " " " " " " " " " " " " " " " " " " " " "的 " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " "
)///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////)///////////////////////////////////////////////////////////////////////////////////////
合办為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為為的為為為為的的為為為為為的的的為為為的的為的的的為為的的的的的的的的的的的的的的的的的為的的的的為的的為的的的的的的的的為的的的的的的的的的的的的的為的的的的的的的在的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的在的的的的的的的的的的的的在的的的在的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的在的的的的的的的的的的的的的的的的的的的经社  為                                      :      的      的   的  的  的   , 的 , 的的 的 的的 , 的 , 的的 , 的,, 的的,,, 的,,, 的的的,, 的,,, 的, 的 的,,的的的,,的的,的的的的的的,,,的的,的,,,,的的,,的,,的的,的,的,的,,,的,的的的的,,的的,的的的的,的,,,的的的的的,的,的的的的的的的的的的的,的的的的的的的的的的,的的的的的的的的的的的的的的的的的的的的的的的,的的的的的的的的的
各种各样,不是第338条所接受的,并且是无法完成的。

的指示编 负 3 是指:
和一视同仁和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和、和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和和
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
时方时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时时
的 页的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的的

"将这些 "  "  "  " "  "  "  "  "  "  "  "  "  "  "  "  "  "  "  "  "  " "  " "  "  "  "  "  "  "  "  "  " "  "  "  "  " "  "  "  "  "  "  "  "  "  " " "  " "  "  " "  "  " "  "  "  "  "  "  "  "  "  "  "  "  "  " "  "  "  "  " "  "  "  " "  " "  " "  "  "  "  " "  " "  " " "  " " " " " " " "  " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " " "
我听说,初级联合产品记录不是捆绑的
鼻子上的`HasIndexedCoproducts ' datum。
大                                                                                                                                                         大                                                                                                    
的指示 页: 1
................................................................................................................................................................................................................................................................
, , , , , , , , , , , ,, , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , , ,

定义明确。
ụ年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年岁年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年年
`eq refl ' 标识部分 " 包装是
的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,的,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,

.
.頭頭頭頭頭 頭 頭頭                                                                         (                                                                                          )                                                                                
情况ص
求助于裁、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、
" i " 和 " j " 类型可证明是
开始实施的作品,在的作品上,在的作品上,在的作品上,在的面上,在的上上,在的上上,在的上上,在的上上,在的上上,在的上上,在的上上,在的上上,在的上上,在的上上,上上上上上。。。 上上上上。的上。。。 的上。。 的上。。。。。 的。。。。。。。。。。。。。的。。。。。。。。。。 。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。的。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。
将杏خ
巷(summands) 而不是他们的脱节结合。
那个
士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士 士士士士士士士士士 士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士 士士士士士士士士士士士士士士士士士 士士士士士士士士士士士士士士士士士士 士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士 士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士士
" 或以左为正字.\
、,、、、、、、、、、、、、、、、、、、、、、、、的、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、的、、、、、、、、、、、、、、的、、、、、、、、、、、、的、、、、、、、、、、、、、、、、、、、、、、、的、、、、、、、的、、、、、、、、、、、、、、、、、、、、、、、、方案、、、、、、、、、、、、、、、、、方案、、、、、、、、、、、、方案、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、、的、、、、、、、、
甲                                                                                                                                                                                                                                                              

.

绸
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.Coproduct.

Generalizable All Variables.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Negative 1 (FORMABILITY): the explicit universe binders are
       load-bearing

    `SigmaCat` is declared `@{ui uo oh op us}` and its constraint block is
    ALL BOUNDS -- `ui <= us`, `uo <= us`, `oh <= op`, the last being
    `Class Category`'s own `h <= p`.  Written WITHOUT binders the same
    body minimizes to a shape that identifies the summands' hom and proof
    universes.  The control and the negative differ in nothing else.

--------
** 负 1（可形成性）：显式宇宙绑定器是承重的

`SigmaCat` 被声明为 `@{ui uo oh op us}`，其约束块为所有界限 -- `ui <= us`，`uo <= us`，`oh <= op`，最后一个是 `Class Category` 自身的 `h <= p`。不使用绑定器书写时，同样的主体会简化为一个形状，该形状识别出加法因子的同构和证明宇宙。控制和负面在其他方面没有区别。
*)

Section BinderBoundary.

Universe uo uh up.
Constraint uh < up.

(*
Control: the ANNOTATED construction is formable with the summands' hom
   and proof universes declared strictly apart.

--------
控制：带注释的构造可以在各项同构和证明宇宙严格分开声明的情况下形成。
*)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) => SigmaCat C).

(* Control: so is its injection, at the same levels. / 对照组：其注射方式相同，剂量也相同。 *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) (i : I) =>
         SigmaCat_inj C i).

(*
The unannotated body, re-declared here so the negative is about the
   ANNOTATION and not about anything else in the file.

--------
未注释的主体，在此重新声明，因此否定是关于注释的，而不是关于文件中的其他任何内容。
*)
Definition sigma_obj_unann {I : Type} (C : I -> Category) : Type :=
  ∃ i : I, C i.

(* NEGATIVE 1. / 否定 1. *)
Fail Check (fun (I : Type) (C : I -> Category@{uo uh up}) =>
              sigma_obj_unann C).

End BinderBoundary.

(**
** Negative 2 (FORMABILITY): the UMP's one identification is
       `Functor_Setoid`'s

    `SigmaCat_ump` displays `C : I → Category@{u7 u9 u9}` and
    `D : Category@{u8 u9 u9}` -- the two OBJECT universes stay apart while
    hom and proof are identified.  The controls show the functor type and
    the `Unique` packaging are both innocent.

--------
** 负 2（可形成性）：UMP 的一个标识是 `Functor_Setoid` 的

`SigmaCat_ump` 显示 `C : I → Category@{u7 u9 u9}` 和
`D : Category@{u8 u9 u9}` —— 两个对象宇宙保持分离，同时同态和证明被识别。 控制显示函子类型和 `Unique` 打包都是无害的。
*)

Section SetoidBoundary.

Universe vo vh vp.
Constraint vh < vp.

(* Control: the functor TYPE elaborates at separated levels. / 控制：函子 TYPE 在分离的层次上进行详细说明。 *)
Check (fun (C D : Category@{vo vh vp}) => (C ⟶ D)).

(* Control: so does a `Unique` over a hom-setoid of such a category. / Control: so does a `Unique` over a hom-setoid of such a category. / 控制：因此在这样一个范畴的同类集上的 `Unique` 也是如此。 *)
Check (fun (C : Category@{vo vh vp}) (x y : C)
           (P : (x ~> y) -> Type) => @Unique _ (@homset C x y) P).

(*
Control: [Functor_Setoid] EXISTS and elaborates at UNCONSTRAINED
   levels -- without this the negative below would still "succeed" after
   a rename of [Functor_Setoid], on a reference-not-found error rather
   than on the universe boundary.  (That vacuity was measured, not
   guessed: an earlier revision of this file omitted this line and the
   rename simulation scored 3/4.)

--------
控制：[Functor_Setoid] 存在并在不受限制的级别上展开 —— 如果没有它，下面的否定仍会在重命名 [Functor_Setoid] 后“成功”，发生在引用未找到错误上，而不是在宇宙边界上。（这种空白是测量得出的，而不是猜测的：这个文件的早期版本省略了这一行，重命名模拟得分为 3/4。）
*)
Check @Functor_Setoid.

(* NEGATIVE 2. / 负 2. *)
Fail Check (fun (C D : Category@{vo vh vp}) => @Functor_Setoid C D).

End SetoidBoundary.

(**
** The packaging is transparent, in all THREE fields

    The construction is stated first at the apex-pinned
    `IsIndexedCoproduct` and only then packaged through
    `Build_HasIndexedCoproducts`, deliberately avoiding
    `Colimit`/`DiscreteCat_Functor`.  Nothing is lost in the packaging:
    the class's object field, its injection field AND its universal-
    property field all return the elementary data at `eq_refl`.  The
    third is the one worth having -- it says the bundled class carries
    the very record `SigmaCat_IsIndexedCoproduct` proves, not a rebuilt
    copy of it.

--------
** 包装是透明的，在所有三个字段中都是如此。

构造首先在顶点固定的 `IsIndexedCoproduct` 中声明，然后才通过 `Build_HasIndexedCoproducts` 进行打包，有意避免使用 `Colimit`/`DiscreteCat_Functor`。在打包过程中没有任何信息丢失：类的对象字段、注入字段以及它的泛性质字段都返回 `eq_refl` 处的基本数据。第三个字段是值得关注的——它表明捆绑的类包含了 `SigmaCat_IsIndexedCoproduct` 证明的记录，而不是其重建副本。
*)

Check @SigmaCat_IsIndexedCoproduct.
Check Cat_HasIndexedCoproducts.

Definition probe_pkg_obj {I : Type} (C : I -> Cat) :
  @indexed_coproduct Cat Cat_HasIndexedCoproducts I C = SigmaCat C
  := eq_refl.

Definition probe_pkg_inj {I : Type} (C : I -> Cat) (i : I) :
  @indexed_coproduct_inj Cat Cat_HasIndexedCoproducts I C i
    = SigmaCat_inj C i := eq_refl.

Definition probe_pkg_ump {I : Type} (C : I -> Cat) :
  @indexed_coproduct_ump Cat Cat_HasIndexedCoproducts I C
    = SigmaCat_IsIndexedCoproduct C := eq_refl.

(**
** Negative 3 (CONVERSION): the binary comparison is an isomorphism
       and nothing stronger

    At `I := bool` the indexed construction and `Construction/Coproduct.v`'s
    binary `Coproduct` are isomorphic AS CATEGORIES
    (`SigmaBool_strict_iso`, in `StrictCat`, both round trips at
    `Functor_StrictEq_Setoid`).  They are not the same category, and the
    obstruction is already in the OBJECT type: a dependent pair against a
    tagged sum.

--------
** 负3（转换）：二元比较是同构的
       并且没有更强的关系

在 `I := bool` 时，索引构造和 `Construction/Coproduct.v` 的二元 `Coproduct` 在类别意义上是同构的
(`SigmaBool_strict_iso`，在 `StrictCat` 中，在 `Functor_StrictEq_Setoid` 上都能双向转换)。它们不是相同的类别，并且障碍已经存在于对象类型：依赖对与带标签的和类型之间。
*)

(* Control: the isomorphism that DOES hold. / 控制：确实成立的同构。 *)
Check @SigmaBool_strict_iso.
Check @SigmaBool_iso.
Check @BoolFam.

(* NEGATIVE 3. / 负三。 *)
Fail Definition probe_bool_obj (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = (obj[C] + obj[D])%type := eq_refl.

(**
** The compiled half of the encoding-(c) refutation

    For provably distinct indices the type `∀ e : i = j, X e` is
    INHABITED, by the function that eliminates the empty equality.  So
    reading a cross-summand hom that way does not give an empty hom-set;
    it gives a one-element one, and the construction would be the
    indiscrete category on the summands rather than their disjoint union.
    The header argues this; here it is, compiled.

--------
** 编码-(c) 反驳的已编译部分

对于可证明不同的索引，类型 `∀ e : i = j, X e` 是可被占据的，由消除空等式的函数提供。因此，以这种方式读取交叉求和的同态不会得到一个空的同态集；它会得到一个单元素集合，而构造将是求和项上的不离散范畴，而不是它们的离散并集。标题对此进行了论证；这里是已编译的版本。
*)

Definition probe_forall_encoding_inhabited
  (C : bool -> Category) (x : C true) (y : C false) :
  ∀ e : true = false, ob_cast C e x ~> y :=
  fun e => match (eq_ind true (fun b : bool => if b then True else False)
                          I false e) with end.

(*
Contrast, from the target: the encoding actually used makes that hom
   EMPTY, which is the point.

--------
对比，来自目标：实际使用的编码使得那个同
   EMPTY，这就是重点。
*)
Check @sigma_hom_cross_empty.
Check @bool_cross_empty_lr.
Check @bool_cross_empty_rl.

(** ** Positive controls for the headline artifacts / ** 标题工件的阳性对照 *)

Check @SigmaCat.
Check @SigmaCat_inj.
Check @SigmaCat_case.
Check @SigmaCat_case_inj.
Check @SigmaCat_case_unique.
Check @SigmaCat_ump.
Check @ob_cast.
Check @mor_cast.

(**
The hypothesis-free/hypothesis-bearing split, and the necessity
    theorem that makes the split principled rather than convenient.

--------
无假设/有假设的划分，以及使这种划分具有原则性而非方便性的必要性定理。
*)

Check @SigmaCat_inj_Full.
Check @sigma_inj_Full_forces_UIP.
Check @inj_Full_forces_UIP_at_One.
Check @SigmaCat_const_inj_Faithful.
Check @SigmaCat_inj_Faithful.
Check @Faithful_cancel.
Check @IdxUIP.

(** Non-vacuity. / 非空性 *)

Check @SigmaCat_empty_no_obj.
Check @SigmaCat_unit_iso.
Check @bool_summands_not_isomorphic.
Check @case_separates_summands.
Check @sigma_poly_unit_dec.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

    Read off the `Fail` commands themselves, not off memory -- an
    earlier revision of this table was written from memory and got two
    of the three rows wrong, crediting Negative 1 with [SigmaCat] and
    [SigmaCat_inj] and Negative 2 with [homset], all three of which
    occur only in that section's positive CONTROLS:

      Negative 1 names [Type], [Category], [sigma_obj_unann]
      Negative 2 names [Category], [Functor_Setoid]
      Negative 3 names [Category], [obj], [SigmaCat], [BoolFam],
                        [eq_refl]

    Excluding core vocabulary ([Type], [Category], [obj], [eq_refl]) on
    the stated ground that it is named by almost every file in the tree
    rather than that it is hard to guard, and excluding the file-local
    [sigma_obj_unann] because renaming it renames both halves at once
    and so guards nothing, the constants a NEGATIVE names are THREE:
    [Functor_Setoid], [SigmaCat], [BoolFam].

    Each of the three is named by a positive control above.  Score:
    3/3, on an unpadded denominator, measured by compiling a renamed
    copy of this file against an instrument-checked baseline and
    confirming each one breaks it.  ([SigmaCat_inj] also breaks the
    file when renamed, via its controls; it is not counted here because
    no negative names it, and counting it was what padded the earlier
    4/4.)

--------
** 测量的重命名模拟分数

NEGATIVES 命名的常数：

直接读取 `Fail` 命令本身，而不是从记忆中读取 —— 该表的早期版本是根据记忆编写的，错误地列出了三行中的两行，把 [SigmaCat] 和 [SigmaCat_inj] 分配给 Negative 1，把 [homset] 分配给 Negative 2，而这三个命令只出现在该部分的正向 CONTROLS 中：

负面 1 名称 [Type]、[Category]、[sigma_obj_unann]
负面 2 名称 [Category]、[Functor_Setoid]
负面 3 名称 [Category]、[obj]、[SigmaCat]、[BoolFam]、
              [eq_refl]

排除核心词汇（[Type]、[Category]、[obj]、[eq_refl]），理由是几乎每个文件中都有它的名称，而不是因为它难以保护；并且排除文件本地的 [sigma_obj_unann]，因为重命名它会同时重命名两部分，因此无法保护任何内容，常量 a NEGATIVE 指代的名称有三个：[Functor_Setoid]、[SigmaCat]、[BoolFam]。

这三者中的每一个都是由上方的阳性控制命名的。评分：3/3，在未填充的分母上，通过将此文件的重命名副本与仪器检查的基线进行编译测量，并确认每一个都会导致其失败。（[SigmaCat_inj] 在重命名后也会通过其控制导致文件失败；这里不计入，因为没有负面命名它，而之前的 4/4 正是因为计入它才填充的。）
*)
