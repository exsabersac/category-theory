Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.

Generalizable All Variables.

(** * Probe: the measured boundaries of Instance/Grp/Limit.v / * 探针：Instance/Grp/Limit.v 的测量边界 *)

(*
Companion to Instance/Grp/Limit.v (Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.1 Theorems 2 and 3).  Everything that file
   claims at [eq_refl] is shipped there as an [Example], so it guards
   itself; what it cannot guard from inside are the two REFUSALS it records
   and the universe boundary a consumer meets.  Those are pinned here, from
   OUTSIDE the target, because an in-file [Fail] renames in lockstep with
   the constant it guards and so cannot detect a rename.

   FOUR negatives of TWO kinds, told apart by the error TEXT rather than by
   label, plus one scope-free instrument check.  Read the KINDS off the
   messages actually produced, which were captured by stripping each [Fail]
   in turn: N1 and N2 report a has-type mismatch between two universe
   INSTANCES of the same head ([Category@{sso so so}] against
   [Category@{_ jh jh}], [Ju ⟶ Sets@{so sso}] against [Ju ⟶ Sets@{jh _}])
   CLOSING WITH the tree's usual formability tail, [(universe
   inconsistency: Cannot enforce so = jh because jh < so)]; N3 reports a
   has-type mismatch carrying a [cannot unify] clause and mentioning no
   universe at all; N4 reports [eq_refl] at the wrong type, likewise with a
   [cannot unify] clause.  So N1 and N2 are told apart from N3 and N4 by the
   universe clause, and N3 from N4 by which term is ill-typed rather than by
   the tail.

     N1  UNIVERSE  [IsALimit] identifies the shape's hom-and-proof universe
                   with the ambient category's, so at a shape whose homs are
                   declared strictly BELOW [Sets]' carrier universe it is
                   refused -- while [Cone] at the very same levels is
                   ACCEPTED, which is what makes the attribution
                   discriminate: the cone vocabulary alone does not impose
                   it.
     N2  UNIVERSE  [sets_limit_ext] is refused at those same levels, and it
                   fires at the FUNCTOR argument -- its binder has already
                   put [Sets]' carrier universe at the shape's hom level,
                   which is the block equation [u0 = u3] the target's header
                   reports on its four generic [Sets] constants.  N1 is what
                   attributes that identification to the donor; nothing here
                   claims [sets_limit_ext] adds one of its own.
     N3  CONVERSION  [CreatesAllLimits] and [StrictlyCreatesLimits] are
                   different types; the target ships an inhabitant of each
                   and neither is an ascription of the other.  Classified by
                   the tree's own convention rather than by shape: the error
                   carries [cannot unify "CreatesLimit K Grp_Forget" and
                   "StrictlyCreatesLimit K Grp_Forget"], and a TYPING
                   negative in this tree is a has-type mismatch with NO such
                   clause.
     N4  CONVERSION  The created group depends on WHICH limit oracle it is
                   fed, definitionally: over [ConeSet_Complete] the carrier
                   is [cone_apex] (the control below) and NOT
                   [Sets_limit_obj], though the two are canonically
                   isomorphic through [limit_unique_iso].  This is what
                   keeps the target's five [grp_complete_*] readbacks
                   honest -- they are statements about the limits
                   [Sets_Complete] chooses, not about limits in general.

   Each negative was stripped ONE AT A TIME in a copy of this WHOLE file --
   not a preamble-plus-command scratch, which would drop the [Section]'s
   [Context] and local [Universes]/[Constraint] declarations and refuse for
   a reason unrelated to the claim -- compiled alone, and its whole error
   read.  Every constant a negative names also appears in a [Check] outside
   every [Fail], so a rename breaks this file loudly instead of turning a
   [Fail] vacuously green.  Measured mechanically: 25 identifiers occur
   inside a [Fail] and 21 also occur outside every one, the four exceptions
   being exhaustively the keyword itself, the two names a [Fail] DECLARES
   (which never enter the environment) and the instrument's deliberately
   absent one.  Rename-simulated 2/2 over the target constants a negative
   names -- [sets_limit_ext] and [Grp_Forget_creates_limits] -- each rename
   breaking this file at a [Check] guard line, never inside a [Fail].

--------
《Instance/Grp/Limit.v》的配套资料（Mac Lane，《Categories for the Working Mathematician》，第2版，第V.1节 定理2和3）。该文件在 [eq_refl] 处声明的一切都会以 [Example] 的形式在那里传输，因此它可以自我保护；它无法在内部保护的，是它记录的两个 REFUSALS 以及消费者遇到的宇宙边界。这些在此固定，是从目标之外进行的，因为文件内的 [Fail] 会与它所保护的常量同步重命名，因此无法检测重命名。

两种类型的四个否定，由错误文本而不是标签区分，再加上一个无作用域的工具检查。根据实际产生的消息读取类型，这些消息是通过依次剥离每个 [Fail] 捕获的：N1 和 N2 报告同一头部的两个宇宙实例之间存在类型不匹配（[Category@{sso so so}] 对 [Category@{_ jh jh}]，[Ju ⟶ Sets@{so sso}] 对 [Ju ⟶ Sets@{jh _}]），以树的一般可形成性尾部结束，[(宇宙不一致：无法强制 so = jh 因为 jh < so)]；N3 报告带有 [cannot unify] 条款的类型不匹配，并且根本没有提到任何宇宙；N4 报告 [eq_refl] 类型错误，同样带有 [cannot unify] 条款。因此，N1 和 N2 可以通过宇宙条款与 N3 和 N4 区分开来，N3 和 N4 则通过哪个术语类型不正确区分，而不是通过尾部。

N1  宇宙  [IsALimit] 将形状的同态和证明宇宙与环境范畴的宇宙进行识别，因此在同态严格声明在 [Sets] 容器宇宙以下的形状上，它会被拒绝——而在完全相同的级别上 [Cone] 则被接受，这正是使归属具有辨别性的原因：仅靠圆锥词汇本身并不会强加它。N2  宇宙  [sets_limit_ext] 在同样的级别上被拒绝，并且它在 FUNCTOR 参数上触发——它的绑定器已经将 [Sets] 的容器宇宙置于形状的同态级别，这是块方程 [u0 = u3] 目标头在其四个通用 [Sets] 常量上报告的内容。
N1 是什么，将该标识归因于捐赠者；这里没有任何内容声称 [sets_limit_ext] 添加了它自己的一项。N3 CONVERSION [CreatesAllLimits] 和 [StrictlyCreatesLimits] 是不同类型；目标运输一个其中每种类型的成员，并且彼此之间没有归属关系。按照树自身的约定而不是形状进行分类：错误包含 [无法统一 "CreatesLimit K Grp_Forget" 和 "StrictlyCreatesLimit K Grp_Forget"]，并且这个树中的 TYPING 负类型是与没有此类条款的类型不匹配。
N4 转换 创建的组依赖于提供给它的限制预言机，从定义上说：在 [ConeSet_Complete] 上，承载者是 [cone_apex]（下面的控制）而不是 [Sets_limit_obj]，尽管两者通过 [limit_unique_iso] 在典型意义上是同构的。这就是为什么目标的五个 [grp_complete_*] 读回保持真实——它们是关于 [Sets_Complete] 选择的限制的陈述，而不是关于限制的一般陈述。

在这个整个文件的副本中，每个负号都是一次性删除的——
   而不是预先的前言加命令的草稿，这样会删除 [Section] 的 [Context] 和本地 [Universes]/[Constraint] 声明，并且拒绝的原因与声明无关——单独编译，并读取其完整错误。每个负号命名的常量也出现在每个 [Fail] 之外的 [Check] 中，因此重命名会明显破坏此文件，而不是抽象地将 [Fail] 变为绿色。机械测量：25 个标识符出现在 [Fail] 中，其中 21 个也出现在每个 [Fail] 之外，四个例外完全是关键字本身、[Fail] 声明的两个名称（它们从未进入环境）以及仪器故意省略的一个。重命名模拟 2/2 作用于负号命名的目标常量——[sets_limit_ext] 和 [Grp_Forget_creates_limits]——每次重命名都会在 [Check] 保护行处破坏此文件，从不在 [Fail] 内。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A name that is not in scope: if the harness were reporting [Fail]
   successes as failures, or vice versa, this line would say so.

--------
一个不在作用域内的名称：如果测试框架将 [Fail] 的成功报告为失败，或者相反，这一行会说明的。
*)

Fail Check probe411_no_such_constant.

(** ** Guards: every constant a negative names, named outside every [Fail] / ** 守卫：每个常量都是负面名称，在每个 [Fail] 外命名 *)

Check @IsALimit.
Check @Cone.
Check @sets_limit_ext.
Check @StrictlyCreatesLimits.
Check @CreatesAllLimits.
Check @Grp_Forget_creates_limits.
Check @Grp_Forget_StrictlyCreatesLimits.
Check @Grp_Forget.
Check @Grp_Complete.
Check @grp_setoid.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @ConeSet_Complete.
Check @Sets_Complete.
Check @creates_limits_Complete.

(** ** N1, N2: the universe boundary, with [Cone] as the control / ** N1, N2：宇宙边界，以 [Cone] 作为控制 *)

Section UniverseBoundary.

Universes jo jh so sso.
Constraint jh < so.
Constraint so < sso.

Context (Ju : Category@{jo jh jh}).
Context (Fj : Ju ⟶ Sets@{so sso}).
Context (cu : obj[Sets@{so sso}]).

(*
Controls: the shape, the diagram and a cone over it are all formable at
   these levels.

--------
控制：在这些级别上，形状、图表以及其上的圆锥都可以成形。
*)
Check Ju.
Check Fj.
Check (@Cone Ju Sets@{so sso} Fj).

(* N1: UNIVERSE -- the donor. / N1：宇宙——捐赠者。 *)
Fail Check (@IsALimit Ju Sets@{so sso} Fj cu).

(* N2: UNIVERSE -- inherited; fires at the functor argument. / N2：宇宙——继承；对函子参数进行触发。 *)
Fail Check (@sets_limit_ext Ju Fj cu).

End UniverseBoundary.

(** ** N3: the two creation classes are different types / ** N3：这两个创作类别是不同类型 *)

Check (Grp_Forget_creates_limits : CreatesAllLimits Grp_Forget).
Check (Grp_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Grp_Forget).

Fail Definition probe411_n3 : StrictlyCreatesLimits Grp_Forget :=
  Grp_Forget_creates_limits.

(** ** N4: the created group depends on the limit oracle / ** N4：创建的组取决于限制预言机 *)

(*
The same creation theorem fed Mac Lane's cone-set oracle instead of the
   compatible-family one.  Built here rather than in the library file: it is
   a second [Complete Grp] and must not become the one a consumer sees.

--------
相同的创建定理喂给了麦克莱恩的锥集预言器，而不是兼容族预言器。在这里构建，而不是在库文件中：它是第二个 [Complete Grp]，不能成为消费者看到的那个。
*)

Definition Grp_ConeSet_Complete : @Complete Grp :=
  creates_limits_Complete Grp_Forget ConeSet_Complete Grp_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (K : J ⟶ Grp).

(* Control: over the cone-set oracle the carrier IS [cone_apex]. / 控制：在圆锥集神谕上，承载者是 [cone_apex]。 *)
Example probe411_ctrl_coneset :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K]) = cone_apex (Grp_Forget ◯ K)
  := eq_refl.

(* N4: CONVERSION. / N4：转换。 *)
Fail Example probe411_n4 :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K])
    = Sets_limit_obj (Grp_Forget ◯ K) := eq_refl.

(*
Control: over the compatible-family oracle it IS [Sets_limit_obj] --
   the target's own [grp_complete_carrier], restated here so that the
   negative's discriminating partner sits beside it.

--------
控制：在兼容系列的 Oracle 上，它是 [Sets_limit_obj] —— 目标自身的 [grp_complete_carrier]，在此重述，以便负面的判别伙伴坐在其旁边。
*)
Example probe411_ctrl_sets :
  grp_setoid (vertex_obj[Grp_Complete J K]) = Sets_limit_obj (Grp_Forget ◯ K)
  := eq_refl.

End Oracle.
