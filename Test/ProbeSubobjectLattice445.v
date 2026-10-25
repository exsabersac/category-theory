Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Orthogonality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Factorization.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Regular.Factorization.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Subobject.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(**
* Probe for Theory/Subobject/Lattice.v, Instance/Sets/SubobjectLattice.v
      and Instance/FinSet/Subobject.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 2, printed p. 126; Riehl, Category Theory in Context, 2nd ed.,
    Definition 4.7.9, printed p. 177; Fong and Spivak, Seven Sketches in
    Compositionality, §1.2.1, printed p. 8.  Issue #445.

    The import list above is the UNION of the three target files' own import
    lists, unabbreviated, plus Theory/Subobject/Functor.v for the one
    readback that needs [sub_reindex].  A short prefix is what makes a probe
    pass vacuously, so nothing is trimmed even where a require is redundant.

    This file guards the strength claims of those three files.  Every
    statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and its
    complete error read; a refutation that holds prints nothing under this
    repo's coqc, so a whole-file rc=0 would establish only THAT each command
    does not typecheck and never WHY.  Each negative is classified by the
    error TEXT, under THIS import list (the parenthetical of a conversion
    error is rendered with the short names in scope, so the same refusal can
    print differently elsewhere):

      TYPING      - "The term T has type X while it is expected to have
                    type Y", with NO trailing "cannot unify" clause and no
                    universe clause.
      CONVERSION  - the same, with a trailing "(cannot unify A and B)".
      FORMABILITY - the statement cannot even be elaborated: an unresolved
                    implicit, "Cannot infer this placeholder", with NO
                    "(no type class instance found)" parenthetical (N3).
      INSTANCE    - an implicit argument of class type that no instance in
                    scope resolves.  The DISCRIMINATOR is the parenthetical
                    "(no type class instance found)", which Rocq appends
                    to either opener -- "Cannot infer the implicit
                    parameter H of ..." (N1, N4) or "Cannot infer this
                    placeholder of type ..." (N7); the opener alone does
                    not separate INSTANCE from FORMABILITY.  NOTE that a
                    bare [Check] TOLERATES such an open evar and succeeds,
                    printing "where ?H : [...]"; every missing-instance
                    negative below is therefore a [Definition], measured to
                    be refused where the [Check] form is accepted.

    The instrument check comes first: a name that does not exist, refused
    for a reason unrelated to any boundary.  Every LIBRARY constant a
    negative names -- in its statement, its section context or its proof
    term -- appears in a positive control outside any refutation command
    (stdlib names such as [Empty_set] and [False] excepted), so that a
    rename cannot leave a negative refused for reference-not-found and
    therefore vacuously green.  An independent audit of the first draft
    found six such constants uncovered ([WidePullback], [IsPullback],
    [IsWidePullback], [ImageOf], [terminal_obj], [Sets_Terminal]); the
    controls below were extended to cover them.

--------
* 探查 Theory/Subobject/Lattice.v、Instance/Sets/SubobjectLattice.v 和 Instance/FinSet/Subobject.v

Mac Lane，《为工作数学家而作的范畴论》，第2版，第V.7节，第126页印刷版定义2；Riehl，《情境中的范畴论》，第2版，第177页印刷版定义4.7.9；Fong 和 Spivak，《组成性中的七个草图》，第1.2.1节，第8页印刷版。问题 #445。

上面的导入列表是三个目标文件自身导入列表的并集，未缩写，加上 Theory/Subobject/Functor.v，用于需要 [sub_reindex] 的回读。一个短前缀会让探针无条件通过，所以即使某个 require 是多余的，也不会被修剪。

该文件保护那三个文件的强度声明。下面声称被驳斥的每个语句都已在该整个文件的副本中去掉了其驳斥关键字，单独编译，并读取其完整错误；在该仓库的 coqc 下，一个有效的驳斥不会打印任何内容，所以整个文件 rc=0 只能说明每个命令无法类型检查，而无法说明原因。每个负面情况根据错误文本分类，在此导入列表下（转换错误的括号内容使用当前作用域内的简短名称呈现，因此相同的拒绝在其他地方可能会有不同显示）：

输入类型（TYPING） - “术语 T 的类型为 X，而预期类型为 Y”，没有尾随的“无法统一”子句，也没有宇宙子句。转换（CONVERSION） - 类似，但带有尾随的“（无法统一 A 和 B）”。可形成性（FORMABILITY） - 该语句甚至无法展开：存在未解决的隐式，‘无法推断此占位符’，没有‘（未找到类型类实例）’的括注（N3）。实例（INSTANCE） - 范围内没有实例可解析的类类型隐式参数。
DISCRIMINATOR 是括号中的“(未找到类型类实例)”，Rocq 将其附加到任一开头——“无法推断隐式参数 H 的 ...”（N1, N4）或“无法推断此占位符的类型 ...”（N7）；仅开头本身并不能将 INSTANCE 与 FORMABILITY 区分开。注意，一个裸的 [Check] 容忍这样的开放 evar 并成功，打印“where ?H : [...]”；因此下面每个缺失实例的负例都是 [Definition]，在接受 [Check] 形式的地方会被拒绝。

仪器检查优先：一个不存在的名称，被拒绝，原因与任何边界无关。每个 LIBRARY 常量的负名称——在其声明、其部分上下文或其证明项中——出现在任何反驳命令之外的正控制中（stdlib 名称如 [Empty_set] 和 [False] 除外），因此重命名不能让一个负名称因未找到引用而被拒绝从而形式上为绿色。对初稿的独立审计发现六个此类常量未被覆盖（[WidePullback]、[IsPullback]、[IsWidePullback]、[ImageOf]、[terminal_obj]、[Sets_Terminal]）；下面的控制已扩展以涵盖它们。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check sub_lattice_no_such_constant.

(** ** Positive controls: every constant the negatives depend on / ** 阳性对照：每一个负对照所依赖的常数 *)

Check @sub_meet.
Check @sub_meet_comm.
Check @sub_meet_is_glb.
Check @sub_wide_intersection.
Check @sub_wide_intersection_IsIntersection.
Check @sub_join.
Check @sub_join_via.
Check @sub_join_via_bot.
Check @sub_join_bot.
Check @sub_bot.
Check @sub_top.
Check @sub_pair.
Check @sub_compose.
Check @sub_reindex.
Check @ImageOf.
Check @ImageOf_of_OFS.
Check @OFS.
Check @MorphismClass.
Check @MonoClass.
Check @EpiClass.
Check @WidePullback.
Check @IsWidePullback.
Check @IsPullback.
Check @binary_wide_pullback.
Check @two_legs.
Check @terminal_obj.
Check @Sets_Terminal.
Check @Sets_HasImages.
Check @Sets_HasWidePullbacks.
Check @Sets_wpull_obj.
Check @fs_union.
Check @fs_pos.
Check @pos_obj.
Check @fs_union_is_positives.
Check @fs_inter_is_empty.
Check @FinSet_HasImages.
Check @ex11_u.
Check @ex11_v.

(** ** Readbacks that HOLD, at the strength stated / ** 按照所述强度保持的回读 *)

Section Readbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
The header of Theory/Subobject/Lattice.v states, and this pins, that the
   binary meet IS the pushforward along u of the reindexing of v along
   sub_mono u -- the same record with the same three fields, at Leibniz
   equality and with no tactic.  Theory/Subobject/Lattice.v does not import
   Theory/Subobject/Functor.v, so the readback lives here.

--------
Theory/Subobject/Lattice.v 的标题指出，并且这确定了，二元交确实是沿着 u 的推前（pushforward）作用到沿 sub_mono u 的 v 的重新索引 —— 使用相同的记录、相同的三个字段，在 Leibniz 等式下且不使用策略。Theory/Subobject/Lattice.v 并没有导入 Theory/Subobject/Functor.v，因此回读在这里进行。
*)
Example p445_meet_is_compose_reindex (u v : SubObj x) :
  sub_meet u v = sub_compose u (sub_reindex (sub_mono u) v) := eq_refl.

End Readbacks.

(*
The FinSet numbers, restated here as the controls the negatives N8 and N9
   are read against: 4 (merging) and 1 (the meet) compute by [eq_refl].

--------
FinSet 数字，在此重新表述为控制负数 N8 和 N9，是针对 4（合并）和 1（交集）由 [eq_refl] 计算读取的。
*)
Example p445_union_four : sub_dom (sub_join ex11_u ex11_v) = 4%nat := eq_refl.
Example p445_meet_one : sub_dom (sub_meet ex11_u ex11_v) = 1%nat := eq_refl.
Example p445_coproduct_five :
  @Coprod FinSet FinSet_Cocartesian 2%nat 3%nat = 5%nat := eq_refl.

(** ** Negatives / ** 负面 *)

Section NoPullbacks.

Context {C : Category}.
Context {x : C}.

(*
N1 -- INSTANCE.  [sub_meet] is conditional on chosen pullbacks; with no
   [HasPullbacks C] in scope the definition is refused with "Cannot infer
   the implicit parameter H of sub_meet whose type is HasPullbacks C (no
   type class instance found)".  Measured: the [Check] form of the same
   term is ACCEPTED, printing the open evar, which is why this is a
   [Definition].

--------
N1 -- 实例。[sub_meet] 取决于所选的回拉；在没有 [HasPullbacks C] 的情况下，定义会被拒绝，并显示“无法推断 sub_meet 的隐式参数 H 的类型为 HasPullbacks C（未找到类型类实例）”。测量结果：相同项的 [Check] 形式被接受，会打印未解决的 evar，这就是为什么这是一个 [Definition]。
*)
Fail Definition n1 (u v : SubObj x) : SubObj x := sub_meet u v.

(*
N3 -- FORMABILITY.  Over an EMPTY index there is no j0 to present the
   intersection at, and the wide pullback is the terminal object rather
   than the top subobject (Structure/Pullback/Wide.v); the hole cannot
   be filled: "Cannot infer this placeholder of type Empty_set".  The
   intersection of the empty family is [sub_top] ([IsIntersection_empty]),
   not anything read off a wide pullback.

--------
N3 -- 可形成性。在一个空索引上，没有 j0 来表示交集，而宽拉回是终对象而不是顶子对象（Structure/Pullback/Wide.v）；这个空洞无法填充：“无法推断此 Empty_set 类型的占位符”。空族的交集是 [sub_top]（[IsIntersection_empty]），而不是从宽拉回中读取的任何东西。
*)
Fail Definition n3 (S : Empty_set → SubObj x)
  (W : WidePullback (fun j => sub_mono (S j))) : SubObj x :=
  sub_wide_intersection S _ W.

End NoPullbacks.

Section WithPullbacks.

Context {C : Category}.
Context `{@HasPullbacks C}.
Context {x : C}.

(*
N2 -- TYPING.  Commutativity of the meet holds at ≈ on [SubObj x] (an
   isomorphism of domains over x) and NOT at Leibniz equality: the two
   chosen pullbacks are different records.  "The term sub_meet_comm u v
   has type sub_meet u v ≈ sub_meet v u while it is expected to have type
   sub_meet u v = sub_meet v u", with no "cannot unify" clause.  The
   statement itself is well-formed; the refusal is at the proof.

--------
N2 -- 输入。 在 [SubObj x]（定义在 x 上的域同构）上，meet 的交换性在 ≈ 下成立，但在 Leibniz 等式下不成立：两个选择的 pullback 是不同的记录。“项 sub_meet_comm u v 的类型为 sub_meet u v ≈ sub_meet v u，但期望类型为 sub_meet u v = sub_meet v u”，没有“无法统一”的条款。该语句本身格式正确；拒绝发生在证明阶段。
*)
Fail Definition n2 (u v : SubObj x) : sub_meet u v = sub_meet v u :=
  sub_meet_comm u v.

(*
N5 -- CONVERSION.  Structure/Pullback/Wide.v's [binary_wide_pullback]
   is stated over [two_fam (sub_dom u) (sub_dom v)], and that family is
   convertible with [fun b => sub_dom (sub_pair u v b)] at the two literals
   but NOT as a function of a variable b: "cannot unify P ~{ C }~>
   two_fam (sub_dom u) (sub_dom v) b and P ~{ C }~> sub_dom (sub_pair u v
   b)" (verbatim, under this import list).  This is
   the measured reason [sub_meet_is_wide_intersection] is proved through
   [IsIntersection_unique] instead of through that lemma.

--------
N5 -- 转换。结构/回拉/宽.v 的 [binary_wide_pullback] 是在 [two_fam (sub_dom u) (sub_dom v)] 上陈述的，并且该系列在两个字面值上可以与 [fun b => sub_dom (sub_pair u v b)] 相互转换，但不能作为变量 b 的函数：“不能统一 P ~{ C }~> two_fam (sub_dom u) (sub_dom v) b 和 P ~{ C }~> sub_dom (sub_pair u v b)”（逐字，根据此导入列表）。这是通过 [IsIntersection_unique] 而不是通过该引理证明 [sub_meet_is_wide_intersection] 的充分理由。
*)
Fail Definition n5 (u v : SubObj x) (P : C)
  (q1 : P ~> sub_dom u) (q2 : P ~> sub_dom v)
  (HP : IsPullback (sub_mono u) (sub_mono v) P q1 q2) :
  IsWidePullback (fun b => sub_mono (sub_pair u v b)) P (two_legs q1 q2) :=
  binary_wide_pullback HP.

End WithPullbacks.

Section NoImages.

Context {C : Category}.
Context `{@Cocartesian C}.
Context {x : C}.

(*
N4 -- INSTANCE.  The join is conditional on images: with a cocartesian
   structure but no [HasImages C], "Cannot infer the implicit parameter H0
   of sub_join whose type is HasImages C (no type class instance found)".
   The [Check] form is accepted, as for N1.

--------
N4 -- 实例。连接依赖于图像：具有余笛卡尔结构但没有 [HasImages C]，“无法推断子连接 sub_join 的隐式参数 H0，其类型为 HasImages C（未找到类型类实例）”。[Check] 形式被接受，与 N1 相同。
*)
Fail Definition n4 (u v : SubObj x) : SubObj x := sub_join u v.

End NoImages.

Section WrongClass.

Context {C : Category}.
Context {E : MorphismClass C}.

(*
N6 -- CONVERSION.  An image as a subobject needs the RIGHT class of the
   factorization system to be the monos, because [fact_m_in] is fed
   directly to the [sub_is_monic] field; an (E, Epi) system is refused:
   "cannot unify EpiClass and MonoClass".

--------
N6 -- 转换。 作为子对象的图像需要分解系统的正确类作为单态，因为 [fact_m_in] 会直接传递到 [sub_is_monic] 字段；(E, Epi) 系统被拒绝："无法统一 EpiClass 和 MonoClass"。
*)
Fail Definition n6 (O : OFS E (@EpiClass C)) {y z : C} (f : y ~> z) :
  ImageOf f := ImageOf_of_OFS O f.

End WrongClass.

Section NoStrictness.

Context {C : Category}.
Context `{I : @Initial C}.
Context {x : C}.

(*
N7 -- INSTANCE.  The bottom subobject needs the arrow out of the initial
   object to be MONIC, which an initial object does not supply by itself:
   "Cannot infer this placeholder of type Monic zero[x] (no type class
   instance found)".  [I] is pinned explicitly because [@Initial C] is a
   notation for [@Terminal (C^op)] and resolution does not see through it,
   which would otherwise add a second, unrelated placeholder to the
   verdict.

--------
N7 -- 实例。底层子对象需要初始对象出的箭头是单射（MONIC），而初始对象本身不能提供：
“无法推断此类型为 Monic zero[x] 的占位符（未找到类型类实例）”。 [I] 被显式固定，因为 [@Initial C] 是 [@Terminal (C^op)] 的记法，而解析无法透过它，否则会给判定添加第二个无关的占位符。
*)
Fail Definition n7 : SubObj x := @sub_bot C I x _.

End NoStrictness.

(*
N8 -- CONVERSION.  Merging versus tagging: the union of {0,1} and
   {1,2,3} inside 4 has FOUR elements (p445_union_four), and the tagged
   count 5 is refused: "cannot unify sub_dom (sub_join ex11_u ex11_v) and
   5%nat".

--------
N8 -- 转换。 合并与标记：{0,1} 和 {1,2,3} 在 4 内的并集有四个元素 (p445_union_four)，而标记计数 5 被拒绝："无法统一子域 (sub_join ex11_u ex11_v) 和 5%nat"。
*)
Fail Example n8 : sub_dom (sub_join ex11_u ex11_v) = 5%nat := eq_refl.

(*
N9 -- CONVERSION.  The meet of the same two has ONE element
   (p445_meet_one); 2, the size of the first factor, is refused: "cannot
   unify sub_dom (sub_meet ex11_u ex11_v) and 2%nat".  So the pullback
   genuinely intersected rather than returning a leg's domain.

--------
N9 -- 转换。同样两者的交集只有一个元素（p445_meet_one）；2，第一个因子的大小，被拒绝：“无法统一 sub_dom（sub_meet ex11_u ex11_v）和 2%nat”。所以这个拉回确实相交，而不是返回某条腿的域。
*)
Fail Example n9 : sub_dom (sub_meet ex11_u ex11_v) = 2%nat := eq_refl.

(*
N10 -- CONVERSION.  In Sets the union of the increasing family is ≈ the
   positive naturals ([fs_union_is_positives], an isomorphism of domains
   over nat) and NOT equal to them on the nose: the image carrier is a
   point of nat with a chosen preimage, not the sig of a positivity proof.
   "cannot unify sub_dom fs_union and pos_obj".

--------
N10 -- 转换。在集合中，递增族的并集≈正自然数（[fs_union_is_positives]，自然数上的域同构），并且并不严格等于它们：像承载的是自然数的一个点，并选取了一个原像，而不是一个正性证明的标记。
“无法统一子域 fs_union 和 pos_obj”。
*)
Fail Example n10 : sub_dom fs_union = pos_obj := eq_refl.

(*
N11 -- CONVERSION.  The empty-index wide pullback in Sets is terminal
   only up to ≅ (Structure/Pullback/Wide.v's [wide_pullback_empty_terminal])
   and is NOT convertible with the chosen terminal setoid: its carrier is
   the setoid of empty coherent families, not [poly_unit].  Refused with
   "cannot unify", the two sides being the wide-pullback object and 1.

--------
N11 -- 转换。在集合中的空索引广拉回是终结的  
仅限于 ≅（Structure/Pullback/Wide.v 的 [wide_pullback_empty_terminal]）  
并且不能与选择的终端集合同构：其载体是空一致族的集合，而不是 [poly_unit]。被拒绝，显示“无法统一”，两边分别是广拉回对象和 1。
*)
Fail Example n11 :
  Sets_wpull_obj (I:=False) (A:=fun i => match i with end)
    (z:=@terminal_obj Sets Sets_Terminal) (fun i => match i with end)
  = @terminal_obj Sets Sets_Terminal := eq_refl.
