Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.Limit.

Generalizable All Variables.

(** * Probe: the measured boundaries of Construction/Product/Limit.v / * 探针：Construction/Product/Limit.v 的测量边界 *)

(*
Companion to Construction/Product/Limit.v (Mac Lane, Categories for the
   Working Mathematician, 2nd ed., §V.2 Exercise 2; Riehl, Category Theory
   in Context, §3.4 Exercise 3.4.v).  Everything that file claims at
   [eq_refl] is shipped there as an [Example], so it guards itself; what
   it cannot guard from inside are the REFUSALS its header records and the
   universe boundary a consumer meets.  Those are pinned here, from OUTSIDE
   the target, because an in-file [Fail] renames in lockstep with the
   constant it guards and so cannot detect a rename.

   SEVEN negatives of TWO kinds — five CONVERSION, two UNIVERSE (each
   pinned by TWO [Fail] commands, the donor and an inherited refusal) —
   told apart by the error TEXT rather than by label, plus one scope-free
   instrument check: nine [Fail] commands beyond the instrument.  The
   kinds were read off the messages actually produced by stripping each
   [Fail] in turn.
   Note N5 in particular: it LOOKS like a typing negative (a wrong
   ascription) but its message carries a [cannot unify] clause, and a
   TYPING negative in this tree is a has-type mismatch with NO such
   clause, so it is classified as conversion.

     N1  CONVERSION  [FCone Fst (prod_cone N1 N2)] is not [N1] as a whole
                   RECORD, though its apex and every leg are [N1]'s on the
                   nose (the two controls beside it): the coherence field is
                   a rebuilt proof and [≈] is Type-valued.
     N2  CONVERSION  The apex of [prod_cone (FCone Fst N) (FCone Snd N)] is
                   [(fst n, snd n)] and not [n]: a [prod] has no
                   definitional eta.  This is why [prod_reflect] goes
                   through the cone isomorphism [prod_cone_iso], whose apex
                   isomorphism is [(id, id)] (the control).
     N3  CONVERSION  [pi_cone (fun i => FCone (PiCat_Proj D i) N)] is not
                   [N] as a whole record EITHER, although here BOTH the apex
                   and every leg are [N]'s on the nose by function eta (the
                   two controls) — so the difference is located exactly in
                   the coherence field, and [pi_cone_iso]'s apex isomorphism
                   is [iso_id].
     N4  CONVERSION  [Opposite (PiCat D)] is not [PiCat (fun i => Opposite
                   (D i))]: [PiCat]'s law fields are [Program] obligations,
                   so the two records differ in those fields although their
                   objects, homs, identities and composition agree.  The
                   control is [Product_Opposite] restated: for the BINARY
                   product the same equation closes by [eq_refl], which is
                   what makes [Product_Cocomplete] free and leaves
                   [PiCat_Cocomplete] undelivered.
     N5  CONVERSION  [Fst_PreservesLimitCone K] ascribed at
                   [PreservesLimitCone K Snd] is refused with [cannot unify
                   "Cone (Snd ◯ K)" and "Cone (Fst ◯ K)"] — the two
                   preservation types unfold to quantifications over
                   different cone types — against the correct ascription as
                   its control.  No universe clause.
     N6  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   factors' homs, the diagram [K : Ju ⟶ Cu ∏ Du] and a
                   [Cone] over it are ACCEPTED while the composite
                   [Fst ◯ K] is refused: [Compose] is declared over three
                   categories sharing ONE hom-and-proof level, and that is
                   the identification every constant of the target
                   inherits (its blocks carry [u0 = u2], [u0 = u4],
                   [u0 = u6], the shape's hom level against both factors'
                   and the product's).  [prod_cone K] is refused at the same
                   levels, firing at that composite.
     N7  UNIVERSE  The [PiCat] half carries a SECOND identification the
                   binary half does not, on the INDEX: at an index type
                   declared strictly ABOVE the factors' hom-and-proof level,
                   [PiCat Du] itself is ACCEPTED (its block is bounds only)
                   while [PiCat_Proj Du] is refused with [Cannot enforce dh
                   = … because dh < ii] — that constant's own binder reads
                   [C : I → Category@{u1 u u}], index at hom level — and so
                   is [PiCat_Complete], whose BINDER reads
                   [D : I → Category@{u5 u u}] with no block equation at all;
                   both refusals fire at the argument [Du], so the inherited
                   constant is not measured apart from the donor.  Every
                   [PiCat]-side constant of the target (twelve) carries it,
                   eleven in the block ([u = u1], [u = u3], [u = u5] in
                   [pi_cone]) and [PiCat_Complete] in the binder alone.
                   Found by the fess audit of the first commit, whose
                   header attributed everything to [Compose].

   Each negative was stripped ONE AT A TIME in a copy of this WHOLE file —
   not a preamble-plus-command scratch, which would drop the [Section]'s
   [Context] and local [Universes]/[Constraint] declarations and refuse for
   a reason unrelated to the claim — compiled alone, and its whole error
   read.  Every constant a negative names also appears in a [Check] outside
   every [Fail], so a rename breaks this file loudly instead of turning a
   [Fail] vacuously green.

--------
Construction/Product/Limit.v 的配套（Mac Lane，《为在职数学家准备的范畴论》，第 2 版，§V.2 练习 2；Riehl，《背景中的范畴论》，§3.4 练习 3.4.v）。该文件在 [eq_refl] 声称的所有内容都作为 [Example] 发送到那儿，因此它自我保护；它无法从内部防护的是其头部记录的 REFUSALS 以及消费者遇到的宇宙边界。那些从目标之外固定在这里，因为文件内的 [Fail] 会与它保护的常量同步重命名，因此无法检测到重命名。

七个负项，分为两类——五个转换类(TWO kinds)，两个全局类(UNIVERSE)，每个都由两个[Fail]命令固定，一个来自捐赠者，一个是继承的拒绝——通过错误文本而不是标签来区分，再加上一个无作用域的工具检查：工具之外的九个[Fail]命令。类型是通过读取实际生成的消息来确定的，每次依次剥离每个[Fail]。特别注意N5：它看起来像是输入类型的负项（一个错误归属），但它的消息包含[cannot unify]条款，而在此树中的输入类型负项是类型不匹配且没有这样的条款，因此被归类为转换类。

N1  转换  [FCone Fst (prod_cone N1 N2)] 整体上不是 [N1] 记录，虽然它的顶点和每条腿都是 [N1] 的正好（旁边的两个控制）：一致性场是重建的证明，[≈] 是类型值。 N2  转换  [prod_cone (FCone Fst N) (FCone Snd N)] 的顶点是 [(fst n, snd n)] 而不是 [n]：一个 [prod] 没有定义性 eta。这就是为什么 [prod_reflect] 通过圆锥同构 [prod_cone_iso]，其顶点同构是 [(id, id)]（控制）。
N3  转换  [pi_cone (fun i => FCone (PiCat_Proj D i) N)] 并不是 [N] 作为整体记录，尽管这里顶点和每一条路径在功能η（两个控制）上都是 [N] 的——所以差异正好位于相干场中，且 [pi_cone_iso] 的顶点同构是 [iso_id]。N4  转换  [Opposite (PiCat D)] 并不是 [PiCat (fun i => Opposite (D i))]：[PiCat] 的律场是 [Program] 的义务，因此尽管它们的对象、态射、恒等和复合相同，这两个记录在那些字段上有所不同。
控制是 [Product_Opposite] 重述的：对于 BINARY 产品，相同的方程通过 [eq_refl] 闭合，这就是使 [Product_Cocomplete] 免费并使 [PiCat_Cocomplete] 未交付的原因。N5 转换 [Fst_PreservesLimitCone K] 在 [PreservesLimitCone K Snd] 处归属被拒绝，提示 [无法统一 "Cone (Snd ◯ K)" 和 "Cone (Fst ◯ K)"] —— 这两种保持类型展开为不同锥类型上的量化 —— 与作为其控制的正确归属类型相悖。没有宇宙子句。
N6 宇宙 在一个其同态严格低于因子同态的形中，图 [K : Ju ⟶ Cu ∏ Du] 及其上的 [Cone] 被接受，而复合体 [Fst ◯ K] 被拒绝：[Compose] 声明在三个共享同一个同态与证明层次的范畴上，而这是目标的每个常量继承的标识（其区块带有 [u0 = u2]、[u0 = u4]、[u0 = u6]，即该形的同态层次，相对于因子和乘积）。[prod_cone K] 在相同层次被拒绝，在该复合体上触发。
N7 宇宙 [PiCat] 的一半携带了二进制半部分没有的第二个标识，在索引上：在严格高于因子的同态与证明级别声明的索引类型上，[PiCat Du] 本身被接受（它的块仅限于边界），而 [PiCat_Proj Du] 被拒绝并显示 [无法强制 dh = … 因为 dh < ii] —— 该常量自身的绑定器读取为 [C : I → Category@{u1 u u}]，索引在同态级别 —— [PiCat_Complete] 也是如此，其绑定器读取为 [D : I → Category@{u5 u u}]，完全没有块方程；两次拒绝都发生在参数 [Du] 上，因此继承的常量没有脱离捐赠者而被测量。
目标的每一个 [PiCat] 端常量（共十二个）都携带它，区块中有十一 个（[u = u1]、[u = u3]、[u = u5] 在 [pi_cone] 中）以及 [PiCat_Complete] 单独在绑定器中。由第一次提交的 fess 审计发现，其头部将所有归因于 [Compose]。

在这个完整文件的副本中，每个负值都是一次性被剥离的——而不是一个前言加命令的草稿，这会丢失 [Section] 的 [Context] 和本地 [Universes]/[Constraint] 声明，并由于与声明无关的原因而拒绝——单独编译，并读取其完整的错误。每个负值命名的常量也出现在每个 [Fail] 外的 [Check] 中，因此重命名会大声破坏该文件，而不是使 [Fail] 空洞地变为绿色。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A name that is not in scope: if the harness were reporting [Fail]
   successes as failures, or vice versa, this line would say so.

--------
一个不在作用域内的名称：如果测试框架将 [Fail] 的成功报告为失败，或者相反，这一行会说明的。
*)

Fail Check probe418_no_such_constant.

(** ** Guards: every constant a negative names, named outside every [Fail] / ** 守卫：每个常量都是负面名称，在每个 [Fail] 外命名 *)

Check @prod_cone.
Check @prod_cone_iso.
Check @FCone.
Check @Fst.
Check @Snd.
Check @Compose.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @pi_cone.
Check @PiCat.
Check @PiCat_Proj.
Check @PiCat_Complete.
Check @Opposite.
Check @Product.
Check @Product_Opposite.
Check @PreservesLimitCone.
Check @Fst_PreservesLimitCone.
Check @Snd_PreservesLimitCone.

(** ** N1, N2: the binary pairing against its projections / ** N1, N2：二进制配对与其投影 *)

Section BinaryRecords.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls: apex and legs of the projected pairing ARE the first cone's. / 控制：投影配对的顶点和腿是第一个圆锥的。 *)
Example probe418_ctrl_fst_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[FCone Fst (prod_cone K N1 N2)] = vertex_obj[N1] := eq_refl.

Example probe418_ctrl_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K))
  (x : J) :
  cone_leg (FCone Fst (prod_cone K N1 N2)) x = cone_leg N1 x := eq_refl.

(* N1: CONVERSION — the whole record is not. / N1: 转换 — 整个记录不是。 *)
Fail Example probe418_n1 (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  FCone Fst (prod_cone K N1 N2) = N1 := eq_refl.

(* N2: CONVERSION — no eta for [prod] on the apex. / N2：转换——[prod] 在顶点上的到达时间未知。 *)
Fail Example probe418_n2 (N : Cone K) :
  vertex_obj[prod_cone K (FCone Fst N) (FCone Snd N)] = vertex_obj[N]
  := eq_refl.

(*
Control: the cone isomorphism the target uses instead, with apex
   isomorphism [(id, id)].

--------
控制：目标使用的圆锥同构，顶点同构为 [(id, id)]。
*)
Example probe418_ctrl_prod_iso (N : Cone K) :
  to `1 (prod_cone_iso K N) = (id, id) := eq_refl.

End BinaryRecords.

(** ** N3: the family pairing against its projections / ** N3：家庭与其投射的对抗 *)

Section FamilyRecords.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

(* Controls: apex AND legs agree on the nose, by function eta. / Controls: apex AND legs agree on the nose, by function eta. / 控制：顶点和腿部在功能上对鼻子达成一致，由 eta 决定。 *)
Example probe418_ctrl_pi_apex (N : Cone K) :
  vertex_obj[pi_cone K (fun i => FCone (PiCat_Proj D i) N)] = vertex_obj[N]
  := eq_refl.

Example probe418_ctrl_pi_leg (N : Cone K) (x : J) :
  cone_leg (pi_cone K (fun i => FCone (PiCat_Proj D i) N)) x = cone_leg N x
  := eq_refl.

(* N3: CONVERSION — the whole record is not; only the coherence differs. / N3：转换——整个记录不是；只有连贯性不同。 *)
Fail Example probe418_n3 (N : Cone K) :
  pi_cone K (fun i => FCone (PiCat_Proj D i) N) = N := eq_refl.

End FamilyRecords.

(**
** N4: the opposite of a set-indexed product is not a set-indexed product
       of opposites on the nose

--------
** N4：集合索引积的对立面不是严格意义上的对立元素的集合索引积
*)

(*
Control: for the binary product it is — Construction/Product.v's
   [Product_Opposite], restated.

--------
控制：对于二元产品，它是——Construction/Product.v 的 [Product_Opposite]，已重述。
*)
Example probe418_ctrl_binary_op (C D : Category) :
  Opposite (C ∏ D) = (Opposite C ∏ Opposite D) := eq_refl.

(* N4: CONVERSION. / N4：转换。 *)
Fail Example probe418_n4 {I : Type} (D : I → Category) :
  Opposite (PiCat D) = PiCat (fun i => Opposite (D i)) := eq_refl.

(** ** N5: the two projections' preservation witnesses are not interchangeable / ** N5：这两个投影的保存见证人不可互换 *)

Section Handedness.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Controls. / 控制。 *)
Check (Fst_PreservesLimitCone K : PreservesLimitCone K Fst).
Check (Snd_PreservesLimitCone K : PreservesLimitCone K Snd).

(* N5: CONVERSION. / N5：转换。 *)
Fail Check (Fst_PreservesLimitCone K : PreservesLimitCone K Snd).

End Handedness.

(** ** N6: the universe boundary, with the functor and the cone as controls / ** N6：宇宙边界，使用函子和圆锥作为控制 *)

Section UniverseBoundary.

Universes jo jh co ch do dh.
Constraint jh < ch.
Constraint jh < dh.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).
Context (K : Ju ⟶ Cu ∏ Du).

(*
Controls: the diagram, a cone over it, and the projection ALONE are all
   formable at these levels — so neither [K] nor [Fst] is the donor.

--------
控件：图表、其上的圆锥以及仅投影在这些层次上都可以形成——因此 [K] 和 [Fst] 都不是供体。
*)
Check K.
Check (@Cone Ju (Cu ∏ Du) K).
Check (@Fst Cu Du).

(*
N6: UNIVERSE — the donor: [Compose] wants one hom level for all three
   categories.

--------
N6：宇宙——捐赠者：[Compose] 希望三类都拥有一个相同等级。
*)
Fail Check (Fst ◯ K).

(* Inherited: [prod_cone] mentions that composite in its type. / 继承：[prod_cone] 提到其类型中的复合。 *)
Fail Check (prod_cone K).

End UniverseBoundary.

(**
** N7: the index boundary of the [PiCat] half, with [PiCat] itself as the
       control

--------
** N7：[PiCat] 半部分的索引边界，[PiCat] 本身作为控制
*)

Section IndexBoundary.

Universes pi_i pi_h.
Constraint pi_h < pi_i.

Context (Iu : Type@{pi_i}).
Context (Du : Iu -> Category@{pi_i pi_h pi_h}).

(*
Control: the set-indexed product itself is formable at an index declared
   strictly above the factors' homs — its block carries bounds only.

--------
控制：集合索引的积本身可以在一个严格高于因子的同态的索引处形成——它的块仅携带界限。
*)
Check (PiCat Du).

(*
N7: UNIVERSE — the donor: [PiCat_Proj]'s binder [C : I → Category@{u1 u u}]
   puts the index at the factors' hom-and-proof level.

--------
N7：宇宙——捐赠者：[PiCat_Proj] 的文件夹 [C : I → Category@{u1 u u}] 将索引置于因素的 hom 和 proof 级别。
*)
Fail Check (PiCat_Proj Du).

(*
Inherited: [PiCat_Complete] reads [D : I → Category@{u5 u u}] in its
   BINDER with no block equation, and is refused at its [Du] argument.

--------
继承自：[PiCat_Complete] 在其 BINDER 中读取 [D : I → Category@{u5 u u}]，没有阻塞方程，并且在其 [Du] 参数处被拒绝。
*)
Fail Check (@PiCat_Complete Iu Du).

End IndexBoundary.
