Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(*
Regression test for issue #213 ("Broken in Rocq CI").

   Rocq's own CI builds this library against Rocq master, and it started
   failing in Instance/Adjoints.v with

       File "./Instance/Adjoints.v", line 104, characters 35-45:
       Error: No such assumption.

   Characters 35-45 of that line are the [assumption] of

       Next Obligation.
         equivalence.
         - transitivity (free_functor y); assumption.
         - transitivity (forgetful_functor y); assumption.
       Qed.

   the [Equivalence] obligation of [adj_morphism_setoid], whose relation is a
   PAIR of natural isomorphisms.  Nothing about that proof mentions symmetry,
   and that was the problem.  [equivalence] splits the goal into its three laws
   and discharges each; the reflexivity and symmetry components of the pair
   were closed only because the tactic reached [solve_crelation], a
   PATTERN-LESS [Hint Extern] in the standard library's [crelations] database,
   through a wide [auto].  Which pattern-less hints a wide [auto] reaches, and
   in what order, is a property of the hint database, not anything this library
   states.

   The break was introduced on our side: the commit that narrowed
   [equivalence]'s fallback from [auto with *] to [auto with category_laws]
   removed the tactic's own path to that hint.  The proofs kept building on the
   released Rocq versions only because the [intuition] step inside
   [equivalence] has its own wide [auto with *] leaf, which on those versions
   still reached [solve_crelation].  On Rocq master that leaf no longer reaches
   it, so symmetry stopped being discharged, the first bullet landed on
   [free_functor y ≅ free_functor x] instead of the transitivity goal it was
   written for, and [assumption] was left facing [free_functor y ≅ free_functor
   y].

   The repair is to stop guessing: [adj_morphism_setoid]'s three laws are now
   proved componentwise from [iso_equivalence] (Theory/Isomorphism.v), and
   [equivalence] closes reflexivity and symmetry deterministically and falls
   back only on [category_laws], a database this library populates itself.

   This file pins the invariant that actually matters -- those proofs go
   through with NO wide hint search available at all -- by re-running both the
   old and the repaired script in an environment where the search has been
   taken away, so the fault reproduces on any Rocq version rather than only on
   master.

--------
针对问题 #213（“在 Rocq CI 中损坏”）的回归测试。

Rocq 自己的 CI 使用 Rocq 主分支构建这个库，并且它开始在 Instance/Adjoints.v 中失败

文件 "./Instance/Adjoints.v"，第104行，字符35-45：
       错误：没有这样的假设。

该行的第35-45个字符是[assumption]的

下一个义务。
         等价性。
         - 传递性 (free_functor y); 假设。
         - 传递性 (forgetful_functor y); 假设。
       已证。

[adj_morphism_setoid] 的 [Equivalence] 义务，其关系是一对自然同构。关于该证明没有提到对称性，而这就是问题所在。[equivalence] 将目标分解为三条定律并逐一处理；该对偶的自反性和对称性部分之所以被闭合，仅仅是因为该策略通过广泛的 [auto] 到达了标准库的 [crelations] 数据库中的无模式 [Hint Extern]，即 [solve_crelation]。哪些无模式提示被广泛的 [auto] 触达，以及顺序如何，是提示数据库的属性，而不是此库所说明的内容。

问题是我们这边引入的：那个将 [equivalence] 的回退从 [auto with *] 缩小到 [auto with category_laws] 的提交，移除了该策略自身到该提示的路径。证明之所以一直可以在已发布的 Rocq 版本上进行，只是因为 [equivalence] 内的 [intuition] 步骤有其自身的宽 [auto with *] 叶节点，而在那些版本上，该叶节点仍然可以到达 [solve_crelation]。在 Rocq 主分支上，该叶节点不再到达它，因此对称性不再被释放，第一个要点落在了 [free_functor y ≅ free_functor x] 上，而不是它原本针对的传递性目标，并且 [assumption] 面临 [free_functor y ≅ free_functor y]。

修复是为了停止猜测：[adj_morphism_setoid] 的三条定律现在可以从 [iso_equivalence]（Theory/Isomorphism.v）逐组件地证明，而且 [equivalence] 以确定性方式处理自反性和对称性，并且仅退回到 [category_laws]，这是本库自己填充的数据库。

这个文件固定了实际上重要的恒定——这些证明在完全没有广泛提示搜索可用的情况下仍然可行——通过在已移除搜索功能的环境中重新运行旧脚本和修复后的脚本，因此故障可以在任何 Rocq 版本上复现，而不仅仅是在主分支上。
*)

(*
Take the wide search away.  [intuition]'s default solver is
   [first [solve [auto] | tryif solve [auto with *] then <warn> else idtac]];
   stubbing it out with [idtac] leaves [intuition] its structural work (it
   still splits the pair) while denying it the [auto with *] leaf -- exactly
   the reach that the released Rocq versions still had and Rocq master lost.

--------
去掉广泛搜索。[intuition] 的默认求解器是 [first [solve [auto] | tryif solve [auto with *] then <warn> else idtac]]； 用 [idtac] 进行存根处理会保留 [intuition] 的结构性工作（它仍然会拆分对偶），同时拒绝它获得 [auto with *] 叶子——恰好是已发布的 Rocq 版本仍然拥有而 Rocq master 丢失的可达性。
*)
Ltac Tauto.intuition_solver ::= idtac.

(*
[equivalence]'s body without the deterministic pass and with no wide
   fallback: what the tactic amounts to once neither the explicit search nor
   [intuition]'s implicit one reaches [solve_crelation].

--------
[equivalence] 的主体在没有确定性通行证且没有广泛回退的情况下：当既没有显式搜索也没有 [intuition] 的隐式搜索达到 [solve_crelation] 时，该战术的实际效果。
*)
Ltac equivalence_old :=
  constructor; repeat intro; simpl; try cat; intuition.

Section Issue213.

Context {C : Category}.
Context {D : Category}.

(* Verbatim the relation of [adj_morphism_setoid]. / 逐字记录[adj_morphism_setoid]的关系。 *)
Definition issue_213_rel (f g : @adj_morphism C D) : Type :=
  (free_functor f ≅[Fun] free_functor g) *
  (forgetful_functor f ≅[Fun] forgetful_functor g).

(*
Confirmation of the reported failure mode.  Denied the wide search, the old
   tactic body leaves the two symmetry components open, so the old script's
   bullets no longer line up with the goals they were written for and no amount
   of [transitivity ...; assumption] closes them.  This is the state Rocq
   master reached; it is recorded here so that a future "simplification" back
   to the old script cannot pass unnoticed.

--------
确认报告的故障模式。 拒绝广泛搜索，旧的策略主体将两个对称组件保持开放，因此旧脚本的要点不再与它们原本编写的目标一致，无论多少 [transitivity ...; assumption] 都无法修复它们。 这是 Rocq 主控达到的状态；这里记录下来，以便未来将旧脚本“简化”回去时不会被忽视。
*)
Example issue_213_old_script_needs_the_wide_search : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  (* The negative half: the old script cannot close the goal here. / 消极的一面：旧脚本无法在这里完成目标。 *)
  assert_fails
    (equivalence_old;
     solve [ transitivity (free_functor y); assumption
           | transitivity (forgetful_functor y); assumption ]).
  (*
The positive half, so this stays a live [Qed] rather than an aborted
     sketch: the relation is an equivalence, closed the deterministic way.

--------
正半部分，所以这保持为一个活动的 [Qed]，而不是一个中止的草图：这个关系是一个等价关系，以确定的方式闭合。
*)
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(*
The mechanism, isolated to the one law that went missing: denied the wide
   search, the old tactic body cannot close symmetry -- though symmetry does
   hold, and closes at once by hand.

--------
该机制，仅限于那条丢失的法律：拒绝了广泛的搜索，旧的策略体系无法闭合对称——尽管对称确实存在，并且可以用手立即闭合。
*)
Example issue_213_symmetry_is_the_missing_law : Symmetric issue_213_rel.
Proof.
  unfold issue_213_rel.
  assert_fails (solve [ repeat intro; simpl; try cat; intuition ]).
  intros f g [Hfree Hforget].
  split; symmetry; assumption.
Qed.

(*
The repaired script, run in that same hostile environment: the three laws
   come from [iso_equivalence] componentwise, so no hint search of any width
   is consulted.

--------
在同样的敌对环境中运行的修复脚本：三条定律是从 [iso_equivalence] 组件逐个得出的，因此没有咨询任何宽度的提示搜索。
*)
Example issue_213_equivalence_unaided : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(*
And the library's own [equivalence] -- the real tactic, not a copy of it --
   still takes the very script that broke in Rocq CI.  This is a guard on
   [Lib/Tactics.v] and not merely on a transcript of it: [intuition]'s
   [auto with *] leaf is stubbed out above, and the tactic's remaining
   fallback is [auto with category_laws], a database that carries no hint
   closing [_ ≅ _].  So it is the tactic's own deterministic reflexivity /
   symmetry pass that discharges those two laws here, and deleting that pass
   fails this example.

--------
图书馆自身的 [equivalence] —— 真正的策略，而不是它的副本 —— 仍然使用在 Rocq CI 中失效的脚本。这是对 [Lib/Tactics.v] 的保护，而不仅仅是对其转录本的保护：[intuition] 的 [auto with *] 叶子在上面被存根化，并且该策略剩余的回退是 [auto with category_laws]，一个不包含关闭 [_ ≅ _] 线索的数据库。因此，正是该策略自身的确定性自反性/对称性通道在这里履行了这两条规则，而删除该通道将导致此示例失败。
*)
Example issue_213_tactic_is_deterministic : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  equivalence.
  - transitivity (free_functor y); assumption.
  - transitivity (forgetful_functor y); assumption.
Qed.

(*
Finally, the instance the library actually exports really is an equivalence
   on [adj_morphism], and [≈] resolves to it.

--------
最后，库实际上导出的实例确实在 [adj_morphism] 上是一个等价，而 [≈] 会解析到它。
*)
Example issue_213_setoid_reflexive (f : @adj_morphism C D) : f ≈ f.
Proof. reflexivity. Qed.

Example issue_213_setoid_symmetric (f g : @adj_morphism C D) : f ≈ g → g ≈ f.
Proof. intros; symmetry; assumption. Qed.

Example issue_213_setoid_transitive (f g h : @adj_morphism C D) :
  f ≈ g → g ≈ h → f ≈ h.
Proof. intros; etransitivity; eassumption. Qed.

End Issue213.
