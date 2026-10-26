(* * * Additional category-specific tactics and [cat] hint database / * 面向范畴的额外策略与 [cat] 提示库 *)

(*
 This file supplements [Lib/Tactics.v] with tactics and hints aimed at the
 recurring shapes of categorical goals: building morphisms by composition,
 simplifying functor application, and closing setoid goals up to
 associativity and respectfulness ([Proper]).  Most of these are wired into
 a single discriminated auto database, [cat], so that [auto with cat] /
 [eauto with cat] can chase the obligations that arise when reasoning about
 universal properties (see [Structure/UniversalProperty*.v], the principal
 clients).

 Unlike the [categories] rewrite database from [Lib/Tactics.v] (consumed by
 [autorewrite]), the [cat] database created here is an *auto* database: its
 externs run goal-directed tactics, and it is searched by [auto]/[eauto].

 These tactics are project-internal conveniences with no external reference;
 the ideas they build on (setoid rewriting, [Proper]/respectful morphisms,
 discriminated hint databases) are standard Coq/Rocq machinery.  None of the
 tactics here cheats: each either makes progress and (for the [solve]-backed
 ones) closes the goal, or fails; none introduces an axiom. 

 --------
 本文件补充 [Lib/Tactics.v]，提供针对范畴证明中反复出现形状的策略与提示：用复合构造态射、化简函子应用，以及在结合律与尊重性（[Proper]）下关闭 setoid 目标。其中多数接入单一判别 auto 库 [cat]，使 [auto with cat]/[eauto with cat] 能追踪关于泛性质推理时产生的义务（见 [Structure/UniversalProperty*.v]，主要客户）。

 与 [Lib/Tactics.v] 的 [categories] rewrite 库（供 [autorewrite] 消费）不同，此处创建的 [cat] 是 *auto* 库：其 extern 运行目标导向策略，由 [auto]/[eauto] 搜索。

 这些策略是项目内部便利设施，无外部文献对应；其所基于的思想（setoid 重写、[Proper]/尊重态射、判别提示库）是标准 Coq/Rocq 机制。此处策略皆不作弊：要么推进并（对基于 [solve] 者）关闭目标，要么失败；不引入公理。
*)

Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.

(* Let [auto] close trivial reflexive goals (e.g. [equiv] reflexivity). / 让 [auto] 关闭平凡自反目标（如 [equiv] 自反） *)
#[export] Hint Extern 1 => reflexivity : core.

(*
 Build a hom [x ~> z] from a hom hypothesis by composing on the matching
 side; the remaining factor is left as a subgoal.  [multimatch] lets
 backtracking try both orientations. 

 --------
 通过在匹配一侧复合，从 hom 假设构造 [x ~> z]；剩余因子留给子目标。[multimatch] 使多解可回溯。
*)
Ltac compose_reduce :=
  multimatch goal with
  | [ f : @hom ?C ?x ?y  |- @hom ?C ?x ?z ] => refine (@compose C x y z _ f)
  | [ f : @hom ?C ?y ?z  |- @hom ?C ?x ?z ] => apply (@compose C x y z f)
  end.

(*
 The [cat] auto database: discriminated so externs are indexed by goal head. 

 --------
 [cat] auto 库：经判别索引，extern 按目标头分类。
*)
Create HintDb cat discriminated.

#[export]
Hint Extern 1 (@hom _ _ _) => compose_reduce : cat.

(* Last-resort hom step: apply a [SetoidMorphism] found in the context. / 最后手段的 hom 步：应用上下文中找到的 [SetoidMorphism]。 *)
Ltac apply_setoid_morphism :=
  match goal with
  | [ H : context[SetoidMorphism ] |- _ ] =>  apply H
  end.

#[export]
Hint Extern 20 => apply_setoid_morphism : cat.

(*
 This is tempting but the “proper” script calls
 intuition, which calls auto with *, so “proper”
 should probably be a top-level command only. 

 --------
 这很诱人，但 “proper” 脚本调用 intuition，而 intuition 调用 auto with *，故 “proper” 若加入 cat 会引起循环。
*)
(* Hint Extern 1 (Proper _ _) => proper : cat. / Hint Extern 1 (Proper _ _) => proper : cat. *)
(* Similarly with cat_simpl. / 对 cat_simpl 同理。 *)
(* Hint Extern 20 => progress(cat_simpl) : cat. / Hint Extern 20 => progress(cat_simpl) : cat. *)
(* Hint Extern 40 (@hom _ _ _) => hom_to_homset : cat. / Hint Extern 40 (@hom _ _ _) => hom_to_homset : cat. *)
#[export] Hint Immediate id : cat.

(*
 Split a [sigT] goal into its witness and proof, leaving the witness open. 

 --------
 把 [sigT] 目标分裂为见证与证明，见证保持开放。
*)
Ltac split_exists := unshelve eapply existT.
#[export] Hint Extern 1 (@sigT _ _) => split_exists : cat.

(*
 Reduce [fobj]/[fmap] applied to a literal [Build_Functor] record to the
 corresponding field by unfolding the projection. 

 --------
 把应用到字面 [Build_Functor] 记录的 [fobj]/[fmap] 经 unfold 化为对应字段。
*)
Ltac functor_simpl :=
  match goal with
  | [ |- context[@fobj _ _ (Build_Functor _ _ _ _ _ _ _)]] => unfold fobj
  | [ |- context[@fmap _ _ (Build_Functor _ _ _ _ _ _ _)]] => unfold fmap
  end.
#[export] Hint Extern 10 => functor_simpl : cat.
#[export] Hint Extern 10 (hom _ _ _) => progress(simpl hom) : cat.
#[export] Hint Extern 40 => progress(cbn in *) : cat.
#[export] Hint Extern 4 (SetoidMorphism _ _) => unshelve eapply Build_SetoidMorphism : cat.
#[export] Hint Extern 4 (hom _ (_ × _)) => apply fork : cat.
#[export] Hint Unfold forall_relation : cat.
#[export] Hint Extern 1 (@equiv _ _ _ _) => reflexivity : cat.
#[export] Hint Extern 1 (@equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _))
     => simple apply compose_respects : cat.

(*
 Prove two composites equivalent by reassociating to one side (trying both
 orientations) and then matching factors with [compose_respects]; trivial
 factors are discharged by [reflexivity], the rest left as subgoals. 

 --------
 通过重结合到一侧（尝试两个方向）再逐因子证明，证两复合等价。
*)
Ltac compose_respects_script :=
first [repeat(rewrite <- comp_assoc);
       apply compose_respects; try(reflexivity)
      |repeat(rewrite -> comp_assoc);
       apply compose_respects; try(reflexivity)].

#[export] Hint Extern 20 (@equiv _ (@homset _ _ _) (@compose _ _ _ _ _ _) (@compose _ _ _ _ _ _))
     => compose_respects_script : cat.

#[export] Hint Extern 10 => progress(autorewrite with categories) : cat.
#[export] Hint Extern 5 => (progress(simplify)) : cat.
#[export] Hint Rewrite <- @comp_assoc : categories.

(*
 Close [f _ ≈ f _] (or the binary [f _ _ ≈ f _ _]) from a [Proper _ f]
 hypothesis: unfold the respectful relation to expose the congruence and
 finish with [auto with cat].  [solve] makes this all-or-nothing. 

 --------
 从 [Proper _ f] 假设关闭 [f _ ≈ f _]（或二元 [f _ _ ≈ f _ _]）：展开尊重性并应用。
*)
Ltac unfold_proper :=
  match goal with
  | [ H : Proper _ ?f |- ?f _ ≈ ?f _ ] => unfold Proper, "==>" in H; simpl in H; assert (QQ:= H)
  | [ H : Proper _ ?f |- ?f _ _ ≈ ?f _ _ ] => unfold Proper, "==>", forall_relation in H;
                                              simpl in H; assert (QQ:= H)
  end; solve [auto with cat].
#[export] Hint Extern 4 (@equiv _ _ (?f _) (?f _)) => unfold_proper : cat.

