Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.

Generalizable All Variables.

(*
   * * Tactics for strict monoidal categories

   In a [StrictMonoidal] category, the structural isomorphisms
   [tensor_assoc], [unit_left], [unit_right] are identities
   (transported along the object-level Leibniz equalities
   [strict_assoc_obj], [strict_unit_left_obj], [strict_unit_right_obj]).

   The [strict_collapse] tactic rewrites these isomorphisms to their
   transported-identity forms.  After [strict_collapse], the goal is
   free of explicit [tensor_assoc] / [unit_left] / [unit_right]
   references — what remains are dependent-transport-of-identity
   expressions.  In a CONCRETE strict monoidal category where the
   object-level equations are [eq_refl], these transports reduce
   further via [cbn] / [simpl]; in an ABSTRACT setting the transport
   is opaque but can be reasoned about via the [transported_iso_*]
   lemmas in [Strict.v]. 

   --------
   * * 严格单体范畴的策略

   在一个 [StrictMonoidal] 范畴中，结构同构 [tensor_assoc]、[unit_left]、[unit_right] 是恒等映射（沿对象层次的 Leibniz 相等 [strict_assoc_obj]、[strict_unit_left_obj]、[strict_unit_right_obj] 传输）。

   [strict_collapse] 策略将这些同构重写为它们的传输恒等形式。经过 [strict_collapse] 之后，目标不再包含显式的 [tensor_assoc] / [unit_left] / [unit_right] 引用——剩下的是恒等的依赖传输表达式。在对象层方程为 [eq_refl] 的具体严格单体范畴中，这些传输可以通过 [cbn] / [simpl] 进一步化简；在抽象环境中，传输是不可见的，但可以通过 [Strict.v] 中的 [transported_iso_*] 引理进行推理。
*)

(* * ** [strict_collapse]: replace structural isos with transported-id form Rewrites until fixpoint using the six [strict_*_to] / [strict_*_from] lemmas. Use [?] so each pattern is optional — the tactic does not fail if none applies. / * ** [strict_collapse]：将结构同构替换为 transport-id 形式 使用六个 [strict_*_to] / [strict_*_from] 引理反复重写直到达到不变点。使用 [?] 使每个模式成为可选 — 如果没有匹配项，该策略不会失败。 *)
Ltac strict_collapse :=
  repeat (rewrite ?strict_assoc_to ||
          rewrite ?strict_assoc_from ||
          rewrite ?strict_unit_left_to ||
          rewrite ?strict_unit_left_from ||
          rewrite ?strict_unit_right_to ||
          rewrite ?strict_unit_right_from).

(* * ** [strict_collapse_in H]: same, targeting hypothesis [H]. / * ** [strict_collapse_in H]：相同，针对假设 [H]。 *)
Tactic Notation "strict_collapse" "in" hyp(H) :=
  repeat (rewrite ?strict_assoc_to in H ||
          rewrite ?strict_assoc_from in H ||
          rewrite ?strict_unit_left_to in H ||
          rewrite ?strict_unit_left_from in H ||
          rewrite ?strict_unit_right_to in H ||
          rewrite ?strict_unit_right_from in H).

(*
   * ** [strict_collapse_all]: rewrite EVERYWHERE.

   Goal AND every hypothesis. 

   --------
   * **  [strict_collapse_all] ：在每个地方重写。

   目标以及每一个假设。
*)
Ltac strict_collapse_all :=
  repeat (rewrite ?strict_assoc_to in * ||
          rewrite ?strict_assoc_from in * ||
          rewrite ?strict_unit_left_to in * ||
          rewrite ?strict_unit_left_from in * ||
          rewrite ?strict_unit_right_to in * ||
          rewrite ?strict_unit_right_from in *).
