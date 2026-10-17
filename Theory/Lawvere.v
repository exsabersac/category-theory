Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(** * Lawvere theories *)

(* nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   经典意义下的 Lawvere 理论是有有限积的范畴，其对象（双射于）自然数，对象 [n] 是
   对象 [1] 的 n 重积——故 [0] 是终对象，对象上的积是加法。

   在本库基于 setoid、宇宙多态的设定中，我们镜像 [Construction/PROP.v] 的 [PROP] 类的
   放松形状：不直接断言 [obj law_cat = nat]，而是提供命名函数
   [law_of_nat : nat -> obj]，连同对象上的命题严格相等（本库中 [=] 在 Type 层的许可用法——
   态射相等永远是 [≈]）：

     law_zero_terminal : law_of_nat 0 = 1        （终对象）
     law_plus_product  : law_of_nat m × law_of_nat n = law_of_nat (m + n)

   这些在 Leibniz 层把笛卡尔结构绑到 ℕ 上的加法幺半群，并在骨骼基实例上由 [eq_refl]
   消解（彼处对象确实是自然数）。

   与 [PROP] 一样，本类*不*要求 [law_of_nat] 在对象上双射（甚至满射）。省略双射性
   捕捉放松的「类 Lawvere 理论」概念——对象幺半群由 ℕ 在积下生成的笛卡尔范畴——
   对函子语义开发已足够。需要到达全部对象的消费者将其作为显式假设陈述
   （Theory/Lawvere/Sets.v 如此）。 *)

(*
   Functorial semantics: theory as 范畴, model as 函子

   本节说明相关定义、性质与动机。 nLab: https://ncatlab.org/nlab/show/Lawvere+theory Thesis: Lawvere, "Functorial Semantics Algebraic Theories", Ph.D. thesis, Columbia University, 1963 (reprinted Reprints Theory Applications 范畴 No.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class LawvereTheory : Type := {
  law_cat : Category;

  law_terminal : @Terminal law_cat;
  law_cartesian : @Cartesian law_cat;

  (** The canonical object correspondence: every natural number names an
      object of [law_cat], with [0] the terminal object and addition
      reflecting binary products. *)
  law_of_nat : nat → law_cat;

  law_zero_terminal :
    law_of_nat 0%nat = @terminal_obj law_cat law_terminal;

  law_plus_product : ∀ m n : nat,
    (@product_obj law_cat law_cartesian (law_of_nat m) (law_of_nat n))
    = law_of_nat (m + n)%nat
}.

Coercion law_cat : LawvereTheory >-> Category.

(*
   * ** Powers of the generic 对象

   本节说明相关定义、性质与动机。 [law_pow n] is explicit n-fold 积 [law_of_nat 1] (right-nested, empty 积 终对象), [law_pow_one] is propositional equality chain showing it agrees [law_of_nat n] — induction from [law_zero_terminal] [law_plus_积].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LawverePow.

Context {T : LawvereTheory}.

Fixpoint law_pow (n : nat) : law_cat :=
  match n with
  | O => @terminal_obj law_cat law_terminal
  | S k => @product_obj law_cat law_cartesian (law_of_nat 1%nat) (law_pow k)
  end.

Theorem law_pow_one (n : nat) : law_pow n = law_of_nat n.
Proof.
  induction n as [|k IH]; simpl.
  - symmetry; apply law_zero_terminal.
  - rewrite IH. apply (law_plus_product 1%nat k).
Defined.

End LawverePow.

