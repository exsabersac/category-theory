Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
From Coq Require Import Arith.Peano_dec.
Import ListNotations.

Generalizable All Variables.

(** * The endomorphism operad of an object in a cartesian category / * 笛卡尔范畴中一个对象的自同态算子阵 *)

(*
nLab: https://ncatlab.org/nlab/show/endomorphism+operad

   Given an object [X] of a cartesian category [C], the endomorphism operad
   End(X) is the one-object multicategory whose n-ary operations are the
   morphisms [X^n ~> X].  The finite power [X^n] is realised as the
   right-nested product fold [pow X n] ([pow X 0 := 1],
   [pow X (S n) := X × pow X n]), so an n-ary operation depends on the source
   list [Γ] only through its LENGTH.

   BOUNDARY CASTS.  Since [mhom Γ c := pow X (length Γ) ~> X], a boundary
   equality [e : Γ = Γ'] acts through [f_equal length e : nat = nat]-level
   data, realised as the reindexing morphism [pow_cast].  The groupoid pack
   ([mcast_id] over an ARBITRARY loop, [mcast_trans]) is discharged by UIP on
   [nat] — provable without axioms via Hedberg ([UIP_nat] from the stdlib's
   [Eqdep_dec] development), so the whole instance is axiom-free.

   THE SYMMETRIC ACTION IS GENUINE.  Although [mhom Γ c] depends on the
   source list only through its LENGTH, the symmetric action [msym p] is
   NOT the trivial boundary reindexing: it permutes the factors of the
   power.  The class's witnesses are the Type-valued [tperm] of
   Theory/Multicategory.v, so [perm_act] is built by structural recursion
   on the derivation — [tperm_swap] acts by the product braid
   [(exl ∘ exr) △ (exl △ (exr ∘ exr))] on the two head factors,
   [tperm_skip] whiskers by [second], and [tperm_trans] composes.  In
   particular a nontrivial self-permutation acts nontrivially (e.g. the
   swap on [X × (X × 1)]), which is the whole content of the symmetry;
   only the canonical [tperm_refl] witness is required to act as the
   identity ([perm_act_refl]).  Equivariance of splicing is proven by
   commuting the action generators past the graft: the whiskering
   combinators become [plug]/[first]/[second] block maps through the
   splitting ([act_app_l_split], [act_app_r_plug], [act_app_l_plug]),
   and the braid case is the fork computation [split_braid].

   SPLICING.  Composition [mcomp f g] precomposes [f] with a fork-pasted
   graft map [pow X (m + (d + k)) ~> pow X (m + S k)] that passes the
   [m]-block through, feeds the [d]-block to [g], and passes the [k]-block.
   The graft is built from the block-splitting combinator
   [pow_split : pow X (m + n) ~> pow X m × pow X n] (an iso; its inverse is
   not needed here, so only the forward direction is defined) by iterating
   [second] over the prefix.  The multicategory laws then reduce to fork
   algebra: associativity of [pow_split] ([pow_split_assoc]), naturality of
   the product associator, and proof-irrelevant [pow_cast] bookkeeping.

--------
nLab：https://ncatlab.org/nlab/show/endomorphism+operad

给定笛卡尔范畴 [C] 的对象 [X]，自同态操作数
 End(X) 是一个单对象多范畴，其 n 元操作是
 态射 [X^n ~> X]。 有限功率 [X^n] 的实现为
 右嵌套产品折叠 [pow X n] ([pow X 0 := 1],
 [pow X (S n) := X × pow X n])，因此 n 元运算取决于源
 仅通过长度列出 [Γ]。

边界铸造。 自 [mhom Γ c := pow X (length Γ) ~> X] 以来，边界
 平等 [e : Γ = Γ'] 通过 [f_equal length e : nat = nat] 级别起作用
 数据，实现为重新索引态射 [pow_cast]。 群形包
 （[mcast_id] 通过任意循环，[mcast_trans]）由 UIP 放电
 [nat] — 通过 Hedberg 无需公理即可证明（来自 stdlib 的 [UIP_nat]
 [Eqdep_dec] 开发），因此整个实例是无公理的。

对称动作是真实的。 虽然 [mhom Γ c] 取决于
 源列表仅通过其长度，对称操作 [msym p] 是
 不是琐碎的边界重新索引：它排列了
 权力。 该类的见证人是类型值 [tperm]
 Theory/Multicategory.v，所以[perm_act]是通过结构递归构建的
 推导上——[tperm_swap]通过产品编织起作用
 [(exl ∘ exr) △ (exl △ (exr ∘ exr))] 对两个头因素的影响，
 [tperm_skip]晶须由[second]和[tperm_trans]组成。 在
 特别是一个非平凡的自排列行为非平凡（例如
 交换[X × (X × 1)]），这是对称性的全部内容；
 仅需要规范的 [tperm_refl] 见证人来充当
 恒等（[perm_act_refl]）。 拼接等效性由下式证明
 将动作发生器通向移植物：胡须
 组合器通过以下方式成为 [plug]/[first]/[second] 块映射
 分裂（[act_app_l_split]、[act_app_r_plug]、[act_app_l_plug]）、
 编织盒为叉算[split_braid]。

拼接。 组合物 [mcomp f g] 预先组合 [f]，并用叉子粘贴
 通过的移植图 [pow X (m + (d + k)) ~> pow X (m + S k)]
 [m] 块通过，将 [d] 块馈送到 [g]，并传递 [k] 块。 
移植物是由块分裂组合器构建的
 [pow_split : pow X (m + n) ~> pow X m × pow X n]（一个 iso；它的逆是
 此处不需要，因此仅定义前向）通过迭代
 [second] 超过前缀。 然后多范畴法则简化为叉子
 代数：[pow_split] ([pow_split_assoc]) 的结合性，自然性
 产品关联器，以及与证明无关的 [pow_cast] 簿记。
*)

Section EndOperad.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (X : C).

(** ** Finite powers / ** 有限幂 *)

(* The right-nested product fold realising [X^n]. / 实现 [X^n] 的右嵌套乘积归约。 *)
Fixpoint pow (n : nat) : C :=
  match n with
  | O => 1%object
  | S n' => (X × pow n')%object
  end.

(** ** Reindexing casts / ** 重新索引投射 *)

(*
Recast a power along a propositional equality of exponents.  [nat] is
   Type-level object data, so [=] is sanctioned here; morphisms are only
   ever compared by [≈].

--------
沿着指数的命题等式重写幂。[nat] 是类型级的对象数据，因此 [=] 在这里是允许的；同态只通过 [≈] 进行比较。
*)
Definition pow_cast {m n : nat} (e : m = n) : pow m ~> pow n :=
  match e in _ = y return pow m ~> pow y with
  | eq_refl => id
  end.

(* Casting along any loop is the identity: UIP on [nat] is axiom-free. / 沿任意环的铸造是恒等式：[nat] 上的 UIP 是无公理的。 *)
Lemma pow_cast_refl {n : nat} (e : n = n) : pow_cast e ≈ id.
Proof. now rewrite (UIP_nat _ _ e eq_refl). Qed.

(* Casting does not depend on the proof cast along. / 铸造不依赖于随附的试样。 *)
Lemma pow_cast_irrel {m n : nat} (e e' : m = n) : pow_cast e ≈ pow_cast e'.
Proof. now rewrite (UIP_nat _ _ e e'). Qed.

(* Casts compose. / 演员们组成。 *)
Lemma pow_cast_fuse {m n p : nat} (e1 : m = n) (e2 : n = p) :
  pow_cast e2 ∘ pow_cast e1 ≈ pow_cast (eq_trans e1 e2).
Proof. destruct e1, e2; simpl; cat. Qed.

(* Tail-carrying form of [pow_cast_fuse], for rewriting inside chains. / [pow_cast_fuse] 的尾部携带形式，用于在链内重写。 *)
Lemma pow_cast_fuse' {m n p : nat} (e1 : m = n) (e2 : n = p)
  {w : C} (t : w ~> pow m) :
  pow_cast e2 ∘ (pow_cast e1 ∘ t) ≈ pow_cast (eq_trans e1 e2) ∘ t.
Proof.
  rewrite comp_assoc.
  now rewrite pow_cast_fuse.
Qed.

(* A cast along a successor equality acts on the tail factor only. / 沿着后继相等进行的类型转换只作用于尾部因子。 *)
Lemma pow_cast_S {m n : nat} (e : m = n) (e' : S m = S n) :
  pow_cast e' ≈ second (z:=X) (pow_cast e).
Proof.
  destruct e.
  rewrite pow_cast_refl.
  unfold second; cat.
Qed.

(** ** Block splitting / ** 区块分割 *)

(*
The inverse product associator, given by its fork formula.  A named
   constant (rather than [prod_assoc⁻¹]) so that [simpl] leaves it folded
   inside the fixpoints below, keeping goals rewritable.

--------
逆乘积结合子，由其叉公式给出。一个命名常量（而不是 [prod_assoc⁻¹]），以便 [simpl] 将其保留在下面的固定点中，使目标可重写。
*)
Definition passoc {x y z : C} : x × (y × z) ~> (x × y) × z :=
  (exl △ (exl ∘ exr)) △ (exr ∘ exr).

Lemma passoc_from {x y z : C} :
  passoc ≈ ((prod_assoc (x:=x) (y:=y) (z:=z))⁻¹).
Proof. reflexivity. Qed.

(*
Split a power at a block boundary: [pow (m + n) ≅ pow m × pow n].  Only
   the forward direction is needed by the graft; it is built by induction on
   the prefix length, reassociating with the product associator.

--------
在块边界处拆分幂：[pow (m + n) ≅ pow m × pow n]。接枝只需要正向；它是通过对前缀长度进行归纳构建的，并与乘积结合子重新结合。
*)
Fixpoint pow_split (m n : nat) : pow (m + n) ~> pow m × pow n :=
  match m with
  | O => one △ id
  | S m' => passoc ∘ second (pow_split m' n)
  end.

(* Projecting away an empty suffix block is the reindexing cast. / 投射掉一个空后缀块就是重建索引的转换。 *)
Lemma pow_split_r0 (m : nat) (e : (m + 0)%nat = m) :
  exl ∘ pow_split m 0%nat ≈ pow_cast e.
Proof.
  induction m; simpl.
  - apply one_unique.
  - rewrite (pow_cast_S (eq_sym (plus_n_O m)) e).
    rewrite comp_assoc.
    unfold passoc.
    rewrite exl_fork.
    apply ump_products; split.
    + rewrite exl_fork_comp.
      apply exl_second.
    + rewrite exr_fork_comp.
      rewrite <- comp_assoc.
      rewrite (exr_second (pow_split m 0%nat)).
      rewrite comp_assoc.
      now rewrite IHm.
Qed.

(** ** Naturality of the product associator / ** 产品结合器的自然性 *)

(*
The inverse associator is natural in each of its three slots.  All three
   are elementary fork algebra.

--------
逆结合子在它的三个位置中都是自然的。三者都是基本叉代数。
*)
Lemma assoc_from_first {x x' y z : C} (u : x ~> x') :
  passoc (x:=x') (y:=y) (z:=z) ∘ first u
    ≈ first (first u) ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

Lemma assoc_from_mid {x y y' z : C} (v : y ~> y') :
  passoc (x:=x) (y:=y') (z:=z) ∘ second (first v)
    ≈ first (second v) ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

Lemma assoc_from_right {x y z z' : C} (w : z ~> z') :
  passoc (x:=x) (y:=y) (z:=z') ∘ second (second w)
    ≈ second w ∘ passoc (x:=x) (y:=y) (z:=z).
Proof. unfold passoc; unfork. Qed.

(*
Tail-carrying forms of the naturality lemmas, for rewriting inside
   right-associated composition chains.

--------
自然性引理的尾部携带形式，用于在右结合的组合链中重写。
*)
Lemma assoc_from_mid' {x y y' z w : C} (v : y ~> y') (t : w ~> x × (y × z)) :
  first (second v) ∘ (passoc ∘ t)
    ≈ passoc ∘ (second (first v) ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- assoc_from_mid.
Qed.

Lemma assoc_from_right' {x y z z' w : C} (u : z ~> z') (t : w ~> x × (y × z)) :
  passoc ∘ (second (second u) ∘ t)
    ≈ second u ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- assoc_from_right.
Qed.

(* The pentagon for the inverse associator, with a tail. / 带尾的逆结合子五边形。 *)
Lemma pentagon_from' {w x y z v : C} (t : v ~> w × (x × (y × z))) :
  first passoc ∘ (passoc ∘ (second passoc ∘ t))
    ≈ passoc ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  unfold passoc; unfork.
Qed.

(*
Associativity of block splitting: splitting off an [a]-block and then a
   [b]-block agrees with splitting at [a + b] and subdividing, up to the
   product associator and the reindexing cast.

--------
块拆分的结合性：先拆分一个 [a] 块然后拆分一个 [b] 块，与在 [a + b] 处拆分并细分是相符的，这与乘积结合子和重索引转换一致。
*)
Lemma pow_split_assoc (a b c : nat)
  (E : (a + (b + c))%nat = ((a + b) + c)%nat) :
  first (pow_split a b) ∘ pow_split (a + b) c ∘ pow_cast E
    ≈ passoc ∘ second (pow_split b c) ∘ pow_split a (b + c).
Proof.
  revert E; induction a; intros E; simpl.
  - (* The cast is a loop, and both sides are elementary fork algebra. / 演员表是一个循环，两边都是初等叉代数。 *)
    rewrite pow_cast_refl, id_right.
    unfold passoc; unfork.
    apply fork_respects; [apply fork_respects|]; try reflexivity.
    apply one_unique.
  - rewrite (pow_cast_S (eq_add_S _ _ E) E).
    rewrite first_comp.
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    rewrite (comp_assoc (first (pow_split a b)) (pow_split (a + b) c)).
    rewrite IHa.
    rewrite !second_comp.
    rewrite <- !comp_assoc.
    rewrite pentagon_from'.
    now rewrite assoc_from_right'.
Qed.

(**
** The graft map

    [graft m d k g] is the splice combinator underlying [mcomp]: it passes
    an [m]-block of inputs through, feeds the next [d]-block to the operation
    [g], and passes the trailing [k]-block.  Built by iterating [second]
    over the prefix; the payload row is [first g ∘ pow_split d k].

--------
** 嫁接图

[graft m d k g] 是 [mcomp] 的基础拼接组合器：它通过一个 [m] 块的输入，将下一个 [d] 块输入提供给操作 [g]，并传递尾随的 [k] 块。通过在前缀上迭代 [second] 构建；有效载荷行是 [first g ∘ pow_split d k]。
*)
Fixpoint graft (m d k : nat) (g : pow d ~> X) :
  pow (m + (d + k)) ~> pow (m + S k) :=
  match m with
  | O => first g ∘ pow_split d k
  | S m' => second (graft m' d k g)
  end.

#[export] Instance graft_respects (m d k : nat) :
  Proper (equiv ==> equiv) (graft m d k).
Proof.
  intros g g' eg.
  induction m; simpl.
  - now rewrite eg.
  - now rewrite IHm.
Qed.

(* Grafting the unary identity operation is the identity. / 嫁接一元恒等操作就是恒等操作。 *)
Lemma graft_id (m k : nat) : graft m 1 k exl ≈ id.
Proof.
  induction m; simpl.
  - unfold passoc; unfork.
  - rewrite IHm.
    now rewrite second_id.
Qed.

(* Two more tail-carrying commutation helpers. / 再两个携带尾部的换位助手。 *)
Lemma second_first' {x x' y y' w : C} (f : x ~> x') (g : y ~> y')
  (t : w ~> x × y) :
  second g ∘ (first f ∘ t) ≈ first f ∘ (second g ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite <- first_second.
Qed.

Lemma assoc_from_first' {x x' y z w : C} (u : x ~> x')
  (t : w ~> x × (y × z)) :
  passoc ∘ (first u ∘ t) ≈ first (first u) ∘ (passoc ∘ t).
Proof.
  rewrite !comp_assoc.
  now rewrite assoc_from_first.
Qed.

(** ** Commuting the graft past block splitting / ** 将贿赂越过区块拆分 *)

(*
Grafting inside the FIRST block commutes with splitting off a trailing
   [n]-block.

--------
在第一个块内进行嫁接与分离尾部的 [n] 块是可交换的。
*)
Lemma split_graft_first (m t k n : nat) (h : pow t ~> X)
  (E1 : (m + S (k + n))%nat = ((m + S k) + n)%nat)
  (E2 : (m + (t + (k + n)))%nat = ((m + (t + k)) + n)%nat) :
  pow_split (m + S k) n ∘ pow_cast E1 ∘ graft m t (k + n) h
    ≈ first (graft m t k h) ∘ pow_split (m + (t + k)) n ∘ pow_cast E2.
Proof.
  revert E1 E2; induction m as [|m IHm]; intros E1 E2; simpl.
  - rewrite first_comp.
    rewrite <- !comp_assoc.
    rewrite pow_cast_refl, id_left.
    rewrite second_first'.
    rewrite assoc_from_first'.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    symmetry; apply pow_split_assoc.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm.
Qed.

(*
Grafting inside the SECOND block commutes with splitting off a leading
   [a]-block.

--------
在第二个块内进行嫁接与分离出前导 [a] 块是可交换的。
*)
Lemma split_graft_second (a m d k : nat) (h : pow d ~> X)
  (E1 : ((a + m) + S k)%nat = (a + (m + S k))%nat)
  (E2 : ((a + m) + (d + k))%nat = (a + (m + (d + k)))%nat) :
  pow_split a (m + S k) ∘ pow_cast E1 ∘ graft (a + m) d k h
    ≈ second (graft m d k h) ∘ pow_split a (m + (d + k)) ∘ pow_cast E2.
Proof.
  revert E1 E2; induction a as [|a IHa]; intros E1 E2; simpl.
  - rewrite !pow_cast_refl, !id_right.
    rewrite second_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + apply one_unique.
    + cat.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite <- assoc_from_right'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHa.
Qed.

(** ** The two associativity cores / ** 两个结合性核心 *)

(*
Nested shape: grafting [h] into the block fed to [g'] agrees with
   grafting [g' ∘ (graft of h)] directly.

--------
嵌套形状：将 [h] 嫁接到供给 [g'] 的模块中，与直接嫁接 [g' ∘ (graft of h)] 相符。
*)
Lemma graft_nested (m1 m2 k1 k2 t : nat)
  (g' : pow (m2 + S k2) ~> X) (h : pow t ~> X)
  (E1 : ((m1 + m2) + S (k2 + k1))%nat = (m1 + ((m2 + S k2) + k1))%nat)
  (E2 : ((m1 + m2) + (t + (k2 + k1)))%nat
          = (m1 + ((m2 + (t + k2)) + k1))%nat) :
  graft m1 (m2 + S k2) k1 g' ∘ pow_cast E1 ∘ graft (m1 + m2) t (k2 + k1) h
    ≈ graft m1 (m2 + (t + k2)) k1 (g' ∘ graft m2 t k2 h) ∘ pow_cast E2.
Proof.
  revert E1 E2; induction m1 as [|m1 IHm1]; intros E1 E2; simpl.
  - rewrite first_comp.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply split_graft_first.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !comp_assoc.
    rewrite <- !second_comp.
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm1.
Qed.

(*
Disjoint shape: two grafts into separate blocks of the same context may
   be performed in either order.

--------
不相交的形状：两个移植物可以在同一上下文的不同区块中进行，顺序可以任意。
*)
Lemma graft_disjoint (m1 m2 m3 dg dh : nat)
  (g : pow dg ~> X) (h : pow dh ~> X)
  (E1 : ((m1 + (dg + m2)) + S m3)%nat = (m1 + (dg + (m2 + S m3)))%nat)
  (E2 : ((m1 + S m2) + S m3)%nat = (m1 + S (m2 + S m3))%nat)
  (E3 : (m1 + S (m2 + (dh + m3)))%nat = ((m1 + S m2) + (dh + m3))%nat)
  (E4 : ((m1 + (dg + m2)) + (dh + m3))%nat
          = (m1 + (dg + (m2 + (dh + m3))))%nat) :
  graft m1 dg (m2 + S m3) g ∘ pow_cast E1 ∘ graft (m1 + (dg + m2)) dh m3 h
    ≈ pow_cast E2 ∘ graft (m1 + S m2) dh m3 h ∘ pow_cast E3
        ∘ graft m1 dg (m2 + (dh + m3)) g ∘ pow_cast E4.
Proof.
  revert E1 E2 E3 E4;
  induction m1 as [|m1 IHm1]; intros E1 E2 E3 E4; simpl.
  - rewrite !pow_cast_refl.
    rewrite id_left, id_right.
    rewrite <- !comp_assoc.
    rewrite second_first'.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply split_graft_second.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite (pow_cast_S (eq_add_S _ _ E3) E3).
    rewrite (pow_cast_S (eq_add_S _ _ E4) E4).
    rewrite <- !comp_assoc.
    rewrite <- !second_comp.
    apply second_respects.
    rewrite !comp_assoc.
    apply IHm1.
Qed.

(** ** The operad data / ** 操作器数据 *)

(*
Length of a concatenation, a hand-written Fixpoint (not a tactic
   proof) so that its computational content is pinned: the unit laws
   below rely on the base case being [eq_refl] on the nose, and a
   tactic-built term would leave that hostage to automation drift.

--------
连接的长度，一个手写的固定点（不是使用策略证明），以便其计算内容被固定：下面的单位律依赖于基本情况严格为 [eq_refl]，而使用策略构建的项会将其置于自动化漂移的风险之中。
*)
Fixpoint len_app {A : Type} (l1 l2 : list A) :
  length (l1 ++ l2) = (length l1 + length l2)%nat :=
  match l1 with
  | [] => eq_refl
  | _ :: t => f_equal S (len_app t l2)
  end.

Definition len_zip (Γ1 Γ2 : list poly_unit) (b : poly_unit) :
  length (Γ1 ++ b :: Γ2) = (length Γ1 + S (length Γ2))%nat :=
  len_app Γ1 (b :: Γ2).

Definition len_splice (Γ1 Δ Γ2 : list poly_unit) :
  length (Γ1 ++ Δ ++ Γ2)
    = (length Γ1 + (length Δ + length Γ2))%nat :=
  eq_trans (len_app Γ1 (Δ ++ Γ2))
           (f_equal (λ n, (length Γ1 + n)%nat) (len_app Δ Γ2)).

(*
Multimorphisms of End(X): the colour set is the one-point type, and an
   operation with source list Γ is a morphism out of the |Γ|-th power.

--------
End(X) 的多态映射：颜色集是单点类型，且源列表为 Γ 的运算是从 |Γ| 次方出的一个态射。
*)
Definition End_hom (Γ : list poly_unit) (_ : poly_unit) : Type :=
  pow (length Γ) ~{C}~> X.

Definition End_mcast {Γ Γ' : list poly_unit} {c : poly_unit} (e : Γ = Γ')
  (f : End_hom Γ c) : End_hom Γ' c :=
  f ∘ pow_cast (f_equal (@length poly_unit) (eq_sym e)).

Definition End_mid (a : poly_unit) : End_hom [a] a := exl.

Definition End_mcomp {Γ1 Γ2 Δ : list poly_unit} {b c : poly_unit}
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom Δ b) :
  End_hom (Γ1 ++ Δ ++ Γ2) c :=
  f ∘ pow_cast (eq_sym (len_zip Γ1 Γ2 b))
    ∘ graft (length Γ1) (length Δ) (length Γ2) g
    ∘ pow_cast (len_splice Γ1 Δ Γ2).

(**
** The symmetric action

    The action of a permutation witness [p : tperm Γ Δ] is GENUINE: it
    permutes the factors of the power, built by structural recursion on
    the witness.  The [tperm_swap] generator acts by the product braid on
    the two head factors; [tperm_skip] whiskers by [second];
    [tperm_trans] composes.  An operation is then relabelled by
    precomposition: [msym p f := f ∘ perm_act p].

--------
** 对称作用

置换证据 [p : tperm Γ Δ] 的作用是真实的：它通过对证据进行结构递归构建幂的因子进行置换。[tperm_swap] 生成器通过乘积编织作用于两个头部因子；[tperm_skip] 通过 [second] 执行触须操作；[tperm_trans] 进行组合。然后通过预组合重新标记一个操作：[msym p f := f ∘ perm_act p]。
*)

(*
The braid on the two head factors of a right-nested product:
   (a, (b, w)) ↦ (b, (a, w)).

--------
右嵌套乘积的两个头元素的交换：
   (a, (b, w)) ↦ (b, (a, w))。
*)
Definition braid {w : C} : X × (X × w) ~> X × (X × w) :=
  (exl ∘ exr) △ (exl △ (exr ∘ exr)).

Fixpoint perm_act {Γ Δ : list poly_unit} (p : tperm Γ Δ) :
  pow (length Δ) ~> pow (length Γ) :=
  match p in tperm Γ0 Δ0
    return pow (length Δ0) ~> pow (length Γ0) with
  | tperm_nil => id
  | tperm_skip x q => second (perm_act q)
  | tperm_swap x y l => braid
  | tperm_trans q r => perm_act q ∘ perm_act r
  end.

Definition End_msym {Γ Δ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) (f : End_hom Γ c) : End_hom Δ c :=
  f ∘ perm_act p.

(** ** The cast pack and respectfulness / ** 演员包和尊重 *)

Lemma End_mcast_respects {Γ Γ' : list poly_unit} {c : poly_unit}
  (e : Γ = Γ') :
  Proper (equiv ==> equiv) (End_mcast (c:=c) e).
Proof.
  intros f g ef; unfold End_mcast.
  now rewrite ef.
Qed.

Lemma End_mcast_id {Γ : list poly_unit} {c : poly_unit} (e : Γ = Γ)
  (f : End_hom Γ c) :
  End_mcast e f ≈ f.
Proof.
  unfold End_mcast.
  now rewrite pow_cast_refl, id_right.
Qed.

Lemma End_mcast_trans {Γ Γ' Γ'' : list poly_unit} {c : poly_unit}
  (e : Γ = Γ') (e' : Γ' = Γ'') (f : End_hom Γ c) :
  End_mcast e' (End_mcast e f) ≈ End_mcast (eq_trans e e') f.
Proof.
  unfold End_mcast.
  rewrite <- comp_assoc.
  rewrite pow_cast_fuse.
  apply compose_respects; [reflexivity|].
  apply pow_cast_irrel.
Qed.

Lemma End_mcomp_respects {Γ1 Γ2 Δ : list poly_unit} {b c : poly_unit} :
  Proper (equiv ==> equiv ==> equiv) (@End_mcomp Γ1 Γ2 Δ b c).
Proof.
  intros f f' ef g g' eg; unfold End_mcomp.
  now rewrite ef, eg.
Qed.

Lemma End_msym_respects {Γ Δ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) :
  Proper (equiv ==> equiv) (End_msym (c:=c) p).
Proof.
  intros f g ef; unfold End_msym.
  now rewrite ef.
Qed.

(** ** The unit laws / ** 单位法律 *)

Lemma End_mcomp_id_left {Δ : list poly_unit} {b : poly_unit}
  (g : End_hom Δ b) :
  End_mcast (splice_eq_unit_left Δ)
    (End_mcomp (Γ1:=[]) (Γ2:=[]) (End_mid b) g) ≈ g.
Proof.
  unfold End_mcast, End_mcomp, End_mid; simpl.
  (*
The zipper cast computes away: [len_app [] [b]] reduces to [eq_refl],
     so [pow_cast] of it is literally [id].

--------
拉链转播计算消失：[len_app [] [b]] 简化为 [eq_refl]，所以它的 [pow_cast] 字面上就是 [id]。
*)
  rewrite id_right.
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse.
  rewrite (comp_assoc exl (first g)).
  rewrite exl_first.
  rewrite <- comp_assoc.
  rewrite (comp_assoc exl (pow_split (length Δ) 0%nat)).
  rewrite (pow_split_r0 (length Δ) (eq_sym (plus_n_O (length Δ)))).
  rewrite pow_cast_fuse.
  now rewrite pow_cast_refl, id_right.
Qed.

Lemma End_mcomp_id_right {Γ1 Γ2 : list poly_unit} {a c : poly_unit}
  (f : End_hom (Γ1 ++ a :: Γ2) c) :
  End_mcast (splice_eq_unit_right Γ1 Γ2 a) (End_mcomp f (End_mid a)) ≈ f.
Proof.
  unfold End_mcast, End_mcomp, End_mid; simpl.
  rewrite graft_id, id_right.
  rewrite <- !comp_assoc.
  rewrite !pow_cast_fuse.
  now rewrite pow_cast_refl, id_right.
Qed.

(** ** The elementary symmetry laws / ** 基本对称定律 *)

(* The canonical reflexivity witness acts trivially. / 典型的自反性见证表现得很平凡。 *)
Lemma perm_act_refl (Γ : list poly_unit) :
  perm_act (tperm_refl Γ) ≈ id.
Proof.
  induction Γ; simpl.
  - reflexivity.
  - rewrite IHΓ.
    apply second_id.
Qed.

Lemma End_msym_id {Γ : list poly_unit} {c : poly_unit} (f : End_hom Γ c) :
  End_msym (tperm_refl Γ) f ≈ f.
Proof.
  unfold End_msym.
  now rewrite perm_act_refl, id_right.
Qed.

Lemma End_msym_compose {Γ Δ Λ : list poly_unit} {c : poly_unit}
  (p : tperm Γ Δ) (q : tperm Δ Λ) (f : End_hom Γ c) :
  End_msym q (End_msym p f) ≈ End_msym (tperm_trans p q) f.
Proof.
  unfold End_msym; simpl.
  now rewrite <- comp_assoc.
Qed.

(**
** Whiskering a tail map under a prefix of factors

    [plug m u] applies [u] under the first [m] factors of a power; the
    graft is [plug m] of its payload row, and the [tperm_app_r]
    whiskering acts by [plug].  These are the joints along which the
    equivariance law is assembled.

--------
** 在因子前缀下对尾部映射进行须状处理

[plug m u] 在幂的前 [m] 个因子下应用 [u]；移植的是其有效载荷行的 [plug m]，且 [tperm_app_r] 须状处理通过 [plug] 起作用。这些是组装等变律的关节。
*)

Fixpoint plug (m : nat) {s s' : nat} (u : pow s ~> pow s') :
  pow (m + s) ~> pow (m + s') :=
  match m with
  | O => u
  | S m' => second (plug m' u)
  end.

#[export] Instance plug_respects (m s s' : nat) :
  Proper (equiv ==> equiv) (@plug m s s').
Proof.
  intros u v eu.
  induction m; simpl.
  - exact eu.
  - now rewrite IHm.
Qed.

Lemma plug_comp (m : nat) {s s' s'' : nat}
  (u : pow s' ~> pow s'') (v : pow s ~> pow s') :
  plug m (u ∘ v) ≈ plug m u ∘ plug m v.
Proof.
  induction m; simpl.
  - reflexivity.
  - rewrite IHm.
    apply second_comp.
Qed.

(* A cast between powers with a common prefix is a plugged cast. / 具有共同前缀的幂之间的强制转换称为插入强制转换。 *)
Lemma plug_cast (m : nat) {s s' : nat} (e : s = s')
  (E : (m + s)%nat = (m + s')%nat) :
  pow_cast E ≈ plug m (pow_cast e).
Proof.
  induction m; simpl.
  - apply pow_cast_irrel.
  - rewrite (pow_cast_S (f_equal (λ n, (m + n)%nat) e) E).
    apply second_respects.
    apply IHm.
Qed.

(* The graft is the plugged payload row. / 移植物是插入的有效载荷行。 *)
Lemma graft_plug (m d k : nat) (g : pow d ~> X) :
  graft m d k g ≈ plug m (s':=S k) (first g ∘ pow_split d k).
Proof.
  induction m; simpl.
  - reflexivity.
  - now rewrite IHm.
Qed.

(*
Splitting after a plugged tail map is the tail map on the second
   block.

--------
在插入尾部映射后拆分就是第二个块上的尾部映射。
*)
Lemma split_plug (a : nat) {s s' : nat} (v : pow s ~> pow s') :
  pow_split a s' ∘ plug a v ≈ second v ∘ pow_split a s.
Proof.
  induction a; simpl.
  - rewrite second_fork.
    rewrite <- fork_comp.
    apply fork_respects.
    + apply one_unique.
    + cat.
  - rewrite <- comp_assoc.
    rewrite <- second_comp.
    rewrite IHa.
    rewrite second_comp.
    rewrite comp_assoc.
    rewrite assoc_from_right.
    now rewrite <- comp_assoc.
Qed.

(* The braid is natural in the tail. / 辫子在尾巴上是自然的。 *)
Lemma braid_natural {w w' : C} (v : w ~> w') :
  braid ∘ second (second v) ≈ second (second v) ∘ braid.
Proof. unfold braid; unfork. Qed.

(* Right whiskering acts by plugging under the prefix. / 右打须通过在前缀下插入起作用。 *)
Lemma act_app_r_plug (Γ : list poly_unit) {Δ Δ' : list poly_unit}
  (q : tperm Δ Δ')
  (E1 : (length Γ + length Δ)%nat = length (Γ ++ Δ))
  (E2 : length (Γ ++ Δ') = (length Γ + length Δ')%nat) :
  perm_act (tperm_app_r Γ q)
    ≈ pow_cast E1 ∘ plug (length Γ) (perm_act q) ∘ pow_cast E2.
Proof.
  induction Γ; simpl.
  - rewrite !pow_cast_refl; cat.
  - rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite <- !second_comp.
    apply second_respects.
    apply IHΓ.
Qed.

(* Splitting off a tail block commutes with the head braid. / 分离尾区块与头部编织是可交换的。 *)
Lemma split_braid (n m : nat) :
  pow_split (S (S n)) m ∘ braid (w:=pow (n + m))
    ≈ first (braid (w:=pow n)) ∘ pow_split (S (S n)) m.
Proof.
  simpl; unfold braid, passoc; unfork.
Qed.

(*
[split_braid] with a reindexing cast interposed: stated at the nat
   level so that the cast can be destructed away.

--------
[split_braid] 带有插入的重建索引转换：在 nat 级别声明，以便转换可以被销毁。
*)
Lemma split_braid_cast (n m j : nat) (e : j = (n + m)%nat)
  (E E' : S (S j) = (S (S n) + m)%nat) :
  pow_split (S (S n)) m ∘ pow_cast E ∘ braid (w:=pow j)
    ≈ first (braid (w:=pow n)) ∘ pow_split (S (S n)) m ∘ pow_cast E'.
Proof.
  subst j.
  assert (HE : pow_cast E ≈ id) by apply pow_cast_refl.
  assert (HE' : pow_cast E' ≈ id) by apply pow_cast_refl.
  rewrite HE, HE', !id_right.
  apply split_braid.
Qed.

(*
Left whiskering: the action of [tperm_app_l p T] is the action of [p]
   on the first block, seen through the block splitting.

--------
左侧胡须化：[tperm_app_l p T] 的动作是 [p] 在第一个块上的动作，通过块拆分可以看到。
*)
Lemma act_app_l_split {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  (T : list poly_unit)
  (E : length (Γ ++ T) = (length Γ + length T)%nat)
  (E' : length (Γ' ++ T) = (length Γ' + length T)%nat) :
  pow_split (length Γ) (length T) ∘ pow_cast E ∘ perm_act (tperm_app_l p T)
    ≈ first (perm_act p) ∘ pow_split (length Γ') (length T) ∘ pow_cast E'.
Proof.
  revert E E'; induction p; intros E E'.
  - (* nil *)
    simpl.
    rewrite perm_act_refl, id_right.
    rewrite first_id, id_left.
    apply compose_respects; [reflexivity|].
    apply pow_cast_irrel.
  - (* skip / 跳过 *)
    simpl.
    rewrite (pow_cast_S (eq_add_S _ _ E) E).
    rewrite (pow_cast_S (eq_add_S _ _ E') E').
    rewrite <- !comp_assoc.
    rewrite assoc_from_mid'.
    rewrite <- !second_comp.
    apply compose_respects; [reflexivity|].
    apply second_respects.
    rewrite !comp_assoc.
    apply IHp.
  - (* swap: the braid case / 交换：编织盒 *)
    simpl perm_act.
    change (length (y :: x :: Γ)) with (S (S (length Γ))).
    change (length (x :: y :: Γ)) with (S (S (length Γ))).
    apply (split_braid_cast (length Γ) (length T) (length (Γ ++ T))
             (len_app Γ T) E E').
  - (* trans / 变换 *)
    simpl.
    rewrite first_comp.
    rewrite comp_assoc.
    rewrite (IHp1 E (len_app Δ T)).
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply IHp2.
Qed.

(* Braid conjugation with reindexing casts, at the nat level. / 在自然数层级，用重新索引的类型转换进行发辫结合。 *)
Lemma braid_plug_cast {s s' j j' : nat} (w : pow s ~> pow s')
  (e : j = s) (e' : j' = s')
  (E1 : S (S j) = S (S s)) (E2 : S (S j') = S (S s'))
  (E3 : S (S s') = S (S j')) (E4 : S (S j) = S (S s)) :
  second (second w) ∘ pow_cast E1 ∘ braid (w:=pow j)
    ≈ pow_cast E2 ∘ braid (w:=pow j') ∘ pow_cast E3
        ∘ second (second w) ∘ pow_cast E4.
Proof.
  subst j j'.
  assert (H1 : pow_cast E1 ≈ id) by apply pow_cast_refl.
  assert (H2 : pow_cast E2 ≈ id) by apply pow_cast_refl.
  assert (H3 : pow_cast E3 ≈ id) by apply pow_cast_refl.
  assert (H4 : pow_cast E4 ≈ id) by apply pow_cast_refl.
  rewrite H1, H2, H3, H4.
  rewrite id_left, !id_right.
  symmetry; apply braid_natural.
Qed.

(* Moving the action of a left whiskering across a plugged tail map. / 在一个被封的尾部地图上移动左侧触须的动作。 *)
Lemma act_app_l_plug {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  {T T' : list poly_unit} (u : pow (length T) ~> pow (length T'))
  (E1 : length (Γ ++ T) = (length Γ + length T)%nat)
  (E2 : length (Γ ++ T') = (length Γ + length T')%nat)
  (E3 : (length Γ' + length T')%nat = length (Γ' ++ T'))
  (E4 : length (Γ' ++ T) = (length Γ' + length T)%nat) :
  plug (length Γ) u ∘ pow_cast E1 ∘ perm_act (tperm_app_l p T)
    ≈ pow_cast E2 ∘ perm_act (tperm_app_l p T') ∘ pow_cast E3
        ∘ plug (length Γ') u ∘ pow_cast E4.
Proof.
  revert E1 E2 E3 E4; induction p; intros E1 E2 E3 E4.
  - (* nil *)
    simpl.
    rewrite !perm_act_refl.
    rewrite !pow_cast_refl.
    cat.
  - (* skip / 跳过 *)
    simpl.
    rewrite (pow_cast_S (eq_add_S _ _ E1) E1).
    rewrite (pow_cast_S (eq_add_S _ _ E2) E2).
    rewrite (pow_cast_S (eq_add_S _ _ E3) E3).
    rewrite (pow_cast_S (eq_add_S _ _ E4) E4).
    rewrite <- !second_comp.
    apply second_respects.
    apply IHp.
  - (* swap / 交换 *)
    simpl perm_act.
    apply (braid_plug_cast (plug (length Γ) u)
             (len_app Γ T) (len_app Γ T') E1 E2 E3 E4).
  - (* trans / 变换 *)
    simpl.
    rewrite comp_assoc.
    rewrite (IHp1 E1 E2 (eq_sym (len_app Δ T')) (len_app Δ T)).
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    apply compose_respects; [reflexivity|].
    rewrite (comp_assoc (plug (length Δ) u) (pow_cast (len_app Δ T))).
    rewrite (IHp2 (len_app Δ T) (len_app Δ T') E3 E4).
    rewrite <- !comp_assoc.
    rewrite pow_cast_fuse'.
    rewrite pow_cast_refl, id_left.
    reflexivity.
Qed.

(*
The payload-level core of the equivariance law: acting on the payload
   block and on the suffix block commutes with the payload row.

--------
等变性定律的有效负载级核心：作用于有效负载块和后缀块与有效负载行是可交换的。
*)
Lemma equivariant_core {Δ Δ' Γ2 Γ2' : list poly_unit}
  (q : tperm Δ Δ') (r : tperm Γ2 Γ2') (g : pow (length Δ) ~> X) :
  ((first g ∘ pow_split (length Δ) (length Γ2)) ∘ pow_cast (len_app Δ Γ2))
    ∘ (perm_act (tperm_app_l q Γ2) ∘ perm_act (tperm_app_r Δ' r))
    ≈ second (perm_act r)
        ∘ ((first (g ∘ perm_act q) ∘ pow_split (length Δ') (length Γ2'))
             ∘ pow_cast (len_app Δ' Γ2')).
Proof.
  rewrite (act_app_r_plug Δ' r (eq_sym (len_app Δ' Γ2)) (len_app Δ' Γ2')).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (pow_cast (len_app Δ Γ2))).
  rewrite (comp_assoc (pow_split (length Δ) (length Γ2))).
  rewrite (comp_assoc (pow_split (length Δ) (length Γ2))).
  rewrite (act_app_l_split q Γ2 (len_app Δ Γ2) (eq_sym (eq_sym (len_app Δ' Γ2)))).
  rewrite <- !comp_assoc.
  rewrite pow_cast_fuse'.
  rewrite pow_cast_refl, id_left.
  rewrite (comp_assoc (pow_split (length Δ') (length Γ2))).
  rewrite split_plug.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (first g)).
  rewrite <- first_comp.
  rewrite (comp_assoc (first (g ∘ perm_act q))).
  rewrite first_second.
  now rewrite <- !comp_assoc.
Qed.

(* Tail-carrying forms for mid-chain rewriting. / 用于中链重写的尾部携带形式。 *)
Lemma plug_comp' (m : nat) {s s' s'' : nat}
  (u : pow s' ~> pow s'') (v : pow s ~> pow s')
  {w : C} (t : w ~> pow (m + s)) :
  plug m u ∘ (plug m v ∘ t) ≈ plug m (u ∘ v) ∘ t.
Proof.
  rewrite comp_assoc.
  now rewrite <- plug_comp.
Qed.

Corollary act_app_l_plug' {Γ Γ' : list poly_unit} (p : tperm Γ Γ')
  {T T' : list poly_unit} (u : pow (length T) ~> pow (length T'))
  (E1 : length (Γ ++ T) = (length Γ + length T)%nat)
  (E2 : length (Γ ++ T') = (length Γ + length T')%nat)
  (E3 : (length Γ' + length T')%nat = length (Γ' ++ T'))
  (E4 : length (Γ' ++ T) = (length Γ' + length T)%nat)
  {w : C} (t : w ~> pow (length (Γ' ++ T))) :
  plug (length Γ) u ∘ (pow_cast E1 ∘ (perm_act (tperm_app_l p T) ∘ t))
    ≈ pow_cast E2
        ∘ (perm_act (tperm_app_l p T')
             ∘ (pow_cast E3
                  ∘ (plug (length Γ') u ∘ (pow_cast E4 ∘ t)))).
Proof.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  apply act_app_l_plug.
Qed.

(** ** Equivariance / ** 等变性 *)

Lemma End_mcomp_equivariant
  {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list poly_unit} {b c : poly_unit}
  (p : tperm Γ1 Γ1') (q : tperm Δ Δ') (r : tperm Γ2 Γ2')
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom Δ b) :
  End_msym (perm_block3 p q r) (End_mcomp f g)
    ≈ End_mcomp (End_msym (perm_block_slot b p r) f) (End_msym q g).
Proof.
  unfold End_msym, End_mcomp, perm_block3, perm_block_slot, tperm_app.
  simpl perm_act.
  rewrite !graft_plug.
  unfold len_splice.
  rewrite <- !pow_cast_fuse.
  rewrite (plug_cast (length Γ1) (len_app Δ Γ2)
             (f_equal (λ n, (length Γ1 + n)%nat) (len_app Δ Γ2))).
  rewrite (plug_cast (length Γ1') (len_app Δ' Γ2')
             (f_equal (λ n, (length Γ1' + n)%nat) (len_app Δ' Γ2'))).
  rewrite (act_app_r_plug Γ1'
             (tperm_trans (tperm_app_l q Γ2) (tperm_app_r Δ' r))
             (eq_sym (len_app Γ1' (Δ ++ Γ2))) (len_app Γ1' (Δ' ++ Γ2'))).
  rewrite (act_app_r_plug Γ1' (tperm_skip b r)
             (eq_sym (len_zip Γ1' Γ2 b)) (len_zip Γ1' Γ2' b)).
  rewrite <- !comp_assoc.
  rewrite !plug_comp'.
  rewrite (act_app_l_plug' p (T':=b :: Γ2)
             ((first g ∘ pow_split (length Δ) (length Γ2))
                ∘ pow_cast (len_app Δ Γ2))
             (len_app Γ1 (Δ ++ Γ2)) (len_zip Γ1 Γ2 b)
             (eq_sym (len_zip Γ1' Γ2 b)) (len_app Γ1' (Δ ++ Γ2))).
  rewrite !pow_cast_fuse'.
  rewrite !pow_cast_refl, !id_left.
  rewrite !plug_comp'.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  apply compose_respects; [apply pow_cast_irrel|].
  apply compose_respects; [|apply pow_cast_irrel].
  apply plug_respects.
  apply equivariant_core.
Qed.

(**
** The associativity laws

    Strategy: make every boundary-cast proof opaque ([generalize]), then
    abstract each concatenation length as a variable and replace it by its
    canonical arithmetic value ([set]/[clearbody]/[subst]).  All casts then
    ride loops or exactly the boundary equations of the nat-level cores
    [graft_nested]/[graft_disjoint], and the goal closes by those cores.

--------
** 结合律定律

    策略：将每个边界转换证明设为不透明（[generalize]），然后将每个连接长度抽象为变量，并用其规范的算术值替换（[set]/[clearbody]/[subst]）。然后所有转换都沿循环或完全沿自然数级内核的边界方程 [graft_nested]/[graft_disjoint] 运行，目标由这些内核完成。
*)

Lemma End_mcomp_assoc_nested {Γ1 Γ2 Δ1 Δ2 Θ : list poly_unit}
  {a b c : poly_unit}
  (f : End_hom (Γ1 ++ b :: Γ2) c) (g : End_hom (Δ1 ++ a :: Δ2) b)
  (h : End_hom Θ a)
  (e1 : Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ a :: (Δ2 ++ Γ2))
  (e2 : Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2 = (Γ1 ++ Δ1) ++ Θ ++ (Δ2 ++ Γ2)) :
  End_mcomp (End_mcast e1 (End_mcomp f g)) h
    ≈ End_mcast e2 (End_mcomp f (End_mcomp g h)).
Proof.
  unfold End_mcast, End_mcomp.
  unfold End_hom in f, g, h.
  generalize (f_equal (@length poly_unit) (eq_sym e1)).
  generalize (f_equal (@length poly_unit) (eq_sym e2)).
  generalize (eq_sym (len_zip Γ1 Γ2 b)).
  generalize (len_splice Γ1 (Δ1 ++ a :: Δ2) Γ2).
  generalize (eq_sym (len_zip (Γ1 ++ Δ1) (Δ2 ++ Γ2) a)).
  generalize (len_splice (Γ1 ++ Δ1) Θ (Δ2 ++ Γ2)).
  generalize (eq_sym (len_zip Δ1 Δ2 a)).
  generalize (len_splice Δ1 Θ Δ2).
  generalize (len_splice Γ1 (Δ1 ++ Θ ++ Δ2) Γ2).
  intros P9 P7 P6 P5 P4 P2 P1 Pe2 Pe1.
  set (j1 := length (Γ1 ++ b :: Γ2)) in *.
  set (j2 := length (Δ1 ++ a :: Δ2)) in *.
  set (j3 := length (Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2)) in *.
  set (j4 := length ((Γ1 ++ Δ1) ++ a :: Δ2 ++ Γ2)) in *.
  set (j5 := length (Γ1 ++ Δ1)) in *.
  set (j6 := length (Δ2 ++ Γ2)) in *.
  set (j8 := length (Δ1 ++ Θ ++ Δ2)) in *.
  set (j9 := length (Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2)) in *.
  set (j10 := length ((Γ1 ++ Δ1) ++ Θ ++ Δ2 ++ Γ2)) in *.
  assert (Hj1 : j1 = (length Γ1 + S (length Γ2))%nat)
    by apply (len_zip Γ1 Γ2 b).
  assert (Hj2 : j2 = (length Δ1 + S (length Δ2))%nat)
    by apply (len_zip Δ1 Δ2 a).
  assert (Hj3 : j3 = (length Γ1 + (j2 + length Γ2))%nat)
    by apply (len_splice Γ1 (Δ1 ++ a :: Δ2) Γ2).
  assert (Hj4 : j4 = (j5 + S j6)%nat)
    by apply (len_zip (Γ1 ++ Δ1) (Δ2 ++ Γ2) a).
  assert (Hj5 : j5 = (length Γ1 + length Δ1)%nat)
    by apply (len_app Γ1 Δ1).
  assert (Hj6 : j6 = (length Δ2 + length Γ2)%nat)
    by apply (len_app Δ2 Γ2).
  assert (Hj8 : j8 = (length Δ1 + (length Θ + length Δ2))%nat)
    by apply (len_splice Δ1 Θ Δ2).
  assert (Hj9 : j9 = (length Γ1 + (j8 + length Γ2))%nat)
    by apply (len_splice Γ1 (Δ1 ++ Θ ++ Δ2) Γ2).
  assert (Hj10 : j10 = (j5 + (length Θ + j6))%nat)
    by apply (len_splice (Γ1 ++ Δ1) Θ (Δ2 ++ Γ2)).
  clearbody j1 j2 j3 j4 j5 j6 j8 j9 j10.
  symmetry in Hj1; destruct Hj1.
  symmetry in Hj3; destruct Hj3.
  symmetry in Hj4; destruct Hj4.
  symmetry in Hj9; destruct Hj9.
  symmetry in Hj10; destruct Hj10.
  symmetry in Hj2; destruct Hj2.
  symmetry in Hj5; destruct Hj5.
  symmetry in Hj6; destruct Hj6.
  symmetry in Hj8; destruct Hj8.
  rewrite !pow_cast_refl.
  rewrite !id_right.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply graft_nested.
Qed.

Lemma End_mcomp_assoc_disjoint {Γ1 Γ2 Γ3 Δ Θ : list poly_unit}
  {a b c : poly_unit}
  (f : End_hom (Γ1 ++ a :: Γ2 ++ b :: Γ3) c)
  (g : End_hom Δ a) (h : End_hom Θ b)
  (d1 : Γ1 ++ Δ ++ Γ2 ++ b :: Γ3 = (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)
  (d2 : Γ1 ++ a :: Γ2 ++ b :: Γ3 = (Γ1 ++ a :: Γ2) ++ b :: Γ3)
  (d3 : (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3 = Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)
  (d4 : Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3 = (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3) :
  End_mcomp (End_mcast d1 (End_mcomp f g)) h
    ≈ End_mcast d4
        (End_mcomp (End_mcast d3 (End_mcomp (End_mcast d2 f) h)) g).
Proof.
  unfold End_mcast, End_mcomp.
  unfold End_hom in f, g, h.
  generalize (f_equal (@length poly_unit) (eq_sym d1)).
  generalize (f_equal (@length poly_unit) (eq_sym d2)).
  generalize (f_equal (@length poly_unit) (eq_sym d3)).
  generalize (f_equal (@length poly_unit) (eq_sym d4)).
  generalize (eq_sym (len_zip Γ1 (Γ2 ++ b :: Γ3) a)).
  generalize (len_splice Γ1 Δ (Γ2 ++ b :: Γ3)).
  generalize (eq_sym (len_zip (Γ1 ++ Δ ++ Γ2) Γ3 b)).
  generalize (len_splice (Γ1 ++ Δ ++ Γ2) Θ Γ3).
  generalize (eq_sym (len_zip (Γ1 ++ a :: Γ2) Γ3 b)).
  generalize (len_splice (Γ1 ++ a :: Γ2) Θ Γ3).
  generalize (eq_sym (len_zip Γ1 (Γ2 ++ Θ ++ Γ3) a)).
  generalize (len_splice Γ1 Δ (Γ2 ++ Θ ++ Γ3)).
  intros PB4 PA4 PB3 PA3 PB2 PA2 PB1 PA1 PD4 PD3 PD2 PD1.
  set (jA := length (Γ1 ++ a :: Γ2 ++ b :: Γ3)) in *.
  set (kA := length (Γ2 ++ b :: Γ3)) in *.
  set (jB := length (Γ1 ++ Δ ++ Γ2 ++ b :: Γ3)) in *.
  set (jC := length ((Γ1 ++ Δ ++ Γ2) ++ b :: Γ3)) in *.
  set (jD := length (Γ1 ++ Δ ++ Γ2)) in *.
  set (jE := length ((Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3)) in *.
  set (jF := length ((Γ1 ++ a :: Γ2) ++ b :: Γ3)) in *.
  set (jG := length (Γ1 ++ a :: Γ2)) in *.
  set (jH := length ((Γ1 ++ a :: Γ2) ++ Θ ++ Γ3)) in *.
  set (jI := length (Γ1 ++ a :: Γ2 ++ Θ ++ Γ3)) in *.
  set (kJ := length (Γ2 ++ Θ ++ Γ3)) in *.
  set (jK := length (Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3)) in *.
  assert (HjA : jA = (length Γ1 + S kA)%nat)
    by apply (len_zip Γ1 (Γ2 ++ b :: Γ3) a).
  assert (HkA : kA = (length Γ2 + S (length Γ3))%nat)
    by apply (len_zip Γ2 Γ3 b).
  assert (HjB : jB = (length Γ1 + (length Δ + kA))%nat)
    by apply (len_splice Γ1 Δ (Γ2 ++ b :: Γ3)).
  assert (HjC : jC = (jD + S (length Γ3))%nat)
    by apply (len_zip (Γ1 ++ Δ ++ Γ2) Γ3 b).
  assert (HjD : jD = (length Γ1 + (length Δ + length Γ2))%nat)
    by apply (len_splice Γ1 Δ Γ2).
  assert (HjE : jE = (jD + (length Θ + length Γ3))%nat)
    by apply (len_splice (Γ1 ++ Δ ++ Γ2) Θ Γ3).
  assert (HjF : jF = (jG + S (length Γ3))%nat)
    by apply (len_zip (Γ1 ++ a :: Γ2) Γ3 b).
  assert (HjG : jG = (length Γ1 + S (length Γ2))%nat)
    by apply (len_zip Γ1 Γ2 a).
  assert (HjH : jH = (jG + (length Θ + length Γ3))%nat)
    by apply (len_splice (Γ1 ++ a :: Γ2) Θ Γ3).
  assert (HjI : jI = (length Γ1 + S kJ)%nat)
    by apply (len_zip Γ1 (Γ2 ++ Θ ++ Γ3) a).
  assert (HkJ : kJ = (length Γ2 + (length Θ + length Γ3))%nat)
    by apply (len_splice Γ2 Θ Γ3).
  assert (HjK : jK = (length Γ1 + (length Δ + kJ))%nat)
    by apply (len_splice Γ1 Δ (Γ2 ++ Θ ++ Γ3)).
  clearbody jA kA jB jC jD jE jF jG jH jI kJ jK.
  symmetry in HjA; destruct HjA.
  symmetry in HjB; destruct HjB.
  symmetry in HjC; destruct HjC.
  symmetry in HjE; destruct HjE.
  symmetry in HjF; destruct HjF.
  symmetry in HjH; destruct HjH.
  symmetry in HjI; destruct HjI.
  symmetry in HjK; destruct HjK.
  symmetry in HkA; destruct HkA.
  symmetry in HjD; destruct HjD.
  symmetry in HjG; destruct HjG.
  symmetry in HkJ; destruct HkJ.
  rewrite !pow_cast_refl.
  rewrite !id_right.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply graft_disjoint.
Qed.

(** ** The endomorphism operad / ** 内自同构操作子 *)

Definition EndOperad : Multicategory := {|
  mobj := poly_unit;
  mhom := End_hom;
  mhomset := λ Γ _, @homset C (pow (length Γ)) X;
  mcast := @End_mcast;
  mcast_respects := @End_mcast_respects;
  mcast_id := @End_mcast_id;
  mcast_trans := @End_mcast_trans;
  mid := End_mid;
  mcomp := @End_mcomp;
  mcomp_respects := @End_mcomp_respects;
  mcomp_id_left := @End_mcomp_id_left;
  mcomp_id_right := @End_mcomp_id_right;
  mcomp_assoc_nested := @End_mcomp_assoc_nested;
  mcomp_assoc_disjoint := @End_mcomp_assoc_disjoint;
  msym := @End_msym;
  msym_respects := @End_msym_respects;
  msym_id := @End_msym_id;
  msym_compose := @End_msym_compose;
  mcomp_equivariant := @End_mcomp_equivariant
|}.

End EndOperad.
