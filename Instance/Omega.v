Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(* * * The ordinal ω as a thin category / * * 序数 ω 作为一个稀疏范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/interval+category
 Wikipedia: https://en.wikipedia.org/wiki/Total_order

 [Omega] is the thin category whose objects are the natural numbers and whose
 morphisms [m ~> n] are proofs of [m ≤ n].  It is the shape category over which
 Adámek's initial-algebra chain [Instance ... Construction/Chain.v] is indexed:
 a functor [Omega ⟶ C] is exactly an ω-indexed diagram
 [X₀ ~> X₁ ~> X₂ ~> ...] in [C].

 The order is carried by a bespoke [Type]-valued relation [le_t] rather than
 the standard library's [le].  Two reasons: (1) [le] is [Prop]-valued and
 cannot eliminate into the [Type]-valued hom-sets of an arbitrary target
 category, which [Construction/Chain.v]'s [chain_hom] requires; (2) avoiding
 the stdlib keeps this file portable across Coq 8.19/8.20 and Rocq 9.1, whose
 [le] lemma names differ.  The explicit universe annotations
 ([le_t@{h}], [Morphism_equality@{o h p}]) are load-bearing: under the
 library-wide [Set Universe Polymorphism] a strictly-bound [Omega@{o h p}]
 must instantiate every polymorphic constant it mentions, exactly as
 [Instance/One.v] writes [Morphism_equality@{o h p}] and [poly_unit@{o}]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/interval+category 
 维基百科：  https://en.wikipedia.org/wiki/Total_order 

 [Omega] 是一个薄范畴，其对象是自然数，态射 [m ~> n] 是 [m ≤ n] 的证明。它是 Adámek 的初代数链 [Instance ... Construction/Chain.v] 所索引的形状范畴：一个函子 [Omega ⟶ C] 正好是 [C] 中的一个 ω 索引图 [X₀ ~> X₁ ~> X₂ ~> ...]。该顺序由一个定制的 [Type] 值关系 [le_t] 维持，而不是标准库的 [le]。有两个原因：（1）[le] 是 [Prop] 值的，不能消解到任意目标范畴的 [Type] 值同态集，这是 [Construction/Chain.v] 的 [chain_hom] 所要求的；（2）避免使用 stdlib 使这个文件可以在 Coq 8.19/8.20 和 Rocq 9.1 上移植，而它们的 [le] 引理名称不同。显式的宇宙注解（[le_t@{h}], [Morphism_equality@{o h p}]）是承重的：在库范围内的 [Set Universe Polymorphism] 下，严格绑定的 [Omega@{o h p}] 必须实例化它提到的每个多态常量，正如 [Instance/One.v] 所写的 [Morphism_equality@{o h p}] 和 [poly_unit@{o}]。
*)

Inductive le_t@{u} (n : nat) : nat → Type@{u} :=
  | le_t_n : le_t n
  | le_t_S {m} : le_t m → le_t (S m).

Arguments le_t_n {n}.
Arguments le_t_S {n m} _.

(*
 Transitivity, by recursion on the second derivation, so that composition in
 [Omega] reduces on closed inputs (needed by [chain_hom]). 

 --------
 传递性，通过对第二次推导进行递归，使得 [Omega] 的组合在封闭输入上简化（[chain_hom] 所需）。
*)
Fixpoint le_t_trans@{u} {m n k} (f : le_t@{u} m n) (g : le_t@{u} n k) :
  le_t@{u} m k :=
  match g in le_t _ k' return le_t@{u} m k' with
  | le_t_n     => f
  | le_t_S g'  => le_t_S (le_t_trans f g')
  end.

(*
 Reflexivity is a strict left unit for [le_t_trans] by the [le_t_n] branch.
 These three unit/associativity lemmas are left with inferred universe
 binders (no explicit [@{u}]): stating an [eq] between [le_t]-terms draws in
 the equality's own universe alongside [le_t]'s, which a single [@{u}] binder
 cannot name on Coq 8.19/8.20 ("unbound universes"); auto-polymorphism binds
 them correctly on every supported version.  The load-bearing annotations are
 the ones inside [Omega] below. 

 --------
 反身性是  [le_t_trans]  的一个严格左单位，由  [le_t_n]  分支提供。这三个单位/结合性引理保留了推断的宇宙绑定器（没有显式的  [@{u}] ）：在  [le_t]  项之间声明一个  [eq]  会将等式自身的宇宙与  [le_t]  的宇宙一起引入，而单个  [@{u}]  绑定器在 Coq 8.19/8.20 中无法命名它们（“未绑定的宇宙”）；自动多态性在每个支持的版本中都能正确绑定它们。承重注释是下面 [Omega]  内的那些。
*)
Lemma le_t_trans_id_l {m n} (f : le_t m n) :
  le_t_trans f le_t_n = f.
Proof. reflexivity. Qed.

Lemma le_t_trans_id_r {m n} (f : le_t m n) :
  le_t_trans le_t_n f = f.
Proof.
  induction f as [| n' f' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma le_t_trans_assoc {m n k l}
  (f : le_t m n) (g : le_t n k) (h : le_t k l) :
  le_t_trans (le_t_trans f g) h = le_t_trans f (le_t_trans g h).
Proof.
  induction h as [| l' h' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Program Definition Omega@{o h p} : Category@{o h p} := {|
  obj     := nat;
  hom     := le_t@{h};
  homset  := Morphism_equality@{o h p};
  id      := fun _ => le_t_n@{h};
  compose := fun _ _ _ f g => le_t_trans@{h} g f
|}.
Solve All Obligations with
  (simpl; intros; try subst;
   rewrite ?le_t_trans_id_l, ?le_t_trans_id_r, ?le_t_trans_assoc;
   try reflexivity).

(* The generating step morphism [n ~> S n]. / 生成步态射 [n ~> S n]。 *)
Definition omega_step (n : nat) : @hom Omega n (S n) := le_t_S le_t_n.
