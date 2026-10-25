Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.

Generalizable All Variables.

(* * * The initial-algebra chain of an endofunctor / * * 一个自函子初代数链 *)

(*
 nLab: https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor

 For an endofunctor [F] on a category [C] with an initial object [0], the
 initial-algebra chain is the ω-indexed diagram

 0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

 whose colimit (when [F] preserves it) carries the initial F-algebra
 (Adámek's theorem, Theory/Adamek.v).  Here it is packaged as a functor
 [Chain : Omega ⟶ C] out of the ordinal ω (Instance/Omega.v).  The section
 is closed before any [Colimit (Chain F)] statement so that the diagram is a
 genuine object of the functor category. 

 --------
 nLab：https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor

 对于一个在类别[C]上具有初始对象[0]的端函子[F]，初始代数链是ω索引的图

 0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

 其余积（当[F]保留它时）携带初始F-代数（Adámek定理，Theory/Adamek.v）。这里它作为一个从序数ω到[Chain : Omega ⟶ C]的函子进行打包（Instance/Omega.v）。该部分在任何[Colimit (Chain F)]陈述之前已关闭，因此该图是函子范畴中的一个真正对象。
*)

Section Chain.

Context {C : Category}.
Context `{@Initial C}.
Context (F : C ⟶ C).

Fixpoint chain_obj (n : nat) : C :=
  match n with
  | O   => initial_obj
  | S k => F (chain_obj k)
  end.

Fixpoint chain_step (n : nat) : chain_obj n ~> chain_obj (S n) :=
  match n with
  | O   => zero
  | S k => fmap[F] (chain_step k)
  end.

(*
 The action on an order proof [m ≤ n]: iterate [chain_step] along the
 derivation. 

 --------
 在订单证明 [m ≤ n] 上的操作：沿着推导迭代 [chain_step]。
*)
Fixpoint chain_hom {m n} (p : le_t m n) : chain_obj m ~> chain_obj n :=
  match p with
  | le_t_n    => id
  | le_t_S p' => chain_step _ ∘ chain_hom p'
  end.

(*
 Functoriality on composites: transporting along a fused order proof is the
 composite of the transports (in the direction fixed by [Omega]'s
 composition [le_t_trans g f]). 

 --------
 复合上的函子性：沿着融合顺序证明的运输是沿运输的复合（按照[Omega]的复合[le_t_trans g f]所固定的方向）。
*)
Lemma chain_hom_trans {m n k} (a : le_t m n) (b : le_t n k) :
  chain_hom (le_t_trans a b) ≈ chain_hom b ∘ chain_hom a.
Proof.
  induction b as [| k' b' IH]; simpl.
  - now rewrite id_left.
  - rewrite IH; now rewrite comp_assoc.
Qed.

(*
   【Chain 定义展开】/ Chain walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      有初对象 0 与自函子 F 时，初代数链：
      0 → F0 → F²0 → …（ω 图）。其（F 保持的）余极限给出初 F-代数（Adámek）。
      Initial-algebra chain as a diagram Omega ⟶ C.
      Haskell 对照：递归类型的「迭代逼近」—— Nat = μX. 1+X 的链 0,1,1+1,…。
      Approximating μF by iterating F on 0.

   2) 零件 / Pieces
      chain_obj / chain_step：对象与一步映射；
      chain_hom：沿 m≤n 的运输；Chain : Omega ⟶ C 打成函子。
      Cochain：对偶（终对象 + 余链）。

   阅读：chain_obj → chain_step → Chain 函子 → 再谈 Colimit。
   Read: objects → steps → functor → then colimit elsewhere.
*)

Program Definition Chain : Omega ⟶ C := {|
  fobj := chain_obj;
  fmap := fun _ _ p => chain_hom p
|}.
(*
 fmap_respects: strict-equality hom-setoid; fmap_id: chain_hom of the
 reflexivity proof is [id] definitionally; fmap_comp: chain_hom_trans. 

 --------
 fmap_respects: 严格相等同态集；fmap_id: 链同态的反身性证明在定义上是 [id]；fmap_comp: 链同态传递。
*)
Solve All Obligations with
  (simpl; intros; try subst; try reflexivity;
   try (now apply chain_hom_trans); try (now rewrite chain_hom_trans); try cat).

End Chain.

(*
 The dual chain (a co-chain into the codomain), for the final-coalgebra
 development, by duality through [C^op]. 

 --------
 双链（一个到余域的共链），用于最终余代数的发展，通过 [C^op] 的对偶性。
*)
Definition Cochain {C : Category} `{@Terminal C} (F : C ⟶ C) :
  Omega^op ⟶ C := (@Chain (C^op) _ (F^op))^op.
