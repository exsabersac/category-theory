Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The Strict structure on the free PROP / * * 自由 PROP 上的严格结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 [FreeCat S] is STRICT monoidal: its objects are natural numbers, its
 tensor on objects is addition, and the arity equations

 [Nat.add_assoc x y z] : x + (y + z) = (x + y) + z   (associativity)
 [Nat.add_0_l x]       : 0 + x = x                   (left unit)
 [Nat.add_0_r x]       : x + 0 = x                   (right unit)

 are honest Leibniz equalities of objects — exactly the object-level
 strictness the [StrictMonoidal] class demands.  The comparison
 fields — that the structural isomorphisms of the monoidal structure
 coincide with the identity transported along those equalities — are
 reflexivity-grade here, because [Structural.v] BUILT the unitors and
 the associator as [T_cast] maps, and [T_cast e] is definitionally
 the very [match e in _ = T return _ ~> T with eq_refl => id end]
 shape that the class's fields ask for (with the SAME proof term [e]
 on both sides, so not even UIP is needed).

 Crucially, [strict_is_monoidal] is [FreeCat_Monoidal S] — THE shared
 [Monoidal] record from [Monoidal.v] that the Braided, Symmetric, and
 PROP instances also name — so all structure projections downstream
 agree definitionally.

 Following the [Free.v] discipline, the comparison proofs are
 standalone, named lemmas and the record is assembled with every
 field explicit, generating no Program obligations. 

 --------
 nLab:  https://ncatlab.org/nlab/show/strict+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 维基百科:  https://en.wikipedia.org/wiki/Monoidal_category 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 [FreeCat S] 是严格单体范畴：它的对象是自然数，它的对象张量是加法，并且算子方程为

 [Nat.add_assoc x y z] : x + (y + z) = (x + y) + z   （结合律）
 [Nat.add_0_l x]       : 0 + x = x                     （左单位元）
 [Nat.add_0_r x]       : x + 0 = x                     （右单位元）是对象的真实莱布尼茨等式——正是 [StrictMonoidal] 类所要求的对象级严格性。比较字段——单体结构的结构同构与沿这些等式传输的恒等式相符合——在这里是自反等级的，因为 [Structural.v] 将幺元子和结合子构建为 [T_cast] 映射，并且 [T_cast e] 在定义上正是 [match e in _ = T return _ ~> T with eq_refl => id end] 形状，类的字段所要求的（两边使用相同的证明项 [e]，因此甚至不需要 UIP）。

 关键是，[strict_is_monoidal] 是 [FreeCat_Monoidal S]——来自 [Monoidal.v] 的共享 [Monoidal] 记录，Braided、Symmetric 和 PROP 实例也都使用这个名称——因此所有下游结构投影在定义上是一致的。遵循 [Free.v] 规范，比较证明是独立的、具名的引理，并且记录是完整组装的，每个字段都明确展示，不会生成程序义务。
*)

Section FreeStrict.

Context (S : Signature).

Open Scope nat_scope.

(*
   * ** Comparison lemmas

   Each states that a structural map of [FreeCat_Monoidal S] equals
   the transported identity along the corresponding arity equation.
   Both sides are the same [match] on the same proof term, so each
   proof is [reflexivity]. 

   --------
   * ** 比较引理

   每个都说明  [FreeCat_Monoidal S]  的一个结构映射等于沿相应元数方程传递的恒等映射。
   双方都是相同的  [match]  在相同的证明项上，所以每个证明都是  [reflexivity] 。
*)

(*
   * The associator [(x + y) + z ≅ x + (y + z)] is the transported
   identity along [eq_sym (Nat.add_assoc x y z)] — the orientation of
   [Structural.v]'s [to]. 

   --------
   * 关联器 [(x + y) + z ≅ x + (y + z)] 是沿 [eq_sym (Nat.add_assoc x y z)] 传输的恒等 — [Structural.v] 的 [to] 的方向。
*)
Lemma FreeCat_strict_assoc_to (x y z : nat) :
  to (@tensor_assoc (FreeCat S) (FreeCat_Monoidal S) x y z)
  ≈ match eq_sym (Nat.add_assoc x y z) in _ = T
      return ((x + y) + z ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * The left unitor [0 + x ≅ x] is the transported identity along
   [Nat.add_0_l x] (definitionally trivial: [Nat.add] is left-strict). 

   --------
   * 左单元子 [0 + x ≅ x] 是沿着 [Nat.add_0_l x] 传输的恒等映射（按定义是平凡的：[Nat.add] 是左严格的）。
*)
Lemma FreeCat_strict_unit_left_to (x : nat) :
  to (@unit_left (FreeCat S) (FreeCat_Monoidal S) x)
  ≈ match Nat.add_0_l x in _ = T
      return (0 + x ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * The right unitor [x + 0 ≅ x] is the transported identity along
   [Nat.add_0_r x] (a genuinely propositional equation). 

   --------
   * 右单位元 [x + 0 ≅ x] 是沿着 [Nat.add_0_r x]（一个真正的命题等式）传输的恒等式。
*)
Lemma FreeCat_strict_unit_right_to (x : nat) :
  to (@unit_right (FreeCat S) (FreeCat_Monoidal S) x)
  ≈ match Nat.add_0_r x in _ = T
      return (x + 0 ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * ** The Strict instance over THE shared Monoidal record 

   --------
   * ** 在共享 Monoidal 记录上的严格实例
*)

Definition FreeCat_Strict : @StrictMonoidal (FreeCat S) := {|
  strict_is_monoidal    := FreeCat_Monoidal S;  (* THE shared record / 共享记录 *)
  strict_assoc_obj      := fun x y z => eq_sym (Nat.add_assoc x y z);
  strict_unit_left_obj  := fun x => Nat.add_0_l x;
  strict_unit_right_obj := fun x => Nat.add_0_r x;
  strict_assoc_to       := fun x y z => FreeCat_strict_assoc_to x y z;
  strict_unit_left_to   := fun x => FreeCat_strict_unit_left_to x;
  strict_unit_right_to  := fun x => FreeCat_strict_unit_right_to x
|}.

End FreeStrict.

Arguments FreeCat_Strict S : assert.
