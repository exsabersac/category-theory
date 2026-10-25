Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Braided.

Generalizable All Variables.

(* * * The symmetric monoidal structure on the free PROP / * * 自由PROP上的对称单体范畴结构 *)

(*
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 A PROP is a SYMMETRIC strict monoidal category, so the braiding
 [T_braid m n] installed on [FreeCat S] by
 [Construction/PROP/Braided.v] must be its own inverse.  That is
 precisely the [TE_braid_invol] axiom of [TermEq]:

 σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n}

 — crossing an [m]-wide bundle of wires past an [n]-wide bundle and
 back again untangles completely.  Since the tensor of [FreeCat S]
 is [Nat.add] on objects, [m ⨂ n] and [m + n] agree definitionally
 and the axiom matches the [braid_invol] field of
 [SymmetricMonoidal] verbatim.

 The [symmetric_is_braided] field names [FreeCat_Braided S], whose
 own [braided_is_monoidal] field names THE shared [Monoidal] record
 [FreeCat_Monoidal S]: the Strict and bundled PROP instances
 downstream project this single record as well, so their agreement
 is definitional.

 The synonym lemma [braid_invol] of [Construction/PROP/Naturality.v]
 is deliberately not imported here: its name would shadow the
 [SymmetricMonoidal] projection of the same name (the [Free.v]
 discipline of standalone-lemma-then-explicit-record keeps the
 record literal free of Program obligations, but the field names
 themselves must still resolve to the class projections). 

 --------
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 Wikipedia:  https://en.wikipedia.org/wiki/Symmetric_monoidal_category 
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 PROP 是一个对称严格幺半范畴，因此在 [FreeCat S] 上由 [Construction/PROP/Braided.v] 安装的编织器 [T_braid m n] 必须是它自身的逆。也就是说，这正是 [TermEq] 的 [TE_braid_invol] 公理:

 σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n}

 — 将宽度为 [m] 的一束电线与宽度为 [n] 的另一束电线交叉再返回，可以完全解开缠结。由于 [FreeCat S] 的张量在对象上是 [Nat.add]，[m ⨂ n] 和 [m + n] 定义上是一致的，该公理与 [SymmetricMonoidal] 的 [braid_invol] 场完全吻合。[symmetric_is_braided] 字段名称 [FreeCat_Braided S]，其自身的 [braided_is_monoidal] 字段名称共享 [Monoidal] 记录 [FreeCat_Monoidal S]：严格和捆绑的 PROP 实例下游项目也会投影此单一记录，因此它们的约定是定义性的。

 [Construction/PROP/Naturality.v] 的同义词词元 [braid_invol] 故意未在此导入：其名称将会遮蔽同名的 [SymmetricMonoidal] 投影（独立词元然后显式记录的 [Free.v] 规则保持记录字面量不承担程序义务，但字段名称本身仍必须解析为类投影）。
*)

Section FreeSymmetric.

Context (S : Signature).

Open Scope nat_scope.

(*
   * ** Braid involution

   The [braid_invol] field of [SymmetricMonoidal] at [x y]: the
   composite [σ_{y,x} ⊙ σ_{x,y} : x + y ⇒ x + y] is the identity.
   This is the primitive constructor [TE_braid_invol] applied at
   [m := x], [n := y]. 

   --------
   * ** 辫子变换

   在 [x y] 上的 [SymmetricMonoidal] 的 [braid_invol] 场：复合的 [σ_{y,x} ⊙ σ_{x,y} : x + y ⇒ x + y] 是恒等。
   这是原始构造器 [TE_braid_invol] 在 [m := x]、[n := y] 上的应用。
*)

Lemma free_braid_invol (x y : nat) :
  TermEq S (T_comp (T_braid y x) (T_braid x y)) (T_id (x + y)).
Proof.
  apply TE_braid_invol.
Qed.

(*
   * ** THE SymmetricMonoidal record on [FreeCat S]

   [symmetric_is_braided] names the ONE braided record
   [FreeCat_Braided S] (hence, through it, the ONE shared [Monoidal]
   record [FreeCat_Monoidal S]); the involution proof is the
   standalone lemma above.  Every field is explicit, so no Program
   obligations are generated. 

   --------
   * ** 关于 [FreeCat S] 的 SymmetricMonoidal 记录

   [symmetric_is_braided] 命名了 ONE 编织记录
   [FreeCat_Braided S] （因此，通过它，ONE 共享的 [Monoidal]
   记录 [FreeCat_Monoidal S] ); 反演的证明是上面的独立引理。每个字段都是显式的，因此不会生成任何 Program 义务。
*)

Program Definition FreeCat_Symmetric : @SymmetricMonoidal (FreeCat S) := {|
  symmetric_is_braided := FreeCat_Braided S;
  braid_invol := fun x y => free_braid_invol x y
|}.

End FreeSymmetric.

Arguments FreeCat_Symmetric S : assert.
