Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.Quotient.

From Coq Require Import Arith.

Generalizable All Variables.

(*
   * * The free PROP, bundled: the library's first inhabited [PROP] 

   --------
   * * 免费道具，捆绑：图书馆第一个有人居住的 [PROP]
*)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Free_category

 This file assembles the bundled [PROP] instance [FreePROP S] on the
 free category [FreeCat S] of a signature [S] — the first inhabitant
 of the [PROP] class in the library.  See the surrounding discussions
 in [Construction/PROP/Free.v] and [Construction/PROP.v] for the
 roadmap of the instance tower that this file completes.

 Every equality field of [FreePROP] is [eq_refl], because the whole
 tower shares ONE [Monoidal] record:

 - [strict_is_monoidal (FreeCat_Strict S)] is, by iota reduction on
 the explicit record literal of [Strict.v], the literal term
 [FreeCat_Monoidal S];
 - [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]
 projects through [FreeCat_Braided S] to the SAME literal term;

 so [prop_monoidal_coherence] — propositional in general, with the
 use-site friction documented at length in [Construction/PROP.v] —
 is DEFINITIONAL for the free PROP.  Likewise [prop_of_nat] is the
 identity on [nat] (the objects of [FreeCat S] ARE the naturals),
 [prop_unit_zero] holds because the unit of [FreeCat_Monoidal S] is
 the literal [0], and [prop_tensor_plus] holds because the object
 action of [FreeCat_Tensor S] is [fun p => fst p + snd p], which
 reduces on the literal pair [(m, n)] to [m + n].

 The file also hosts the two side-condition instances that the
 interpretation and universal-property files require of [FreeCat S],
 both drawn from the fully general kit of [Construction/Quotient.v]:

 - [HomEqProp (FreeCat S)]: the hom-setoid equivalence of
 [FreeCat S] IS the [Prop]-valued [TermEq S] after delta/beta
 reduction of [Free.v]'s [Term_Setoid], so both directions of the
 reflection are the identity;
 - [ObjDecEq (FreeCat S)]: objects are [nat], so [Nat.eq_dec]
 decides object equality, giving axiom-free UIP on objects.

 Machine-checked [Example]s at the end pin the definitional
 behaviour, so any regression in the shared-record wiring is caught
 here rather than at a distant use site. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/free+category
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)
 维基百科：https://en.wikipedia.org/wiki/Free_category

 该文件将捆绑的[PROP]实例[FreePROP S]组装在签名[S]的自由范畴[FreeCat S]上——这是库中[PROP]类的第一个成员。有关该文件完成的实例塔的路线图，请参阅[Construction/PROP/Free.v]和[Construction/PROP.v]中的相关讨论。

 [FreePROP]的每个等式字段都是[eq_refl]，因为整个塔共享一个[Monoidal]记录：

 - 通过对[Strict.v]的显式记录字面量进行iota化简，[strict_is_monoidal (FreeCat_Strict S)]是字面量项[FreeCat_Monoidal S]；
 - [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]通过[FreeCat_Braided S]投影到同一个字面量项；所以 [prop_monoidal_coherence]——总体上是命题性的，并且在 [Construction/PROP.v] 中详细记录了使用场所的摩擦——对于自由 PROP 是定义性的。同样，[prop_of_nat] 是 [nat]（[FreeCat S] 的对象是自然数）上的恒等式，[prop_unit_zero] 成立是因为 [FreeCat_Monoidal S] 的单位就是字面意义上的 [0]，[prop_tensor_plus] 成立是因为 [FreeCat_Tensor S] 的对象作用是 [fun p => fst p + snd p]，这在字面对 [(m, n)] 上化简为 [m + n]。

 该文件还包含解释和泛性质文件对 [FreeCat S] 所要求的两个附带条件实例，均来自 [Construction/Quotient.v] 的完全通用工具包。- [HomEqProp (FreeCat S)]：[FreeCat S] 的同态集合等价是 [Prop] 值的 [TermEq S]，在对 [Free.v] 的 [Term_Setoid] 进行 delta/beta 归约之后，因此反射的两个方向都是恒等的；
 - [ObjDecEq (FreeCat S)]：对象是 [nat]，因此 [Nat.eq_dec] 决定对象的相等性，为对象提供无公理的 UIP。

 机器校验的 [Example] 在末尾固定了定义行为，因此共享记录连接中的任何回归都会在这里被发现，而不是在远处的使用地点。
*)

Section FreePROP.

Context (S : Signature).

Open Scope nat_scope.

(*
   * ** The bundled instance

   All three structure fields name records that project to THE shared
   [FreeCat_Monoidal S], so each equality field below is [eq_refl].
   If [prop_monoidal_coherence := eq_refl] ever stops typechecking,
   the shared-record wiring broke — fix the wiring; do not generalize
   the field. 

   --------
   * ** 捆绑实例

   所有三个结构字段都命名为投射到共享的[FreeCat_Monoidal S]的记录，所以下面的每个相等字段都是[eq_refl]。
   如果[prop_monoidal_coherence := eq_refl]停止类型检查，
   共享记录的连接破坏了——修复连接；不要泛化字段。
*)

Definition FreePROP : PROP := {|
  prop_cat       := FreeCat S;
  prop_strict    := FreeCat_Strict S;
  prop_symmetric := FreeCat_Symmetric S;

  (*
 [strict_is_monoidal (FreeCat_Strict S)] and
 [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]
 both reduce to the literal term [FreeCat_Monoidal S]. 

 --------
 [strict_is_monoidal (FreeCat_Strict S)] 和 [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))] 都简化为字面术语 [FreeCat_Monoidal S]。
*)
  prop_monoidal_coherence := eq_refl;

  (* Objects of [FreeCat S] are literally the naturals. / [FreeCat S] 的对象字面上就是自然数。 *)
  prop_of_nat := fun n : nat => n;

  (*
 [I] of [FreeCat_Monoidal S] is the literal [0]. 

 --------
 [I] 的 [FreeCat_Monoidal S] 是字面上的 [0]。
*)
  prop_unit_zero := eq_refl;

  (*
 [fobj (FreeCat_Tensor S) (m, n)] reduces to [m + n]. 

 --------
 [fobj (FreeCat_Tensor S) (m, n)] 缩减为 [m + n]。
*)
  prop_tensor_plus := fun m n => eq_refl
|}.

(*
   * ** Side-condition instances for the interpretation files

   The hom-setoid equivalence of [FreeCat S] is [TermEq S] by
   delta/beta reduction of [Term_Setoid], and [TermEq S] is already
   [Prop]-valued, so the [Prop] reflection is the identity in both
   directions. 

   --------
   * ** 解释文件的副条件实例

   [FreeCat S] 的同集合等价是 [TermEq S]，通过 [Term_Setoid] 的 delta/beta 化简得到，并且 [TermEq S] 已经是 [Prop] 值，所以 [Prop] 反射在两个方向上都是恒等的。
*)

#[export] Instance FreeCat_HomEqProp : HomEqProp (FreeCat S) :=
  Build_HomEqProp (FreeCat S)
    (fun m n : nat => @TermEq S m n)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(*
   * Objects of [FreeCat S] are [nat], whose equality is decidable. 

   --------
   * [FreeCat S] 的对象是 [nat]，其等式是可判定的。
*)

#[export] Instance FreeCat_ObjDecEq : ObjDecEq (FreeCat S) := Nat.eq_dec.

(*
   * ** Machine-checked sanity

   Each [Example] holds by [eq_refl], witnessing that the
   corresponding field of [FreePROP] is definitional. 

   --------
   * ** 机器检查的合理性

   每个 [Example] 由 [eq_refl] 保持，证明 [FreePROP] 对应的字段是定义性的。
*)

(*
   * The coherence between the strict and symmetric [Monoidal] paths is
   the reflexivity proof itself — the "known limitation" discussed in
   [Construction/PROP.v] does not bite on the free PROP. 

   --------
   * 严格且对称的 [Monoidal] 路径之间的一致性就是反身性证明本身——在 [Construction/PROP.v] 中讨论的“已知限制”并不会影响自由 PROP。
*)
Example FreePROP_coherence_is_refl :
  @prop_monoidal_coherence FreePROP = eq_refl := eq_refl.

(** The object correspondence is the identity on [nat]. / 对象对应是 [nat] 上的恒等映射。 *)
Example FreePROP_of_nat_id (n : nat) :
  @prop_of_nat FreePROP n = n := eq_refl.

(** The monoidal unit is the literal object [0]. / 单位对象是字面对象 [0]。 *)
Example FreePROP_I :
  @I _ (@strict_is_monoidal _ (@prop_strict FreePROP)) = 0%nat := eq_refl.

(*
   * Tensor-on-objects is literally addition, with [eq_refl] proof. 

   --------
   * 张量作用于对象字面上就是加法，并有 [eq_refl] 证明。
*)
Example FreePROP_tensor_plus_is_refl (m n : nat) :
  @prop_tensor_plus FreePROP m n = eq_refl := eq_refl.

(*
   * [PROP.v]'s successor decomposition [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧] applies to
   [FreePROP]; whichever [Monoidal] path its statement was elaborated
   through, conversion closes the gap here, because both paths project
   the one shared record. 

   --------
   * [PROP.v] 的继承者分解 [⟦S n⟧ = [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧] ⨂ ⟦n⟧] 适用于 [FreePROP]；无论其语句是通过哪条 [Monoidal] 路径展开的，转换在这里都弥合了差距，因为两条路径都投影了同一个共享记录。
*)
Example FreePROP_of_nat_S_smoke (n : nat) :
  @prop_of_nat FreePROP (Datatypes.S n)
  = ((@prop_of_nat FreePROP 1)
       ⨂[@strict_is_monoidal _ (@prop_strict FreePROP)]
     (@prop_of_nat FreePROP n))%object :=
  prop_of_nat_S FreePROP n.

End FreePROP.

Arguments FreePROP S : assert.
