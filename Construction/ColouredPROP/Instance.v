Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.Quotient.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(*
   * * The free coloured PROP, bundled: the library's first [ColouredPROP] 

   --------
   * * 免费彩色 PROP，捆绑：图书馆的第一个 [ColouredPROP]
*)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 This file assembles the bundled [ColouredPROP] instance
 [FreeColouredPROP S Cdec] on the free category [CFreeCat S] of a
 coloured signature [S] — the first inhabitant of the
 [ColouredPROP] class of [Construction/ColouredPROP.v] — merging
 the one-sorted spine's donor pair [Construction/PROP/Strict.v] +
 [Construction/PROP/Instance.v], the same layout compression as
 the earlier files of this directory.

 ** Strictness

 [CFreeCat S] is STRICT monoidal: its objects are colour words
 (lists over [Colour]), its tensor on objects is concatenation,
 and the boundary equations

 [eq_sym (app_assoc x y z)] : (x ++ y) ++ z = x ++ (y ++ z)
 [app_nil_l x]              : [] ++ x = x
 [app_nil_r x]              : x ++ [] = x

 are honest Leibniz equalities of objects — exactly the
 object-level strictness the [StrictMonoidal] class demands.  The
 comparison fields — that the structural isomorphisms coincide
 with the identity transported along those equalities — are
 reflexivity-grade here, because [Cast.v] BUILT the unitors and
 the associator as [CT_cast] maps, and [CT_cast e] is
 definitionally the very [match e in _ = T return _ ~> T with
 eq_refl => id end] shape that the class's fields ask for (with
 the SAME proof term [e] on both sides, so not even UIP on colour
 words is needed).  Note the stdlib orientation of [app_assoc]
 (right-to-left reassociation), so the associator's [to] is the
 [eq_sym] cast — the orientation fixed once in [Cast.v] and
 repeated verbatim in [strict_assoc_obj] below.

 Crucially, [strict_is_monoidal] is [CFreeCat_Monoidal S Cdec] —
 THE shared [Monoidal] record from [Monoidal.v] that the Braided
 and Symmetric instances of [Braided.v] also name — so all
 structure projections downstream agree definitionally.

 ** The bundled instance

 Every equality field of [FreeColouredPROP] is [eq_refl], because
 the whole tower shares that ONE [Monoidal] record:

 - [strict_is_monoidal CFreeCat_Strict] is, by iota reduction on
 the explicit record literal below, the literal term
 [CFreeCat_Monoidal S Cdec];
 - [braided_is_monoidal (symmetric_is_braided
 (CFreeCat_Symmetric S Cdec))] projects through
 [CFreeCat_Braided S Cdec] to the SAME literal term;

 so [cprop_monoidal_coherence] — propositional in general, with
 the use-site friction documented at length in
 [Construction/PROP.v] — is DEFINITIONAL for the free coloured
 PROP.  Likewise [cprop_of_list] is the identity on colour words
 (the objects of [CFreeCat S] ARE the lists of colours),
 [cprop_unit_nil] holds because the unit of
 [CFreeCat_Monoidal S Cdec] is the literal [[]], and
 [cprop_tensor_app] holds because the object action of
 [CFreeCat_Tensor S] is [fun p => fst p ++ snd p], which reduces
 on the literal pair [(cs, ds)] to [cs ++ ds].

 D2 WARNING (see the foot of [Monoidal.v]): the shared record
 [CFreeCat_Monoidal S Cdec] depends on the colour decider [Cdec],
 so every one of those [eq_refl]s presumes that ONE canonical
 [Cdec] is fixed per colour type at each instance site.  Mixing
 deciders surfaces as an opaque unification error at exactly the
 [cprop_monoidal_coherence := eq_refl] field.  If that [eq_refl]
 ever stops typechecking, the shared-record wiring broke — fix the
 wiring; never generalize the field.  The machine-checked
 [Example]s at the end of this file exist to catch such
 violations at their source.

 ** Side-condition instances

 The file also hosts the two side-condition instances that the
 interpretation and universal-property files require of
 [CFreeCat S], both drawn from the fully general kit of
 [Construction/Quotient.v]:

 - [HomEqProp (CFreeCat S)]: the hom-setoid equivalence of
 [CFreeCat S] IS the [Prop]-valued [CTermEq S] after
 delta/beta reduction of [Free.v]'s [CTerm_Setoid], so both
 directions of the reflection are the identity;
 - [ObjDecEq (CFreeCat S)]: objects are colour words, so
 [list_eq_dec Cdec] decides object equality, giving axiom-free
 UIP on objects.  Per the D2 decidability discipline this one
 is a plain [Definition], not an [Instance]: it is
 [Cdec]-conditional, and call sites pass it explicitly, naming
 the one canonical decider of the ambient development.

 Following the [Free.v] discipline, the comparison proofs are
 standalone, named lemmas and the records are assembled with every
 field explicit, generating no Program obligations. 

 --------
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 此文件组装了捆绑的 [ColouredPROP] 实例 [FreeColouredPROP S Cdec] 在彩色签名 [S] 的自由范畴 [CFreeCat S] 上——这是 [Construction/ColouredPROP.v] 类的第一个成员 [ColouredPROP]——合并了单排序主干的供体对 [Construction/PROP/Strict.v] + [Construction/PROP/Instance.v]，与本目录之前文件的布局压缩相同。

 ** 严格性

 [CFreeCat S] 是严格单体的：其对象是颜色词（[Colour] 上的列表），对象上的张量是连接运算，并且边界方程为

 [eq_sym (app_assoc x y z)] : (x ++ y) ++ z = x ++ (y ++ z)
 [app_nil_l x] : [] ++ x = x
 [app_nil_r x] : x ++ [] = x是真正的莱布尼茨对象等式——正是 [StrictMonoidal] 类所要求的对象级严格性。比较域——结构同构与沿这些等式传递的恒等式相一致——在这里是自反级别的，因为 [Cast.v] 将单位子和结合子构建为 [CT_cast] 映射，并且 [CT_cast e] 在定义上正是该类字段所要求的 [match e in _ = T return _ ~> T with eq_refl => id end] 形状（两边使用相同的证明项 [e]，因此甚至不需要对颜色词的 UIP）。注意 [app_assoc] 的标准库方向（从右向左重新结合），因此结合子的 [to] 是 [eq_sym] 类型转换——方向在 [Cast.v] 中固定一次，并在下面的 [strict_assoc_obj] 中逐字重复。至关重要的是，[strict_is_monoidal] 就是 [CFreeCat_Monoidal S Cdec] —— 这是来自 [Monoidal.v] 的共享 [Monoidal] 记录，Braided 和 Symmetric 的 [Braided.v] 实例也使用该记录命名 —— 因此所有下游的结构投影在定义上保持一致。

 ** 捆绑实例

 [FreeColouredPROP] 的每个相等字段都是 [eq_refl]，因为整个结构塔共用那一个 [Monoidal] 记录：

 - [strict_is_monoidal CFreeCat_Strict] 是通过下方显式记录字面量的 iota 简化得到的字面量项 [CFreeCat_Monoidal S Cdec]；
 - [braided_is_monoidal (symmetric_is_braided (CFreeCat_Symmetric S Cdec))] 通过 [CFreeCat_Braided S Cdec] 投影到相同的字面量项;所以 [cprop_monoidal_coherence] — 一般来说是命题性的，其在使用场所的摩擦在 [Construction/PROP.v] 中有详细记录 — 对自由彩色 PROP 是定义性的。同样，[cprop_of_list] 是颜色词的恒等式（[CFreeCat S] 的对象是颜色列表），[cprop_unit_nil] 成立，因为 [CFreeCat_Monoidal S Cdec] 的单位是字面上的 [[]，而 [cprop_tensor_app] 成立，因为 [CFreeCat_Tensor S] 的对象作用是 [fun p => fst p ++ snd p]，它在字面对 [(cs, ds)] 上简化为 [cs ++ ds]。D2 警告（见 [Monoidal.v] 页脚）：共享记录 [CFreeCat_Monoidal S Cdec] 依赖于颜色判定器 [Cdec]，因此每一个 [eq_refl] 都假定每个实例站点的每种颜色类型固定一个规范的 [Cdec]。混合判定器会在 [cprop_monoidal_coherence := eq_refl] 字段产生不透明的统一错误。如果 [eq_refl] 任何时候停止类型检查，则说明共享记录的连接断开——修复连接；切勿泛化该字段。此文件末尾的机器检查 [Example] 存在是为了在源头捕获此类违规行为。

 ** 边条件实例

 该文件还包含两个边条件实例，这是解释文件和通用属性文件对 [CFreeCat S] 的要求，均取自 [Construction/Quotient.v] 的完全通用工具包。- [HomEqProp (CFreeCat S)] ：[CFreeCat S] 的同构集合等价是 [Prop] 值的 [CTermEq S]，在对 [Free.v] 的 [CTerm_Setoid] 进行 delta/beta 规约后，因此反射的两个方向都是恒等；
 - [ObjDecEq (CFreeCat S)] ：对象是颜色词，因此 [list_eq_dec Cdec] 决定对象相等性，为对象提供无公理的 UIP。根据 D2 可判定性规范，这个是普通的 [Definition]，而不是 [Instance]：它是 [Cdec] 条件的，而且调用位置会显式传递它，并命名环境开发中唯一的标准决定器。

 遵循 [Free.v] 规范，比对证明是独立的，作为命名引理，并且记录的每个字段都是显式组装的，不会生成 Program 义务。
*)

Section FreeColouredPROP.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).

(*
   * ** Comparison lemmas

   Each states that a structural map of [CFreeCat_Monoidal S Cdec]
   equals the transported identity along the corresponding boundary
   equation.  Both sides are the same [match] on the same proof
   term, so each proof is [reflexivity]. 

   --------
   * ** 比较引理

   每个引理都说明了  [CFreeCat_Monoidal S Cdec] 的一个结构映射
   等于沿相应边界方程传递的恒等映射。两边都是相同的  [match]，
   在相同的证明项上，因此每个证明都是  [reflexivity] 。
*)

(*
   * The associator [(x ++ y) ++ z ≅ x ++ (y ++ z)] is the transported
   identity along [eq_sym (app_assoc x y z)] — the orientation of
   [Cast.v]'s [to]. 

   --------
   * 结合子 [(x ++ y) ++ z ≅ x ++ (y ++ z)] 是沿着 [eq_sym (app_assoc x y z)] 传输的恒等式 — [Cast.v] 的 [to] 的方向。
*)
Lemma CFreeCat_strict_assoc_to (x y z : list Colour) :
  to (@tensor_assoc (CFreeCat S) (CFreeCat_Monoidal S Cdec) x y z)
  ≈ match eq_sym (app_assoc x y z) in _ = T
      return ((x ++ y) ++ z ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * The left unitor [[] ++ x ≅ x] is the transported identity along
   [app_nil_l x] (definitionally trivial: [app] is left-strict). 

   --------
   * 左单位元 [[] ++ x ≅ x] 是沿着 [app_nil_l x] 传输的恒等变换（定义上平凡：[app] 是左严格的）。
*)
Lemma CFreeCat_strict_unit_left_to (x : list Colour) :
  to (@unit_left (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_l x in _ = T
      return ([] ++ x ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * The right unitor [x ++ [] ≅ x] is the transported identity along
   [app_nil_r x] (a genuinely propositional equation). 

   --------
   * 右单位元 [x ++ [] ≅ x] 是沿 [app_nil_r x]（一个真正的命题方程）传输的恒等式。
*)
Lemma CFreeCat_strict_unit_right_to (x : list Colour) :
  to (@unit_right (CFreeCat S) (CFreeCat_Monoidal S Cdec) x)
  ≈ match app_nil_r x in _ = T
      return (x ++ [] ~{ CFreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(*
   * ** The Strict instance over THE shared Monoidal record 

   --------
   * ** 在共享 Monoidal 记录上的严格实例
*)

Definition CFreeCat_Strict : @StrictMonoidal (CFreeCat S) := {|
  strict_is_monoidal    := CFreeCat_Monoidal S Cdec;  (* THE shared record / 共享记录 *)
  strict_assoc_obj      := fun x y z => eq_sym (app_assoc x y z);
  strict_unit_left_obj  := fun x => app_nil_l x;
  strict_unit_right_obj := fun x => app_nil_r x;
  strict_assoc_to       := fun x y z => CFreeCat_strict_assoc_to x y z;
  strict_unit_left_to   := fun x => CFreeCat_strict_unit_left_to x;
  strict_unit_right_to  := fun x => CFreeCat_strict_unit_right_to x
|}.

(*
   * ** The bundled instance

   All three structure fields name records that project to THE
   shared [CFreeCat_Monoidal S Cdec], so each equality field below
   is [eq_refl].  The record is an explicit [Build_ColouredPROP]
   application, so no inference is left to a record literal. 

   --------
   * ** 捆绑实例

   所有三个结构字段名称记录都投射到共享的 [CFreeCat_Monoidal S Cdec]，所以下面的每个相等字段都是 [eq_refl]。该记录是显式的 [Build_ColouredPROP] 应用，因此没有推断留给记录字面值。
*)

Definition FreeColouredPROP : ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (CFreeCat S)
    CFreeCat_Strict
    (CFreeCat_Symmetric S Cdec)

    (*
 [strict_is_monoidal CFreeCat_Strict] and
 [braided_is_monoidal (symmetric_is_braided
 (CFreeCat_Symmetric S Cdec))] both reduce to the literal
 term [CFreeCat_Monoidal S Cdec]. 

 --------
 [strict_is_monoidal CFreeCat_Strict] 和 [braided_is_monoidal (symmetric_is_braided (CFreeCat_Symmetric S Cdec))] 都化简为字面项 [CFreeCat_Monoidal S Cdec]。
*)
    eq_refl

    (*
 Objects of [CFreeCat S] are literally the colour words. 

 --------
 [CFreeCat S] 的对象字面上就是颜色词。
*)
    (fun cs : list Colour => cs)

    (*
 [I] of [CFreeCat_Monoidal S Cdec] is the literal [[]]. 

 --------
 [I] 的 [CFreeCat_Monoidal S Cdec] 是字面上的 [[] ]。
*)
    eq_refl

    (*
 [fobj (CFreeCat_Tensor S) (cs, ds)] reduces to [cs ++ ds]. 

 --------
 [fobj (CFreeCat_Tensor S) (cs, ds)] 缩减为 [cs ++ ds]。
*)
    (fun cs ds : list Colour => eq_refl).

(*
   * ** Side-condition instances for the interpretation files

   The hom-setoid equivalence of [CFreeCat S] is [CTermEq S] by
   delta/beta reduction of [CTerm_Setoid], and [CTermEq S] is
   already [Prop]-valued, so the [Prop] reflection is the identity
   in both directions. 

   --------
   * ** 解释文件的附加条件实例

   通过 [CTerm_Setoid] 的 delta/beta 规约，[CFreeCat S] 的同态集合等价于 [CTermEq S]，并且 [CTermEq S] 已经是 [Prop] 值的，因此 [Prop] 的反射在两个方向上都是恒等的。
*)

#[export] Instance CFreeCat_HomEqProp : HomEqProp (CFreeCat S) :=
  Build_HomEqProp (CFreeCat S)
    (fun cs ds : list Colour => @CTermEq Colour S cs ds)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(*
   * Objects of [CFreeCat S] are colour words, whose equality
   [list_eq_dec Cdec] decides.  A [Definition], not an [Instance]:
   it is [Cdec]-conditional (D2), and call sites pass it explicitly
   so that exactly one canonical decider circulates per colour
   type. 

   --------
   * [CFreeCat S] 的对象是颜色词，其相等性由 [list_eq_dec Cdec] 决定。一个 [Definition]，而不是 [Instance]：它是 [Cdec] 条件的（D2），调用点显式传递它，以便每种颜色类型正好流通一个规范的判定器。
*)

Definition CFreeCat_ObjDecEq : ObjDecEq (CFreeCat S) := list_eq_dec Cdec.

(*
   * ** Machine-checked sanity

   Each [Example] holds by a closed proof term — all but the last by
   [eq_refl], witnessing that the corresponding field of
   [FreeColouredPROP] is definitional; the final cons decomposition
   instead pins the recorded [cprop_tensor_app] conversion between
   the object correspondence and the shared strict [Monoidal]
   path. 

   --------
   * ** 机器检查的健全性

   每个 [Example] 都由闭合证明项保持 —— 除了最后一个，其他由 [eq_refl] 支持，证明相应的 [FreeColouredPROP] 字段是定义性的；最终的 cons 分解则固定了记录的 [cprop_tensor_app] 转换，连接对象对应关系和共享的严格 [Monoidal] 路径。
*)

(*
   * The coherence between the strict and symmetric [Monoidal] paths
   is the reflexivity proof itself — the "known limitation"
   discussed in [Construction/PROP.v] does not bite on the free
   coloured PROP. 

   --------
   * 严格且对称的 [Monoidal] 路径之间的一致性就是反身性证明本身——在 [Construction/PROP.v] 中讨论的“已知限制”并不会影响自由有色 PROP。
*)
Example FreeColouredPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour FreeColouredPROP = eq_refl := eq_refl.

(** The object correspondence is the identity on colour words. / 对象对应在颜色词上是恒等映射。 *)
Example FreeColouredPROP_of_list_id (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) cs = cs := eq_refl.

(*
   * The monoidal unit of THE shared record is the literal empty
   word. 

   --------
   * THE 共享记录的幺元是字面上的空词。
*)
Example FreeColouredPROP_I :
  @I (CFreeCat S) (CFreeCat_Monoidal S Cdec) = ([] : list Colour) := eq_refl.

(*
   * The same unit, projected through the bundled instance — pinning
   that the instance path and the shared record agree on the
   nose. 

   --------
   * 同一单元，通过捆绑实例投射 —— 固定实例路径和共享记录在鼻子上保持一致。
*)
Example FreeColouredPROP_I_instance :
  @I (CFreeCat S)
     (@strict_is_monoidal (CFreeCat S) (@cprop_strict Colour FreeColouredPROP))
  = ([] : list Colour) := eq_refl.

(*
   * Tensor-on-objects is literally concatenation, with [eq_refl]
   proof. 

   --------
   * 张量作用于对象字面上就是连接，并有 [eq_refl] 证明。
*)
Example FreeColouredPROP_tensor_app_is_refl (cs ds : list Colour) :
  cprop_tensor_app (ColouredPROP := FreeColouredPROP) cs ds = eq_refl
  := eq_refl.

(*
   * The singleton wire object for colour [c] is the literal
   one-element word [[c]]. 

   --------
   * 颜色 [c] 的单例线对象是字面上的单元素词 [[c] ]。
*)
Example FreeColouredPROP_wire (c : Colour) :
  wire (P := FreeColouredPROP) c = [c] := eq_refl.

(*
   * Cons decomposition smoke test: prepending a colour to a word is
   the tensor of its wire with the tail, THROUGH the shared strict
   [Monoidal] path.  The proof term is not bare [eq_refl] but
   [eq_sym (cprop_tensor_app [c] cs)]: it exercises the recorded
   tensor/concatenation conversion at the definitional boundary
   [[c] ++ cs = c :: cs], the coloured analogue of the one-sorted
   donor's [FreePROP_of_nat_S_smoke] (Construction/PROP/Instance.v),
   and would catch any regression in the shared-record wiring that
   the identity-shaped [Example]s above cannot see. 

   --------
   * Cons 分解烟雾测试：在一个单词前加上颜色，
   是它的导线与尾部的张量，通过共享的严格 [Monoidal] 路径。  
   证明项不是裸露的 [eq_refl]，而是 [eq_sym (cprop_tensor_app [c] cs）：它在定义边界 [[c] ++ cs = c :: cs 处测试了记录的张量/连接转换，
   是单排序捐赠者 [FreePROP_of_nat_S_smoke] (Construction/PROP/Instance.v) 的有色类比，
   并且能够捕捉共享记录连接中的任何回归，而上面的身份形状 [Example] 无法发现。
*)
Example FreeColouredPROP_cons_decomp (c : Colour) (cs : list Colour) :
  cprop_of_list (ColouredPROP := FreeColouredPROP) (c :: cs)
  = (wire (P := FreeColouredPROP) c
       ⨂[@strict_is_monoidal (CFreeCat S)
           (@cprop_strict Colour FreeColouredPROP)]
     cprop_of_list (ColouredPROP := FreeColouredPROP) cs)%object
  := eq_sym (cprop_tensor_app (ColouredPROP := FreeColouredPROP) [c] cs).

End FreeColouredPROP.

Arguments CFreeCat_Strict {Colour} S Cdec : assert.
Arguments FreeColouredPROP {Colour} S Cdec : assert.
Arguments CFreeCat_HomEqProp {Colour} S : assert.
(*
 [ObjDecEq] is a definitional (singleton) class, so the constant's
 argument list continues with the two objects being compared. 

 --------
 [ObjDecEq] 是一个定义性（单例）类，因此常量的参数列表继续包含正在比较的两个对象。
*)
Arguments CFreeCat_ObjDecEq {Colour} S Cdec x y : assert.
