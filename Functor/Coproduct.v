Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.

(** The fold (codiagonal) functor [Id, Id] : C ∐ C ⟶ C.  / 折叠（共对角）函子 [Id, Id] ： C ∐ C ⟶ C。*)

(*
nLab: https://ncatlab.org/nlab/show/codiagonal
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   This is the copairing of the identity functor with itself, the functor out
   of the coproduct category C ∐ C (defined in Construction/Coproduct.v) that
   collapses both summands back onto C. On objects it sends both inl x and
   inr x to x (sum_obj); on morphisms it is the identity on each summand's
   hom-set, the cross-summand homs being empty (False) and so eliminated by [!].
   It is the unique functor [Id, Id] : C ∐ C ⟶ C with [Id, Id] ∘ inl = Id and
   [Id, Id] ∘ inr = Id, furnished by the universal property of the coproduct in
   Cat (a functor C ∐ C ⟶ E is the same as a pair of functors C ⟶ E and
   C ⟶ E). It is the Cat-level analogue, and dual, of the binary diagonal
   Δ : C ⟶ C ∏ C of Functor/Diagonal.v.

   Note this is the codiagonal *functor* out of the coproduct *category*, which
   needs nothing of C; it should not be confused with the codiagonal *morphism*
   ∇ : x + x ~> x inside a cocartesian category (merge id id, the copairing
   id ▽ id of Structure/Cocartesian.v). Accordingly the [@Cocartesian C]
   hypothesis below is not used by the construction and is retained only to
   record the intended cocartesian setting; the functor is well defined for any
   category C. 

--------
nLab：https://ncatlab.org/nlab/show/codiagonal
 维基百科：https://en.wikipedia.org/wiki/Coproduct

这是恒等函子与其自身的配对，函子出
 联积类别 C ∐ C （在 Construction/Coproduct.v 中定义）
 将两个被加数折叠回 C。在对象上，它发送 inl x 和
 inr x 到 x (sum_obj); 对于态射，它是每个被加数的恒等式
 hom-set，交叉加数 homs 为空（False），因此被 [!] 消除。 
它是唯一函子 [Id, Id] : C ∐ C ⟶ C 且 [Id, Id] ∘ inl = Id 且
 [Id, Id] ∘ inr = Id，由余积的通用性质提供
 Cat（函子 C ∐ C ⟶ E 与一对函子 C ⟶ E 相同，并且
 C⟶E）。 它是二进制对角线的 Cat 级模拟和对偶
 Δ : Functor/Diagonal.v 的 C ⟶ C ∏ C。

请注意，这是余积*类别*中的余对角*函子*，其中
 不需要 C 的任何东西； 它不应该与余对角*态射*相混淆
 ∇ : x + x ~> x 在 cocartesian 类别内（合并 id id，copairing
 id ▽ Structure/Cocartesian.v 的 id）。 因此 [@Cocartesian C]
 下面的假设没有被构造所使用，仅被保留
 记录预期的笛卡尔设置； 函子对于任何都被明确定义
 C类。 
*)

Section Coproduct.

Context {C : Category}.
Context `{@Cocartesian C}.

(*
Object action: both inl x and inr x are sent to x. [const C] is the (non-
   dependent) motive of [sum_rect]; both branches are the identity on objects. 

--------
对象动作：inl x 和 inr x 都发送到 x。 [const C] 是（非
 [sum_rect] 的依赖）动机； 两个分支都是对象上的标识。 
*)
Definition sum_obj : C ∐ C → C :=
  sum_rect (const C) Datatypes.id Datatypes.id.

Section sum_map.

#[local] Set Transparent Obligations.

(*
Morphism action: identity on each summand's hom-set (the [_] branches solve
   x ~> y from f : x ~> y in C); the off-diagonal homs are False, so [!] derives
   the goal from the impossible hypothesis. 

--------
态射动作：每个被加数的 hom 集上的恒等式（[_] 分支解决
 x ~> y 来自 f : x ~> y in C); 非对角线 homs 为 False，因此 [!] 导出
 不可能的假设的目标。 
*)
Program Definition sum_map (a : C ∐ C) (b : C ∐ C) (f : a ~> b) :
  sum_obj a ~> sum_obj b :=
  match a, b with
  | Datatypes.inl x, Datatypes.inl y => _
  | Datatypes.inl _, Datatypes.inr _ => !
  | Datatypes.inr x, Datatypes.inl _ => !
  | Datatypes.inr x, Datatypes.inr y => _
  end.

End sum_map.

#[export]
Program Instance CoproductFunctor : C ∐ C ⟶ C := {
  fobj := sum_obj;    (* inl x, inr x ↦ x *)
  fmap := sum_map;    (* identity on each summand's morphisms  / 每个被加数的态射相同*)
}.
Next Obligation.
  proper; destruct x, y; simpl; tauto.
Qed.
Next Obligation.
  destruct x; simpl; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z; simpl; cat; tauto.
Qed.

End Coproduct.
