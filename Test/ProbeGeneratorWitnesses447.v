Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Grp.Generator.
Require Import Category.Instance.Ab.Generator.

Generalizable All Variables.

(**
* Probe for the #447 witnesses: Instance/Sets/Generator.v,
      Instance/Grp/Generator.v, Instance/Ab/Generator.v

    Mac Lane §V.7 Definition 4 (p. 127), Awodey §7.2 (p. 154).  The
    general theory has its own probe, Test/ProbeGenerator447.v.

    The import list above is the UNION of the three witness files' own
    import lists, unabbreviated, in the order the Sets file uses (Theory/
    Concrete after Instance/Sets, so that the two [bool_setoid_object]s
    shadow the way they do there; no bare occurrence of that name appears
    below).

    Every negative below has been STRIPPED of its refutation keyword in a
    copy of this WHOLE file and its complete error read; all five are
    CONVERSION refusals ("cannot unify A and B").  The instrument check
    comes first, and every library constant a negative names has a
    positive control outside any refutation command.  "The empty setoid
    is not a separator" is NOT here: it is a theorem about a well-typed
    statement with no inhabitant, delivered as
    [Sets_empty_not_separates], and a refusal probe cannot express it.

--------
* 探测 #447 见证者：Instance/Sets/Generator.v, Instance/Grp/Generator.v, Instance/Ab/Generator.v

Mac Lane §V.7 定义 4 (第 127 页), Awodey §7.2 (第 154 页)。一般理论有其自己的探针，Test/ProbeGenerator447.v。

上面的导入列表是三个证人文件自身导入列表的并集，完整列出，按 Sets 文件使用的顺序（实例/Sets 之后是理论/具体），这样两个 [bool_setoid_object] 就会像在那里一样产生遮蔽；在下面不会出现该名称的单独出现。

下面的每一个否定都在这个整个文件的副本中被剥除了反驳关键词，并且其完整错误已被读取；所有五个都是转换拒绝（“无法统一 A 和 B”）。仪器检查先行，而每个库常量对应的否定在任何反驳命令之外都有一个正控制。“空集合体不是分离器”不在这里：它是关于一个没有元素的良类型语句的定理，以 [Sets_empty_not_separates] 提供，并且拒绝探针无法表达它。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check generator_witness_447_no_such_constant.

(** ** Positive controls / ** 阳性对照 *)

Check @IsSeparator.
Check @Generator.
Check @gen_index.
Check @gen_obj.
Check @Generator_of_separator.
Check @separator_iso.
Check @IsSeparator_of_Separator.
Check @Sets_Separator.
Check @Sets_unit_separates.
Check @Sets_terminal_separates.
Check @Sets_terminal_separates_by_transport.
Check @Sets_terminal_separates_from_Concrete.
Check @Sets_Generator.
Check @Sets_terminal_Generator.
Check @Sets_terminal_unit_iso.
Check @Sets_empty_not_separates.
Check @Sets_empty_not_separates_pick.
Check @Grp_free_one_separates.
Check @Grp_Generator.
Check @Ab_free_one_separates.
Check @Ab_Generator.
Check @FreeGrpObject.
Check @FreeAbObject.
Check @ab_int.
Check @unit_setoid_object.
Check @Unit_Setoid.
Check @Sets_Terminal.
Check @Sets_Initial.
Check @terminal_obj.

(** ** Readbacks that HOLD / ** 保持的回读 *)

(*
The Generator packages are the expected one-object families, on the
   nose.

--------
生成器包是预期的一对象族，正中要害。
*)
Example p447w_g1 : gen_index Sets_Generator = unit := eq_refl.
Example p447w_g2 : gen_obj Sets_Generator tt = unit_setoid_object := eq_refl.
Example p447w_g3 :
  gen_obj Sets_terminal_Generator tt = @terminal_obj Sets Sets_Terminal
  := eq_refl.

(*
The terminal object's setoid field IS Instance/Sets.v's [Unit_Setoid];
   the singleton's is Lib/Setoid.v's [unit_setoid] -- which is why N1
   below is refused.

--------
终端对象的 setoid 字段是 Instance/Sets.v 的 [Unit_Setoid]；单例的是 Lib/Setoid.v 的 [unit_setoid] —— 这就是为什么下面的 N1 被拒绝的原因。
*)
Example p447w_t1 : @terminal_obj Sets Sets_Terminal
  = {| carrier := poly_unit ; is_setoid := Unit_Setoid |} := eq_refl.

(* The initial object's carrier is [False], on the nose. / 初始对象的承载者是 [False]，就在正面。 *)
Example p447w_empty : carrier (@terminal_obj (Sets^op) Sets_Initial) = False
  := eq_refl.

(*
Control for N4: the free abelian group on one generator IS what the
   theorem is about.

--------
N4 的控制：一个生成元上的自由阿贝尔群就是定理所讨论的内容。
*)
Definition p447w_ab : @IsSeparator Ab (FreeAbObject unit_setoid_object) :=
  Ab_free_one_separates.

(** ** Negatives / ** 负面 *)

(*
N1 -- CONVERSION.  The singleton is not the terminal object on the
   nose: "cannot unify "1" and "unit_setoid_object"" (the [1] being the
   terminal-object notation this import list puts in scope).

--------
N1 -- 转换。单例并不是端对象本身：“无法统一‘1’和‘unit_setoid_object’”（[1] 是此导入列表中范围内的端对象符号表示）。
*)
Fail Example n1 : @terminal_obj Sets Sets_Terminal = unit_setoid_object
  := eq_refl.

(*
N2 -- CONVERSION.  Separation is at ≈, not at Leibniz =:
   "cannot unify "f ∘ k = g ∘ k" and "f ∘ k ≈ g ∘ k"".

--------
N2 -- 转换。分离在 ≈，而不是在莱布尼茨 =：
   “无法统一‘f ∘ k = g ∘ k’和‘f ∘ k ≈ g ∘ k’”。
*)
Fail Definition n2 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : unit_setoid_object ~{Sets}~> X, f ∘ k = g ∘ k) -> f = g
  := Sets_unit_separates.

(*
N3 -- CONVERSION.  The two composites swapped -- the COseparator's
   postcomposition in place of the separator's precomposition:
   "cannot unify "unit_setoid_object ~{ Sets }~> x" and
   "y ~{ Sets }~> unit_setoid_object"".  This is the quantifier exchange
   that Structure/Generator/Dual.v's bridge performs.

--------
N3 -- 转换。两个复合互换 -- CO分离器的后组合代替了分离器的前组合："无法统一 'unit_setoid_object ~{ Sets }~> x' 和 'y ~{ Sets }~> unit_setoid_object'"。这是 Structure/Generator/Dual.v 的桥执行的量词交换。
*)
Fail Definition n3 :
  forall (X Y : SetoidObject) (f g : X ~{Sets}~> Y),
    (forall k : Y ~{Sets}~> unit_setoid_object, k ∘ f ≈ k ∘ g) -> f ≈ g
  := Sets_unit_separates.

(*
N4 -- CONVERSION.  Mac Lane's ℤ is not, in tree, the free abelian
   group on one generator: "cannot unify
   "FreeAbObject unit_setoid_object ~{ Ab }~> x" and "ab_int ~{ Ab }~> x"".
   The isomorphism between them is not in tree (see the Ab header).

--------
N4 -- 转换。Mac Lane 的 ℤ 在树中不是单生成元的自由阿贝尔群：“无法统一‘FreeAbObject unit_setoid_object ~{ Ab }~> x’ 和 ‘ab_int ~{ Ab }~> x’”。它们之间的同构不在树中（见 Ab 头文件）。
*)
Fail Definition n4 : @IsSeparator Ab ab_int := Ab_free_one_separates.

(*
N5 -- CONVERSION.  The singleton proof does not prove the
   terminal-object statement: "cannot unify
   "unit_setoid_object ~{ Sets }~> x" and "1 ~{ Sets }~> x"" -- N1 lifted
   from the objects to the theorems, and the reason
   [Sets_terminal_separates] is a separate constant.

--------
N5 -- 转换。单例证明并没有证明终对象陈述：“无法统一‘unit_setoid_object ~{ Sets }~> x’ 和 ‘1 ~{ Sets }~> x’” -- N1 从对象提升到定理，并且原因是 [Sets_terminal_separates] 是一个独立常量。
*)
Fail Definition n5 : @IsSeparator Sets (@terminal_obj Sets Sets_Terminal)
  := Sets_unit_separates.
