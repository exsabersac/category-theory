Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(**
* Probe for the term-valued properness fields of [Sets] (issue #1347)

    Instance/Sets.v gives [setoid_morphism_id] and
    [setoid_morphism_compose] their [proper_morphism] fields as terms.
    Before #1347 instance resolution filled them, through the standard
    library's [subrelation_id_proper], [subrelation_refl],
    [Reflexive_partial_app_morphism], [proper_proper_proxy] and
    [CMorphisms.compose_proper_obligation_1], every one opaque (by
    [Print Opaque Dependencies] on the two constants), and in [Sets] the
    composite of a morphism with the identity did not convert with the
    morphism.  This file pins the new strength: both unit laws and
    associativity hold at [eq_refl], of the two constants and of the
    category [Sets] built from them.  It pins one consequence downstream
    as well (C9): the unit of Instance/Mod/Free.v's free-module adjunction
    is the basis insertion as a whole setoid morphism, at [eq_refl].

    THE IMPORT LIST is Instance/Sets.v's own [Require] lines, in order,
    and that target.  C9's section, after every other command, adds the
    nine of Instance/Mod/Free.v's fourteen [Require] lines that the list
    above lacks, in that file's order, and that target.

    DISCIPLINE.  The one negative is an [Example], never a [Check].  It is
    the instrument: it compares the identity with an arbitrary endomorphism
    of the same setoid, which no strength of the fields can make
    convertible, and it is refused with a "cannot unify" parenthetical.
    Each control, wrapped in the refutation keyword in a copy of this
    WHOLE file, stops the build at that command with the report that the
    command was accepted: nine of nine, the File line of the error
    compared with the command's extent.  Stripped in such a
    copy, the instrument stops inside its command:
      (cannot unify "setoid_morphism_id" and "f")
    Against the tree before #1347 (master 687ac356), in copies of this
    WHOLE file with the other controls wrapped, each control is
    refused inside its command with "cannot unify", so every one of them
    pins a strength that the fields as terms deliver.

    KINDS.  The instrument is CONVERSION.  Its cause is STRUCTURAL: the two
    sides are an identity and a variable.

    LABELS.  C1 [p1347_c1_id_right], C2 [p1347_c2_id_left], C3
    [p1347_c3_assoc], C4 [p1347_c4_sets_id_right], C5
    [p1347_c5_sets_id_left], C6 [p1347_c6_sets_assoc], C7
    [p1347_c7_id_field], C8 [p1347_c8_compose_field] and C9
    [p1347_c9_free_module_unit]; "the instrument" is [p1347_instrument].

--------
* 探测 [Sets] 的值类型规范字段（问题 #1347）

Instance/Sets.v 给 [setoid_morphism_id] 和 [setoid_morphism_compose] 他们的 [proper_morphism] 字段作为项。在 #1347 之前，通过标准库的 [subrelation_id_proper]、[subrelation_refl]、[Reflexive_partial_app_morphism]、[proper_proper_proxy] 和 [CMorphisms.compose_proper_obligation_1]，每一个都是不透明的（通过 [Print Opaque Dependencies] 对这两个常量），并且在 [Sets] 中，一个与恒等映射的同态复合没有随同态转换。这个文件固定了新的强度：在 [eq_refl] 上，两个常量及由它们构建的类别 [Sets] 的单位律和结合律都成立。它也固定了一个下游的结果（C9）：Instance/Mod/Free.v 的自由模伴随的单位是作为整个集体态射的基插入，在 [eq_refl] 上。

IMPORT 列表是 Instance/Sets.v 自身的 [Require] 行，按顺序排列，并指定目标。C9 的部分在每个其他命令之后，添加 Instance/Mod/Free.v 的十四行 [Require] 中该列表缺少的九行，按该文件中的顺序，并指定目标。

纪律。唯一的负面是 [Example]，从不是 [Check]。它是工具：它将恒等映射与同一个集合的任意自同态进行比较，而无论场的强度如何都无法使其可转换，并且会以“无法统一”的括号形式被拒绝。每个控制，在此整个文件的副本中用否定关键字包裹，会在该命令处停止构建，并报告该命令已被接受：九个中的九个，错误的文件行与命令的范围进行了比较。在这样的副本中被剥离后，该工具会在其命令内部停止：
  （无法统一“setoid_morphism_id”和“f”）
针对 #1347（master 687ac356）之前的树，在用其他控制包裹的此整个文件的副本中，每个控制在其命令内部都被“无法统一”拒绝，因此每一个都固定了作为项的场所提供的强度。

种类。该工具是转换。其原因是结构性的：两边是恒等式和变量。

标签。C1 [p1347_c1_id_right]，C2 [p1347_c2_id_left]，C3 [p1347_c3_assoc]，C4 [p1347_c4_sets_id_right]，C5 [p1347_c5_sets_id_left]，C6 [p1347_c6_sets_assoc]，C7 [p1347_c7_id_field]，C8 [p1347_c8_compose_field] 和 C9 [p1347_c9_free_module_unit]；“仪器”是 [p1347_instrument]。
*)

(** ** The two constants / ** 两个常数 *)

(* C1 *)
Example p1347_c1_id_right@{o h p} (x y : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x y) :
  setoid_morphism_compose@{o h p} f (@setoid_morphism_id@{o h p} x) = f
  := eq_refl.

(* C2 *)
Example p1347_c2_id_left@{o h p} (x y : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x y) :
  setoid_morphism_compose@{o h p} (@setoid_morphism_id@{o h p} y) f = f
  := eq_refl.

(* C3 *)
Example p1347_c3_assoc@{o h p} (w x y z : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} w x) (g : SetoidMorphism@{o h p} x y)
  (h : SetoidMorphism@{o h p} y z) :
  setoid_morphism_compose@{o h p} h (setoid_morphism_compose@{o h p} g f)
    = setoid_morphism_compose@{o h p} (setoid_morphism_compose@{o h p} h g) f
  := eq_refl.

(** ** The category [Sets] / ** 类别 [Sets] *)

(* C4 *)
Example p1347_c4_sets_id_right@{o so} (x y : Sets@{o so})
  (f : x ~{Sets@{o so}}~> y) : f ∘[Sets@{o so}] id = f := eq_refl.

(* C5 *)
Example p1347_c5_sets_id_left@{o so} (x y : Sets@{o so})
  (f : x ~{Sets@{o so}}~> y) : id ∘[Sets@{o so}] f = f := eq_refl.

(* C6 *)
Example p1347_c6_sets_assoc@{o so} (w x y z : Sets@{o so})
  (f : w ~{Sets@{o so}}~> x) (g : x ~{Sets@{o so}}~> y)
  (h : y ~{Sets@{o so}}~> z) :
  h ∘[Sets@{o so}] (g ∘[Sets@{o so}] f)
    = (h ∘[Sets@{o so}] g) ∘[Sets@{o so}] f := eq_refl.

(** ** The fields themselves / ** 田地本身 *)

(* C7 *)
Example p1347_c7_id_field@{o h p} (x : SetoidObject@{o p}) (a b : x)
  (H : a ≈ b) :
  proper_morphism (@setoid_morphism_id@{o h p} x) a b H = H := eq_refl.

(* C8 *)
Example p1347_c8_compose_field@{o h p} (x y z : SetoidObject@{o p})
  (g : SetoidMorphism@{o h p} y z) (f : SetoidMorphism@{o h p} x y)
  (a b : x) (H : a ≈ b) :
  proper_morphism (setoid_morphism_compose@{o h p} g f) a b H
    = proper_morphism g _ _ (proper_morphism f a b H) := eq_refl.

(** ** The instrument / ** 乐器 *)

(* The instrument / 乐器 *)
Fail Example p1347_instrument@{o h p} (x : SetoidObject@{o p})
  (f : SetoidMorphism@{o h p} x x) :
  @setoid_morphism_id@{o h p} x = f := eq_refl.

(** ** Guard *)

Check Category.Instance.Sets.setoid_morphism_id.
Check Category.Instance.Sets.setoid_morphism_compose.

(* ------------------------------------------------------------------------ *)
(** ** Downstream: the free module's unit / ** 下游：自由模块的单元 *)

(*
Loaded here, after every other command, so that the modules below
   change the environment of this control alone.  They are the nine of
   Instance/Mod/Free.v's fourteen [Require] lines that the list above
   does not already load, in that file's order, and that target.

--------
在这里加载，位于每个其他命令之后，以便下面的模块仅更改此控件的环境。它们是 Instance/Mod/Free.v 中十四个 [Require] 行中的九个，上述列表尚未加载的，按该文件的顺序，并且目标是该控件。
*)
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Mod.Free.

(*
C9: the unit of the free-module adjunction IS the basis insertion, as
   a whole setoid morphism.  Instance/Mod/Free.v states it pointwise
   ([free_module_unit_is_insert]); the unit is the composite of
   [fmap[RMod_Forget R] id] with [fv_insert X], by that file's comment,
   and the whole equation is refused against the tree before #1347
   (measured as for C1 to C8, above).

--------
C9：自由模伴随的单位是基的插入，作为一个整体的集合等价映射。Instance/Mod/Free.v 在点上给出了它（[free_module_unit_is_insert]）；根据该文件的注释，单位是 [fmap[RMod_Forget R] id] 与 [fv_insert X] 的复合，并且整个方程在 #1347 之前的树上被拒绝（如上文 C1 到 C8 的测量方法）。
*)
Example p1347_c9_free_module_unit (R : RingObject) (X : Sets) :
  free_module_unit R X = fv_insert X := eq_refl.
