Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Monad.Graded.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.

Generalizable All Variables.

(**
* Rig connections: AndGrade, and the FinSet shadow

    The two reconciliations Theory/Algebra/Rig.v's header promises, kept
    in a companion file so the algebra spine does not import the graded
    monad machinery or the skeletal finite sets.

    ANDGRADE.  Monad/Graded.v's [AndGrade] is the grading monoid
    (bool, true, andb) of the exception-graded monad.  It is literally
    the multiplicative half of [Bool_Rig] — same carrier, same unit, same
    operation, on the nose — so the two developments cannot drift.

    THE FINSET SHADOW (Example 5.37, categorified).  On the skeletal
    [FinSet] the objects are literally the naturals, the coproduct object
    of m and n is [m + n] and the product object is [m * n]
    (Instance/FinSet.v's [FinSet_Cocartesian],
    Instance/FinSet/Product.v's [FinSet_Cartesian]).  The rig operations
    of [Nat_Rig] therefore agree definitionally with the object actions
    of the (co)cartesian structure: the rig of naturals is the
    decategorified shadow of finite sets under disjoint union and
    cartesian product — the direction of agreement the issue asks to
    record.  (The converse packaging — that the BiCCC isomorphisms of
    Structure/BiCCC.v descend to the equations of [Nat_Rig] along
    skeletality — is the deeper statement and remains outside this
    file's scope.)

--------
* 绑定连接：AndGrade，以及 FinSet 阴影

两个调和理论/代数/Rig.v 的头文件承诺被保存在一个伴随文件中，这样代数骨干就不会导入分级单子机制或骨架有限集。

ANDGRADE。Monad/Graded.v 的 [AndGrade] 是异常分级单子（exception-graded monad）的分级幺半群 (bool, true, andb)。它实际上是 [Bool_Rig] 的乘法部分——相同的载体、相同的单位、相同的运算——完全一致，因此这两个开发不能偏离。

有限集的影子（例 5.37，范畴化）。在骨架 [FinSet] 上，对象实际上是自然数，m 和 n 的余积对象是 [m + n]，积对象是 [m * n]（Instance/FinSet.v 的 [FinSet_Cocartesian]，Instance/FinSet/Product.v 的 [FinSet_Cartesian]）。因此，[Nat_Rig] 的环操作在定义上与（余）笛卡尔结构的对象作用一致：自然数环是有限集在不相交并集和笛卡尔积下的去范畴化影子——这是问题要求记录的一致方向。（相反的包装——Structure/BiCCC.v 的 BiCCC 同构沿骨架性下降到 [Nat_Rig] 的方程——是更深的陈述，仍在此文件范围之外。）
*)

(** ** AndGrade is the multiplicative half of Bool_Rig / ** AndGrade 是 Bool_Rig 的乘法部分的一半 *)

Example Bool_Rig_carrier_AndGrade : carrier (rig_setoid Bool_Rig) = grade AndGrade
  := eq_refl.
Example Bool_Rig_one_AndGrade : rig_one Bool_Rig = gunit AndGrade := eq_refl.
Example Bool_Rig_mul_AndGrade : rig_mul Bool_Rig = gmul AndGrade := eq_refl.

(** ** Nat_Rig is the object-level shadow of FinSet / ** Nat_Rig 是 FinSet 的对象级影子 *)

(* The coproduct object of FinSet is rig addition, on the nose. / FinSet 的余积对象严格对应于半环加法。 *)
Example Nat_Rig_add_FinSet_coproduct (m n : nat) :
  @product_obj _ FinSet_Cocartesian m n = rig_add Nat_Rig m n := eq_refl.

(* The product object of FinSet is rig multiplication, on the nose. / FinSet 的积对象是严格乘法，恰如其分。 *)
Example Nat_Rig_mul_FinSet_product (m n : nat) :
  @product_obj _ FinSet_Cartesian m n = rig_mul Nat_Rig m n := eq_refl.

(* The empty and singleton finite sets are the rig units. / 空集合和单元素有限集是环单位元。 *)
Example Nat_Rig_zero_FinSet : rig_zero Nat_Rig = 0%nat := eq_refl.
Example Nat_Rig_one_FinSet : rig_one Nat_Rig = 1%nat := eq_refl.

(**
** An independent witness for the converse bridge direction

    [EndRig] applied to a preadditive category the Rig development did
    not itself build: Instance/CMon/Biproduct.v's [CMon_Preadditive].
    Every commutative monoid M thus yields the rig of its monoid
    endomorphisms — addition pointwise, multiplication composition —
    inhabiting the converse direction of the bridge away from the
    delooping it would otherwise be tested on.

--------
** 逆向桥接方向的独立证人

[EndRig] 应用于预加范畴，而 Rig 开发本身并未构建它：Instance/CMon/Biproduct.v 中的 [CMon_Preadditive]。因此，每个交换幺半群 M 都会产生其幺半群同态的 rig——加法按点定义，乘法为复合——存在于远离其本应被测试的 delooping 的桥接逆方向上。
*)
Definition CMon_EndRig (M : CMonObject) : RigObject :=
  EndRig CMon_Preadditive M.
