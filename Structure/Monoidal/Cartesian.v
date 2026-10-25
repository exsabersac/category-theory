Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 The forward relationship between products and tensors: every cartesian
 category -- a category with binary products ([Cartesian]) and a terminal
 object ([Terminal]) -- is monoidal, with the tensor given by the
 categorical product and the unit by the terminal object,

 x ⨂ y := x × y,        I := 1.

 This is the direction most users want, because it lets every theorem about
 general monoidal categories specialize to cartesian products for free.

 The construction itself, together with all of its coherence proofs (the
 associator and unitors built from [prod_assoc]/[prod_one_l]/[prod_one_r],
 the triangle and pentagon identities, and the symmetric / relevant /
 semicartesian tower stacked on top), lives in
 [Category.Structure.Monoidal.Internal.Product] as [CC_Monoidal] and the
 [CC_*] family.  That file is re-exported here so that the forward direction
 has a name where readers naturally look for it; [Cartesian_Monoidal] below
 is the headline result.  A concrete use is [Instance/Coq.v], where
 [Coq_Monoidal := @CC_Monoidal Coq Coq_Cartesian Coq_Terminal].

 The *reverse* direction -- that a relevant and semicartesian monoidal
 category is itself cartesian (Fox 1976 / Heunen-Vicary) -- is the
 [CartesianMonoidal] typeclass in
 [Category.Structure.Monoidal.Heunen_Vicary]. 

 --------
 nLab：https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 积与张量之间的正向关系：每个笛卡尔范畴——一个具有二元积（[Cartesian]）和终对象（[Terminal]）的范畴——都是单性的，其中张量由范畴积给出，单位由终对象给出，

 x ⨂ y := x × y,        I := 1。

 这是大多数用户希望的方向，因为它允许关于一般单范畴的每个定理免费地专门应用于笛卡尔积。构造本身，以及它的所有相干性证明（由 [prod_assoc] / [prod_one_l] / [prod_one_r] 构建的结合子和单位子，三角形和五边形恒等式，以及堆叠在上面的对称/相关/半笛卡尔塔），存在于 [Category.Structure.Monoidal.Internal.Product] 中，作为 [CC_Monoidal] 和 [CC_*] 家族。该文件在此被重新导出，以便正向方向有一个读者自然查找的名字；下面的 [Cartesian_Monoidal] 是主要结果。一个具体的应用是 [Instance/Coq.v]，其中 [Coq_Monoidal := @CC_Monoidal Coq Coq_Cartesian Coq_Terminal]。

 *逆向*方向——一个相关和半笛卡尔单元范畴本身是笛卡尔的（Fox 1976 / Heunen-Vicary）——是 [Category.Structure.Monoidal.Heunen_Vicary] 中的 [CartesianMonoidal] 类型类。
*)

Section CartesianIsMonoidal.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(*
 The cartesian monoidal structure: tensor := ×, unit := 1.  This is a plain
 [Definition] rather than an [Instance] (mirroring [CC_Monoidal]): making it
 an instance would let typeclass resolution silently pick the product as
 *the* monoidal structure on every cartesian category, conflicting with
 hand-rolled monoidal structures elsewhere.  Callers select it explicitly. 

 --------
 笛卡尔幺半群结构：tensor := ×，unit := 1。这是一个普通的 [Definition]，而不是 [Instance]（对应 [CC_Monoidal]）：将其设为实例会让类型类解析在每个笛卡尔范畴中自动选择积作为*唯一*的幺半群结构，从而与其他地方手工定义的幺半群结构冲突。调用者需要显式选择它。
*)
Definition Cartesian_Monoidal : @Monoidal C := CC_Monoidal.

End CartesianIsMonoidal.
