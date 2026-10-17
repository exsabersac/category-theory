Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.

Generalizable All Variables.

(* * * Complete cocomplete 范畴 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Complete_category

   Wikipedia：「范畴 C 完备，若每个图 F : J → C（J 小）在 C 中有极限。」对偶地，C 余完备
   若每个此类图有余极限。nLab：范畴「有全部小极限」当「每个小图 F : D → C（D 小范畴）
   在 C 中有极限。」库记号中完备性条件读作：

       ∀ (D : Category) (F : D ⟶ C), Limit F,

   即对 C 中每个形状为 D 的图 F 有 [Limit]（终/普遍锥，见 [Structure/Limit.v]）。余完备性
   是精确对偶，要求每个图有 [Colimit]；因 [Colimit F := Limit (F^op)]，C 余完备当且仅当
   C^op 完备，匹配两来源记录的对偶。

   关于指标类：两来源都把 J（此处 D）限制为*小*。Wikipedia 指出要求*所有*（真类大小）图的
   极限「过强，无实际意义」——此类 C 将被强制为薄。下文定义量化 [∀ (D : Category)]
   而无显式小性假设；大小纪律改由库的宇宙多态隐式携带。实例化 [Complete]/[Cocomplete] 时，
   D 的宇宙层级相对 C 受约束，即「D 相对 C 小」的宇宙多态替身。故这些陈述「对每个（适当小的）
   图有极限」而非不一致的全图读法。态射层相等是 C 的 setoid [≈]，在 [Limit]/[Cone] 内供给；
   此处不出现。

   （文首大小注记若仍长篇英文，属细节后续；本定义块已译。） *)

(*
   nLab:  https://ncatlab.org/nlab/show/complete+small+category
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Paper: Hyland, "A small complete category", Annals of Pure and Applied

   本节说明（余）极限、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* C is complete: every diagram F : D ⟶ C has a limit (terminal cone) in C. *)
Definition Complete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Limit@{r so h o} F.

(* 相关说明。 （已译） *)
Definition Cocomplete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Colimit@{r so h o} F.
