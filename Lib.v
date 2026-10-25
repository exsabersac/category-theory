(**
* Project-wide settings and core library re-exports.

   Establishes the global flags every file in the development inherits
   (primitive projections, universe polymorphism, uniform inductive
   parameters, the "!" single-goal selector, [Default Proof Using "Type"],
   opaque [Program] obligations, etc.) and re-exports the foundational
   datatypes.  Importing this module is what puts a file under the
   library's universe-polymorphic, setoid-based regime.

--------
* 项目范围的设置和核心库重导出。

建立开发中每个文件继承的全局标志（原始投影、宇宙多态、统一归纳参数、“！”单目标选择器、[Default Proof Using "Type"]、不透明 [Program] 义务等）并重导出基础数据类型。导入此模块即可将文件置于库的宇宙多态、基于集合论的体系下。
*)

#[export] Set Primitive Projections.
#[export] Set Universe Polymorphism.
#[export] Set Uniform Inductive Parameters.
#[export] Set Default Proof Using "Type".
#[export] Set Default Goal Selector "!".
#[export] Unset Transparent Obligations.
#[export] Unset Intuition Negation Unfolding.
#[export] Unset Universe Minimization ToSet.

Require Export Category.Lib.Datatypes.
