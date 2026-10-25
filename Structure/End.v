Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Wedge.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Ends and coends / * 端和余端 *)

(*
 The END of a functor of mixed variance `F : C^op ∏ C ⟶ D`, written
 `∫_c F(c,c)`, is the UNIVERSAL (terminal) WEDGE: a wedge `(e, ω)` with apex
 `e : D` and legs `ω_x : e ~> F (x, x)` through which every other wedge
 factors uniquely. It is the dinatural analogue of a limit, and packages a
 family of legs constrained by the wedge (extranaturality) condition of
 Structure/Wedge.

 nLab:      https://ncatlab.org/nlab/show/end
 Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

 Universal property (the end UMP), in this library's notation: for every
 wedge `W` (apex `wedge_obj[W]`, legs `wedge_map[W]`) there is a unique
 mediating morphism `u : W ~> e` (i.e. `wedge_obj[W] ~{D}~> e`) commuting with
 the legs,

 ∃! u : W ~> e, ∀ x : C, wedge_map[end_wedge] ∘ u ≈ wedge_map[W]

 so `u` runs from the arbitrary wedge's apex *to* the end (terminal direction)
 and recovers each leg of `W` by post-composition with the end's leg. This is
 the standard statement `β_x = ω_x ∘ u` (Wikipedia's `h : x → e`).

 The dual is the COEND `∫^c F(c,c)`, the universal (initial) cowedge; it is
 defined below by taking the end in the opposite categories. 

 --------
 混合变异函子的 END `F : C^op ∏ C ⟶ D`，记作 `∫_c F(c,c)`，是普遍（终端）楔子：一个 apex 为 `e : D`、腿为 `ω_x : e ~> F (x, x)` 的楔子 `(e, ω)`，通过它每个其他楔子都可以唯一地分解。它是极限的双自然（dinatural）类似物，并打包了一族由 Structure/Wedge 的楔子（额外自然性）条件约束的腿。

 nLab: https://ncatlab.org/nlab/show/end
 Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

 普遍性性质（end 的 UMP），在本库的符号表示中：对于每个楔子 `W`（顶点 `wedge_obj [W]ZZ `，腿 `wedge_map [W]ZZ `），存在唯一的中介态射 `u : W ~> e`（即 `wedge_obj [W]ZZ  ~{D}~> e`），与腿交换，

 ∃! u : W ~> e, ∀ x : C, wedge_map [end_wedge] ∘ u ≈ wedge_map [W]所以 `u` 从任意楔形的顶点*到*终点（终端方向）运行，并通过与终点的腿后组合恢复 `W` 的每一条腿。这是标准的表述 `β_x = ω_x ∘ u`（维基百科的 `h : x → e`）。

 对偶是 COEND `∫^c F(c,c)`，即泛（初始）余楔；它在下面通过在相反范畴中取终点来定义。
*)
Class End `(F : C^op ∏ C ⟶ D) := {
  end_wedge : Wedge F;                     (* the universal wedge `(e, ω)` / 通用楔形 `(e, ω)` *)

  (* the end UMP: every wedge `W` factors uniquely through `end_wedge`, with `u : W ~> end_wedge` mediating in `D` and `ω_x ∘ u ≈ wedge_map[W]` / 终结 UMP：每个楔形 `W` 都能唯一地通过 `end_wedge` 分解，其中 `u : W ~> end_wedge` 在 `D` 和 `ω_x ∘ u ≈ wedge_map [W]ZZ ` 中起中介作用 *)
  ump_ends : ∀ W : Wedge F, ∃! u : W ~> end_wedge, ∀ x : C,
    wedge_map[end_wedge] ∘ u ≈ @wedge_map _ _ _ W x
}.

Arguments End {_%_category _%_category} F%_functor.
Arguments end_wedge {_%_category _%_category} F%_functor {_}.

(*
 An end of `F` may be used directly as its apex object of `D` (and hence,
 transitively through `Wedge`'s own coercion, as that wedge). 

 --------
 `F` 的一个端可以直接用作 `D` 的顶点对象（因此，通过 `Wedge` 自身的强制转换，间接作为那个楔形）。
*)
Coercion wedge_obj `(F : C^op ∏ C ⟶ D) (E : End F) := @end_wedge _ _ _ E.

Require Import Category.Functor.Opposite.

(*
 The COEND `∫^c F(c,c)` is the universal (initial) cowedge, dual to the end.
 As with `Cowedge` in Structure/Wedge, it is obtained as an end in the
 opposite categories: a coend for `F` is literally an end for
 `F^op : (C^op)^op ∏ C^op ⟶ D^op`, so its legs `F (x, x) ~{D}~> d` are the
 reversed wedge legs and the UMP runs `d ~> x` out of the coend. 

 --------
 COEND `∫^c F(c,c)` 是普遍（初始）余楔，与端对象相对。正如在 Structure/Wedge 中的 `Cowedge` 一样，它是在对偶范畴中作为端对象获得的：`F` 的余端字面上是 `F^op : (C^op)^op ∏ C^op ⟶ D^op` 的端对象，因此它的腿 `F (x, x) ~{D}~> d` 是反向楔腿，而 UMP `d ~> x` 从余端运行出来。
*)
Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).
