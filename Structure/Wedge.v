Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Wedges, ends and coends / * 楔子、极限与余极 *)

(*
 A wedge to a functor of mixed variance `F : C^op ∏ C ⟶ D` is the dinatural
 analogue of a cone: an apex `w : D` together with a family of legs
 `wedge_map_x : w ~> F (x, x)`, one per object `x : C`, landing on the
 diagonal. In place of a naturality square the legs satisfy the wedge
 (extranaturality / dinaturality) condition. A wedge is exactly a dinatural
 transformation from the constant functor `Δw` to `F` (see Theory/Dinatural),
 for which the source legs collapse to `id`.

 nLab:      https://ncatlab.org/nlab/show/end#wedges
 Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

 The wedge condition, for `f : x ~> y`, with both sides `w ~> F (x, y)`
 (in this library's variance-explicit notation):

 bimap[F] id f ∘ wedge_map[x] ≈ bimap[F] (op f) id ∘ wedge_map[y]

 Here `bimap[F] id f` is the covariant action `F(1,f)` on the second
 argument and `bimap[F] (op f) id` is the contravariant action `F(f,1)` on
 the first; the condition forces the two routes `w ~> F (x, x) ~> F (x, y)`
 and `w ~> F (y, y) ~> F (x, y)` to agree. This corresponds to the standard
 statement `F(1,f) ∘ ω_x ≈ F(f,1) ∘ ω_y`.

 This file supplies only the wedge *data*. The universal (terminal) wedge is
 the END of `F`, defined in Structure/End; dually the universal (initial)
 cowedge is the COEND. 

 --------
 混变函子 `F : C^op ∏ C ⟶ D` 的楔子是圆锥的共自然类比：一个顶点 `w : D` 以及一族腿 `wedge_map_x : w ~> F (x, x)`，每个对象 `x : C` 各有一条，落在对角线上。腿满足楔子（外自然性/共自然性）条件，而不是自然性方格。楔子正好是从常函子 `Δw` 到 `F` 的共自然变换（参见 Theory/Dinatural），其源腿坍塌为 `id`。

 nLab: https://ncatlab.org/nlab/show/end#wedges 
 维基百科: https://en.wikipedia.org/wiki/End_(category_theory) 

 对于 `f : x ~> y` 的楔子条件，两边均为 `w ~> F (x, y)` （在此库的方差显式符号表示法中）：

 bimap [F] id f ∘ wedge_map [x] ≈ bimap [F] (op f) id ∘ wedge_map [y]这里 `bimap [F]ZZ  id f` 是作用在第二个参数上的协变作用 `F(1,f)`，`bimap [F]ZZ  (op f) id` 是作用在第一个参数上的逆变作用 `F(f,1)`；该条件强制两个路径 `w ~> F (x, x) ~> F (x, y)` 和 `w ~> F (y, y) ~> F (x, y)` 一致。这对应于标准陈述 `F(1,f) ∘ ω_x ≈ F(f,1) ∘ ω_y`。

 此文件仅提供楔形*数据*。普遍（末端）楔形是 `F` 的 END，在 Structure/End 中定义；对偶地，普遍（初始）余楔形是 COEND。
*)
Class Wedge `(F : C^op ∏ C ⟶ D) := {
  wedge_obj : D;                          (* the apex `w` of the wedge / 楔形的顶点 `w` *)

  wedge_map {x : C} : wedge_obj ~{D}~> F (x, x);   (* leg `w ~> F (x, x)` *)

  (*
 wedge condition for `f : x ~> y`, both sides `w ~> F (x, y)`:
 `bimap[F] id f ∘ wedge_map[x] ≈ bimap[F] (op f) id ∘ wedge_map[y]` 

 --------
 `f : x ~> y` 的楔形条件，两边 `w ~> F (x, y)`：
 `bimap [F]ZZ  id f ∘ wedge_map [x]ZZ  ≈ bimap [F]ZZ  (op f) id ∘ wedge_map [y]ZZ `
*)
  ump_wedges {x y : C} (f : x ~{C}~> y) :
    bimap[F] id f ∘ wedge_map ≈ bimap[F] (op f) id ∘ wedge_map
}.

Coercion Wedge_to_obj `(F : C^op ∏ C ⟶ D) (W : Wedge F) : D :=
  @wedge_obj _ _ _ W.

Notation "wedge_map[ C ]" := (@wedge_map _ _ _ C _)
  (at level 9, format "wedge_map[ C ]") : category_scope.

(*
 A cowedge is the dual of a wedge: an apex `d : D` with legs
 `F (x, x) ~> d` satisfying the dual condition. It is obtained as a wedge in
 the opposite categories, `Wedge` of `F^op : (C^op)^op ∏ C^op ⟶ D^op`, so a
 cowedge for `F` is literally a wedge for `F^op` (its apex is an object of
 `D^op`, i.e. of `D`, and each leg `d ~{D^op}~> F (x, x)` is a leg
 `F (x, x) ~{D}~> d`). The universal (initial) cowedge is the COEND. 

 --------
 共楔是楔的对偶：一个顶点 `d : D`，带有满足对偶条件的边 `F (x, x) ~> d`。它是作为对偶范畴中的楔获得的，即 `Wedge` 的 `F^op : (C^op)^op ∏ C^op ⟶ D^op`，因此 `F` 的共楔实际上是 `F^op` 的楔（它的顶点是 `D^op` 的一个对象，即 `D`，并且每条边 `d ~{D^op}~> F (x, x)` 是 `F (x, x) ~{D}~> d` 的一条边）。普适（初始）共楔是 COEND。
*)
Definition Cowedge `(F : C^op ∏ C ⟶ D) := @Wedge (C^op) (D^op) (F^op).
