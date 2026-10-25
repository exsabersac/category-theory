Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Constant.

Generalizable All Variables.

(** * Functors compatible with embedded constants  / * 与嵌入常量兼容的函子*)

(*
nLab: https://ncatlab.org/nlab/show/monoidal+functor
   nLab: https://ncatlab.org/nlab/show/global+element
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   Given a functor `F : C ⟶ D` and a shared type `T` of foreign constants
   embedded into both `C` and `D` as families of global elements (see
   Structure/Constant.v), this structure says that `F` carries the embedding
   on the source over to the embedding on the target, up to comparison maps.

   It is the global-element analogue of the *unit comparison map* of a (lax)
   monoidal functor `ψ_I : I ~> F I`: with the terminal object `1` playing the
   role of the monoidal unit, `unmap_one` is the comparison between the units,
   and `map_const` compares the host objects of each constant. Because `1` is
   terminal in `D`, the unit comparison is forced to run `F 1 ~> 1` (the unique
   map into the terminal object), the reverse of the lax-monoidal direction.

   Beware that the two `Terminal`/`Constant` instances in scope (`CT`,`H` on the
   `C` side and `DT`,`H0` on the `D` side) make some textually-identical
   notations resolve differently. In `unmap_one`, `F 1` is `F` of `C`'s
   terminal object while the codomain `1` is `D`'s terminal object. In
   `map_const`, the domain `constant_obj T x` is the `D`-side host object while
   the `constant_obj T x` under `F` is the `C`-side host object. The coherence
   law then states `fmap (constant x) ≈ map_const x ∘ constant x ∘ unmap_one`,
   where the left `constant x` is the `C`-side global element and the right one
   is the `D`-side global element. 

--------
nLab：https://ncatlab.org/nlab/show/monoidal+functor
 nLab：https://ncatlab.org/nlab/show/global+element
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

给定一个函子 `F : C ⟶ D` 和一个外部常量的共享类型 `T`
 作为全局元素族嵌入到“C”和“D”中（参见
 Structure/Constant.v)，该结构表示“F”携带嵌入
 从源到目标的嵌入，再到比较图。

它是 a (lax) 的*单位比较图*的全局元素类似物
 幺半群函子 `ψ_I : I ~> F I`：终端对象 `1` 播放
 幺半群单元的作用，`unmap_one`是单元之间的比较，
 `map_const` 比较每个常量的宿主对象。 因为‘1’是
 在“D”中的终端，单位比较被迫运行“F 1 ~> 1”（唯一的
 映射到终端对象），与松散单向方向相反。

请注意，范围内的两个“Terminal”/“Constant”实例（“CT”、“H”）
 “C”侧和“D”侧的“DT”、“H0”）使一些文本相同
 符号的解析方式不同。 在`unmap_one`中，`F 1`是`C`的`F`
 终端对象，而余域“1”是“D”的终端对象。 在
 `map_const`，域`constant_obj T x`是`D`端宿主对象，而
 “F”下的“constant_obj T x”是“C”端宿主对象。 连贯性
 然后定律指出“fmap (constant x) ≈ map_const x ∘constant x ∘ unmap_one”，
 其中左侧“constant x”是“C”端全局元素，右侧是“constant x”
 是“D”侧全局元素。 
*)

Section ConstantFunctor.

Context `{F : C ⟶ D}.
Context `{@Constant C CT T}.
Context `{@Constant D DT T}.

Class ConstantFunctor := {
  unmap_one : F 1 ~{D}~> 1;     (* unit comparison: F of C's `1` into D's `1`  / 单位比较：C的“1”中的F变为D的“1”*)

  (* host-object comparison: D-side `constant_obj x` into F of the C-side one  / 主机-对象比较：D端`constant_obj x`到C端的F中*)
  map_const {x : T} : constant_obj T x ~> F (constant_obj T x);

  (*
coherence: F of the C-side global element of `x` agrees with the D-side
     global element of `x` transported through the comparison maps 

--------
一致性：‘x’的C端全局元素F与D端一致
 通过比较映射传输的“x”的全局元素 
*)
  fmap_constant (x : T) :
    fmap (constant x) ≈ @map_const x ∘ constant x ∘ unmap_one;
}.

End ConstantFunctor.
