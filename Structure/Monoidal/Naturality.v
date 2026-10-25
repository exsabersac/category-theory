Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section MonoidalNaturality.

Context `{M : @Monoidal C}.

(** Naturality glue for monoidal categories. / 单体范畴的自然性粘合 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 In a monoidal category the tensor ⊗ is a bifunctor (functorial in each
 argument) and the associator alpha = [tensor_assoc], left unitor lambda =
 [unit_left] and right unitor rho = [unit_right] are natural isomorphisms.
 This file feeds those facts to the `natural`/`Mapping` machinery of
 Theory/Naturality.v, so that monoidal naturality obligations elsewhere
 (e.g. [strength_natural] in Functor/Strong.v and [braid_natural] in
 Structure/Monoidal/Braided.v) are discharged by instance resolution.

 For an object map P : C → C with a `Mapping` action map = P f, the partial
 applications of the tensor are themselves morphism actions:

 fun x => P x ⨂ y    with action  map f ⨂ id      ([Tensor_Left_Map]),
 fun y => x ⨂ P y    with action  id ⨂ map f      ([Tensor_Right_Map]),
 fun x => P x ⨂ P x  with action  map f ⨂ map f    ([Tensor_Both_Map]).

 Registering these `Mapping` instances lets the per-argument `Arity*`
 naturality squares of Theory/Naturality.v be computed for families built
 from a tensor whose factors are functorial, without materialising a single
 `C ⟶ C` functor. The companion `Program Definition`s ([Tensor_Left],
 [Tensor_Right], [Tensor_Both]) bundle the same actions as genuine functors
 `C ⟶ C`; they record functoriality but are not used by the resolution
 machinery (only the `Mapping` instances are).

 The closing theorem [monoidal_naturality] then states naturality of the
 three structural isomorphisms as the product of their `to`/`from` squares;
 `prove_naturality` reduces it to the `*_natural` fields of [M].

 Note: [Tensor_Right] is declared `#[export] Program Instance` whereas its
 siblings [Tensor_Left] and [Tensor_Both] are plain `Program Definition`.
 None of the three functor forms is referenced elsewhere, so this asymmetry
 is harmless, but registering an unconstrained `C ⟶ C` functor as a global
 instance is a resolution-hygiene wrinkle; left as-is to keep the change
 minimal. 

 --------
 nLab：https://ncatlab.org/nlab/show/monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Monoidal_category

 在一个幺半群范畴中，张量 ⊗ 是一个双函子（在每个参数上都是函子），关联子 alpha = [tensor_assoc]，左单位子 lambda = [unit_left] 和右单位子 rho = [unit_right] 都是自然同构。
 该文件将这些事实提供给 Theory/Naturality.v 的 `natural` / `Mapping` 机制，以便其他地方的幺半群自然性义务（例如 Functor/Strong.v 中的 [strength_natural] 和 Structure/Monoidal/Braided.v 中的 [braid_natural]）通过实例解析得以满足。

 对于一个对象映射 P : C → C 以及一个 `Mapping` 作用映射 = P f，张量的部分应用本身就是态射作用：fun x => P x ⨂ y    其操作为 action  map f ⨂ id      ( [Tensor_Left_Map] ),
 fun y => x ⨂ P y    其操作为 action  id ⨂ map f      ( [Tensor_Right_Map] ),
 fun x => P x ⨂ P x  其操作为 action  map f ⨂ map f    ( [Tensor_Both_Map] ).

 注册这些  `Mapping`  实例可以让 Theory/Naturality.v 中按参数的  `Arity*` 
 自然性方块被计算出来，用于由张量构建的族，其中张量的因子是函子性的，无需实例化单个
 `C ⟶ C`  函子。配套的  `Program Definition` s ( [Tensor_Left] ,
 [Tensor_Right] ,  [Tensor_Both] ) 捆绑了与真实函子相同的操作 `C ⟶ C`；它们记录了函子性，但不会被解析机制使用
 （仅使用  `Mapping`  实例）。闭合定理 [monoidal_naturality] 然后陈述了三个结构同构的自然性，作为它们 `to` / `from` 方的乘积；ZW30WZZ 将其简化为 `*_natural` 的 [M] 域。

 注意：ZW15WZZ 被声明为 `# [export]ZZ  Program Instance`，而它的同级 [Tensor_Left] 和 [Tensor_Both] 则是普通的 `Program Definition`。这三种函子形式都没有在其他地方被引用，所以这种不对称性是无害的，但将一个不受约束的 `C ⟶ C` 函子注册为全局实例是一个解析卫生的小问题；按原样保留以保持更改最小化。
*)

Program Definition Tensor_Left {F : C ⟶ C} {y : C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ y)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] id
|}.
Next Obligation.
  proper; apply bimap_respects; rewrites; reflexivity.
Defined.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Left_Map `{@Mapping C P} {y : C} :
  @Mapping C (fun x => P x ⨂ y)%object := {
  map := fun _ _ f => map f ⨂ id;
}.

#[export] Program Instance Tensor_Right {F : C ⟶ C} {x : C} : C ⟶ C := {
  fobj := fun y => (x ⨂ F y)%object;
  fmap := fun _ _ f => id ⨂[M] fmap[F] f
}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Right_Map `{@Mapping C P} {x : C} :
  @Mapping C (fun y => x ⨂ P y)%object := {
  map := fun _ _ f => id ⨂ map f;
}.

Program Definition Tensor_Both `{F : C ⟶ C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ F x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] fmap[F] f
|}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Both_Map `{@Mapping C P} :
  @Mapping C (fun x => P x ⨂ P x)%object := {
  map := fun _ _ f => map f ⨂ map f;
}.

Theorem monoidal_naturality :
  natural (@unit_left _ M) *
  natural (@unit_right _ M) *
  natural (@tensor_assoc _ M).
Proof. prove_naturality M normal. Qed.

End MonoidalNaturality.
