Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* * * The category of cones over a diagram / * * 某一图表上的圆锥的范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

 The cones over a fixed diagram F : J ⟶ C form a category. Its objects are
 the cones over F, i.e. apex objects N : C equipped with a coherent leg
 family ψx : N ~> F x (see [Cone]). A morphism from a cone N (legs ψ) to a
 cone L (legs φ) is a single apex map u : N ~> L of C that is compatible
 with both leg families: φx ∘ u ≈ ψx for every object x of J, so that u
 transports N's legs onto L's. (Viewing cones as natural transformations
 Δ N ⟹ F, such a u is the unique component to which any compatible
 Δ N ⟹ Δ L collapses.) Two cone morphisms are identified exactly when
 their underlying apex maps agree under ≈; the commutativity witness is
 proof-irrelevant. Composition is composition of apex maps, and the
 identity cone morphism is the identity apex map.

 The limit of F is the terminal object of this category: the universal cone
 through which every other cone factors uniquely (see Cones/Limit). 

 --------
 nLab:  https://ncatlab.org/nlab/show/cone
 Wikipedia:  https://en.wikipedia.org/wiki/Cone_(category_theory)

 固定图 F : J ⟶ C 的锥体（cones）组成一个范畴。它的对象是 F 上的锥体，即配备有相干腿族 ψx : N ~> F x 的顶点对象 N : C（参见 [Cone]）。从锥体 N（腿为 ψ）到锥体 L（腿为 φ）的态射是 C 中的单个顶点映射 u : N ~> L，它与两族腿兼容：对 J 中的每个对象 x，φx ∘ u ≈ ψx，因此 u 将 N 的腿映射到 L 的腿。（将锥体视为自然变换 Δ N ⟹ F，这样的 u 是任何兼容的 Δ N ⟹ Δ L 崩缩到的唯一分量。）当且仅当两个锥体态射的底层顶点映射在 ≈ 下相等时，它们才被视为相同；交换性证明是不相关的。复合是顶点映射的复合，身份锥体态射是身份顶点映射。F 的极限是该范畴的终对象：通过它每个其他圆锥都能唯一分解的通用圆锥（参见 圆锥/极限）。
*)

Program Definition Cones `(F : J ⟶ C) : Category := {|
  obj     := Cone F;
  hom     := fun N L => { u : vertex_obj[N] ~> vertex_obj[L]
                              & ∀ j, vertex_map[L] ∘ u ≈ @vertex_map _ _ _ F
                                       (@coneFrom _ _ _ N) j };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _);
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite X0; auto.
Qed.

(*
 The category of cocones over F is dually the category of cones over the
 opposite diagram F^op : J^op ⟶ C^op: its objects are the cocones over F
 (see [Cocone]), its arrows apex maps in C^op, and its TERMINAL object is
 the colimit of F -- "initial in the category of cocones" reads as terminal
 here because the arrows run in C^op (see Cones/Limit, [Cocones_Colimit]). 

 --------
 F 的余锥范畴在对偶意义上是对偶图 F^op : J^op ⟶ C^op 的锥范畴：它的对象是 F 的余锥（参见 [Cocone]），它的箭头是在 C^op 中的顶点映射，其终对象是 F 的余极限——“在余锥范畴中初对象”在这里读作终对象，因为箭头在 C^op 中运行（参见 Cones/Limit, [Cocones_Colimit]）。
*)
Definition Cocones `(F : J ⟶ C) := Cones (F^op).
