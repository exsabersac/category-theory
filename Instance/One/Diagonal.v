Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(* * * The constant diagram factors through the terminal category 1. / * * 恒定图经过终端范畴1。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/constant+functor
 nLab:      https://ncatlab.org/nlab/show/diagonal+functor
 Wikipedia: https://en.wikipedia.org/wiki/Diagonal_functor

 The constant diagram Δ[J](d) : J ⟶ D (every object ↦ d, every morphism ↦
 id[d]) does not depend on J's structure, only on d. nLab records this as a
 factorization through the point: "a constant functor can be expressed as the
 composite C → 1 → D", where the first arrow is the unique functor `! : J ⟶ 1`
 ([one], here [Erase J] at Cat's Terminal instance) and the second is the
 functor `1 ⟶ D` picking out d — which is exactly the constant diagram on the
 terminal index category, Δ[1](d), written here Δ(d).

 So Δ[J](d) ≈ Δ(d) ∘ ! in Cat. Both functors send every object to d and every
 morphism to id[d], so they are equal on the nose; the witnessing natural
 isomorphism (Cat's hom-setoid identifies functors up to natural iso) is the
 identity iso [iso_id] at every j : J, and naturality is discharged by [cat].
 This is the J-indexed analogue of [1, C] ≃ C: every constant diagram is an
 object of D inflated along the unique map to 1.  That analogue is itself a
 theorem, Theory/Shapes.v's [One_Fun_iso], proven there over that file's own
 name [Point d] for the constant functor 1 ⟶ D on d. 

 --------
 nLab:       https://ncatlab.org/nlab/show/constant+functor 
 nLab:       https://ncatlab.org/nlab/show/diagonal+functor 
 Wikipedia:  https://en.wikipedia.org/wiki/Diagonal_functor 

 常量图 Δ [J] (d) : J ⟶ D（每个对象映射到 d，每个态射映射到 id [d]）不依赖于 J 的结构，只依赖于 d。nLab 将其记录为通过点的分解：“常量函子可以表示为复合 C → 1 → D”，其中第一条箭头是唯一的函子 `! : J ⟶ 1`（[one]，这里在 Cat 的终端实例中为 [Erase J]），第二条是选取 d 的函子 `1 ⟶ D`——这恰好是终端指标范畴上的常量图 Δ [1] (d)，在此处写作 Δ(d)。所以 Δ [J] (d) ≈ Δ(d) ∘ ! 在 Cat 中。两个函子都将每个对象映射到 d，将每条态射映射到 id [d]，因此它们完全相等；见证的自然同构（Cat 的 Hom 集合同类将函子按自然同构进行识别）是在每个 j : J 上的恒等同构 [iso_id]，自然性由 [cat] 保证。这是 [1, C] ≃ C 的 J 索引类比：每个常量图都是沿唯一映射到 1 扩张的 D 的一个对象。该类比本身是一个定理，Theory/Shapes.v 的 [One_Fun_iso]，在该文件上使用其自身名称 [Point d] 对常量函子 1 ⟶ D 在 d 上进行了证明。
*)

Corollary Diagonal_Unique (J C : Category) {D : Category} (d : D) :
  Δ[J](d) ≈[Cat] Δ(d) ∘[Cat] one.
Proof. exists (fun _ => iso_id); simpl; intros; cat. Qed.
