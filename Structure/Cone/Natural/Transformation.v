Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

 A cone over a diagram F : J ⟶ C with apex d is the same data as a natural
 transformation Δ[J](d) ⟹ F out of the constant (diagonal) functor at d:
 the components of the transformation are the legs of the cone, and the
 naturality squares are the cone's commuting triangles (Wikipedia: “ψ is a
 cone from N to F” iff “ψ is a natural transformation from Δ(N) to F”). This
 is the equivalence (a) ↔ (b) of that article; (c), the comma-category form
 (Δ ↓ F), is treated separately.

 [Cone_Transform] restates this as Δ[J](d) ⟹ F ↔ { c : Cone F | vertex_obj =
 d }: a cone bundled with its apex pinned to d. The apex is matched by object
 equality (=) rather than ≈, since it identifies objects (not morphisms).
 Structure/Cone/Const.v proves the same equivalence in the unbundled form
 Δ[J](N) ⟹ F ↔ Cone[N] F (a bare leg family with apex N). 

 --------
 nLab:  https://ncatlab.org/nlab/show/cone 
 维基百科:  https://en.wikipedia.org/wiki/Cone_(category_theory) 

 顶点为 d 的图 F : J ⟶ C 上的锥，与从 d 的常量（对角线）函子到 F 的自然变换 Δ [J] (d) ⟹ F 是相同的数据：变换的分量是锥的各条边，自然性方形是锥的交换三角形（维基百科：“ψ 是从 N 到 F 的锥”当且仅当 “ψ 是从 Δ(N) 到 F 的自然变换”）。这就是该文章中 (a) ↔ (b) 的等价；(c)，逗号范畴形式 (Δ ↓ F) 单独处理。[Cone_Transform] 将其重新表述为 Δ [J] (d) ⟹ F ↔ { c : Cone F | vertex_obj = d }：一个顶点固定在 d 的锥体。顶点通过对象相等 (=) 而不是 ≈ 来匹配，因为它识别的是对象（而不是态射）。Structure/Cone/Const.v 在未绑定的形式中证明了相同的等价性 Δ [J] (N) ⟹ F ↔ Cone [N] F（一个顶点为 N 的裸腿族）。
*)

Monomorphic Theorem Cone_Transform `(F : J ⟶ C) (d : C) :
  Δ[J](d) ⟹ F ↔ { c : Cone F | vertex_obj = d }.
Proof.
  split; intros.
  - unshelve eexists.
    + unshelve econstructor; intros; [ exact d | unshelve econstructor ].
      * apply X.
      * abstract(simpl; intros;
        rewrite (naturality[X]); cat).
    + reflexivity.
  - transform; simpl; intros;
    destruct X; subst.
    + apply x0.
    + cat; apply cone_coherence.
    + cat; symmetry; apply cone_coherence.
Defined.
