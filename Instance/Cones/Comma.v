Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * The category of cones over F is the comma category (Δ ↓ F) / * * 关于 F 的锥的范畴是逗号范畴 (Δ ↓ F) *)

(*
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

 A cone over a diagram F : J ⟶ C with apex c is exactly a natural
 transformation Δ(c) ⟹ F from the constant functor at c to F. Collecting
 these into a category, the category of cones to F is the comma category
 (Δ ↓ F): its objects are pairs (c, ψ) with ψ : Δ(c) ⟹ F, and a cone
 morphism (c, ψ) ~> (c', ψ') is a single arrow u : c ~> c' in C making every
 leg triangle commute (ψ'x ∘ u ≈ ψx), since the diagonal acts trivially on
 arrows. Here =(F) denotes the constant functor 1 ⟶ [J, C] picking out F, so
 that the J-indexed diagonal Δ : C ⟶ [J, C] and =(F) share the codomain
 [J, C] needed to form the comma category. The limit of F, when it exists, is
 the terminal object of this category; dually, cocones to F form (F ↓ Δ).

 [Cones_to_Comma] and [Cones_from_Comma] build the two comparison functors,
 and [Cones_Comma] assembles them into an isomorphism in Cat. 

 --------
 nLab:  https://ncatlab.org/nlab/show/cone 
 Wikipedia:  https://en.wikipedia.org/wiki/Cone_(category_theory) 

 一个以顶点 c 为顶点的图 F : J ⟶ C 的锥，恰好是从常值函子 Δ(c) 到 F 的一个自然变换 Δ(c) ⟹ F。将这些收集成一个范畴，F 的锥的范畴就是逗号范畴 (Δ ↓ F)：它的对象是成对 (c, ψ)，其中 ψ : Δ(c) ⟹ F，而一个锥的态射 (c, ψ) ~> (c', ψ') 是 C 中的单个箭头 u : c ~> c'，使得每条腿的三角形均交换 (ψ'x ∘ u ≈ ψx)，因为对角函子在箭头上起到平凡作用。这里 =(F) 表示常值函子 1 ⟶  [J, C] 选取 F，因此 J 标号的对角Δ : C ⟶  [J, C] 和 =(F) 共享形成逗号范畴所需的陪域 [J, C]。F 的极限，如果存在，就是这个范畴的终对象；对偶地，F 的余锥形成 (F ↓ Δ) 。[Cones_to_Comma] 和 [Cones_from_Comma] 构建了两个比较函子，[Cones_Comma] 将它们组装成 Cat 中的一个同构。
*)

Theorem Cones_to_Comma `(F : [J, C]) : Cones F ⟶ (Δ ↓ =(F)).
Proof.
  functor; simpl; intros.
  - exists (vertex_obj[X], ttt).
    transform; simpl; intros.
    + apply @vertex_map. exact (@coneFrom _ _ _ X).
    + abstract (rewrite id_right; apply cone_coherence).
    + abstract (rewrite id_right; symmetry; apply cone_coherence).
  - exists (`1 f, ttt); abstract (simpl; intros; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

Theorem Cones_from_Comma `(F : [J, C]) : (Δ ↓ =(F)) ⟶ Cones F.
Proof.
  functor; simpl; intros.
  - construct; simpl; intros.
    + exact (fst ``X).
    + exists (transform[`2 X]). abstract (intros; rewrite (naturality[`2 X]); cat).
  - destruct f; simpl in *.
    exists (fst x0); abstract (intros; rewrite e; cat).
  - abstract proper.
  - abstract cat.
  - abstract cat.
Defined.

(*
 nLab: https://ncatlab.org/nlab/show/comma+category
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)

 Cones F and (Δ ↓ =(F)) are not merely equivalent but isomorphic in Cat: the
 two comparison functors are mutually inverse on the nose. This reflects how
 directly the data line up — an apex with a coherent leg family on one side is
 literally a pair (object, natural transformation Δ(c) ⟹ F) on the other, and
 a cone morphism is the same single arrow either way (the second comma
 component lives in the terminal category 1, hence is ttt). Both Wikipedia and
 nLab record this identification: "morphisms of cones are then just morphisms
 in this [comma] category," the diagonal acting trivially on arrows. 

 --------
 nLab：https://ncatlab.org/nlab/show/comma+category
 Wikipedia：https://en.wikipedia.org/wiki/Cone_(category_theory)

 锥 F 与 (Δ ↓ =(F)) 不仅仅是等价的，而是在 Cat 中同构的：两个比较函子在本质上互为逆。 这反映了数据的对齐方式是多么直接——一侧有一个顶点及其一致的腿族，在另一侧实际上就是一对（对象，自然变换 Δ(c) ⟹ F），而锥态射无论在哪一边都是同一个箭头（第二个逗号组件存在于终端范畴 1 中，因此为 ttt）。Wikipedia 和 nLab 都记录了这一对应关系：“锥态射就是在这个 [comma] 范畴中的态射，”对角线在箭头上作用平凡。
*)

Theorem Cones_Comma `(F : [J, C]) : Cones F ≅[Cat] (Δ ↓ =(F)).
Proof.
  isomorphism; simpl; intros.
  - apply Cones_to_Comma.
  - apply Cones_from_Comma.
  - constructive.
    + exists (id, ttt); abstract cat.
    + exists (id, ttt); abstract cat.
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
  - constructive.
    + exists id; abstract (intros; cat).
    + exists id; abstract (intros; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
    + abstract (simpl; cat).
Qed.
