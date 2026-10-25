Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Structure.Factorization.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Images in [Sets] / * [Sets] 中的图片 *)

(*
 nLab:      https://ncatlab.org/nlab/show/image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)

 Concrete images in the category of setoids: every morphism f : X ~> Y
 of [Sets] splits as an epimorphism onto its image followed by a
 monomorphism into its codomain.

 The image object carries the proof-relevant sigma type

 { y : Y & { x : X & f x ≈ y } }

 — a point of Y together with a chosen preimage and the witness that f
 sends that preimage to it — and its setoid compares Y-components only:

 (y1; _) ≈ (y2; _)  :=  y1 ≈ y2.

 The epi leg sends x to (f x; (x; _)), the mono leg is the first
 projection, and their composite agrees with f pointwise on the nose.

 Both class memberships are established directly from these definitions;
 in particular the construction needs no epis-are-surjections result for
 [Sets] — the factorization is direct.  The left leg is epic because two
 morphisms out of the image that agree on all points of the shape
 (f x; (x; _)) agree everywhere: every image point is ≈ to one of that
 shape by its stored witness.  The right leg is monic because agreement
 of first projections is exactly the image setoid's equivalence.  The
 whole package is bundled as [Sets_Image_Factorization], an (Epi, Mono)
 [Factorization] in the sense of Structure/Factorization.v. 

 --------
 nLab: https://ncatlab.org/nlab/show/image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(category_theory)

 集合等价类范畴中的具体对象: 每一个 [Sets] 的态射 f : X ~> Y 都可以分解为先映射到其象的一个满射(epimorphism)，再映射到其陪域的一个单射(monomorphism)。

 象对象携带证明相关的西格玛类型(sigma type)

 { y : Y & { x : X & f x ≈ y } }

 — Y中的一个点，以及一个选定的原像和证明 f 将该原像映射到该点的证据 — 并且它的集合等价类仅比较 Y 分量：

 (y1; _) ≈ (y2; _)  :=  y1 ≈ y2.

 满射部分将 x 映射为 (f x; (x; _))，单射部分是第一个投影，它们的复合在点上与 f 完全一致。这两个类的成员都是直接由这些定义建立的；特别是这个构造不需要 [Sets] 的 epis-are-surjections 结果——因式分解是直接的。左边的箭头是满射的，因为从像中出发的两个态射在所有形状的点 (f x; (x; _)) 上相等，因此在所有点上都相等：每个像点通过其存储的见证与该形状的某个点≈。右边的箭头是单射的，因为第一投影的相等正好是像等价类的等价关系。整个包封装为 [Sets_Image_Factorization]，一个按 Structure/Factorization.v 的意义上的 (Epi, Mono) [Factorization]。
*)

Section SetsImage.

Context {X Y : SetoidObject}.
Context (f : X ~{Sets}~> Y).

(*
 Comparing image points by their Y-components only is an equivalence,
 inherited from the setoid on Y. 

 --------
 仅通过它们的 Y 分量比较图像点是一种等价关系，它继承自 Y 上的集合等价类。
*)
Lemma Sets_Image_equivalence :
  Equivalence (fun p q : ∃ y : Y, ∃ x : X, f x ≈ y => `1 p ≈ `1 q).
Proof.
  constructor.
  - intro p.
    simpl.
    reflexivity.
  - intros p q H.
    simpl in *.
    symmetry.
    exact H.
  - intros p q r H1 H2.
    simpl in *.
    transitivity (`1 q).
    + exact H1.
    + exact H2.
Qed.

(* The setoid of image points: pairs of a point of Y with a chosen f-preimage, compared by their Y-components only. / 像点的集合：由 Y 中的一个点与所选 f-原像组成的对，仅通过它们的 Y 分量进行比较。 *)
Definition Sets_Image_setoid : Setoid (∃ y : Y, ∃ x : X, f x ≈ y) := {|
  equiv        := fun p q => `1 p ≈ `1 q;
  setoid_equiv := Sets_Image_equivalence
|}.

(* The image of f as an object of [Sets]. / f 在 [Sets] 中作为一个对象的像。 *)
Definition Sets_Image : SetoidObject := {|
  carrier   := ∃ y : Y, ∃ x : X, f x ≈ y;
  is_setoid := Sets_Image_setoid
|}.

(* The epi leg X ~> Sets_Image: send x to f x, remembering x itself as the chosen preimage. / 上射腿 X ~> Sets_Image：将 x 发送到 f x，同时记住 x 本身作为所选择的原像。 *)
Definition Sets_Image_epi : X ~{Sets}~> Sets_Image.
Proof.
  unshelve refine {| morphism        := fun x => (f x; (x; _))
                   ; proper_morphism := _ |}.
  - reflexivity.
  - repeat intro.
    simpl.
    now apply (proper_morphism f).
Defined.

(*
 The mono leg Sets_Image ~> Y: the first projection.  Respectfulness is
 the identity: the image equivalence IS agreement of first projections. 

 --------
 单腿 Sets_Image ~> Y：第一个投影。 尊重性是身份：图像等价是第一个投影的一致性。
*)
Definition Sets_Image_mono : Sets_Image ~{Sets}~> Y.
Proof.
  unshelve refine {| morphism        := fun p => `1 p
                   ; proper_morphism := _ |}.
  repeat intro.
  assumption.
Defined.

(* The two legs compose to f, pointwise by reflexivity. / 这两条腿逐点由自反性组成 f。 *)
Lemma Sets_Image_comm : Sets_Image_mono ∘ Sets_Image_epi ≈ f.
Proof.
  intro x.
  simpl.
  reflexivity.
Qed.

(*
 The epi leg is epic: given g1 ∘ epi ≈ g2 ∘ epi and an image point
 (y; (x; hx)), rewrite it to the canonical point (f x; (x; _)) using the
 stored witness hx : f x ≈ y, where the hypothesis applies. 

 --------
 Epi 引理是史诗级的：给定 g1 ∘ epi ≈ g2 ∘ epi 和一个像点 (y; (x; hx))，使用存储的证据 hx : f x ≈ y（在假设适用的地方），将其重写为规范点 (f x; (x; _))。
*)
Lemma Sets_Image_epi_epic : Epic Sets_Image_epi.
Proof.
  constructor.
  intros Z g1 g2 HB.
  simpl in HB.
  intro p.
  destruct p as [y [x hx]].
  transitivity (g1 (Sets_Image_epi x)).
  - apply (proper_morphism g1).
    simpl.
    symmetry.
    exact hx.
  - transitivity (g2 (Sets_Image_epi x)).
    + exact (HB x).
    + apply (proper_morphism g2).
      simpl.
      exact hx.
Qed.

(*
 The mono leg is monic: mono ∘ g1 ≈ mono ∘ g2 says the first projections
 agree pointwise, which is precisely the image setoid's equivalence. 

 --------
 单腿是单的：mono ∘ g1 ≈ mono ∘ g2 表示第一个投影在每一点上都相等，这正是像集合等价关系。
*)
Lemma Sets_Image_mono_monic : Monic Sets_Image_mono.
Proof.
  constructor.
  intros Z g1 g2 HB.
  intro p.
  exact (HB p).
Qed.

(* The bundled (Epi, Mono)-factorization of f through its image. / 通过其像的 f 的捆绑 (Epi, Mono) 分解。 *)
Definition Sets_Image_Factorization :
  Factorization f EpiClass MonoClass :=
  @Build_Factorization Sets X Y f EpiClass MonoClass
    Sets_Image
    Sets_Image_epi
    Sets_Image_epi_epic
    Sets_Image_mono
    Sets_Image_mono_monic
    Sets_Image_comm.

End SetsImage.
