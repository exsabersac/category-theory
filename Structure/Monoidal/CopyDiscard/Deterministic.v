Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
   * * Deterministic morphisms in a copy-discard category

   A [CopyDiscard] category deliberately imposes NO naturality on [copy] and
   [discard]: a general morphism need not commute with duplication or
   deletion.  Following Fritz (Definition 10.1 of arXiv:1908.07021), a
   morphism [f : x ~> y] is DETERMINISTIC when it does commute with both,
   i.e. when it is a comonoid homomorphism between the canonical comonoids:

   copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]        (copying the output of [f]
   is running [f] twice on a
   copied input)
   discard[y] ∘ f ≈ discard[x]             (running [f] and discarding
   is just discarding)

   When other files cite these squares under the Cho–Jacobs name, the
   shorthand means exactly these two comonoid-homomorphism squares taken
   over the Cho–Jacobs CD structure (Definition 2.2 of arXiv:1709.00322);
   the determinism condition itself is Fritz's.  In a Markov category
   these two squares single out exactly the morphisms that carry no
   randomness.  Deterministic morphisms contain the
   identities and are closed under composition and under ⨂; all the
   structural isomorphisms of the symmetric monoidal base — braiding,
   unitors, associator — are deterministic, and so are the generators
   [copy] and [discard] themselves ([deterministic_copy] /
   [deterministic_discard]).  Consequently the deterministic morphisms
   form a wide (lluf) subcategory [Det] of [C], packaged here through
   [Construction/Subcategory.v].

   The structural-morphism proofs are instances of the classical fact that
   the squaring functor [x ↦ x ⨂ x] of a symmetric monoidal category is
   itself symmetric (strong) monoidal, with structure map the middle
   interchange [(a ⨂ b) ⨂ (c ⨂ d) ≅ (a ⨂ c) ⨂ (b ⨂ d)].  That
   interchange, [swap_inner], and its coherence laws ([swap_inner_braid],
   [swap_inner_assoc], [swap_inner_unit_left] / [swap_inner_unit_right])
   are developed for any symmetric monoidal category in the shared toolkit
   of Structure/Monoidal/Braided/Proofs.v; this file identifies its
   diagonal with Hypergraph.v's [mid_swap_inv] ([swap_inner_diag]) and
   restates the coherences in the [mid_swap_inv] form the determinism
   proofs consume ([mid_swap_inv_braid], [mid_swap_inv_assoc],
   [mid_swap_inv_unit_left] / [mid_swap_inv_unit_right]).

   The structural determinism lemmas are direct coherence chases at the
   canonical [cd_comonoid] supply.  The [Comonoid_Iso] transport of
   Theory/Algebra/Comonoid/Hom.v cannot be used for them: determinism
   demands a [ComonoidHom] between the canonical comonoids at BOTH
   endpoints, whereas transporting a comonoid along a structural
   isomorphism only produces homomorphisms into the transported comonoid
   [Comonoid_Iso i _], which is not the canonical one.

   The headline citation-ready facts are [copy_natural_on_deterministic]
   and [discard_natural_on_deterministic]: copy/discard ARE natural once
   restricted to deterministic morphisms.

   nLab:      https://ncatlab.org/nlab/show/Markov+category
   Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
   string diagrams", MSCS 29(7):938–971, 2019
   (arXiv:1709.00322), §2
   Reference: Fritz, "A synthetic approach to Markov kernels, conditional
   independence and theorems on sufficient statistics",
   Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §10 

   --------
   * * 在复制-丢弃范畴中的确定性态射

   一个[CopyDiscard]范畴故意对[copy]和[discard]不施加自然性条件：一般态射不需要与复制或删除交换。根据Fritz（arXiv:1908.07021的定义10.1），一个态射[f : x ~> y]是确定性的，当且仅当它与两者都交换，即当它是标准余幺半群之间的余幺半群同态：

   copy [y] ∘ f ≈ (f ⨂ f) ∘ copy [x]         （复制[f]的输出相当于在复制的输入上运行[f]两次）
   discard [y] ∘ f ≈ discard [x]              （运行[f]然后丢弃就相当于直接丢弃）当其他文件在 Cho–Jacobs 名下引用这些方格时，简写的意思正是这两个在 Cho–Jacobs CD 结构下的 comonoid-同态方格（arXiv:1709.00322 的定义 2.2）；确定性条件本身是 Fritz 的。在马尔可夫范畴中，这两个方格正好标出那些不携带随机性的态射。确定性态射包含恒等态射，并且在复合和 ⨂ 下封闭；对称幺半范畴基的所有结构同构——换位子、单位子、结合子——都是确定性的，生成元 [copy] 和 [discard] 本身也是确定性的（[deterministic_copy] / [deterministic_discard]）。因此，确定性态射形成了 [C] 的一个宽（lluf）子范畴 [Det]，在这里通过 [Construction/Subcategory.v] 打包。结构-同态证明是经典事实的实例，即对称幺半范畴的平方函子 [x ↦ x ⨂ x] 本身也是对称（强）幺半的，其结构映射是中间交换 [(a ⨂ b) ⨂ (c ⨂ d) ≅ (a ⨂ c) ⨂ (b ⨂ d)]。该交换 [swap_inner] 及其相干律（[swap_inner_braid]、[swap_inner_assoc]、[swap_inner_unit_left] / [swap_inner_unit_right]）在 Structure/Monoidal/Braided/Proofs.v 的共享工具集中为任何对称幺半范畴开发；该文件将其对角与 Hypergraph.v 的 [mid_swap_inv] ([swap_inner_diag]) 关联，并以 [mid_swap_inv] 形式重新陈述相干律，这种形式被确定性证明所使用（[mid_swap_inv_braid]、[mid_swap_inv_assoc]、[mid_swap_inv_unit_left] / [mid_swap_inv_unit_right]）。结构决定性引理是对规范的 [cd_comonoid] 供应的直接相干追逐。[Comonoid_Iso] 的 Theory/Algebra/Comonoid/Hom.v 传输不能用于它们：决定性要求在两个端点的规范 comonoid 之间存在 [ComonoidHom]，而沿结构同构传输 comonoid 只会产生到传输 comonoid [Comonoid_Iso i _] 的同态，而它不是规范的。 头条可引用的事实是 [copy_natural_on_deterministic] 和 [discard_natural_on_deterministic]：一旦限制在确定性态射上，拷贝/丢弃就是自然的。nLab:       https://ncatlab.org/nlab/show/Markov+category
   参考文献: Cho & Jacobs, 《通过弦图的分解与贝叶斯反演》, MSCS 29(7):938–971, 2019 (arXiv:1709.00322), §2
   参考文献: Fritz, 《对马尔可夫核、条件独立性及充分统计定理的综合方法》, Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §10
*)

(* ------------------------------------------------------------------ *)

(*
   * ** Diagonal corollaries of the interchange

   The four-object middle interchange [swap_inner] and its coherence laws
   are developed for any symmetric monoidal category in the shared toolkit
   of Structure/Monoidal/Braided/Proofs.v.  Its diagonal
   [swap_inner x x y y] is definitionally Hypergraph.v's [mid_swap_inv]
   ([swap_inner_diag]); the corollaries below restate the interchange
   coherences in [mid_swap_inv] form, which is the shape the determinism
   proofs consume.  Braided/Proofs.v itself stays independent of the
   hypergraph stack; Theory/Algebra/Comonoid/Tensor.v restates the same
   bridge in the mirror orientation ([mid_swap_inv_swap_inner]) for the
   tensor-comonoid laws. 

   --------
   * ** 交换的对角推论

   四对象中间交换 [swap_inner] 及其相干律 
   已在 Structure/Monoidal/Braided/Proofs.v 的共享工具包中针对任意对称单体范畴进行了开发。其对角 
   [swap_inner x x y y] 在定义上是 Hypergraph.v 的 [mid_swap_inv] ([swap_inner_diag])；下面的推论以 [mid_swap_inv] 形式重新表述了交换相干性，这是确定性证明使用的形状。Braided/Proofs.v 本身保持独立于超图栈；Theory/Algebra/Comonoid/Tensor.v 在镜像方向（[mid_swap_inv_swap_inner]）中重新表述了相同的桥，用于张量-余单体律。
*)

Section MidSwapCoherence.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(* [mid_swap_inv] (Hypergraph.v) is the diagonal of the interchange. / [mid_swap_inv]（Hypergraph.v）是互换的对角线。 *)
Lemma swap_inner_diag (x y : C) : swap_inner x x y y ≈ mid_swap_inv x y.
Proof. reflexivity. Qed.

Corollary mid_swap_inv_braid {x y : C} :
  mid_swap_inv y x ∘ braid
    ≈ (@braid C _ x y ⨂ @braid C _ x y) ∘ mid_swap_inv x y.
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_braid.
Qed.

Corollary mid_swap_inv_assoc {x y z : C} :
  mid_swap_inv x (y ⨂ z)
    ∘ ((id[(x ⨂ x)%object] ⨂ mid_swap_inv y z) ∘ to tensor_assoc)
    ≈ (to tensor_assoc ⨂ to tensor_assoc)
        ∘ (mid_swap_inv (x ⨂ y) z ∘ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])).
Proof.
  rewrite <- !swap_inner_diag.
  apply swap_inner_assoc.
Qed.

(* The unit coherence, left form: conjugating [mid_swap_inv I x] by the canonical unit isomorphisms is the left unitor. / 单位相干性，左形式：通过规范单位同构对 [mid_swap_inv I x] 进行结合是左单位子。 *)
Corollary mid_swap_inv_unit_left {x : C} :
  (unit_left ⨂ unit_left) ∘ mid_swap_inv I x
    ∘ (unit_left⁻¹ ⨂ id[(x ⨂ x)%object])
    ≈ @unit_left C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_left.
Qed.

(* The unit coherence, right form. / 单位一致性，正确形式。 *)
Corollary mid_swap_inv_unit_right {x : C} :
  (unit_right ⨂ unit_right) ∘ mid_swap_inv x I
    ∘ (id[(x ⨂ x)%object] ⨂ unit_left⁻¹)
    ≈ @unit_right C _ (x ⨂ x).
Proof.
  rewrite <- swap_inner_diag.
  apply swap_inner_unit_right.
Qed.

End MidSwapCoherence.

(* ------------------------------------------------------------------ *)

(** ** Deterministic morphisms / ** 确定性态射 *)

Section Deterministic.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{CD : @CopyDiscard C S}.

(*
 A morphism is deterministic when it is a comonoid homomorphism between
 the canonical copy/discard comonoids (deterministic in the sense of
 Fritz, Definition 10.1 of arXiv:1908.07021, stated over the Cho–Jacobs
 CD structure, Definition 2.2 of arXiv:1709.00322). 

 --------
 当一个态射是典型的复制/丢弃余单元之间的余单元同态时，它是确定性的（在Fritz的意义上确定性，见arXiv:1908.07021的定义10.1，根据Cho–Jacobs CD结构，见arXiv:1709.00322的定义2.2）。
*)
Definition deterministic {x y : C} (f : x ~> y) : Type :=
  ComonoidHom (cd_comonoid x) (cd_comonoid y) f.

Lemma deterministic_id {x : C} : deterministic (id[x]).
Proof. apply ComonoidHom_id. Qed.

Lemma deterministic_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  deterministic f → deterministic g → deterministic (f ∘ g).
Proof. apply ComonoidHom_comp. Qed.

Lemma deterministic_equiv {x y : C} {f g : x ~> y} :
  f ≈ g → deterministic f → deterministic g.
Proof. apply ComonoidHom_equiv. Qed.

(*
   * The headline: copy and discard ARE natural once restricted to
   deterministic morphisms.  These are the two squares whose breakdown for
   general morphisms is the defining negative space of [CopyDiscard]. 

   --------
   * 标题：一旦限制于确定性同态，“复制和丢弃”就是自然的。这是两个方格，对于一般同态，它们的破坏构成了 [CopyDiscard] 的定义性负空间。
*)

Theorem copy_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x].
Proof. intro F. exact (@hom_delta _ _ _ _ _ _ _ F). Qed.

Theorem discard_natural_on_deterministic {x y : C} (f : x ~> y) :
  deterministic f → discard[y] ∘ f ≈ discard[x].
Proof. intro F. exact (@hom_epsilon _ _ _ _ _ _ _ F). Qed.

(* Closure under the tensor: the δ-square pastes through [mid_swap_inv_natural], the ε-square through the unit. / 张量下的闭合性：δ平方穿过 [mid_swap_inv_natural]，ε平方穿过单位。 *)
Lemma deterministic_tensor {x x' y y' : C} {f : x ~> y} {f' : x' ~> y'} :
  deterministic f → deterministic f' → deterministic (f ⨂ f').
Proof.
  intros [Fd Fe] [Fd' Fe'].
  split.
  - change (copy[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ ((f ⨂ f') ⨂ (f ⨂ f')) ∘ copy[(x ⨂ x')%object]).
    rewrite !copy_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fd, Fd'.
    rewrite bimap_comp.
    rewrite comp_assoc.
    rewrite mid_swap_inv_natural.
    rewrite <- comp_assoc.
    reflexivity.
  - change (discard[(y ⨂ y')%object] ∘ (f ⨂ f')
              ≈ discard[(x ⨂ x')%object]).
    rewrite !discard_tensor.
    rewrite <- comp_assoc.
    rewrite <- bimap_comp.
    rewrite Fe, Fe'.
    reflexivity.
Qed.

(* The inverse of a deterministic isomorphism is deterministic. / 确定性同构的逆是确定性的。 *)
Lemma deterministic_iso_from {x y : C} (i : x ≅ y) :
  deterministic (to i) → deterministic (i⁻¹).
Proof.
  intros [Fd Fe].
  split.
  - rewrite <- (id_left (delta[ccomon_comonoid] ∘ i⁻¹)).
    rewrite <- bimap_id_id.
    rewrite <- (iso_from_to i).
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i ⨂ to i)).
    rewrite <- Fd.
    rewrite <- !comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
  - rewrite <- Fe.
    rewrite <- comp_assoc.
    rewrite iso_to_from, id_right.
    reflexivity.
Qed.

(*
   * *** The generators copy and discard are themselves deterministic

   The canonical generators are the standard first examples of
   deterministic morphisms (Fritz §10, over the CD structure of
   Cho–Jacobs §2): [copy] is a
   comonoid homomorphism precisely because the supply is coassociative
   and cocommutative — its δ-square says [mid_swap_inv] fixes the
   two-fold copy — and [discard] is one by the counit and unit
   coherences.  These two lemmas are what a copy-discard supply on
   [Det] itself would require of its structure morphisms. 

   --------
   * *** 生成器“复制”和“丢弃”本身是确定性的

   规范生成器是确定性态射的标准首例（Fritz §10，关于 Cho–Jacobs §2 的 CD 结构）：[copy] 是一个余幺半群态射，正因为其供应是余结合且余交换的——其 δ-square 表明 [mid_swap_inv] 固定了二重复制——而 [discard] 则因余单位与单位的相容性而成为态射。这两个引理正是 [Det] 上的复制-丢弃供应本身对其结构态射所要求的。
*)

(* The comonoid laws of the canonical supply, restated in copy/discard form for rewriting (the class fields state them at [delta] and [epsilon] of the underlying comonoid). / 标准供应的余单元律，在复制/丢弃形式下重新表述以便重写（类字段在基础余单元的 [delta] 和 [epsilon] 处声明它们）。 *)

Lemma copy_coassoc {x : C} :
  (copy[x] ⨂ id[x]) ∘ copy[x]
    ≈ tensor_assoc⁻¹ ∘ ((id[x] ⨂ copy[x]) ∘ copy[x]).
Proof.
  rewrite comp_assoc.
  exact (@delta_coassoc C _ x (cd_comonoid x)).
Qed.

(* Coassociativity solved for the forward associator. / 针对前向结合子解决了余结合性问题。 *)
Lemma copy_coassoc_to {x : C} :
  to tensor_assoc ∘ ((copy[x] ⨂ id[x]) ∘ copy[x])
    ≈ (id[x] ⨂ copy[x]) ∘ copy[x].
Proof.
  rewrite copy_coassoc.
  rewrite comp_assoc.
  now rewrite iso_to_from, id_left.
Qed.

Lemma copy_cocomm {x : C} : braid ∘ copy[x] ≈ copy[x].
Proof. exact (@delta_cocommutative_of_ccomon C S x (cd_comonoid x)). Qed.

Lemma copy_counit_left {x : C} :
  (discard[x] ⨂ id[x]) ∘ copy[x] ≈ unit_left⁻¹.
Proof. exact (@delta_counit_left C _ x (cd_comonoid x)). Qed.

(*
 The δ-square of copy: [mid_swap_inv] fixes the two-fold copy
 (δ ⨂ δ) ∘ δ.  The chase pushes all three copies into the right-hand
 nest with coassociativity ([Key]), where the conjugated inner braid
 dies against cocommutativity ([Inner]), and comes back down ([Key2]). 

 --------
 复制的 δ-平方：[mid_swap_inv] 固定了二重复制 (δ ⨂ δ) ∘ δ。追踪将所有三个复制推入右边的嵌套中，并应用余关联性 ([Key])，其中共轭的内部编织在余交换性下消失 ([Inner])，然后返回下来 ([Key2])。
*)
Lemma copy_copy {x : C} :
  copy[(x ⨂ x)%object] ∘ copy[x] ≈ (copy[x] ⨂ copy[x]) ∘ copy[x].
Proof.
  rewrite copy_tensor.
  (*
 The α-normalized two-fold copy: all three copies pushed into the
 right-hand nest. 

 --------
 α-归一化的两倍拷贝：所有三个拷贝都被推入右侧巢穴。
*)
  assert (Key : to (@tensor_assoc C _ x x (x ⨂ x)%object)
                  ∘ ((copy[x] ⨂ copy[x]) ∘ copy[x])
                  ≈ (id[x] ⨂ ((id[x] ⨂ copy[x]) ∘ copy[x])) ∘ copy[x]).
  { rewrite <- (bimap_id_left_right (copy x) (copy x)).
    rewrite <- (@bimap_id_id C C C (@tensor C _) x x).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to tensor_assoc)).
    rewrite <- to_tensor_assoc_natural.
    rewrite <- comp_assoc.
    rewrite copy_coassoc_to.
    rewrite comp_assoc.
    rewrite <- bimap_comp_id_left.
    reflexivity. }
  (* Its inverse form, for coming back down. / 它的逆向形式，用于返回下降。 *)
  assert (Key2 : (@tensor_assoc C _ x x (x ⨂ x)%object)⁻¹
                   ∘ ((id[x] ⨂ ((id[x] ⨂ copy[x]) ∘ copy[x])) ∘ copy[x])
                   ≈ (copy[x] ⨂ copy[x]) ∘ copy[x]).
  { rewrite bimap_comp_id_left.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (tensor_assoc⁻¹)).
    rewrite <- from_tensor_assoc_natural.
    rewrite bimap_id_id.
    rewrite <- comp_assoc.
    rewrite <- copy_coassoc.
    rewrite comp_assoc.
    rewrite bimap_id_left_right.
    reflexivity. }
  (* Conjugating the inner braid by the associators fixes the nest: cocommutativity. / 通过结合子对内部编织进行共轭固定巢：共交换性。 *)
  assert (Inner : to (@tensor_assoc C _ x x x)
                    ∘ ((braid ⨂ id[x])
                         ∘ ((@tensor_assoc C _ x x x)⁻¹
                              ∘ ((id[x] ⨂ copy[x]) ∘ copy[x])))
                    ≈ (id[x] ⨂ copy[x]) ∘ copy[x]).
  { rewrite <- copy_coassoc.
    rewrite (comp_assoc (braid ⨂ id[x])).
    rewrite <- bimap_comp_id_right.
    rewrite copy_cocomm.
    apply copy_coassoc_to. }
  rewrite <- comp_assoc.
  unfold mid_swap_inv.
  rewrite <- !comp_assoc.
  rewrite Key.
  rewrite (comp_assoc (id[x] ⨂ (@tensor_assoc C _ x x x)⁻¹)).
  rewrite <- bimap_comp_id_left.
  rewrite (comp_assoc (id[x] ⨂ (braid ⨂ id[x]))).
  rewrite <- bimap_comp_id_left.
  rewrite (comp_assoc (id[x] ⨂ to (@tensor_assoc C _ x x x))).
  rewrite <- bimap_comp_id_left.
  rewrite Inner.
  apply Key2.
Qed.

(* The ε-square of copy: the counit laws. / 拷贝的ε平方：余单位律。 *)
Lemma discard_copy {x : C} :
  discard[(x ⨂ x)%object] ∘ copy[x] ≈ discard[x].
Proof.
  rewrite discard_tensor.
  rewrite <- (bimap_id_left_right (discard x) (discard x)).
  rewrite <- !comp_assoc.
  rewrite copy_counit_left.
  rewrite from_unit_left_natural.
  rewrite comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Theorem deterministic_copy {x : C} : deterministic (copy x).
Proof.
  split.
  - exact copy_copy.
  - exact discard_copy.
Qed.

(* The δ-square of discard: both sides are the counit pushed through the left unitor. / 丢弃的 δ-方：两边都是通过左单位器作用的余单位。 *)
Lemma copy_discard {x : C} :
  copy[I] ∘ discard[x] ≈ (discard[x] ⨂ discard[x]) ∘ copy[x].
Proof.
  rewrite copy_unit.
  rewrite <- (bimap_id_left_right (discard x) (discard x)).
  rewrite <- comp_assoc.
  rewrite copy_counit_left.
  rewrite from_unit_left_natural.
  reflexivity.
Qed.

(* The ε-square of discard: the unit coherence. / 舍弃的ε平方：单位相干性。 *)
Lemma discard_discard {x : C} :
  discard[I] ∘ discard[x] ≈ discard[x].
Proof.
  rewrite discard_unit.
  apply id_left.
Qed.

Theorem deterministic_discard {x : C} : deterministic (discard x).
Proof.
  split.
  - exact copy_discard.
  - exact discard_discard.
Qed.

(* * *** The structural isomorphisms are deterministic / * *** 结构同构是确定性的 *)

(* Braiding: the δ-square is the interchange/braid compatibility, the ε-square degenerates through [braid_I_I]. / 编织：δ-方形是交换/编织兼容性，ε-方形通过 [braid_I_I] 退化。 *)

Lemma copy_braid {x y : C} :
  copy[(y ⨂ x)%object] ∘ braid ≈ (braid ⨂ braid) ∘ copy[(x ⨂ y)%object].
Proof.
  rewrite !copy_tensor.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite (comp_assoc (mid_swap_inv y x)).
  rewrite mid_swap_inv_braid.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma discard_braid {x y : C} :
  discard[(y ⨂ x)%object] ∘ braid ≈ discard[(x ⨂ y)%object].
Proof.
  rewrite !discard_tensor.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_I_I.
  rewrite id_right.
  reflexivity.
Qed.

Theorem deterministic_braid {x y : C} : deterministic (@braid C _ x y).
Proof.
  split.
  - exact copy_braid.
  - exact discard_braid.
Qed.

(* Left unitor. / 左单位元 *)

Lemma copy_unitor_left {x : C} :
  copy[x] ∘ unit_left
    ≈ (unit_left ⨂ unit_left) ∘ copy[(I ⨂ x)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_left_natural.
  rewrite <- (bimap_id_right_left ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_left.
Qed.

Lemma discard_unitor_left {x : C} :
  discard[x] ∘ unit_left ≈ discard[(I ⨂ x)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_left_natural.
  reflexivity.
Qed.

Theorem deterministic_unit_left_to {x : C} :
  deterministic (to (@unit_left C _ x)).
Proof.
  split.
  - exact copy_unitor_left.
  - exact discard_unitor_left.
Qed.

Theorem deterministic_unit_left_from {x : C} :
  deterministic ((@unit_left C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_left_to). Qed.

(* Right unitor. / 右单位元 *)

Lemma copy_unitor_right {x : C} :
  copy[x] ∘ unit_right
    ≈ (unit_right ⨂ unit_right) ∘ copy[(x ⨂ I)%object].
Proof.
  rewrite copy_tensor.
  rewrite copy_unit.
  rewrite to_unit_right_natural.
  rewrite <- (bimap_id_left_right ((@unit_left C _ I)⁻¹) (copy x)).
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  apply mid_swap_inv_unit_right.
Qed.

Lemma discard_unitor_right {x : C} :
  discard[x] ∘ unit_right ≈ discard[(x ⨂ I)%object].
Proof.
  rewrite discard_tensor.
  rewrite discard_unit.
  rewrite to_unit_right_natural.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_unit_right_to {x : C} :
  deterministic (to (@unit_right C _ x)).
Proof.
  split.
  - exact copy_unitor_right.
  - exact discard_unitor_right.
Qed.

Theorem deterministic_unit_right_from {x : C} :
  deterministic ((@unit_right C _ x)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_unit_right_to). Qed.

(* Associator: the δ-square is the associativity hexagon of the interchange, the ε-square a triangle-and-Kelly computation. / 关联器：δ平方是交换的结合六边形，ε平方是三角-凯利计算。 *)

Lemma copy_tensor_assoc {x y z : C} :
  copy[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ (to tensor_assoc ⨂ to tensor_assoc) ∘ copy[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !copy_tensor.
  assert (E1 : (copy x ⨂ (mid_swap_inv y z ∘ (copy y ⨂ copy z)))
                 ≈ (id[(x ⨂ x)%object] ⨂ mid_swap_inv y z)
                     ∘ (copy x ⨂ (copy y ⨂ copy z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((mid_swap_inv x y ∘ (copy x ⨂ copy y)) ⨂ copy z)
                 ≈ (mid_swap_inv x y ⨂ id[(z ⨂ z)%object])
                     ∘ ((copy x ⨂ copy y) ⨂ copy z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (copy x) (copy y) (copy z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  apply mid_swap_inv_assoc.
Qed.

Lemma discard_tensor_assoc {x y z : C} :
  discard[(x ⨂ (y ⨂ z))%object] ∘ to tensor_assoc
    ≈ discard[((x ⨂ y) ⨂ z)%object].
Proof.
  rewrite !discard_tensor.
  assert (E1 : (discard x ⨂ (unit_left ∘ (discard y ⨂ discard z)))
                 ≈ (id[I] ⨂ to (@unit_left C _ I))
                     ∘ (discard x ⨂ (discard y ⨂ discard z))).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E1; clear E1.
  assert (E2 : ((unit_left ∘ (discard x ⨂ discard y)) ⨂ discard z)
                 ≈ (to (@unit_left C _ I) ⨂ id[I])
                     ∘ ((discard x ⨂ discard y) ⨂ discard z)).
  { rewrite <- bimap_comp.
    rewrite id_left.
    reflexivity. }
  rewrite E2; clear E2.
  spose (to_tensor_assoc_natural (discard x) (discard y) (discard z)) as X.
  rewrite <- !comp_assoc.
  rewrite X; clear X.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  rewrite <- unit_identity.
  reflexivity.
Qed.

Theorem deterministic_tensor_assoc_to {x y z : C} :
  deterministic (to (@tensor_assoc C _ x y z)).
Proof.
  split.
  - exact copy_tensor_assoc.
  - exact discard_tensor_assoc.
Qed.

Theorem deterministic_tensor_assoc_from {x y z : C} :
  deterministic ((@tensor_assoc C _ x y z)⁻¹).
Proof. exact (deterministic_iso_from _ deterministic_tensor_assoc_to). Qed.

(* * *** The wide deterministic subcategory [Det] (Fritz §10) / * *** 宽确定性子类别 [Det] （Fritz §10） *)

Program Definition DeterministicSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => deterministic f;
  scomp := fun _ _ _ _ _ _ _ _ df dg => deterministic_comp df dg;
  sid   := fun _ _ => deterministic_id
|}.

Definition Det : Category := Sub C DeterministicSub.

Lemma Det_wide : Wide C DeterministicSub.
Proof. intro x; exact ttt. Qed.

(*
 The inclusion Det ⟶ C is the generic (faithful) [Incl C DeterministicSub]
 from Construction/Subcategory.v. 

 --------
 包含 Det ⟶ C 是 Construction/Subcategory.v 中的通用（忠实）[Incl C DeterministicSub]。
*)

End Deterministic.
