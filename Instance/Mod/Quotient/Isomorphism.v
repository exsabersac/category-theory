Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The module isomorphism theorems, from the universal property

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.1
   Exercise 5 (printed p. 59, PDF p. 68) [maclane:III.1:ex5].
   nLab: https://ncatlab.org/nlab/show/isomorphism+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Isomorphism_theorems

   Mac Lane's point at §III.1 is that the isomorphism theorems follow
   from the universality of the projection ALONE, without a second look
   at cosets.  This file takes that seriously, and the honest accounting
   of how far it goes is the first thing below, because “derived from
   universality” is a claim about the SHAPE of a proof and is easy to
   assert falsely.  The grading is the same as
   Instance/Grp/Quotient/Isomorphism.v's and is repeated rather than
   cited, because the proofs here are not that file's proofs.

   HOW EACH THEOREM IS ACTUALLY OBTAINED.

   The comparisons for the FIRST and THIRD are produced by ONE
   mechanism: [universal_element_iso] (Theory/Universal/Element.v),
   which turns two universal elements of the SAME functor into an
   isomorphism of their carriers, together with its uniqueness clause
   [universal_element_iso_unique]; neither is built by exhibiting
   mutually inverse maps and checking round trips.  The SECOND is not of
   that form and this header does not pretend otherwise.  What differs
   between the three is the cost of exhibiting the SECOND universal
   element:

   - THIRD ([mod_third_isomorphism_theorem], (M/S)/(T/S) ≅ M/T).  A pure
   universal-property chase, and the cleanest of the three:
   [mquot_universal_T_over_S] derives the second universal element
   from [mquot_universal_element T] and [mquot_proj_epic S] by
   composing and cancelling [mquot_proj S] on the right.  THE STEPS
   THAT CARRY ELEMENTWISE CONTENT -- not every step that MENTIONS
   an element, since several obligations bind an element variable
   and then never inspect it -- and none of them destructures one: [mquot_step_kills] and
   [mod_third_precompose_kills], which say respectively that the
   comparison kills T/S and that k ∘ p_S kills T -- both are
   [mquot_rel_zero_iff] or the given killing hypothesis applied at
   a variable, and both are unavoidable in any formulation, since
   “kills” is an elementwise predicate BY DEFINITION -- and the
   `≈`-saturation obligation of [TmodS], which is the only one that
   COMPUTES with elements and which is a prerequisite to STATING
   the theorem rather than a step in proving it.  No coset is
   manipulated and no representative is chosen.

   - FIRST ([mod_first_isomorphism_theorem], M/ker f ≅ im f).  The second
   universal element ([mod_image_universal_element]) is exhibited
   directly, and the mediator [mod_image_med] READS A PREIMAGE out
   of the image-membership witness -- [mod_image_med_wd] being what
   makes that well defined.  The witness is DATA ([ImageSubmod]'s
   membership is a sigma), so nothing is chosen, but an element IS
   destructured, which is the honest difference from the third.
   It is fair to call this a
   universal-property derivation of the ISOMORPHISM whose input is
   an elementwise construction of the comparison universal element.
   Nothing shortens that input: the image is DEFINED elementwise, as
   a submodule of the codomain, so any map out of it must consume a
   membership witness.

   - SECOND ([mod_second_isomorphism_theorem], S/(S ∩ T) ≅ (S + T)/T).  A
   COROLLARY of the first, in the textbook manner: the composite
   S ↪ S + T ↠ (S + T)/T is surjective with kernel S ∩ T.  Its two
   elementwise inputs are named and proved separately
   ([mod_psi_kernel_is_meet], [mod_psi_surjective]).  Downstream of those
   two the argument is again universality -- BUT read the
   composition honestly: this theorem is
   [mod_first_isomorphism_theorem mod_psi] composed with
   [mod_surjective_image_iso], and THAT one IS built as an inverse pair
   with two round trips, as is [mquot_congr]
   (Instance/Mod/Quotient.v) which the literal form composes with.
   Both are degenerate as inverse pairs -- every leg the identity on
   underlying elements, every round trip [reflexivity] or
   [mquot_rel_refl] -- but they are not instances of
   [universal_element_iso], and the claim above is scoped to the
   comparisons, not to every isomorphism this file names.

   So: one theorem is a pure chase, one has an elementwise construction
   of its comparison object, and one is a corollary of that plus two
   identity-carrier repackagings.  NONE of them manipulates cosets, for
   the structural reason that the setoid quotient of
   Instance/Mod/Quotient.v forms no coset object at all -- but that is a
   property of the PRESENTATION, and the elementwise steps above would
   still be elementwise in any presentation.

   WHERE THE MODULE CASE IS GENUINELY CHEAPER THAN THE GROUP CASE, and
   it is not a matter of degree.  Instance/Grp/Quotient/Isomorphism.v
   needs [product_shuffle] and [inverse_shuffle] -- two normality
   manipulations, associativity chains of four and five rewrites
   respectively -- to make [SubgroupProduct] closed under product and
   inverse, and it must require its second argument to be a NORMAL
   subgroup for the product to be a subgroup at all.  Here
   [SubmoduleSum] takes TWO arbitrary submodules, closure under
   addition is one commutativity shuffle, closure under negation is
   not even a field, and the SUM is symmetric in its two arguments
   ([SubmoduleSum_comm], at the level of membership) in a way the
   group product cannot be.  Nothing in this file conjugates
   anything.

   WHAT IS DELIVERED.  The image of a homomorphism as an object with its
   corestriction; the first isomorphism theorem with its uniqueness
   clause and the epi-mono mod_factorization; the third with its uniqueness
   clause; the second over an explicit [SubmoduleSum]; and non-vacuity
   witnesses at ℤ for all three.

   WHAT IS NOT DELIVERED.  No fourth (“correspondence”/lattice) theorem;
   no modular law; no butterfly lemma; no exact sequences; and no
   naturality of the isomorphisms in f, S or T.  The second theorem's
   two universal elements are not compared by a uniqueness clause, it
   being a composite of three isomorphisms rather than a single
   comparison. 

   --------
   * * 模块同构定理，来自泛性质

   Mac Lane，《工作数学家的范畴论》，第二版，第III.1节
   练习 5（印刷版第59页，PDF第68页） [maclane:III.1:ex5]。
   nLab：https://ncatlab.org/nlab/show/isomorphism+theorem
   维基百科：https://en.wikipedia.org/wiki/Isomorphism_theorems

   Mac Lane在第III.1节指出，同构定理仅仅从投射的普遍性就能得出，而无需再次考虑陪集。这个文件严肃对待这一点，并且下面首先给出了其取得的范围，因为“源自普遍性”是关于证明形式的声明，很容易被错误地断言。评分标准与Instance/Grp/Quotient/Isomorphism.v中的相同，并重复列出而不是引用，因为这里的证明不是那个文件的证明。

   每个定理实际的获得方式。对于第一和第三的比较，是由一个机制产生的：[universal_element_iso]（Theory/Universal/Element.v），它将两个具有相同函子的通用元件转化为它们载体的同构，并附带其唯一性条款 [universal_element_iso_unique]；两者都不是通过展示相互逆映射并检查往返来构建的。第二个不是这种形式，而且此标题并不假装它是。三者之间的不同在于展示第二个通用元件的成本：- 第三（[mod_third_isomorphism_theorem]，(M/S)/(T/S) ≅ M/T）。一个纯粹的通用性质追逐，也是三者中最干净的：
   [mquot_universal_T_over_S] 通过将 [mquot_proj S]  在右侧组合并抵消，从 [mquot_universal_element T] 和 [mquot_proj_epic S] 推导出第二个通用元素。逐步操作携带元素内容——并非每个提到元素的步骤，因为有几个义务会绑定一个元素变量然后从未检查它——且没有一个会进行解构：[mquot_step_kills] 和 [mod_third_precompose_kills]，分别说明比较会消除 T/S，以及 k ∘ p_S 会消除 T——两者都是 [mquot_rel_zero_iff] 或者在某个变量上应用的给定消除假设，并且在任何形式下都是不可避免的，因为“消除”按定义是一个元素级谓词——以及 [TmodS] 的 `≈` 饱和义务，这是唯一一个与元素进行计算的，并且是陈述定理的先决条件，而不是证明定理的步骤。没有操作任何伴随类，也没有选择任何代表。- 首先（[mod_first_isomorphism_theorem]，M/ker f ≅ im f）。第二个通用元素（[mod_image_universal_element]）被直接展示，并且中介者[mod_image_med]从像的隶属见证中读取一个原象——[mod_image_med_wd]就是使其定义良好的条件。这个见证是数据（[ImageSubmod]的隶属是一个σ），所以没有选择任何元素，而是一个元素被解构，这是与第三种情况的真正区别。称之为同构的通用性质推导是合理的，其输入是对比通用元素的逐元素构造。没有任何东西缩短了该输入：像是逐元素定义的，作为陪域的子模，因此从中映射任何映射都必须使用一个隶属见证。- 第二 ([mod_second_isomorphism_theorem], S/(S ∩ T) ≅ (S + T)/T)。按照教材的方式，这是第一定理的一个推论：复合映射 S ↪ S + T ↠ (S + T)/T 是满射，其核为 S ∩ T。其两个元素级输入被分别命名并证明 ([mod_psi_kernel_is_meet], [mod_psi_surjective])。在这两个输入之后，论证再次使用了普遍性——但要如实地阅读该复合：该定理是 [mod_first_isomorphism_theorem mod_psi] 与 [mod_surjective_image_iso] 的复合，而 [mod_surjective_image_iso] 是作为逆对构建的，带有两次往返，[mquot_congr] (Instance/Mod/Quotient.v) 也是如此，其字面形式可以进行组合。两者作为逆对都是退化的——对底层元素的每条引理都是恒等映射，每次往返 [reflexivity] 或 [mquot_rel_refl] ——但它们不是 [universal_element_iso] 的实例，上述主张的范围是比较，而不是本文件命名的每个同构。

   因此：一个定理是纯追踪，一个定理具有其比较对象的按元素构造，一个定理是该定理加上两个恒等承载重新包装的推论。它们都不操作余类，其结构原因是 Instance/Mod/Quotient.v 的集合商根本不形成余类对象——但这是表示的问题，上述按元素的步骤在任何表示中仍然是按元素进行的。当模块情况确实比群情况便宜时，并且这不是程度问题。Instance/Grp/Quotient/Isomorphism.v 需要 [product_shuffle] 和 [inverse_shuffle] —— 两个正规性操作，分别是四步和五步重写的结合性链 —— 以使 [SubgroupProduct] 在乘积和逆元下封闭，并且它必须要求其第二个参数是一个正规子群，乘积才能成为子群。在这里，[SubmoduleSum] 取两个任意子模块，加法封闭是一种交换重排，关于取负封闭甚至不是一个域，并且它的和在两个参数（[SubmoduleSum_comm]，在元素级别）中是对称的，而群乘积无法实现这一点。这个文件中没有任何东西会共轭任何东西。交付内容：同态的像作为一个带核心限制的对象；第一同构定理及其唯一性条款以及正射-单射模分解；第三同构定理及其唯一性条款；第二同构定理在一个明确的 [SubmoduleSum] 上的情况；以及三个定理在 ℤ 上的非空见证。

   未交付内容：没有第四个（“对应”/格）定理；没有模律；没有蝴蝶引理；没有正合列；也没有 f、S 或 T 中同构的自然性。第二定理的两个普遍元素没有通过唯一性条款进行比较，它是三个同构的复合，而不是单一比较。
*)

(* * ** The image of a homomorphism, as an object of [RMod R] / * ** 作为 [RMod R] 对象的同态的像 *)

Definition ImageMod {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModObject R := SubmoduleMod (ImageSubmod f).

(* The corestriction of f to its image: the same map, carrying its own witness. / 将 f 限制到它的像：同一个映射，携带它自己的证明。 *)
Program Definition mod_image_cores {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : M ~{RMod R}~> ImageMod f := {|
  rm_hom := {| cmon_map := {| morphism := fun a : carrier (cmon_setoid M) =>
      existT _ (cmon_map (rm_hom f) a) (existT _ a (reflexivity _)) |} |}
|}.
Next Obligation. intros R M N f a b Hab; simpl; now rewrite Hab. Qed.
Next Obligation.
  intros R M N f; simpl; apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f a b; simpl; apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation. intros R M N f r a; simpl; apply (rm_map_smul f). Qed.

(*
 The inclusion of the image recovers f: the triangle
 f = (im f ↪ N) ∘ (M ↠ im f) holds pointwise by reflexivity, the
 corestriction changing no element. 

 --------
 图像的包含恢复了 f: 三角形
 f = (im f ↪ N) ∘ (M ↠ im f) 在每一点上都成立，由于自反性，余限制不改变任何元素。
*)
Lemma mod_image_factors {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  smod_incl (ImageSubmod f) ∘ mod_image_cores f ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

Lemma mod_image_cores_surjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective (mod_image_cores f).
Proof.
  intro p; simpl.
  exists (`1 (`2 p)); simpl.
  exact (`2 (`2 p)).
Qed.

(* A surjective homomorphism identifies its image with its codomain. The inverse map sends b to b together with its preimage witness, which is DATA, so nothing is chosen. / 一个满射同态将其像与其余域相对应。逆映射将 b 映射到 b 以及其原像证据，该证据是 DATA，所以没有任何被选择。 *)
Program Definition mod_surjective_image_iso {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) (Hs : RModSurjective f) :
  ImageMod f ≅[RMod R] N := {|
  to := smod_incl (ImageSubmod f);
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun b : carrier (cmon_setoid N) =>
         existT _ b (Hs b) |} |} |}
|}.
Next Obligation. intros R M N f Hs a b Hab; exact Hab. Qed.
Next Obligation. intros R M N f Hs; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a b; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs r a; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a; simpl; reflexivity. Qed.

(* * ** The image carries the second universal element / * ** 该图像包含第二个普遍元素 *)

Section ImageUniversal.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Lemma mod_image_cores_kills (a : carrier (cmon_setoid M)) :
  smod_mem (KernelSub f) a →
  cmon_map (rm_hom (mod_image_cores f)) a ≈ cmon_zero (ImageMod f).
Proof. intro Ha; simpl in *; exact Ha. Qed.

Definition mod_image_elem : MKills (KernelSub f) (ImageMod f) :=
  existT _ (mod_image_cores f) mod_image_cores_kills.

Section ImageMediator.

Context {K : RModObject R}.
Context (x : MKills (KernelSub f) K).

(*
 Well-definedness, isolated as one lemma: elements with the same image
 under f have the same image under the given map, because they differ
 by an element of ker f, which that map kills.  This is the ONE place
 an element is inspected, and everything the mediator owes is
 discharged from it.

 Isolating it is not tidiness -- it is what makes the construction
 independent of whether [ImageSubmod]'s closure obligations are
 transparent.  They are [Program] obligations and hence [Qed]-opaque,
 so the preimage witness that [ImageMod]'s operations carry does NOT
 reduce, and the zero, addition and scalar laws below cannot be closed
 by computation; they are closed by comparing f-images instead. 

 --------
 良定义性，被孤立为一个引理：在 f 下具有相同像的元素在给定映射下也具有相同的像，因为它们相差一个 f 的核中的元素，而该映射会消去这个元素。这是唯一检查元素的地方，并且调解者的所有责任都已从中解除。

 将其孤立不是整洁性——它使得构造独立于 [ImageSubmod] 的闭包义务是否透明。它们是 [Program] 的义务，因此对 [Qed] 是不透明的，所以 [ImageMod] 的操作所携带的原像证据不会简化，下面的零、加法和标量法则也不能通过计算闭合；它们是通过比较 f-像来闭合的。
*)
Lemma mod_image_med_wd (a b : carrier (cmon_setoid M)) :
  cmon_map (rm_hom f) a ≈ cmon_map (rm_hom f) b →
  cmon_map (rm_hom (`1 x)) a ≈ cmon_map (rm_hom (`1 x)) b.
Proof.
  intro Hab.
  apply (mkills_descends (KernelSub f) x).
  (*
 [mquot_rel] is the [inhabited] truncation of membership since the PR
 “algebraic carriers are sets” (2026-09-17), so one [constructor] is owed
 before the membership proof itself. 

 --------
 [mquot_rel] 是自 PR “代数承载是集合” (2026-09-17) 以来会员资格的 [inhabited] 截断，因此在会员资格证明本身之前欠一个 [constructor]。
*)
  unfold mquot_rel; simpl.
  constructor.
  rewrite (ab_map_sub (rm_hom f) a b), Hab.
  apply ab_sub_self.
Qed.

Program Definition mod_image_med : ImageMod f ~{RMod R}~> K := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun p : carrier (cmon_setoid (ImageMod f)) =>
         cmon_map (rm_hom (`1 x)) (`1 (`2 p)) |} |}
|}.
Next Obligation.
  intros p q Hpq; simpl in *.
  apply mod_image_med_wd.
  rewrite (`2 (`2 p)), (`2 (`2 q)).
  exact Hpq.
Qed.
Next Obligation.
  simpl.
  transitivity (cmon_map (rm_hom (`1 x)) (cmon_zero M)).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (cmon_zero (ImageMod f)))); simpl.
    symmetry; apply (cmon_map_zero (rm_hom f)).
  - apply (cmon_map_zero (rm_hom (`1 x))).
Qed.
Next Obligation.
  intros p q; simpl.
  transitivity (cmon_map (rm_hom (`1 x))
                  (cmon_plus M (`1 (`2 p)) (`1 (`2 q)))).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (cmon_plus (ImageMod f) p q))).
    rewrite (cmon_map_plus (rm_hom f)).
    now rewrite (`2 (`2 p)), (`2 (`2 q)).
  - apply (cmon_map_plus (rm_hom (`1 x))).
Qed.
Next Obligation.
  intros r p; simpl.
  transitivity (cmon_map (rm_hom (`1 x)) (rm_smul M r (`1 (`2 p)))).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (rm_smul (ImageMod f) r p))).
    rewrite (rm_map_smul f).
    now rewrite (`2 (`2 p)).
  - apply (rm_map_smul (`1 x)).
Qed.

Lemma mod_image_med_commutes : mod_image_med ∘ mod_image_cores f ≈ `1 x.
Proof. intro a; simpl; reflexivity. Qed.

Lemma mod_image_med_unique (v : ImageMod f ~{RMod R}~> K)
  (Hv : v ∘ mod_image_cores f ≈ `1 x) : mod_image_med ≈ v.
Proof.
  intro p; simpl.
  transitivity (cmon_map (rm_hom v)
                  (cmon_map (rm_hom (mod_image_cores f)) (`1 (`2 p)))).
  - symmetry; exact (Hv (`1 (`2 p))).
  - apply proper_morphism; simpl.
    exact (`2 (`2 p)).
Qed.

End ImageMediator.

(*
 ⟨im f, corestriction⟩ is a universal element of the SAME functor of
 which ⟨M/ker f, projection⟩ is one. 

 --------
 ⟨im f, corestriction⟩ 是同一函子（SAME functor）的一个普遍元，其中 ⟨M/ker f, projection⟩ 也是其一个元。
*)
Program Definition mod_image_universal_element :
  AUniversalElement (MKillsFunctor (KernelSub f)) (ImageMod f) := {|
  aue_elem := mod_image_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := mod_image_med x |}.
  - exact (mod_image_med_commutes x).
  - intros v Hv; simpl in *.
    exact (mod_image_med_unique x v Hv).
Defined.

End ImageUniversal.

(** ** The first isomorphism theorem / ** 第一个同构定理 *)

(*
 Two universal elements of one functor: [universal_element_iso] does
 the rest.  Nothing here builds a map or checks a round trip. 

 --------
 一个函子有两个通用元素：[universal_element_iso]做其余的。这里没有构建映射或检查往返。
*)
Definition mod_first_isomorphism_theorem {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  QuotientMod (KernelSub f) ≅[RMod R] ImageMod f :=
  universal_element_iso (mquot_universal_element (KernelSub f))
                        (mod_image_universal_element f).

Lemma mod_first_isomorphism_triangle {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    ≈ mod_image_cores f.
Proof.
  exact (ue_med_commutes (mquot_universal_element (KernelSub f))
                         (mod_image_universal_element f)).
Qed.

(*
 BOTH LEGS ARE THE TWO MEDIATORS, by convertibility -- the [eq_refl]
 exception to the `≈` discipline.  [ue_med] is
 [unique_obj (aue_universal U1 (aue_elem U2))]
 (Theory/Universal/Element.v), and since both universal elements
 above were built with their mediators as [unique_obj], the generic
 machinery rebuilds neither map.  The strict form was tried FIRST and
 holds; the boundary that does NOT hold strictly is the mediator's
 triangle, which is `≈` and not Leibniz (pinned in
 Test/ProbeModQuotient.v). 

 --------
 两条腿都是两个中介，通过可转换性——[eq_refl]是`≈`规则的例外。[ue_med]是[unique_obj (aue_universal U1 (aue_elem U2))]（Theory/Universal/Element.v），并且由于上述两个通用元素是以它们的中介作为[unique_obj]构建的，所以通用机制不会重新构建任何映射。严格形式首先被尝试并成立；不严格成立的边界是中介的三角形，它是`≈`，而不是莱布尼茨（固定在Test/ProbeModQuotient.v中）。
*)
Example mod_first_isomorphism_to_is_mquot_med {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  to (mod_first_isomorphism_theorem f)
    = mquot_med (KernelSub f) (mod_image_elem f).
Proof. reflexivity. Qed.

Example mod_first_isomorphism_from_is_image_med {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  from (mod_first_isomorphism_theorem f)
    = mod_image_med f (mquot_elem (KernelSub f)).
Proof. reflexivity. Qed.

(*
 UNIQUENESS, proved rather than cited: any isomorphism carrying the
 projection to the corestriction IS this one. 

 --------
 唯一性，经证明而非引用：任何将投射映射到余限制的同构都是这个同构。
*)
Theorem mod_first_isomorphism_unique {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N)
  (v : QuotientMod (KernelSub f) ≅[RMod R] ImageMod f)
  (Hv : to v ∘ mquot_proj (KernelSub f) ≈ mod_image_cores f) :
  mod_first_isomorphism_theorem f ≈ v.
Proof.
  exact (universal_element_iso_unique
           (mquot_universal_element (KernelSub f))
           (mod_image_universal_element f) v Hv).
Qed.

(* * ** The epi-mono mod_factorization / * ** 外层-单调 模因子分解 *)

Theorem mod_factorization {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  smod_incl (ImageSubmod f)
    ∘ to (mod_first_isomorphism_theorem f)
    ∘ mquot_proj (KernelSub f)
  ≈ f.
Proof.
  rewrite <- comp_assoc.
  rewrite (mod_first_isomorphism_triangle f).
  apply mod_image_factors.
Qed.

Theorem mod_factorization_epi {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic (mquot_proj (KernelSub f)).
Proof. apply mquot_proj_epic. Qed.

Theorem mod_factorization_mono {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Monic (smod_incl (ImageSubmod f)).
Proof. apply smod_incl_monic. Qed.

(* f is injective exactly when its kernel is trivial. / 当且仅当它的核是平凡的时候，f 是单射。 *)
Theorem mod_injective_iff_kernel_trivial {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  RModInjective f
    ↔ (∀ a : carrier (cmon_setoid M), smod_mem (KernelSub f) a →
         a ≈ cmon_zero M).
Proof.
  split.
  - intros Hinj a Ha; simpl in Ha.
    apply Hinj.
    rewrite Ha.
    symmetry; apply (cmon_map_zero (rm_hom f)).
  - intros Htriv a b Hab.
    apply (fst (ab_sub_eq_zero_iff M a b)).
    apply Htriv; simpl.
    rewrite (ab_map_sub (rm_hom f) a b), Hab.
    apply ab_sub_self.
Qed.

Theorem mod_monic_iff_kernel_trivial {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  Monic f ↔ (∀ a : carrier (cmon_setoid M), smod_mem (KernelSub f) a →
               a ≈ cmon_zero M).
Proof.
  split.
  - intro Hm.
    apply (fst (mod_injective_iff_kernel_trivial f)).
    exact (fst (rmod_monic_iff_injective f) Hm).
  - intro Ht.
    apply (snd (rmod_monic_iff_injective f)).
    exact (snd (mod_injective_iff_kernel_trivial f) Ht).
Qed.

(** ** The third isomorphism theorem / ** 第三同构定理 *)

Section Third.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S T : Submodule M).
Context (Hsub : ∀ a : carrier (cmon_setoid M), smod_mem S a → smod_mem T a).

(*
 T read as a submodule of M/S.  AN EARLIER REVISION said “the membership
 predicate is UNCHANGED; only the saturation law is new, since M/S's `≈` is
 coarser than M's.”  Since the PR “algebraic carriers are sets”
 (2026-09-17) the membership predicate is the TRUNCATION of T's, and that is
 forced by the same coarseness: M/S's `≈` is [mquot_rel S], which is itself
 the truncation of membership in S, so the saturation law asks to move a
 [Type]-valued membership along a [Prop]-valued congruence and cannot.
 Truncating this one predicate is exactly enough -- the witness is opened in
 a [Prop] goal and re-wrapped -- and everything downstream follows with one
 [constructor] or one [destruct].  The other three laws are still the very
 terms T carries, because M/S's zero, addition and action ARE M's. 

 --------
 T 被读取为 M/S 的一个子模块。早期的修订版本说“成员资格谓词保持不变；只有饱和律是新的，因为 M/S 的 `≈` 比 M 的粗。”自从 PR “代数承载体是集合”（2026-09-17）以来，成员资格谓词是 T 的截断，这也是由于相同的粗性所强制：M/S 的 `≈` 是 [mquot_rel S]，而 [mquot_rel S] 本身是 S 中成员资格的截断，所以饱和律要求沿着 [Prop] 值的同余移动一个 [Type] 值的成员资格，这是不可能的。截断这个唯一的谓词正好足够——在 [Prop] 的目标中打开见证并重新包装——之后所有下游内容都可以通过一个 [constructor] 或一个 [destruct] 来完成。其他三个定律仍然是 T 所承载的术语，因为 M/S 的零、加法和作用就是 M 的。
*)
Program Definition TmodS : Submodule (QuotientMod S) := {|
  smod_mem := fun a : carrier (cmon_setoid (QuotientMod S)) =>
                inhabited (smod_mem T a)
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Hab as [Hab], Ha as [Ha]; constructor.
  (* b ≈ a - (a - b), and both a and a - b lie in T / b ≈ a - (a - b)，并且 a 和 a - b 都在 T 中 *)
  apply (smod_at T (a := ab_sub M a (ab_sub M a b))).
  - unfold ab_sub.
    rewrite ab_neg_plus.
    rewrite (ab_neg_invol M b).
    rewrite <- cmon_plus_assoc.
    rewrite ab_neg_right.
    apply cmon_plus_zero_l.
  - exact (smod_sub T _ _ Ha (Hsub _ Hab)).
Qed.
Next Obligation. simpl; exact (inhabits (smod_zero T)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; constructor.
  exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *.
  destruct Ha as [Ha]; constructor.
  exact (smod_smul T _ _ Ha).
Qed.

(*
 The comparison M/S ↠ M/T: the identity function again, well defined
 because S ⊆ T. 

 --------
 比较 M/S ↠ M/T：恒等函数，再次是良定义的，因为 S ⊆ T。
*)
Program Definition mquot_step : QuotientMod S ~{RMod R}~> QuotientMod T := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun a : carrier (cmon_setoid (QuotientMod S)) => a |} |}
|}.
Next Obligation.
  intros a b Hab; simpl in Hab |- *.
  destruct Hab as [Hab]; constructor; exact (Hsub _ Hab).
Qed.
Next Obligation. simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros a b; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros r a; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_step_triangle : mquot_step ∘ mquot_proj S ≈ mquot_proj T.
Proof. intro a; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_step_kills (a : carrier (cmon_setoid (QuotientMod S))) :
  smod_mem TmodS a →
  cmon_map (rm_hom mquot_step) a ≈ cmon_zero (QuotientMod T).
Proof.
  intro Ha; simpl in *.
  destruct Ha as [Ha].
  exact (mquot_rel_of_mem T a Ha).
Qed.

Definition mquot_step_elem : MKills TmodS (QuotientMod T) :=
  existT _ mquot_step mquot_step_kills.

Section ThirdMediator.

Context {K : RModObject R}.
Context (x : MKills TmodS K).

(*
 ONE OF THE TWO ELEMENTWISE STEPS of this theorem, the other being
 [mquot_step_kills] as the header records: transferring the killing
 hypothesis across the projection.  A member of T is projected by p_S
 to a member of T/S -- definitionally, the membership predicates being
 the same and p_S the identity function -- so k ∘ p_S kills T. 

 --------
 本定理的两个逐元素步骤之一，另一个正如标题记录的 [mquot_step_kills]：将杀死假设通过投影传递。T 的一个成员通过 p_S 投影到 T/S 的一个成员——从定义上讲，成员谓词相同且 p_S 是恒等函数——因此 k ∘ p_S 杀死 T。
*)
Lemma mod_third_precompose_kills (a : carrier (cmon_setoid M)) :
  smod_mem T a →
  cmon_map (rm_hom (`1 x ∘ mquot_proj S)) a ≈ cmon_zero K.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  exact (`2 x a (inhabits Ha)).
Qed.

Definition mod_third_precompose : MKills T K :=
  existT _ (`1 x ∘ mquot_proj S) mod_third_precompose_kills.

Definition mod_third_med : QuotientMod T ~{RMod R}~> K :=
  mquot_med T mod_third_precompose.

(* Its triangle against the comparison map, obtained by cancelling the epimorphism p_S on the right -- no element inspected. / 它的三角形针对比较图，通过在右侧取消满射 p_S 得到——未检查任何元素。 *)
Lemma mod_third_med_commutes : mod_third_med ∘ mquot_step ≈ `1 x.
Proof.
  apply (epic (Epic := mquot_proj_epic S)).
  rewrite <- comp_assoc.
  rewrite mquot_step_triangle.
  exact (mquot_med_commutes T mod_third_precompose).
Qed.

Lemma mod_third_med_unique (v : QuotientMod T ~{RMod R}~> K)
  (Hv : v ∘ mquot_step ≈ `1 x) : mod_third_med ≈ v.
Proof.
  apply (mquot_med_unique T mod_third_precompose).
  rewrite <- mquot_step_triangle.
  rewrite comp_assoc.
  now rewrite Hv.
Qed.

End ThirdMediator.

Program Definition mquot_universal_T_over_S :
  AUniversalElement (MKillsFunctor TmodS) (QuotientMod T) := {|
  aue_elem := mquot_step_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := mod_third_med x |}.
  - exact (mod_third_med_commutes x).
  - intros v Hv; simpl in *.
    exact (mod_third_med_unique x v Hv).
Defined.

Definition mod_third_isomorphism_theorem :
  QuotientMod TmodS ≅[RMod R] QuotientMod T :=
  universal_element_iso (mquot_universal_element TmodS)
                        mquot_universal_T_over_S.

Lemma mod_third_isomorphism_triangle :
  to mod_third_isomorphism_theorem ∘ mquot_proj TmodS ≈ mquot_step.
Proof.
  exact (ue_med_commutes (mquot_universal_element TmodS)
                         mquot_universal_T_over_S).
Qed.

Theorem mod_third_isomorphism_unique
  (v : QuotientMod TmodS ≅[RMod R] QuotientMod T)
  (Hv : to v ∘ mquot_proj TmodS ≈ mquot_step) :
  mod_third_isomorphism_theorem ≈ v.
Proof.
  exact (universal_element_iso_unique (mquot_universal_element TmodS)
                                      mquot_universal_T_over_S v Hv).
Qed.

End Third.

Arguments TmodS {R M} S T Hsub.
Arguments mquot_step {R M} S T Hsub.
Arguments mod_third_isomorphism_theorem {R M} S T Hsub.
Arguments mod_third_isomorphism_unique {R M} S T Hsub.

(* * ** The second isomorphism theorem / * ** 第二同构定理 *)

Section Second.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S T : Submodule M).

(*
 The sum S + T, as a submodule.  Membership carries the decomposition
 as DATA, so the elementwise steps below read it back out with nothing
 chosen.  NOTE what is NOT here: the group case
 (Instance/Grp/Quotient/Isomorphism.v's [SubgroupProduct]) needs its
 second argument NORMAL and spends [product_shuffle] and
 [inverse_shuffle]; here both arguments are arbitrary submodules and
 closure is [ab_sub_plus]-style commutativity plus the derived
 [smod_neg]. 

 --------
 和 S + T 的和，作为子模。成员资格携带作为 DATA 的分解，因此下面的逐元素步骤会在没有选择的情况下把它读出来。注意这里没有的内容：群情况（Instance/Grp/Quotient/Isomorphism.v 的 [SubgroupProduct]）需要它的第二个参数 NORMAL 并使用 [product_shuffle] 和 [inverse_shuffle]；在这里两个参数都是任意子模，并且闭包是 [ab_sub_plus] 风格的交换性加上推导出的 [smod_neg]。
*)
Definition in_sum (x : carrier (cmon_setoid M)) : Type :=
  { s : carrier (cmon_setoid M) & { t : carrier (cmon_setoid M) &
      ((smod_mem S s * smod_mem T t) * (x ≈ cmon_plus M s t))%type } }.

Program Definition SubmoduleSum : Submodule M := {|
  smod_mem := in_sum
|}.
Next Obligation.
  intros a b Hab [s [t [Hst Ha]]].
  exists s, t; split; [ exact Hst | now rewrite <- Hab ].
Qed.
Next Obligation.
  exists (cmon_zero M), (cmon_zero M).
  split; [ split; [ exact (smod_zero S) | exact (smod_zero T) ] | ].
  symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros a b [s [t [[Hs Ht] Ha]]] [s' [t' [[Hs' Ht'] Hb]]].
  exists (cmon_plus M s s'), (cmon_plus M t t').
  split.
  - split.
    + exact (smod_plus S _ _ Hs Hs').
    + exact (smod_plus T _ _ Ht Ht').
  - rewrite Ha, Hb.
    (*
 (s + t) + (s' + t') ≈ (s + s') + (t + t'): commutativity, and
 nothing else. 

 --------
 (s + t) + (s' + t') ≈ (s + s') + (t + t'): 交换律，仅此而已。
*)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity |].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [| reflexivity ].
    apply cmon_plus_comm.
Qed.
Next Obligation.
  intros r a [s [t [[Hs Ht] Ha]]].
  exists (rm_smul M r s), (rm_smul M r t).
  split.
  - split.
    + exact (smod_smul S _ _ Hs).
    + exact (smod_smul T _ _ Ht).
  - rewrite Ha.
    apply rm_smul_distr_l.
Qed.

Lemma T_in_sum (t : carrier (cmon_setoid M)) :
  smod_mem T t → smod_mem SubmoduleSum t.
Proof.
  intro Ht.
  exists (cmon_zero M), t.
  split; [ split; [ exact (smod_zero S) | exact Ht ] | ].
  symmetry; apply cmon_plus_zero_l.
Qed.

(* T, read as a submodule of S + T. / T，被读作 S + T 的子模块。 *)
Program Definition TinSum : Submodule (SubmoduleMod SubmoduleSum) := {|
  smod_mem := fun p : carrier (cmon_setoid (SubmoduleMod SubmoduleSum)) =>
                smod_mem T (`1 p)
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *; exact (smod_resp T _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (smod_zero T). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *; exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *; exact (smod_smul T _ _ Ha).
Qed.

(* S, as a submodule of S + T -- the inclusion S ↪ S + T. / S，作为 S + T 的一个子模——包括映射 S ↪ S + T。 *)
Program Definition S_into_Sum :
  SubmoduleMod S ~{RMod R}~> SubmoduleMod SubmoduleSum := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : carrier (cmon_setoid (SubmoduleMod S)) =>
      existT _ (`1 p)
        (existT _ (`1 p) (existT _ (cmon_zero M)
           (pair (pair (`2 p) (smod_zero T))
                 (symmetry (cmon_plus_zero_r M (`1 p)))))) |} |}
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros p q; simpl; reflexivity. Qed.
Next Obligation. intros r p; simpl; reflexivity. Qed.

(* The composite S ↪ S + T ↠ (S + T)/T. / 复合 S ↪ S + T ↠ (S + T)/T。 *)
Definition mod_psi : SubmoduleMod S ~{RMod R}~> QuotientMod TinSum :=
  mquot_proj TinSum ∘ S_into_Sum.

(*
 ELEMENTWISE INPUT ONE: the kernel of ψ is S ∩ T -- as a biconditional
 on membership, not merely an inclusion. 

 --------
 逐元素输入一：ψ 的核是 S ∩ T —— 作为成员资格的双条件，而不仅仅是包含关系。
*)
Lemma mod_psi_kernel_is_meet (p : carrier (cmon_setoid (SubmoduleMod S))) :
  smod_mem (KernelSub mod_psi) p ↔ inhabited (smod_mem T (`1 p)).
Proof.
(*
 AN EARLIER REVISION stated the right-hand side as the bare
 [smod_mem T (`1 p)].  Since the PR “algebraic carriers are sets”
 (2026-09-17) the left-hand side is congruence to zero in a quotient, which
 is the [inhabited] truncation of membership, so the biconditional holds up
 to that truncation and is stated so.  Both directions are [Prop]-to-[Prop]
 eliminations; [simpl] is what exposes the named relation, whose ascribed
 sort would otherwise be [Type]. 

 --------
 早期修订规定右侧为裸露
 [smod_mem T (`1 p)]。由于PR“代数载流子是集合”
 （2026-09-17）左边在商中与零同余，满足
 是成员关系的[inhabited]截断，因此双条件成立
 对该截断和 的描述。两方向均为 -to-[Prop] [Prop]
 消去;[simpl] 是揭示命名关系的部分，其归属于
 否则排序会[Type]。
*)
  split.
  - intro Hp; simpl in Hp.
    destruct Hp as [Hp]; constructor.
    apply (smod_at T (a := ab_sub M (`1 p) (cmon_zero M))).
    + apply ab_sub_zero_r.
    + exact Hp.
  - intro Hp; simpl.
    destruct Hp as [Hp]; constructor.
    apply (smod_at T (a := `1 p)).
    + symmetry; apply ab_sub_zero_r.
    + exact Hp.
Qed.

(*
 ELEMENTWISE INPUT TWO: ψ is surjective.  Every member of S + T is
 s + t for data s ∈ S, t ∈ T, and s + t is congruent to s modulo T
 because s - (s + t) ≈ -t lies in T.  The group case needs one
 normality computation here; this needs none. 

 --------
 逐元素输入二：ψ 是满射。S + T 的每个成员都是 s + t，其中 s ∈ S，t ∈ T，并且 s + t 与 s 在模 T 意义下同余，因为 s - (s + t) ≈ -t 属于 T。群情况在这里需要一个正规性计算；而这个情况不需要。
*)
Lemma mod_psi_surjective : RModSurjective mod_psi.
Proof.
  intro q.
  destruct (`2 q) as [s [t [[Hs Ht] Hq]]].
  exists (existT _ s Hs).
  simpl.
  unfold mquot_rel; simpl.
  constructor.
  apply (smod_at T (a := ab_neg M t)).
  - rewrite Hq.
    unfold ab_sub.
    rewrite ab_neg_plus.
    rewrite <- cmon_plus_assoc.
    rewrite ab_neg_right.
    symmetry; apply cmon_plus_zero_l.
  - exact (smod_neg T _ Ht).
Qed.

(*
 Mac Lane §III.1 Exercise 5, second isomorphism theorem, as a corollary
 of the first: S/(S ∩ T) is S/ker ψ, which the first theorem identifies
 with im ψ, which surjectivity identifies with (S + T)/T. 

 --------
 Mac Lane 第 III.1 节 练习 5，第二同构定理，作为第一个同构定理的推论：S/(S ∩ T) 是 S/ker ψ，第一个定理将其与 im ψ 识别，而满射性则将其识别为 (S + T)/T。
*)
Definition mod_second_isomorphism_theorem :
  QuotientMod (KernelSub mod_psi) ≅[RMod R] QuotientMod TinSum :=
  iso_compose (mod_surjective_image_iso mod_psi mod_psi_surjective)
              (mod_first_isomorphism_theorem mod_psi).

(*
 S ∩ T, as a submodule of S: membership in T, read on elements of S.
 This is the literal left-hand side of the theorem.

 AN EARLIER REVISION wrote the predicate as the bare [smod_mem T (`1 p)].
 Since the PR “algebraic carriers are sets” (2026-09-17) it is the
 [inhabited] truncation of that, and the reason is the identification
 [mod_second_isomorphism_theorem_literal] makes: this submodule has to be
 coextensive with [KernelSub mod_psi], whose membership is congruence to
 zero in a quotient and hence already truncated.  Nothing is lost at the
 witnesses that matter -- the [Z] readbacks at the end of the file supply
 and consume the truncation with one [constructor] and one [destruct]. 

 --------
 S ∩ T，作为 S 的一个子模：属于 T，根据 S 中的元素来读取。 这是定理的字面左边。 

 早期的修订将谓词写成了单独的 [smod_mem T (`1 p)]。 自从“代数载体是集合”(2026-09-17) 的 PR 之后，它是那个的 [inhabited] 截断，而原因是 [mod_second_isomorphism_theorem_literal] 的识别：这个子模必须与 [KernelSub mod_psi] 共延，其成员资格在商中与零同余，因此已经被截断。在重要的见证者那里没有任何损失——文件末尾的 [Z] 读回提供并消耗了截断，同时有一个 [constructor] 和一个 [destruct]。
*)
Program Definition MeetSub : Submodule (SubmoduleMod S) := {|
  smod_mem := fun p : carrier (cmon_setoid (SubmoduleMod S)) =>
                inhabited (smod_mem T (`1 p))
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (smod_resp T _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (inhabits (smod_zero T)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; constructor; exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (smod_smul T _ _ Ha).
Qed.

(*
 The two membership transfers go through the truncation now: the kernel's
 membership is congruence to zero in a quotient, hence [inhabited].  In one
 direction that means wrapping with [inhabits]; in the other, opening the
 [inhabited] -- which is legitimate because [mquot_congr]'s own hypotheses
 land in [Prop]-valued memberships of the two quotients.  Neither direction
 loses a witness: [MeetSub]'s membership IS [inhabited (smod_mem T (`1 p))]
 on the nose, so the two transfers are the identity. 

 --------
 现在两个成员转移通过截断进行：核的成员在一个商中同余于零，因此是 [inhabited]。在一个方向上，这意味着使用 [inhabits] 进行封装；在另一个方向上，打开 [inhabited] ——这是合法的，因为 [mquot_congr] 自身的假设落在两个商的 [Prop] 值成员中。两个方向都没有丢失见证者：[MeetSub] 的成员恰好是 [inhabited (smod_mem T (`1 p))]，因此两个转移都是恒等映射。
*)
Definition mod_second_isomorphism_theorem_literal :
  QuotientMod MeetSub ≅[RMod R] QuotientMod TinSum :=
  iso_compose mod_second_isomorphism_theorem
    (mquot_congr MeetSub (KernelSub mod_psi)
       (fun p Hp => snd (mod_psi_kernel_is_meet p) Hp)
       (fun p Hp => fst (mod_psi_kernel_is_meet p) Hp)).

End Second.

Arguments SubmoduleSum {R M} S T.
Arguments TinSum {R M} S T.
Arguments MeetSub {R M} S T.
Arguments mod_psi {R M} S T.
Arguments mod_second_isomorphism_theorem {R M} S T.
Arguments mod_second_isomorphism_theorem_literal {R M} S T.

(*
 The sum is SYMMETRIC in its two arguments, which the group-level
 [SubgroupProduct] cannot be (there the second argument must be
 normal).  Both directions, at the level of membership. 

 --------
 该和在其两个参数中是对称的，而群级别的 [SubgroupProduct] 不能是（在那里第二个参数必须是正规）。在成员级别，两个方向都是如此。
*)
Lemma SubmoduleSum_comm {R : RingObject} {M : RModObject R}
  (S T : Submodule M) (x : carrier (cmon_setoid M)) :
  smod_mem (SubmoduleSum S T) x → smod_mem (SubmoduleSum T S) x.
Proof.
  intros [s [t [[Hs Ht] Hx]]].
  exists t, s.
  split; [ split; assumption |].
  rewrite Hx; apply cmon_plus_comm.
Qed.

(*
   * ** Non-vacuity at ℤ

   All three theorems above hold for every module, so nothing yet shows
   any of them is about a nondegenerate situation.  Instance/Mod.v's
   [Int_RMod] with the even integers (Instance/Mod/Quotient.v's
   [EvenSub]) supplies witnesses for each, and ℤ's setoid is Leibniz
   equality, so every check is a computation.  The multiples of 4 give
   the strictly smaller submodule the third theorem needs, and the
   multiples of 3 give a second submodule whose sum with [EvenSub] is
   everything -- so the second theorem is instantiated at a pair whose
   sum is NOT either summand. 

   --------
   * ** 在 ℤ 上的非空性

   上述所有三个定理对于每个模都是成立的，所以目前还没有任何迹象表明其中任何一个涉及非退化情况。Instance/Mod.v 中的 [Int_RMod] 与偶数（Instance/Mod/Quotient.v 中的 [EvenSub]）为每一个定理提供了实例，并且 ℤ 的集合等价是 Leibniz 等式，因此每个检查都是一次计算。4 的倍数提供了第三个定理所需的严格较小的子模，而 3 的倍数提供了第二个子模，其与 [EvenSub] 的和是整个集合——因此第二个定理在一个其和不是任一加数的对子上得到了实例。
*)

Definition FourSub_mem (a : Z) : Type := { k : Z & a = (4 * k)%Z }.

Program Definition FourSub : Submodule Int_RMod := {|
  smod_mem := FourSub_mem
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

Lemma four_in_even (a : Z) : smod_mem FourSub a → smod_mem EvenSub a.
Proof.
  intros [k Hk]; exists (2 * k)%Z; lia.
Qed.

(*
 4ℤ is STRICTLY smaller than 2ℤ, so the third theorem is applied to a
 proper inclusion. 

 --------
 4ℤ严格小于2ℤ，所以第三定理适用于一个真包含。
*)
Theorem four_in_even_strict : smod_mem FourSub 2%Z → False.
Proof. intros [k Hk]; lia. Qed.

Definition ThreeSub_mem (a : Z) : Type := { k : Z & a = (3 * k)%Z }.

Program Definition ThreeSub : Submodule Int_RMod := {|
  smod_mem := ThreeSub_mem
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

(* *** The first theorem at ℤ / *** 在整数集 ℤ 的第一个定理 *)

Definition Z_first_iso :
  QuotientMod (KernelSub (mquot_proj EvenSub))
    ≅[RMod Int_Ring] ImageMod (mquot_proj EvenSub) :=
  mod_first_isomorphism_theorem (mquot_proj EvenSub).

(* The kernel of the projection is exactly 2ℤ, in both directions, so the left-hand side really is ℤ/2ℤ. / 投影的核在两个方向上正好是2ℤ，因此左边确实是ℤ/2ℤ。 *)
(* Restated up to the truncation, in lockstep with Instance/Mod/Quotient.v's [mquot_proj_kernel]. / 重新表述直到截断，与 Instance/Mod/Quotient.v 的 [mquot_proj_kernel] 保持一致。 *)
Lemma Z_proj_kernel_is_EvenSub (a : Z) :
  smod_mem (KernelSub (mquot_proj EvenSub)) a ↔ inhabited (smod_mem EvenSub a).
Proof. exact (mquot_proj_kernel EvenSub a). Qed.

(* Nondegenerate: the image of the projection has two elements apart in its own setoid. / 非退化：投影的像在其自身的集合等价类中有两个不同的元素。 *)
Theorem Z_first_iso_nondegenerate :
  cmon_map (rm_hom (mod_image_cores (mquot_proj EvenSub))) 1%Z
    ≈ cmon_map (rm_hom (mod_image_cores (mquot_proj EvenSub))) 0%Z → False.
Proof.
  intro H.
  exact (Z_mod_2Z_not_collapsed H).
Qed.

(* *** The third theorem at ℤ: (ℤ/4ℤ)/(2ℤ/4ℤ) ≅ ℤ/2ℤ / *** ℤ 的第三定理: (ℤ/4ℤ)/(2ℤ/4ℤ) ≅ ℤ/2ℤ *)

Definition Z_third_iso :
  QuotientMod (TmodS FourSub EvenSub four_in_even)
    ≅[RMod Int_Ring] QuotientMod EvenSub :=
  mod_third_isomorphism_theorem FourSub EvenSub four_in_even.

(* Nondegenerate on the left: 1 is still apart from 0 in (ℤ/4ℤ)/(2ℤ/4ℤ). / 左侧非退化：在 (ℤ/4ℤ)/(2ℤ/4ℤ) 中，1 仍然与 0 不相同。 *)
Theorem Z_third_iso_nondegenerate :
  mquot_rel (TmodS FourSub EvenSub four_in_even) 1%Z 0%Z → False.
Proof.
  (*
 The membership equation is CONVERTIBLE to one about plain ℤ -- the
 [eq_refl] exception again -- and [exact] is what performs the
 conversion.  [rewrite] cannot: the subtraction here is taken in
 [QuotientMod FourSub] rather than in [Int_RMod], and although the
 two agree on every projection they are not the same term.

 THREE layers of intro pattern, not one: since the PR “algebraic carriers
 are sets” (2026-09-17) [mquot_rel] is [inhabited] of a membership, and
 [TmodS]'s own membership is [inhabited] of [EvenSub]'s, which is itself
 the sigma [ZEvenMod]. 

 --------
 成员关系方程可以转换为关于普通 ℤ 的方程——再次出现 [eq_refl] 异常——而 [exact] 执行转换。[rewrite] 无法做到：这里的减法是在 [QuotientMod FourSub] 中进行的，而不是在 [Int_RMod] 中，尽管两者在每个投影上都一致，但它们不是相同的项。

 三个层次的引入模式，而不是一个：由于 PR “代数载体是集合”（2026-09-17），[mquot_rel] 是某个成员的 [inhabited]，而 [TmodS] 自身的成员是 [EvenSub] 的 [inhabited]，这本身是 sigma [ZEvenMod]。
*)
  intros [[[k Hk]]].
  assert (Hz : (1 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

(*
 And the middle quotient is not the whole of ℤ/4ℤ either: 1 is not in
 2ℤ/4ℤ, while 2 is -- so the theorem is not being applied at a
 degenerate inclusion. 

 --------
 中间商也不是ℤ/4ℤ的全部：1不在2ℤ/4ℤ中，而2在——因此定理并不是在退化的包含下应用的。
*)
Theorem Z_third_middle_proper :
  smod_mem (TmodS FourSub EvenSub four_in_even) 1%Z → False.
Proof.
  intros [[k Hk]].
  assert (Hz : (1 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z_third_middle_nontrivial :
  smod_mem (TmodS FourSub EvenSub four_in_even) 2%Z.
Proof. constructor; exists 1%Z; reflexivity. Qed.

(* *** The second theorem at ℤ: 2ℤ/(2ℤ ∩ 3ℤ) ≅ (2ℤ + 3ℤ)/3ℤ / *** 在整数集 ℤ 的第二定理：2ℤ/(2ℤ ∩ 3ℤ) ≅ (2ℤ + 3ℤ)/3ℤ *)

Definition Z_second_iso :
  QuotientMod (KernelSub (mod_psi EvenSub ThreeSub))
    ≅[RMod Int_Ring] QuotientMod (TinSum EvenSub ThreeSub) :=
  mod_second_isomorphism_theorem EvenSub ThreeSub.

Definition Z_second_iso_literal :
  QuotientMod (MeetSub EvenSub ThreeSub)
    ≅[RMod Int_Ring] QuotientMod (TinSum EvenSub ThreeSub) :=
  mod_second_isomorphism_theorem_literal EvenSub ThreeSub.

(*
 The pair is nondegenerate in the way the theorem's hypotheses ask
 for.  NEITHER submodule contains the other: 2 is even and not a
 multiple of 3, 3 is a multiple of 3 and not even.  So the sum is
 strictly larger than both. 

 --------
 这个对在定理假设要求的方式下是非退化的。两个子模都不包含彼此：2是偶数但不是3的倍数，3是3的倍数但不是偶数。所以它们的和严格大于两者。
*)
Theorem EvenSub_not_in_ThreeSub : smod_mem ThreeSub 2%Z → False.
Proof. intros [k Hk]; lia. Qed.

Theorem ThreeSub_not_in_EvenSub : smod_mem EvenSub 3%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 1 lies in 2ℤ + 3ℤ (as 3 + (-2)), so the sum is all of ℤ and is strictly larger than either summand. / 1 位于 2ℤ + 3ℤ（因为 3 + (-2)），所以这个和是整个 ℤ，并且严格大于任意一个加数。 *)
Theorem one_in_sum : smod_mem (SubmoduleSum EvenSub ThreeSub) 1%Z.
Proof.
  exists (-2)%Z, 3%Z.
  split.
  - split.
    + exists (-1)%Z; reflexivity.
    + exists 1%Z; reflexivity.
  - reflexivity.
Qed.

(* Nondegenerate on the left: 2ℤ ∩ 3ℤ is 6ℤ, so 2 stays apart from 0 in 2ℤ/(2ℤ ∩ 3ℤ). / 在左侧非退化：2ℤ ∩ 3ℤ 是 6ℤ，所以 2 在 2ℤ/(2ℤ ∩ 3ℤ) 中远离 0。 *)
Theorem Z_second_iso_nondegenerate :
  mquot_rel (MeetSub EvenSub ThreeSub)
    (existT _ 2%Z (existT (fun k : Z => 2%Z = (2 * k)%Z) 1%Z eq_refl))
    (cmon_zero (SubmoduleMod EvenSub))
  → False.
Proof.
  (* Three layers: [mquot_rel] is [inhabited], [MeetSub]'s membership is [inhabited] of [ThreeSub]'s, and that is the sigma. / 三层：[mquot_rel] 是 [inhabited]，[MeetSub] 的成员是 [inhabited] 的 [ThreeSub]，这就是西格玛。 *)
  intros [[[k Hk]]].
  assert (Hz : (2 = 3 * k)%Z) by exact Hk.
  lia.
Qed.

(* And on the RIGHT: 1, read as an element of 2ℤ + 3ℤ, stays apart from 0 in (2ℤ + 3ℤ)/3ℤ. So both sides have at least two elements. / 在右边：1，作为2ℤ + 3ℤ的一个元素阅读，在(2ℤ + 3ℤ)/3ℤ中与0保持分离。因此两边至少都有两个元素。 *)
Definition Z_one_in_sum :
  carrier (cmon_setoid (SubmoduleMod (SubmoduleSum EvenSub ThreeSub))) :=
  existT _ 1%Z one_in_sum.

Theorem Z_second_iso_codomain_nondegenerate :
  mquot_rel (TinSum EvenSub ThreeSub) Z_one_in_sum
    (cmon_zero (SubmoduleMod (SubmoduleSum EvenSub ThreeSub)))
  → False.
Proof.
  (* Two layers: [mquot_rel] is [inhabited], and [TinSum]'s membership is the sigma. / 两层：[mquot_rel] 是 [inhabited]，而 [TinSum] 的成员是 sigma。 *)
  intros [[k Hk]].
  assert (Hz : (1 = 3 * k)%Z) by exact Hk.
  lia.
Qed.
