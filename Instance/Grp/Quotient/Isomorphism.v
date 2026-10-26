Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The isomorphism theorems, from the universal property

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §III.1
   Exercise 4 (printed p. 59) [maclane:III.1:ex4]; Awodey, “Category
   Theory”, 2nd ed., §4.2 Corollary 4.5 (printed p. 85)
   [awodey:4.2:cor5].
   nLab: https://ncatlab.org/nlab/show/isomorphism+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Isomorphism_theorems

   Mac Lane's point at §III.1 is that the isomorphism theorems follow
   from the universality of the projection ALONE, without a second look
   at cosets.  This file takes that seriously, and the honest accounting
   of how far it goes is the first thing below, because “derived from
   universality” is a claim about the SHAPE of a proof and is easy to
   assert falsely.

   HOW EACH THEOREM IS ACTUALLY OBTAINED, stated before the theorems so
   that no reader has to reverse-engineer it.

   The comparisons for the FIRST and THIRD are produced by ONE
   mechanism: [universal_element_iso] (Theory/Universal/Element.v),
   which turns two universal elements of the SAME functor into an
   isomorphism of their carriers, together with its uniqueness clause
   [universal_element_iso_unique]; neither of those two is built by
   exhibiting mutually inverse maps and checking round trips.  The
   SECOND is not of that form and this header does not pretend
   otherwise: it is the FIRST's comparison composed with two
   identity-carrier inverse pairs ([surjective_image_iso] below, and
   [quot_congr] in Instance/Grp/Quotient.v), each hand-built with
   explicit [to] and [from] and their round trips discharged.  Both are
   degenerate — every leg the identity on elements, every round trip
   reflexivity — but degenerate is not the same as absent, and the
   paragraphs below grade all three accordingly.  What differs between
   the three theorems is the cost of exhibiting the SECOND universal
   element:

   - THIRD ([third_isomorphism_theorem], (G/M)/(N/M) ≅ G/N).  A pure
   universal-property chase, and the cleanest of the three:
   [quot_universal_N_over_M] derives the second universal element
   from [quot_universal_element N] and [quot_proj_epic M] by
   composing and cancelling [quot_proj M] on the right, and inspects
   no element of any group.  Elementwise steps, exhaustively: the
   `≈`-saturation obligation of [NmodM], which is a prerequisite to
   STATING the theorem rather than a step in proving it, and
   [third_precompose_kills], which transfers the hypothesis “k kills
   N/M” to “k ∘ p_M kills N” and is unavoidable in any formulation,
   since “kills” is an elementwise predicate by definition.  No coset
   is manipulated and no representative is chosen.

   - FIRST ([first_isomorphism_theorem], G/ker h ≅ im h).  The second
   universal element ([image_universal_element]) is exhibited
   directly, and its descent step ([image_med_wd]) reads a preimage
   out of the image-membership witness.  That witness is DATA --
   Epi.v's [GrpImage] is a sigma -- so nothing is chosen, but an
   element IS inspected.  This is NOT a coset argument: no coset
   object exists anywhere in the construction, and the mediator's
   uniqueness is still the universal property's.  It is fair to call
   it a universal-property derivation of the ISOMORPHISM whose input
   is an elementwise construction of the comparison universal
   element.  Nothing shortens that input: the image is DEFINED
   elementwise, as a subgroup of the codomain, so any map out of it
   must consume a membership witness.

   - SECOND ([second_isomorphism_theorem], SN/N ≅ S/(S ∩ N)).  A
   COROLLARY of the first, in the textbook manner: the composite
   S ↪ SN ↠ SN/N is surjective with kernel S ∩ N.  Its two
   elementwise inputs are named and proved separately
   ([psi_kernel_is_meet], [psi_surjective]), and each is a single
   normality computation.  Downstream of those two lemmas the
   argument is again universality -- BUT read the composition
   honestly: this theorem is [first_isomorphism_theorem psi]
   composed with [surjective_image_iso], and THAT one IS built as an
   inverse pair with two round trips, as is [quot_congr]
   (Instance/Grp/Quotient.v) which the literal form
   [second_isomorphism_theorem_literal] composes with.  Both are
   degenerate as inverse pairs -- every leg is the identity on
   underlying elements and every round trip closes by [reflexivity]
   or [quot_rel_refl] -- but they are not instances of
   [universal_element_iso] and the claim above is scoped to the
   comparisons, not to every isomorphism this file names.

   So: one theorem is a pure chase, one has an elementwise construction
   of its comparison object, and one is a corollary of that plus two
   identity-carrier repackagings.  NONE of them manipulates cosets, for
   the structural reason that the setoid quotient of
   Instance/Grp/Quotient.v forms no coset object at all -- but the reader
   should note that this is a property of the PRESENTATION, and that the
   elementwise steps above would still be elementwise in any
   presentation.

   WHAT IS DELIVERED.  The image of a homomorphism as a subgroup of the
   codomain with its corestriction; the first isomorphism theorem
   together with Awodey's Corollary 4.5 (the factorization
   G ↠ G/ker h ≅ im h ↪ K, and h monic iff its kernel is trivial); the
   third; the second, over an explicit [SubgroupProduct]; and non-vacuity
   witnesses at S3 for all three.

   UNIQUENESS is proved, not merely available: [first_isomorphism_unique]
   and [third_isomorphism_unique] say that any isomorphism carrying the
   one universal element to the other IS the comparison.  The second
   theorem has no such clause, being a composite of three isomorphisms
   rather than a single comparison.

   WHAT IS NOT DELIVERED.  No fourth (“correspondence”/lattice) theorem;
   no Zassenhaus, Schreier or Jordan-Hölder; no butterfly lemma; and no
   naturality of the isomorphisms in h, S or N.  The second theorem is
   stated as S/(S ∩ N) ≅ SN/N ([second_isomorphism_theorem_literal]),
   the mirror of the orientation the issue writes; isomorphism being
   symmetric, no separate statement is given for the other reading. 

   --------
   * * 从泛性质出发的同构定理

   Mac Lane，《为工作中的数学家准备的范畴》，第2版，§III.1
   练习4（印刷第59页）[maclane:III.1:ex4]；Awodey，《范畴论》，第2版，§4.2 推论4.5（印刷第85页）[awodey:4.2:cor5]。
   nLab：https://ncatlab.org/nlab/show/isomorphism+theorem
   维基百科：https://en.wikipedia.org/wiki/Isomorphism_theorems

   Mac Lane在§III.1中的观点是，同构定理仅从投影的普遍性就可以得到，而无需再次查看陪集。这个文件认真对待了这一点，并且下面首先说明它能够达到的程度，因为“从普遍性导出”是关于证明形态的说法，很容易被错误地断言。

   每个定理是如何实际获得的，在定理前陈述，以便读者不必逆向推理。第一个和第三个的比较是由一个机制产生的：[universal_element_iso]（Theory/Universal/Element.v），它将两个相同函子的通用元素转化为其承载的同构，并附带其唯一性条款[universal_element_iso_unique]；这两者都不是通过展示相互逆映射并检查往返步骤来构建的。第二个不是这种形式，并且这个标题也不假装是：它是第一个的比较，与两个身份承载逆对（如下的[surjective_image_iso]，以及Instance/Grp/Quotient.v中的[quot_congr]）组合，每个都是通过显式的[to]和[from]以及它们的往返步骤手工构建的。两者都是退化的——每条边在元素上都是恒等，每次往返都是自反的——但退化并不等同于不存在，下面的段落对所有三个进行了相应的评分。三条定理之间的区别在于展示第二个全称元素的成本：- 第三（[third_isomorphism_theorem]，(G/M)/(N/M) ≅ G/N）。一个纯粹的通用性质推导，也是三者中最干净的：[quot_universal_N_over_M]通过在右侧组合并消去[quot_proj M]，从[quot_universal_element N]和[quot_proj_epic M]导出第二个通用元素，并且不检查任何群的元素。按元素的步骤，详尽无遗：[NmodM]的`≈`-饱和义务，这是陈述定理的前提，而不是证明定理的步骤，以及[third_precompose_kills]，它将假设“k消去N/M”转移为“k ∘ p_M消去N”，在任何表述中都是不可避免的，因为根据定义，“消去”是按元素的谓词。没有操作任何陪集，也没有选择任何代表。- 首先 ([first_isomorphism_theorem]，G/ker h ≅ im h)。第二个通用元素 ([image_universal_element]) 被直接展示，它的下降步骤 ([image_med_wd]) 从像成员证明中读取一个原像。那个证明就是 DATA——Epi.v 的 [GrpImage] 是一个 sigma——所以没有选择任何东西，但会检查一个元素。这不是一个陪集论证：在构造中任何地方都不存在陪集对象，并且调解器的唯一性仍然是通用性质的。称其为同构的通用性质推导是合理的，其输入是比较通用元素的逐元素构造。没有任何东西缩短那个输入：像被逐元素定义为伴随域的一个子群，因此从其映射出的任何映射必须使用成员证明。- 第二个（[second_isomorphism_theorem]，SN/N ≅ S/(S ∩ N)）。以教材方式，作为第一个的推论：复合映射 S ↪ SN ↠ SN/N 是满射，其核为 S ∩ N。它的两个逐元素输入分别命名并独立证明（[psi_kernel_is_meet]，[psi_surjective]），每个都是一次单独的正规性计算。在这两个引理之后，论证再次使用普适性——但是要诚实地阅读这个复合：这个定理是 [first_isomorphism_theorem psi] 与 [surjective_image_iso] 的复合，并且那个是作为一个带有两次往返的反函数对构建的，[quot_congr]（Instance/Grp/Quotient.v）同样如此，其字面形式 [second_isomorphism_theorem_literal] 进行复合。两者作为逆对都是退化的——每条腿在底层元素上都是恒等映射，并且每次往返都会通过 [reflexivity] 或 [quot_rel_refl] 闭合——但它们不是 [universal_element_iso] 的实例，上述陈述的范围是比较，而不是本文件中命名的每个同构。

   所以：一个定理是纯粹的追逐，一个定理有其比较对象的逐元素构造，还有一个定理是由前两者加上两个保持恒等载体的重新打包推导而来的。它们中没有一个操作陪集，其结构性原因在于 Instance/Grp/Quotient.v 的集合类商根本不形成陪集对象——但读者应该注意，这只是表述的一个特性，上述逐元素步骤在任何表述中仍然是逐元素的。交付的内容。将同态的像视为陪域的一个子群及其上限制；第一同构定理以及Awodey的推论4.5（分解 G ↠ G/ker h ≅ im h ↪ K，当且仅当其核平凡时 h 为单态）；第三定理；第二定理，作用在一个明确的 [SubgroupProduct] 上；以及三者在 S3 上的非空性证据。

   唯一性是被证明的，而不仅仅是可用的：[first_isomorphism_unique] 和 [third_isomorphism_unique] 表明，任何将一个通用元映射到另一个通用元的同构就是比较映射。第二定理没有这样的条款，它是三个同构的复合，而不是单个比较。未提供的内容。没有第四（“对应”/格）定理；没有扎森豪斯、施赖尔或乔丹-霍尔德定理；没有蝴蝶引理；也没有关于 h、S 或 N 中同构的自然性。第二条定理表述为 S/(S ∩ N) ≅ SN/N（[second_isomorphism_theorem_literal]），这是该问题所写方向的镜像；由于同构是对称的，因此未给出另一种理解的单独表述。
*)

(* * ** The image of a homomorphism, as a subgroup of the codomain / * ** 同态映射的像，作为陪域的一个子群 *)

(* [GrpImage] and its four closure lemmas are Instance/Grp/Epi.v; they are exactly the four [Subgroup] laws, so this record is assembled rather than proved. / [GrpImage]及其四个闭包引理是Instance/Grp/Epi.v；它们正好是四条[Subgroup]定律，因此这个记录是汇编的，而不是证明的。 *)
Definition ImageSub {G K : GrpObject} (h : G ~{Grp}~> K) : Subgroup K :=
  {| sub_mem := GrpImage h
   ; sub_resp := GrpImage_respects h
   ; sub_unit := GrpImage_unit h
   ; sub_mul := GrpImage_mul h
   ; sub_inv := GrpImage_inv h |}.

Definition ImageGrp {G K : GrpObject} (h : G ~{Grp}~> K) : GrpObject :=
  SubgroupGrp (ImageSub h).

(* The corestriction of h to its image: the same map, carrying its own witness. / 将 h 限制到它的像：同一个映射，携带它自己的证明。 *)
Program Definition image_cores {G K : GrpObject} (h : G ~{Grp}~> K) :
  G ~{Grp}~> ImageGrp h := {|
  grp_map := {| morphism := fun a : carrier G =>
                  existT _ (grp_map h a) (existT _ a (reflexivity _)) |}
|}.
Next Obligation. intros G K h a b Hab; simpl; now rewrite Hab. Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation. intros G K h a b; simpl; apply (grp_map_mul h). Qed.

(*
 The inclusion of the image recovers h: the triangle
 h = (im h ↪ K) ∘ (G ↠ im h) holds pointwise by reflexivity, the
 corestriction changing no element. 

 --------
 图像的包含恢复了 h: 三角形
 h = (im h ↪ K) ∘ (G ↠ im h) 在每一点上成立，由于自反性，
 核限制没有改变任何元素。
*)
Lemma image_factors {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h) ∘ image_cores h ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

(* The corestriction is surjective, by construction. / 通过构造，余限制是满射。 *)
Lemma image_cores_surjective {G K : GrpObject} (h : G ~{Grp}~> K) :
  GrpSurjective (image_cores h).
Proof.
  intro p; simpl.
  exists (`1 (`2 p)).
  simpl.
  exact (`2 (`2 p)).
Qed.

(*
 A surjective homomorphism identifies its image with its codomain.  The
 inverse map sends b to b together with its preimage witness, which is
 DATA (Epi.v's [GrpImage] is a sigma), so nothing is chosen. 

 --------
 一个满射同态将其像与其余域辨认为相同。逆映射将 b 发送到 b 以及它的原像证明，这就是 DATA (Epi.v 的 [GrpImage] 是一个 sigma)，所以没有进行选择。
*)
Program Definition surjective_image_iso {G K : GrpObject} (h : G ~{Grp}~> K)
  (Hs : GrpSurjective h) : ImageGrp h ≅[Grp] K := {|
  to := sub_incl (ImageSub h);
  from := {| grp_map := {| morphism := fun b : carrier K =>
               existT _ b (Hs b) |} |}
|}.
Next Obligation. intros G K h Hs a b Hab; exact Hab. Qed.
Next Obligation. intros G K h Hs; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a b; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.

(* * ** The image carries the second universal element / * ** 该图像包含第二个普遍元素 *)

Section ImageUniversal.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

(* The corestriction kills the kernel of h. / 余限制杀死了 h 的核。 *)
Lemma image_cores_kills (a : carrier G) :
  sub_mem (KernelNS h) a →
  grp_map (image_cores h) a ≈ grp_unit (ImageGrp h).
Proof. intro Ha; simpl in *; exact Ha. Qed.

Definition image_elem : Kills (KernelNS h) (ImageGrp h) :=
  existT _ (image_cores h) image_cores_kills.

Section ImageMediator.

Context {K' : GrpObject}.
Context (x : Kills (KernelNS h) K').

(*
 Well-definedness, isolated as one lemma: elements with the same image
 under h have the same image under the given map, because they differ by
 an element of ker h, which that map kills.  This is the ONE place an
 element is inspected, and everything the mediator owes is discharged
 from it.

 Isolating it is not tidiness -- it is what makes the construction
 independent of whether Instance/Grp/Epi.v's closure lemmas are
 transparent.  [GrpImage_unit], [GrpImage_mul] and [GrpImage_inv] are
 [Qed]-opaque there, so the preimage witness the group operations of
 [ImageGrp] carry does NOT reduce, and the unit and product laws below
 cannot be closed by computation; they are closed by comparing h-images
 instead. 

 --------
 良定义性，作为一个单独引理：在 h 下有相同像的元素，在给定映射下也有相同的像，因为它们相差一个被该映射消去的 ker h 元素。这是检查元素的唯一地方，调解器所欠的一切义务都从这里得到履行。

 将其单独列出不是整洁性——它是使构造独立于 Instance/Grp/Epi.v 的闭包引理是否透明的原因。[GrpImage_unit]、[GrpImage_mul] 和 [GrpImage_inv] 在那里是 [Qed] 不透明的，因此 [ImageGrp] 的群运算的原像见证不能被化简，下面的单位和乘法律也不能通过计算闭合；它们是通过比较 h 像来闭合的。
*)
Lemma image_med_wd (a b : carrier G) :
  grp_map h a ≈ grp_map h b → grp_map (`1 x) a ≈ grp_map (`1 x) b.
Proof.
  intro Hab.
  apply (kills_descends (KernelNS h) x).
  unfold quot_rel; simpl.
  rewrite (grp_map_mul h), (grp_map_inv h), Hab.
  apply (grp_mul_inv_r K).
Qed.

(* The mediator out of the image: read the preimage out of the membership witness and apply the given map to it. / 图像之外的中介：从成员证据中读出原像，并将给定的映射应用于它。 *)
Program Definition image_med : ImageGrp h ~{Grp}~> K' := {|
  grp_map := {| morphism := fun p : carrier (ImageGrp h) =>
                  grp_map (`1 x) (`1 (`2 p)) |}
|}.
Next Obligation.
  intros p q Hpq; simpl in *.
  apply image_med_wd.
  rewrite (`2 (`2 p)), (`2 (`2 q)).
  exact Hpq.
Qed.
Next Obligation.
  simpl.
  transitivity (grp_map (`1 x) (grp_unit G)).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_unit (ImageGrp h)))).
    simpl.
    symmetry; apply (grp_map_unit h).
  - apply (grp_map_unit (`1 x)).
Qed.
Next Obligation.
  intros p q; simpl.
  transitivity (grp_map (`1 x)
                  (grp_mul G (`1 (`2 p)) (`1 (`2 q)))).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_mul (ImageGrp h) p q))).
    rewrite (grp_map_mul h).
    rewrite (`2 (`2 p)), (`2 (`2 q)).
    reflexivity.
  - apply (grp_map_mul (`1 x)).
Qed.

Lemma image_med_commutes : image_med ∘ image_cores h ≈ `1 x.
Proof. intro a; simpl; reflexivity. Qed.

Lemma image_med_unique (v : ImageGrp h ~{Grp}~> K')
  (Hv : v ∘ image_cores h ≈ `1 x) : image_med ≈ v.
Proof.
  intro p; simpl.
  transitivity (grp_map v (grp_map (image_cores h) (`1 (`2 p)))).
  - symmetry; exact (Hv (`1 (`2 p))).
  - apply proper_morphism; simpl.
    exact (`2 (`2 p)).
Qed.

End ImageMediator.

(*
 ⟨im h, corestriction⟩ is a universal element of the SAME functor of
 which ⟨G/ker h, projection⟩ is one. 

 --------
 ⟨im h, 核限制⟩ 是同一函子下的一个泛元素，其中 ⟨G/ker h, 投影⟩ 是其中的一个。
*)
Program Definition image_universal_element :
  AUniversalElement (KillsFunctor (KernelNS h)) (ImageGrp h) := {|
  aue_elem := image_elem
|}.
Next Obligation.
  intros K' x.
  unshelve refine {| unique_obj := image_med x |}.
  - exact (image_med_commutes x).
  - intros v Hv; simpl in *.
    exact (image_med_unique x v Hv).
Defined.

End ImageUniversal.

(** ** The first isomorphism theorem / ** 第一个同构定理 *)

(*
 Two universal elements of one functor: [universal_element_iso] does the
 rest.  Nothing here builds a map or checks a round trip. 

 --------
 一个函子（functor）的两个通用元素：[universal_element_iso] 处理其余部分。这里没有任何东西构建映射或检查来回转换。
*)
Definition first_isomorphism_theorem {G K : GrpObject} (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  universal_element_iso (quot_universal_element (KernelNS h))
                        (image_universal_element h).

(* The comparison carries the projection to the corestriction, which is the triangle the reader wants and is [ue_med_commutes] read at these two universal elements. / 该比较将投射带到余限制上，这是读者所希望的三角形，并且在这两个普遍元素上读作 [ue_med_commutes]。 *)
Lemma first_isomorphism_triangle {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) ∘ quot_proj (KernelNS h)
    ≈ image_cores h.
Proof.
  exact (ue_med_commutes (quot_universal_element (KernelNS h))
                         (image_universal_element h)).
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
 Test/ProbeGrpQuotient.v). 

 --------
 两条腿都是两个中介，通过可转换性——[eq_refl]是`≈`规则的例外。[ue_med]是[unique_obj (aue_universal U1 (aue_elem U2))]（理论/泛型/元素.v），由于上面两个泛型元素是以它们的中介作为[unique_obj]构建的，所以通用机制不会重新构建任何映射。严格形式首先被尝试并成立；不严格成立的边界是中介的三角形，它是`≈`，而不是莱布尼茨（固定在Test/ProbeGrpQuotient.v中）。
*)
Example first_isomorphism_to_is_quot_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example first_isomorphism_from_is_image_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(*
 UNIQUENESS, proved rather than cited: any isomorphism carrying the
 projection to the corestriction IS this one.  This is
 [universal_element_iso_unique] at the two universal elements, and it is
 what makes the comparison canonical rather than merely existent. 

 --------
 独特性，通过证明而非引用得出：任何将投射映射到余限制的同构都是这个同构。这在两个通用元素上是 [universal_element_iso_unique]，并且这使得比较具有典范性，而不仅仅是存在性。
*)
Theorem first_isomorphism_unique {G K : GrpObject} (h : G ~{Grp}~> K)
  (v : QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h)
  (Hv : to v ∘ quot_proj (KernelNS h) ≈ image_cores h) :
  first_isomorphism_theorem h ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element (KernelNS h))
                                      (image_universal_element h) v Hv).
Qed.

(* * ** Awodey Corollary 4.5: the epi-mono factorization / * ** Awodey 推论 4.5：正射-单射分解 *)

(*
 h = (im h ↪ K) ∘ (comparison) ∘ (G ↠ G/ker h), the middle map an
 isomorphism.  The proof composes the two triangles above. 

 --------
 h = (im h ↪ K) ∘ (comparison) ∘ (G ↠ G/ker h)，中间的映射是同构。证明将上面的两个三角形组合起来。
*)
Theorem factorization {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h)
    ∘ to (first_isomorphism_theorem h)
    ∘ quot_proj (KernelNS h)
  ≈ h.
Proof.
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle h).
  apply image_factors.
Qed.

(*
 The left leg is epic and the right leg monic, so this is an epi-mono
 factorization in the literal sense. 

 --------
 左腿是史诗性的，右腿是单子的，所以从字面意义上看，这是一个史诗-单子分解。
*)
Theorem factorization_epi {G K : GrpObject} (h : G ~{Grp}~> K) :
  Epic (quot_proj (KernelNS h)).
Proof. apply quot_proj_epic. Qed.

Theorem factorization_mono {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic (sub_incl (ImageSub h)).
Proof. apply sub_incl_monic. Qed.

(*
 Awodey's corollary proper: h is injective exactly when its kernel is
 trivial.  Both directions are elementary; the forward one is the
 observation that the unit is already in the kernel. 

 --------
 Awodey 的推论本身：h 当且仅当其核平凡时是单射。两个方向都是基础的；正向的观察是单位元素已经在核中。
*)
Theorem injective_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  (∀ a b : carrier G, grp_map h a ≈ grp_map h b → a ≈ b)
    ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intros Hinj a Ha; simpl in Ha.
    apply Hinj.
    rewrite Ha.
    symmetry; apply (grp_map_unit h).
  - intros Htriv a b Hab.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite (grp_mul_inv_r G b).
    apply Htriv; simpl.
    rewrite (grp_map_mul h), (grp_map_inv h), Hab.
    apply (grp_mul_inv_r K).
Qed.

(* And the same statement with [Monic], through Instance/Grp.v's biconditional. / 以及通过 Instance/Grp.v 的双条件，与 [Monic] 的相同陈述。 *)
Theorem monic_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic h ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intro Hm.
    apply (fst (injective_iff_kernel_trivial h)).
    exact (snd (Grp_injectivity_is_monic h) Hm).
  - intro Ht.
    apply (fst (Grp_injectivity_is_monic h)).
    exact (snd (injective_iff_kernel_trivial h) Ht).
Qed.

(** ** The third isomorphism theorem / ** 第三同构定理 *)

Section Third.

Context {G : GrpObject}.
Context (M N : NormalSubgroup G).
Context (Hsub : ∀ a : carrier G, sub_mem M a → sub_mem N a).

(*
 N read as a normal subgroup of G/M.  The membership predicate is
 UNCHANGED; only the saturation law is new, since G/M's `≈` is coarser
 than G's.  The other four laws are the very terms N carries, because
 G/M's unit, product and inverse ARE G's. 

 --------
 N 被视为 G/M 的一个正规子群。其成员资格谓词保持不变；只有饱和律是新的，因为 G/M 的 `≈` 比 G 的更粗。其他四条律则正是 N 所携带的项，因为 G/M 的单位、乘积和逆元就是 G 的。
*)
(*
 RECORDED STRENGTH CHANGE.  An earlier revision read
 [sub_mem := fun a : carrier (QuotientGrp M) => sub_mem N a].
 Since the PR “algebraic carriers are sets” (2026-09-17) the quotient's `≈`
 is the propositional truncation of [quot_rel], and the SATURATION law of a
 [Subgroup] demands that a member's `≈`-partner be a member: from
 [inhabited (quot_rel M a b)] and [sub_mem N a] one must produce membership
 of [b].  That is an elimination of a [Prop] into a [Type] unless the
 membership is itself a [Prop], so N/M's membership is the truncation of
 [N]'s.  This is exactly the move Instance/Mod/Quotient/Isomorphism.v makes
 for [TmodS] and [MeetSub], and for the same reason.  [N]'s own [sub_mem]
 is untouched and stays [Type]-valued. 

 --------
 记录的强度变化。早期的修订版本写为 [sub_mem := fun a : carrier (QuotientGrp M) => sub_mem N a]。自从 PR “代数承载体是集合” (2026-09-17) 后，商的 `≈` 是 [quot_rel] 的命题截断，而 [Subgroup] 的饱和律要求成员的 `≈` 伴侣也必须是成员：由 [inhabited (quot_rel M a b)] 和 [sub_mem N a] 必须生成 [b] 的成员关系。这相当于将 [Prop] 消去到 [Type]，除非该成员自身就是 [Prop]，因此 N/M 的成员关系是 [N] 的截断。这正是 Instance/Mod/Quotient/Isomorphism.v 对 [TmodS] 和 [MeetSub] 所做的操作，原因相同。[N] 自身的 [sub_mem] 未受影响，仍然是 [Type] 值。
*)
Program Definition NmodM : NormalSubgroup (QuotientGrp M) := {|
  ns_sub := {| sub_mem := fun a : carrier (QuotientGrp M) =>
                            inhabited (sub_mem N a) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Hab as [Hab], Ha as [Ha]; constructor.
  (* b ≈ (a * b⁻¹)⁻¹ * a, and both factors lie in N / b ≈ (a * b⁻¹)⁻¹ * a，并且两个因子都位于 N 中 *)
  apply (sub_at N (a := grp_mul G (grp_inv G (grp_mul G a (grp_inv G b))) a)).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    rewrite (grp_mul_assoc G b (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    apply (grp_mul_unit_r G).
  - exact (sub_mul N _ _ (sub_inv N _ (Hsub _ Hab)) Ha).
Qed.
Next Obligation. simpl; exact (inhabits (sub_unit N)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; exact (inhabits (sub_mul N _ _ Ha Hb)).
Qed.
Next Obligation.
  intros a Ha; simpl in *.
  destruct Ha as [Ha]; exact (inhabits (sub_inv N _ Ha)).
Qed.
Next Obligation.
  intros t a Ha; simpl in *.
  destruct Ha as [Ha]; exact (inhabits (ns_conj N t _ Ha)).
Qed.

(*
 The comparison G/M ↠ G/N: the identity function again, well defined
 because M ⊆ N. 

 --------
 比较 G/M ↠ G/N：恒等函数，再次是良定义的，因为 M ⊆ N。
*)
Program Definition quot_step : QuotientGrp M ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp M) => a |}
|}.
Next Obligation.
  intros a b Hab.
  change (inhabited (quot_rel M a b)) in Hab.
  change (inhabited (quot_rel N a b)).
  destruct Hab as [Hab]; exact (inhabits (Hsub _ Hab)).
Qed.
Next Obligation. simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation. intros a b; simpl; constructor; apply quot_rel_refl. Qed.

(* The triangle relating the three projections. / 涉及三个投影的三角形。 *)
Lemma quot_step_triangle : quot_step ∘ quot_proj M ≈ quot_proj N.
Proof. intro a; simpl; constructor; apply quot_rel_refl. Qed.

(* The comparison kills N/M. / 比较会杀死N/M。 *)
Lemma quot_step_kills (a : carrier (QuotientGrp M)) :
  sub_mem NmodM a → grp_map quot_step a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl in *.
  destruct Ha as [Ha]; constructor.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

Definition quot_step_elem : Kills NmodM (QuotientGrp N) :=
  existT _ quot_step quot_step_kills.

Section ThirdMediator.

Context {K : GrpObject}.
Context (x : Kills NmodM K).

(*
 THE ONE ELEMENTWISE STEP of this theorem: transferring the killing
 hypothesis across the projection.  A member of N is projected by p_M to
 a member of N/M -- p_M being the identity function -- so k ∘ p_M kills N.
 An earlier revision said “the membership predicates being the same”; since
 the PR “algebraic carriers are sets” (2026-09-17) N/M's membership is the
 TRUNCATION of N's (see [NmodM]), so the step is that projection followed
 by one [inhabits]. 

 --------
 这个定理的单个逐元素步骤：将消除假设通过投影转移。N 的一个成员通过 p_M 投影到 N/M 的一个成员——p_M 是恒等函数——所以 k ∘ p_M 消除了 N。早期的修订版说“成员谓词相同”；由于 PR “代数载体是集合”（2026-09-17），N/M 的成员资格是 N 的截断（参见 [NmodM]），所以这一步是投影之后再进行一次 [inhabits]。
*)
Lemma third_precompose_kills (a : carrier G) :
  sub_mem N a → grp_map (`1 x ∘ quot_proj M) a ≈ grp_unit K.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  exact (`2 x a (inhabits Ha)).
Qed.

Definition third_precompose : Kills N K :=
  existT _ (`1 x ∘ quot_proj M) third_precompose_kills.

(*
 From here the argument is a chase.  The mediator is the one G/N's
 universal property produces for k ∘ p_M. 

 --------
 从这里开始，这个论证就是一个追逐。中介者是 G/N 的通用性质为 k ∘ p_M 产生的那个。
*)
Definition third_med : QuotientGrp N ~{Grp}~> K := quot_med N third_precompose.

(* Its triangle against the comparison map, obtained by cancelling the epimorphism p_M on the right -- no element inspected. / 它的三角形针对比较图，通过在右侧取消满射 p_M 得到——没有检查任何元素。 *)
Lemma third_med_commutes : third_med ∘ quot_step ≈ `1 x.
Proof.
  apply (epic (Epic := quot_proj_epic M)).
  rewrite <- comp_assoc.
  rewrite quot_step_triangle.
  exact (quot_med_commutes N third_precompose).
Qed.

Lemma third_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_step ≈ `1 x) : third_med ≈ v.
Proof.
  apply (quot_med_unique N third_precompose).
  rewrite <- quot_step_triangle.
  rewrite comp_assoc.
  rewrite Hv.
  reflexivity.
Qed.

End ThirdMediator.

(*
 ⟨G/N, comparison⟩ is a universal element of the kills-(N/M) functor on
 G/M.  Every step above used only [quot_universal_element N], the
 epimorphism [quot_proj_epic M], and the triangle. 

 --------
 ⟨G/N，比较⟩ 是 G/M 上 kills-(N/M) 函子的一般元素。上面的每一步只使用了 [quot_universal_element N]、满射 [quot_proj_epic M] 和该三角形。
*)
Program Definition quot_universal_N_over_M :
  AUniversalElement (KillsFunctor NmodM) (QuotientGrp N) := {|
  aue_elem := quot_step_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := third_med x |}.
  - exact (third_med_commutes x).
  - intros v Hv; simpl in *.
    exact (third_med_unique x v Hv).
Defined.

(* Mac Lane §III.1 Exercise 4, third isomorphism theorem. / Mac Lane §III.1 练习 4，第三同构定理。 *)
Definition third_isomorphism_theorem :
  QuotientGrp NmodM ≅[Grp] QuotientGrp N :=
  universal_element_iso (quot_universal_element NmodM) quot_universal_N_over_M.

Lemma third_isomorphism_triangle :
  to third_isomorphism_theorem ∘ quot_proj NmodM ≈ quot_step.
Proof.
  exact (ue_med_commutes (quot_universal_element NmodM)
                         quot_universal_N_over_M).
Qed.

(* Uniqueness, as for the first theorem. / 唯一性，如同第一个定理一样。 *)
Theorem third_isomorphism_unique
  (v : QuotientGrp NmodM ≅[Grp] QuotientGrp N)
  (Hv : to v ∘ quot_proj NmodM ≈ quot_step) :
  third_isomorphism_theorem ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element NmodM)
                                      quot_universal_N_over_M v Hv).
Qed.

End Third.

Arguments NmodM {G} M N Hsub.
Arguments quot_step {G} M N Hsub.
Arguments third_isomorphism_theorem {G} M N Hsub.
Arguments third_isomorphism_unique {G} M N Hsub.

(* * ** The second isomorphism theorem / * ** 第二同构定理 *)

(*
 Two shuffles, isolated so that the subgroup laws below are one-liners.
 Both are the standard normality manipulations, and both are proved by
 right-associating everything and cancelling one inverse pair. 

 --------
 两次洗牌，孤立处理，以便下面的子群法则成为一行。两者都是标准的正规性操作，并且两者的证明方法都是通过右结合所有内容并消去一对逆元素。
*)
Lemma product_shuffle (G : GrpObject) (s n s' n' : carrier G) :
  grp_mul G (grp_mul G s n) (grp_mul G s' n')
  ≈ grp_mul G (grp_mul G s s')
      (grp_mul G (grp_mul G (grp_mul G (grp_inv G s') n) s') n').
Proof.
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G s' (grp_inv G s')
                (grp_mul G n (grp_mul G s' n'))).
  rewrite (grp_mul_inv_r G s').
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Lemma inverse_shuffle (G : GrpObject) (s n : carrier G) :
  grp_inv G (grp_mul G s n)
  ≈ grp_mul G (grp_inv G s)
      (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
Proof.
  rewrite (grp_inv_mul G s n).
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G s) s
                (grp_mul G (grp_inv G n) (grp_inv G s))).
  rewrite (grp_mul_inv_l G s).
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Section Second.

Context {G : GrpObject}.
Context (S : Subgroup G).
Context (N : NormalSubgroup G).

(*
 The product set SN, as a subgroup.  Membership carries the
 decomposition as DATA, so the second isomorphism theorem's elementwise
 steps read it back out with nothing chosen.  Closure under product and
 inverse is where normality is spent:
 (s n)(s' n') = (s s') ((s'⁻¹ n s') n')   and
 (s n)⁻¹      = s⁻¹ (s n⁻¹ s⁻¹). 

 --------
 产品集 SN，作为一个子群。成员身份包含作为 DATA 的分解，因此第二同构定理的逐元素步骤可以在不选择任何元素的情况下读出来。积和逆元下的封闭性是正规性体现的地方：
 (s n)(s' n') = (s s') ((s'⁻¹ n s') n')   并且
 (s n)⁻¹      = s⁻¹ (s n⁻¹ s⁻¹)。
*)
Definition in_product (x : carrier G) : Type :=
  { s : carrier G & { n : carrier G &
      ((sub_mem S s * sub_mem N n) * (x ≈ grp_mul G s n))%type } }.

Program Definition SubgroupProduct : Subgroup G := {|
  sub_mem := in_product
|}.
Next Obligation.
  intros a b Hab [s [n [Hsn Ha]]].
  exists s, n; split; [ exact Hsn | now rewrite <- Hab ].
Qed.
Next Obligation.
  exists (grp_unit G), (grp_unit G).
  split; [ split; [ exact (sub_unit S) | exact (sub_unit N) ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros a b [s [n [[Hs Hn] Ha]]] [s' [n' [[Hs' Hn'] Hb]]].
  exists (grp_mul G s s').
  exists (grp_mul G
            (grp_mul G (grp_mul G (grp_inv G s') n) (grp_inv G (grp_inv G s')))
            n').
  split.
  - split.
    + exact (sub_mul S _ _ Hs Hs').
    + exact (sub_mul N _ _ (ns_conj N (grp_inv G s') _ Hn) Hn').
  - rewrite Ha, Hb.
    rewrite (grp_inv_inv G s').
    apply product_shuffle.
Qed.
Next Obligation.
  intros a [s [n [[Hs Hn] Ha]]].
  exists (grp_inv G s).
  exists (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
  split.
  - split.
    + exact (sub_inv S _ Hs).
    + exact (ns_conj N s _ (sub_inv N _ Hn)).
  - rewrite Ha.
    apply inverse_shuffle.
Qed.

(* N sits inside SN, and is normal there. / N 位于 SN 内，并且在那里是正规子群。 *)
Lemma N_in_product (n : carrier G) : sub_mem N n → sub_mem SubgroupProduct n.
Proof.
  intro Hn.
  exists (grp_unit G), n.
  split; [ split; [ exact (sub_unit S) | exact Hn ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.

Program Definition NinSN : NormalSubgroup (SubgroupGrp SubgroupProduct) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp SubgroupProduct) =>
                            sub_mem N (`1 p) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (sub_unit N). Qed.
Next Obligation. intros a b Ha Hb; simpl in *; exact (sub_mul N _ _ Ha Hb). Qed.
Next Obligation. intros a Ha; simpl in *; exact (sub_inv N _ Ha). Qed.
Next Obligation. intros t a Ha; simpl in *; exact (ns_conj N _ _ Ha). Qed.

(* S sits inside SN too, as a homomorphism of groups. / S 也作为群的同态嵌入在 SN 中。 *)
Program Definition S_into_SN :
  SubgroupGrp S ~{Grp}~> SubgroupGrp SubgroupProduct := {|
  grp_map := {| morphism := fun p : carrier (SubgroupGrp S) =>
     existT _ (`1 p)
       (existT _ (`1 p) (existT _ (grp_unit G)
          (pair (pair (`2 p) (sub_unit N))
                (symmetry (grp_mul_unit_r G (`1 p)))))) |}
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros p q; simpl; reflexivity. Qed.

(*
 The composite S ↪ SN ↠ SN/N, whose kernel is S ∩ N and which is
 surjective. 

 --------
 复合映射 S ↪ SN ↠ SN/N，它的核是 S ∩ N，并且是满射。
*)
Definition psi : SubgroupGrp S ~{Grp}~> QuotientGrp NinSN :=
  quot_proj NinSN ∘ S_into_SN.

(*
 ELEMENTWISE INPUT ONE: the kernel of ψ is S ∩ N -- as a biconditional
 on membership, not merely an inclusion. 

 --------
 逐元素输入一：ψ 的核是 S ∩ N —— 作为成员关系的双条件，而不仅仅是包含关系。
*)
(*
 AN EARLIER REVISION stated the right-hand side as the bare
 [sub_mem N (`1 p)].  Since the PR “algebraic carriers are sets”
 (2026-09-17) the left-hand side is congruence to the unit in a quotient,
 which is the [inhabited] truncation of membership, so the biconditional
 holds up to that truncation and is stated so.  Both directions are
 [Prop]-to-[Prop]; the untruncated direction is available as
 [psi_kernel_of_meet] below, with its witness intact. 

 --------
 早期的一个修订将右侧表示为单纯的 [sub_mem N (`1 p)]。由于 PR “代数载体是集合”（2026-09-17），左侧在一个商中的单位下是同余的，它是隶属关系的 [inhabited] 截断，因此该双条件在该截断下成立，并如此陈述。两个方向都是 [Prop] 到 [Prop]；未截断的方向可作为下面的 [psi_kernel_of_meet] 获得，其证据保持完整。
*)
Lemma psi_kernel_is_meet (p : carrier (SubgroupGrp S)) :
  sub_mem (KernelNS psi) p ↔ inhabited (sub_mem N (`1 p)).
Proof.
  split.
  - intro Hp; simpl in Hp.
    unfold quot_equiv in Hp.
    destruct Hp as [Hp]; constructor.
    apply (sub_at N (a := grp_mul G (`1 p) (grp_inv G (grp_unit G)))).
    + rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
    + exact Hp.
  - intro Hp; simpl.
    destruct Hp as [Hp]; constructor.
    unfold quot_rel; simpl.
    apply (sub_at N (a := `1 p)).
    + rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
    + exact Hp.
Qed.

(* The direction that keeps its [Type]-valued hypothesis whole. / 保持其 [Type] 值假设完整的方向。 *)
Lemma psi_kernel_of_meet (p : carrier (SubgroupGrp S)) :
  sub_mem N (`1 p) → sub_mem (KernelNS psi) p.
Proof. intro Hp; exact (snd (psi_kernel_is_meet p) (inhabits Hp)). Qed.

(* ELEMENTWISE INPUT TWO: ψ is surjective. Every member of SN is s·n for data s ∈ S, n ∈ N, and s·n is congruent to s modulo N because (s n) s⁻¹ lies in N -- one normality computation. / 逐元素输入二：ψ 是满射的。SN 的每个成员都是 s·n，其中数据 s ∈ S，n ∈ N，并且 s·n 与 s 模 N 同余，因为 (s n) s⁻¹ 位于 N 中 —— 一个正规性计算。 *)
Lemma psi_surjective : GrpSurjective psi.
Proof.
  intro q.
  destruct (`2 q) as [s [n [[Hs Hn] Hq]]].
  exists (existT _ s Hs).
  simpl.
  constructor.
  unfold quot_rel; simpl.
  (* s * (s n)⁻¹ lies in N / s * (s n)⁻¹ 位于 N *)
  apply (sub_at N (a := grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s))).
  - rewrite Hq.
    rewrite (grp_inv_mul G s n).
    rewrite (grp_mul_assoc G s (grp_inv G n) (grp_inv G s)).
    reflexivity.
  - exact (ns_conj N s _ (sub_inv N _ Hn)).
Qed.

(*
 Mac Lane §III.1 Exercise 4, second isomorphism theorem, as a corollary
 of the first: S/(S ∩ N) is S/ker ψ, which the first theorem identifies
 with im ψ, which surjectivity identifies with SN/N. 

 --------
 Mac Lane §III.1 练习 4，第二同构定理，作为第一同构定理的推论：S/(S ∩ N) 是 S/ker ψ，第一同构定理将其确定为 im ψ，而满射性将其确定为 SN/N。
*)
Definition second_isomorphism_theorem :
  QuotientGrp (KernelNS psi) ≅[Grp] QuotientGrp NinSN :=
  iso_compose (surjective_image_iso psi psi_surjective)
              (first_isomorphism_theorem psi).

(*
 S ∩ N, as a normal subgroup of S: membership in N, read on elements of
 S.  This is the literal left-hand side of the theorem, and the
 statement below is the literal one -- [second_isomorphism_theorem]
 above says S/ker ψ, which is the same group only because
 [psi_kernel_is_meet] says the two memberships coincide, and
 [quot_congr] is what turns that coincidence into an isomorphism. 

 --------
 S ∩ N，作为 S 的正规子群：属于 N，在 S 的元素上阅读。这是定理的字面左边，并且下面的陈述是字面的——上面 [second_isomorphism_theorem] 说 S/ker ψ，这是同一个群，仅仅因为 [psi_kernel_is_meet] 说这两个成员关系一致，而 [quot_congr] 使这种一致性变为同构。
*)
(*
 AN EARLIER REVISION wrote the predicate as the bare [sub_mem N (`1 p)].
 Since the PR “algebraic carriers are sets” (2026-09-17) it is the
 [inhabited] truncation of that, and the reason is the identification
 [second_isomorphism_theorem_literal] makes: this subgroup has to be
 coextensive with [KernelNS psi], whose membership is congruence to the
 unit in a quotient and hence already truncated.  The same move is made at
 Instance/Mod/Quotient/Isomorphism.v's [MeetSub], for the same reason. 

 --------
 早期的修订将谓词写成了纯粹的 [sub_mem N (`1 p)]。
 自从 PR “代数载体是集合”（2026-09-17）之后，它就是 [inhabited] 的截断，其原因在于 [second_isomorphism_theorem_literal] 所作的识别：这个子群必须与 [KernelNS psi] 完全一致，而 [KernelNS psi] 的元素是与商中的单位同余的，因此已经被截断。相同的操作也出现在 Instance/Mod/Quotient/Isomorphism.v 的 [MeetSub]，原因相同。
*)
Program Definition MeetNS : NormalSubgroup (SubgroupGrp S) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp S) =>
                            inhabited (sub_mem N (`1 p)) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (inhabits (sub_unit N)). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *.
  destruct Ha as [Ha], Hb as [Hb]; constructor; exact (sub_mul N _ _ Ha Hb).
Qed.
Next Obligation.
  intros a Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (sub_inv N _ Ha).
Qed.
Next Obligation.
  intros t a Ha; simpl in *.
  destruct Ha as [Ha]; constructor; exact (ns_conj N _ _ Ha).
Qed.

Definition second_isomorphism_theorem_literal :
  QuotientGrp MeetNS ≅[Grp] QuotientGrp NinSN :=
  iso_compose second_isomorphism_theorem
    (quot_congr MeetNS (KernelNS psi)
       (fun p Hp => snd (psi_kernel_is_meet p) Hp)
       (fun p Hp => fst (psi_kernel_is_meet p) Hp)).

End Second.

Arguments SubgroupProduct {G} S N.
Arguments MeetNS {G} S N.
Arguments NinSN {G} S N.
Arguments psi {G} S N.
Arguments second_isomorphism_theorem {G} S N.
Arguments second_isomorphism_theorem_literal {G} S N.

(*
   * ** Non-vacuity at S3

   All three theorems above hold for every group, so nothing yet shows
   any of them is about a nondegenerate situation.  S3 with its rotation
   subgroup A3 (Instance/Grp/Quotient.v) supplies witnesses for each, and
   the degeneracies are excluded by proof: S3 is nonabelian, A3 is a
   PROPER NONTRIVIAL normal subgroup, and the quotient does not
   collapse. 

   --------
   * ** S3 的非空性

   上述三个定理对每个群都成立，所以目前还没有显示它们中的任何一个与非退化情况有关。S3 及其旋转子群 A3（Instance/Grp/Quotient.v）为每个定理提供了实例，并且通过证明排除了退化情况：S3 是非交换的，A3 是一个**适当的非平凡正规子群**，且商群不会坍缩。
*)

(*
 The projection S3 ↠ S3/A3 has kernel A3, in both directions.  Together
 with [S3_mod_A3_not_collapsed] this makes the first isomorphism theorem
 at this map a statement about a two-element quotient of a six-element
 group, not about a degenerate one. 

 --------
 投射 S3 ↠ S3/A3 在两个方向上的核都是 A3。 与 [S3_mod_A3_not_collapsed] 一起，这使得这个映射下的第一同构定理成为关于一个六元群的二元商的陈述，而不是关于一个退化的一元群。
*)
(*
 Restated up to the truncation, in lockstep with [quot_proj_kernel]: since
 the PR “algebraic carriers are sets” (2026-09-17) the kernel's membership
 is congruence to the unit in a quotient, hence [inhabited].  The direction
 that keeps its witness whole is [quot_proj_kills]. 

 --------
 按照截断重述，与 [quot_proj_kernel] 保持步调一致：自从 PR “代数载体是集合”（2026-09-17）以来，核的成员关系与商中的单位同余，因此 [inhabited]。保持其见证整体的方向是 [quot_proj_kills]。
*)
Lemma S3_proj_kernel_is_A3 (a : carrier S3) :
  sub_mem (KernelNS (quot_proj A3)) a ↔ inhabited (sub_mem A3 a).
Proof. exact (quot_proj_kernel A3 a). Qed.

(* The first isomorphism theorem instantiated: S3/ker(p) ≅ im(p). / 第一同构定理实例化：S3/ker(p) ≅ im(p)。 *)
Definition S3_first_iso :
  QuotientGrp (KernelNS (quot_proj A3)) ≅[Grp] ImageGrp (quot_proj A3) :=
  first_isomorphism_theorem (quot_proj A3).

(* And it is nondegenerate: the image of the projection has two elements apart in its own setoid. / 并且它是非退化的：投影的像在其自身的集合等价类中有两个元素是分开的。 *)
(*
 The hypothesis is the quotient's truncated `≈` since the PR “algebraic
 carriers are sets” (2026-09-17); the goal is [False], so it is unwrapped
 at no cost.  Likewise for the three theorems below over [quot_rel] at a
 truncated membership. 

 --------
 该假设是商的截断 `≈`，因为 PR “代数载体是集合”（2026-09-17）；目标是 [False]，因此可以无成本展开。同样，对于下面在截断成员下的 [quot_rel] 上的三个定理也是如此。
*)
Theorem S3_first_iso_nondegenerate :
  grp_map (image_cores (quot_proj A3)) S3_s
    ≈ grp_map (image_cores (quot_proj A3)) s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
 The third isomorphism theorem at M = trivial, N = A3: (S3/1)/(A3/1) ≅
 S3/A3.  The inclusion hypothesis is that everything ≈-equal to the unit
 is a rotation. 

 --------
 第三同构定理在 M = 平凡，N = A3 时: (S3/1)/(A3/1) ≅ S3/A3。包含假设是，所有与单位元 ≈ 相等的元素都是旋转。
*)
Lemma trivial_in_A3 (a : carrier S3) : sub_mem (TrivialNS S3) a → sub_mem A3 a.
Proof. intro Ha; simpl in *; now subst. Qed.

Definition S3_third_iso :
  QuotientGrp (NmodM (TrivialNS S3) A3 trivial_in_A3)
    ≅[Grp] QuotientGrp A3 :=
  third_isomorphism_theorem (TrivialNS S3) A3 trivial_in_A3.

(*
 Nondegenerate: the reflection is still apart from the unit on the left
 of the isomorphism. 

 --------
 非退化：反射仍然位于同构左侧的单位之外。
*)
Theorem S3_third_iso_nondegenerate :
  quot_rel (NmodM (TrivialNS S3) A3 trivial_in_A3) S3_s s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
 The second isomorphism theorem is instantiated at S = the two-element
 reflection subgroup and N = A3.  That pair is nondegenerate in the way
 the theorem's hypotheses ask for: S is a plain [Subgroup] and is
 provably NOT normal (Instance/Grp/Quotient.v's [S3_refl_sub_not_normal]),
 so the statement is not being applied in a case where the
 plain-subgroup generality is idle. 

 --------
 第二同构定理在 S = 二元素反射子群 和 N = A3 的情况下被实例化。这个对子在定理假设所要求的方式下是非退化的：S 是一个普通的 [Subgroup]，并且可以证明它不是正规子群（Instance/Grp/Quotient.v 的 [S3_refl_sub_not_normal]），因此该陈述并不是应用在普通子群泛化无效的情况下。
*)

Definition S3_second_iso :
  QuotientGrp (KernelNS (psi S3_refl_sub A3))
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem S3_refl_sub A3.

(* Nondegenerate on the left: S ∩ N is trivial here (a rotation-free element that is a rotation is the unit), so S/(S ∩ N) still separates the reflection from the unit. / 左侧非退化：这里 S ∩ N 是平凡的（一个无旋转的旋转元素是单位元），因此 S/(S ∩ N) 仍然可以将反射与单位元分开。 *)
Theorem S3_second_iso_nondegenerate :
  quot_rel (KernelNS (psi S3_refl_sub A3))
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
 The literal form, whose left-hand side is S/(S ∩ N) rather than
 S/ker ψ. 

 --------
 字面形式，其左侧是 S/(S ∩ N) 而不是 S/ker ψ。
*)
Definition S3_second_iso_literal :
  QuotientGrp (MeetNS S3_refl_sub A3)
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem_literal S3_refl_sub A3.

Theorem S3_second_iso_literal_nondegenerate :
  quot_rel (MeetNS S3_refl_sub A3)
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(*
 And nondegenerate on the RIGHT as well: the reflection, read as an
 element of SN via the decomposition s = s · e, stays apart from the
 unit in SN/N.  So both sides of the second isomorphism have at least
 two elements and the theorem is not identifying two collapsed
 groups. 

 --------
 并且在右侧也非退化：通过分解 s = s · e，将反射作为 SN 的一个元素来读取，它在 SN/N 中远离单位元素。因此，第二同构的两边至少都有两个元素，并且该定理并没有将两个坍缩的群体认同起来。
*)
Definition S3_s_in_SN : carrier (SubgroupGrp (SubgroupProduct S3_refl_sub A3)).
Proof.
  refine (existT _ S3_s _).
  exists S3_s, s3_unit.
  split; [ split | ].
  - exact (eq_refl : fst S3_s = rot0).
  - exact (eq_refl : snd s3_unit = false).
  - vm_compute; reflexivity.
Defined.

Theorem S3_second_iso_codomain_nondegenerate :
  quot_rel (NinSN S3_refl_sub A3) S3_s_in_SN
    (grp_unit (SubgroupGrp (SubgroupProduct S3_refl_sub A3)))
  → False.
Proof. simpl; discriminate. Qed.
