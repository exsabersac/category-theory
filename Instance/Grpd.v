Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The category of groupoids / * 群族的类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Grpd
 nLab:      https://ncatlab.org/nlab/show/groupoid
 Wikipedia: https://en.wikipedia.org/wiki/Groupoid

 Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
 Example 4.1.15, printed p. 137 (PDF pp. 157-158)
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §I.5, printed p. 19

 [Grpd] is the full subcategory of [Cat] whose objects are the categories
 in which every morphism is invertible.  It is built with
 Construction/Subcategory.v's [Build_Subcategory] out of exactly one
 predicate on objects, Structure/Groupoid.v's [IsGroupoid], and the
 maximal choice of morphisms: [shom] ignores its arguments and returns
 [True], so the two closure conditions are [I] and fullness
 ([Grpd_Full]) is [I] as well.  This is the shape Instance/Variety.v uses
 for the algebras of a variety, and it is used here for the same reason
 the header of that file gives: a fresh [Category] record duplicating
 [Cat]'s composition and hom-setoid would have to re-derive every law that
 [Sub] already derives once and generically, and the inclusion would have
 to be built by hand instead of being read off as [Incl].

 The objects of [Grpd] are therefore PAIRS: a category together with a
 chosen inverse-assigning function, since [IsGroupoid] is [Type]-valued
 and its inhabitant carries a chosen inverse for each arrow.  The choice
 is immaterial up to `≈` (Structure/Groupoid.v's [ginv_choice_irrelevant]),
 but it is data, so two membership proofs for one category give two
 objects of [Grpd] -- isomorphic, by [Full_membership_iso]; no [=]
 between them is asserted anywhere here.
 The morphisms are functors between the underlying categories, with no
 condition whatever: a functor between groupoids preserves inverses
 automatically, which is precisely what fullness of the inclusion records.

 The inclusion [Grpd_Incl : Grpd ⟶ Cat] is [Incl], and it is faithful
 ([Grpd_Incl_Faithful], generic) and full ([Grpd_Incl_Full], from
 [Grpd_Full]).  Construction/Groupoid/Core.v makes the maximal-subgroupoid
 construction of Construction/Groupoid.v into its right adjoint. 

 --------
 nLab:       https://ncatlab.org/nlab/show/Grpd 
 nLab:       https://ncatlab.org/nlab/show/groupoid 
 Wikipedia:  https://en.wikipedia.org/wiki/Groupoid 

 书籍: Riehl, 《Category Theory in Context》，Dover 2016，§4.1，
 示例 4.1.15，印刷页 137（PDF 页 157-158）
 书籍: Mac Lane, 《Categories for the Working Mathematician》，第二版，
 §I.5，印刷页 19[Grpd] 是 [Cat] 的满子范畴，其对象是每个态射都是可逆的类别。它通过 Construction/Subcategory.v 的 [Build_Subcategory] 构建，由恰好一个对象上的谓词、Structure/Groupoid.v 的 [IsGroupoid]，以及态射的最大选择：[shom] 忽略其参数并返回 [True]，因此两个闭包条件是 [I]，并且满性（[Grpd_Full]）也是 [I]。这是形状 Instance/Variety.v 用于一个品类的代数的方式，并且它在这里被使用的原因与该文件头部所说明的相同：一个新的 [Category] 记录复制 [Cat] 的组合和同态集合将不得不重新推导 [Sub] 已经一次并且通用地推导的每一个定律，并且包含关系必须手工建立，而不能像 [Incl] 那样直接读取。因此，[Grpd] 的对象是成对的：一个范畴以及一个选定的逆分配函数，因为 [IsGroupoid] 是 [Type] 值的，其元素为每个箭头携带一个选定的逆。这个选择在 `≈`（Structure/Groupoid.v 的 [ginv_choice_irrelevant]）下是无关紧要的，但它是数据，因此对于一个范畴的两个归属证明会产生 [Grpd] 的两个对象 —— 根据 [Full_membership_iso]，它们是同构的；这里没有声明它们之间存在 [=]。态射是底层范畴之间的函子，没有任何条件：群范畴之间的函子自动保持逆，这正是包含的满性所记录的内容。包含 [Grpd_Incl : Grpd ⟶ Cat] 是 [Incl]，并且它是忠实的（[Grpd_Incl_Faithful]，泛化的）且是满的（[Grpd_Incl_Full]，来自 [Grpd_Full]）。Construction/Groupoid/Core.v 将 Construction/Groupoid.v 的最大子群oid构造变为其右伴随。
*)

(*
 Why a category of groupoids, and why it sits inside Cat

 nLab:  https://ncatlab.org/nlab/show/core
 Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
 the London Mathematical Society 19, 1987
 Paper: Hofmann and Streicher, "The groupoid model refutes uniqueness of
 identity proofs", LICS 1994

 A single groupoid generalises a group by letting the symmetries move
 between objects rather than fixing one; the CATEGORY of groupoids
 generalises the category of groups in the same way, and it is the
 setting in which that generalisation pays.  Brown's survey makes the
 case with the van Kampen theorem: stated for fundamental GROUPS it needs
 a connected intersection, while the groupoid statement -- one base point
 per component, the conclusion a pushout in [Grpd] -- proves a stronger
 theorem more simply (Brown 1987, following Higgins).  A pushout is a
 colimit, so it is a statement about the category of groupoids, not about
 any one of them; the object-level construction alone cannot express it.

 [Grpd] sits inside [Cat] in an unusually strong way.  The inclusion has
 adjoints on BOTH sides -- the left one inverts every morphism formally
 (the category of fractions), the right one discards the non-invertible
 ones (the core) -- so [Grpd] is simultaneously reflective and
 coreflective in [Cat] (Riehl §4.1, Example 4.1.15; nLab: core).  This
 file and Construction/Groupoid/Core.v deliver the right-hand half of that
 adjoint triple as a theorem.  An earlier revision of this sentence added
 that the left-hand half "remains prose"; that is a correction to make,
 because Construction/Fractions/Adjunction.v now proves it, and
 [riehl_4_1_15] there assembles the whole triple over THIS [Grpd] and
 THIS inclusion.

 The type-theoretic reading is not an analogy.  In intensional Martin-Löf
 type theory the identity proofs of a type compose, invert and associate,
 so every type carries the structure of a groupoid, and the interpretation
 of types as OBJECTS OF [Grpd] -- functions as functors between them -- is
 what Hofmann and Streicher used to show that uniqueness of identity
 proofs is not derivable (LICS 1994).  That model is a functor into
 [Grpd], which again is a statement one can only make once the category
 exists. 

 --------
 为什么是一个群的范畴，以及为什么它位于Cat之内

 nLab: https://ncatlab.org/nlab/show/core
 论文: Brown，《从群到群群：简要综述》，伦敦数学会公报 19, 1987
 论文: Hofmann 和 Streicher，《群群模型反驳身份证明的唯一性》，LICS 1994一个单一群类通过让对称性在对象之间移动而不是固定在某一对象上，从而推广了群；群类的范畴以同样的方式推广了群的范畴，并且这是该推广发挥作用的背景。布朗的综述通过 van Kampen 定理说明了这一点：如果以基本群陈述，则需要一个连通的交集，而群类陈述——每个分支一个基点，结论是在 [Grpd] 中的推挤——更简单地证明了一个更强的定理（布朗 1987，继希金斯之后）。推挤是余极限，因此它是关于群类范畴的陈述，而不是关于其中任何一个；单纯的对象层构造无法表达它。[Grpd] 以一种异常强的方式包含在  [Cat] 中。该包含在两边都有伴随——左边的伴随形式上反转每个态射（分数范畴），右边的伴随丢弃不可逆的态射（核心）——因此 [Grpd] 同时在 [Cat] 中是反射的和共反射的（Riehl §4.1，例 4.1.15；nLab: core）。该文件和 Construction/Groupoid/Core.v 提供了该伴随三重关系的右边部分作为定理。该句的早期修订版本补充说明左边部分“保持为文字描述”；这是需要更正的，因为 Construction/Fractions/Adjunction.v 现在已经证明了它，并且 [riehl_4_1_15] 在那里将整个三重关系组装在此 [Grpd] 及其包含上。类型理论的解读不是一种类比。在强意向性的Martin-Löf类型理论中，一个类型的身份证明可以组合、逆转和结合，因此每个类型都携带一个群oid的结构，而将类型解释为[Grpd]的对象——作为它们之间函子的函数——正是Hofmann和Streicher用来证明身份证明的唯一性不可推导的方法（LICS 1994）。那个模型是一个到[Grpd]的函子，这同样是在该范畴存在之后才能说的陈述。
*)

(** ** The subcategory data / ** 子类别数据 *)

(*
 Full, and cut out by a predicate on objects alone: [shom] discards its
 morphism argument entirely.  Every closure proof is therefore [I]. 

 --------
 完整，并且仅通过对对象的谓词进行裁剪：[shom] 完全丢弃了它的态射参数。因此，每个闭包证明都是 [I]。
*)

Definition Grpd_sub : Subcategory Cat :=
  @Build_Subcategory Cat
    IsGroupoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Grpd : Category := Sub Cat Grpd_sub.

(*
   * ** Accessors

   An object of [Grpd] is a category paired with a proof that it is a
   groupoid; these two projections name the halves, so that downstream
   files need not spell `1 and `2 at every use. 

   --------
   * ** 访问器

   [Grpd] 的一个对象是一个类别，并附有证明它是一个群oid；这两个投影命名了两半，这样下游文件在每次使用时就不需要拼写 `1 and ` 2。
*)

Definition grpd_cat (G : Grpd) : Category := `1 G.

Definition grpd_is_groupoid (G : Grpd) : IsGroupoid (grpd_cat G) := `2 G.

(** ** Fullness and the inclusion / ** 充实感和包容性 *)

Definition Grpd_Full : Full Cat Grpd_sub := fun _ _ _ _ _ => I.

Definition Grpd_Incl : Grpd ⟶ Cat := Incl Cat Grpd_sub.

Definition Grpd_Incl_Faithful : Functor.Faithful Grpd_Incl :=
  Incl_Faithful Cat Grpd_sub.

(*
 The inclusion is FULL as a functor, not merely full as data:
 Construction/Subcategory.v turns the one into the other. 

 --------
 包含是作为函子是完全的，而不仅仅是作为数据完全的：
 Construction/Subcategory.v 将一种转化为另一种。
*)

Definition Grpd_Incl_Full : Functor.Full Grpd_Incl :=
  Full_Implies_Full_Functor Cat Grpd_sub Grpd_Full.

(*
 [shom] ignores its morphism argument, so it is closed under `≈` for the
 trivial reason; this is the hypothesis Construction/Subcategory.v's
 [Full_Functor_Implies_Full] needs, and with it the "full subcategory iff
 full inclusion" biconditional holds for [Grpd] in both directions. 

 --------
 [shom] 忽略其态射参数，所以它在 `≈` 下是封闭的，这是一个平凡的原因；这是 Construction/Subcategory.v 的假设 [Full_Functor_Implies_Full] 所需要的，有了它，对于 [Grpd]，“完全子范畴当且仅当完全包含”的双条件在两个方向上都成立。
*)

Definition Grpd_ShomRespects : ShomRespects Cat Grpd_sub :=
  fun _ _ _ _ _ _ _ _ => I.

(*
   * ** Repleteness

   A category isomorphic in [Cat] to a groupoid is a groupoid.  Note what
   `≅[Cat]` means here: Instance/Cat.v's hom-setoid is [Functor_Setoid], so
   the two round trips are NATURAL ISOMORPHISMS, not identities -- the
   statement proved is therefore the one about equivalences, not the
   stricter one about isomorphisms on the nose.  The transported inverse of
   h : x ~> y is conjugated by the components of that natural isomorphism,
   which is where the two [comp_assoc] chains below come from. 

   --------
   * ** 完备性

   与群族同构的类别在 [Cat] 中是一个群族。注意这里的 `≅ [Cat]ZZ ` 的意思：Instance/Cat.v 的 hom-setoid 是 [Functor_Setoid]，因此两次往返是自然同构，而不是恒等——因此证明的陈述是关于等价的，而不是严格的关于严格同构的。h : x ~> y 的传输逆由该自然同构的分量共轭，这就是下面两个 [comp_assoc] 链出现的原因。
*)

Lemma IsGroupoid_transport (C D : Category) (i : C ≅[Cat] D) :
  IsGroupoid C → IsGroupoid D.
Proof.
  intros HC x y h.
  (* The counit-side natural isomorphism: to i ◯ from i ≈ Id[D]. / 余单位侧的自然同构：to i ◯ from i ≈ Id [D] 。 *)
  destruct (iso_to_from i) as [n Hn].
  pose proof (Hn _ _ h) as Hnat; simpl in Hnat.
  (* Hnat : fmap[to i] (fmap[from i] h) ≈ from (n y) ∘ h ∘ to (n x) / Hnat : fmap [to i] (fmap [from i] h) ≈ from (n y) ∘ h ∘ to (n x) *)
  assert (Hl : h ∘ to (n x) ≈ to (n y) ∘ fmap[to i] (fmap[from i] h)).
  { rewrite Hnat.
    rewrite !comp_assoc.
    rewrite (iso_to_from (n y)), id_left.
    reflexivity. }
  assert (Hr : from (n y) ∘ h ≈ fmap[to i] (fmap[from i] h) ∘ from (n x)).
  { rewrite Hnat.
    rewrite <- !comp_assoc.
    rewrite (iso_to_from (n x)), id_right.
    reflexivity. }
  unshelve econstructor.
  - exact (to (n x) ∘ fmap[to i] (ginv HC (fmap[from i] h)) ∘ from (n y)).
  - (* h ∘ h⁻¹ ≈ id *)
    rewrite !comp_assoc.
    rewrite Hl.
    rewrite <- (comp_assoc (to (n y))).
    (* Keyed rewriting does not pick this occurrence up from the bare [fmap_comp]; the instance is therefore given in full. / 键控重写不会从裸 [fmap_comp] 中捕捉到此出现；因此，该实例已完整给出。 *)
    rewrite <- (@fmap_comp _ _ (to i) _ _ _
                  (fmap[from i] h) (ginv HC (fmap[from i] h))).
    rewrite ginv_right, fmap_id, id_right.
    apply (iso_to_from (n y)).
  - (* h⁻¹ ∘ h ≈ id *)
    rewrite <- !comp_assoc.
    rewrite Hr.
    rewrite (comp_assoc (fmap[to i] (ginv HC (fmap[from i] h)))).
    rewrite <- fmap_comp.
    rewrite ginv_left, fmap_id, id_left.
    apply (iso_to_from (n x)).
Qed.

Definition Grpd_Replete : Replete Cat Grpd_sub :=
  fun x ox y f => (IsGroupoid_transport x y f ox; (I, I)).

(*
   * ** Not vacuous, and not the whole of Cat

   [Grpd] is a PROPER subcategory of [Cat]: the delooping of (ℕ, +) is a
   category whose arrow 1 has no inverse, so it is not an object of [Grpd].
   The witness is Structure/Groupoid.v's [deloop_nat_not_groupoid], whose
   own content is the specific non-invertible arrow rather than an appeal
   to "ℕ is not a group".  Without this the whole development would be
   consistent with [Grpd_sub] selecting every object of [Cat], in which
   case Construction/Groupoid/Core.v's [Core] would be the identity and its
   adjunction trivial. 

   --------
   * ** 不是空的，也不是整个 Cat

   [Grpd] 是 [Cat] 的一个适当子范畴：(ℕ, +) 的去环化是一个范畴，其箭头 1 没有逆，所以它不是 [Grpd] 的对象。证明者是 Structure/Groupoid.v 中的 [deloop_nat_not_groupoid]，其自身内容是具体的不可逆箭头，而不是诉诸于“ℕ 不是群”。没有这个，整个发展将与 [Grpd_sub] 选择 [Cat] 的每个对象一致，在这种情况下，Construction/Groupoid/Core.v 中的 [Core] 将是恒等式，其伴随是平凡的。
*)

Lemma Grpd_proper_subcategory : sobj Cat Grpd_sub (Deloop Nat_Plus) → False.
Proof. exact deloop_nat_not_groupoid. Qed.

(* The companion witness: the delooping of Z/2 IS a groupoid, so the predicate cutting [Grpd] out separates the two deloopings. / 伴随证人：Z/2 的去环化确实是一个群oid，所以将 [Grpd] 剪切出来的谓词将两个去环化分开。 *)

Definition Grpd_Deloop_Bool : Grpd :=
  (Deloop Bool_Xor_Grp; deloop_bool_groupoid).
