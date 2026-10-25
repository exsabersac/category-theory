(*
   * * Coreflective subcategories, read covariantly

   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, §IV.3, printed p. 91 (PDF p. 100), read from the
   page image: "Dually, A ⊂ B is coreflective in B when the inclusion
   functor A → B has a right adjoint.  (Warning: Mitchell [1965] has
   interchanged the meanings of "reflection" and "coreflection".)"
   The example printed on p. 92 (PDF p. 101) is the torsion subgroup:
   "A coreflective subcategory of Ab is the full subcategory of all
   torsion abelian groups (a group is torsion if all elements have
   finite order); the coreflector sends each abelian group A to the
   subgroup TA of all elements of finite order in A."  That example is
   Instance/Ab/Torsion.v, the first consumer of this file.
   Riehl, "Category Theory in Context", §4.6, printed p. 169 (PDF
   p. 189), read from the page image: Lemma 4.6.11 lists, for an
   adjunction F ⊣ G, "(iii) G is full and faithful if and only if ε is
   an isomorphism" and dually "(iii) F is full and faithful if and only
   if η is an isomorphism"; "The third conditions in each list
   characterize adjunctions defined by reflective subcategories or
   coreflective subcategories."
   nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

   BACKGROUND.  nLab defines a coreflective subcategory as "a full
   subcategory whose inclusion functor has a right adjoint R (a cofree
   functor)", calls the reflective subcategory its dual concept, and
   refers there "for more details".  Mac Lane's warning records that the
   two words were once used the other way round, so the side on which
   the adjoint sits is the whole content of the definition: a reflector
   is LEFT adjoint to the inclusion, a coreflector RIGHT adjoint.  The
   first of nLab's equivalent characterizations is that a left adjoint
   is fully faithful exactly when its unit is a natural isomorphism,
   which is Riehl's second (iii); an inclusion is fully faithful, so at
   an object of a coreflective subcategory the unit is invertible.
   That is [coreflective_unit_iso] below.

   WHY THIS FILE EXISTS.  Construction/Reflective.v defines
   [Coreflective S] as [Reflective (C^op) (op_subcategory S)]: a record
   whose reflector is typed [C^op ⟶ Sub (C^op) (op_subcategory S)] and
   whose adjunction relates opposite categories.  Nothing in the tree
   read such a record back covariantly, so a coreflection could not be
   stated as Mac Lane states it -- the inclusion has a right adjoint --
   and be an inhabitant of the record at once.  The two halves of the
   bridge:

   - [Coreflective_of_adjunction full G A : Coreflective S], built
   from covariant data: fullness of S, a functor [G : C ⟶ Sub C S]
   and an adjunction [A : Incl C S ⊣ G];
   - [coreflective_full], [coreflector] and [coreflective_adj], which
   read any record back as covariant data, the adjunction at the
   type [Incl C S ⊣ coreflector R].

   Each is built field by field.  The functor laws and the four
   naturality fields of [Adjunction] are the donor's own with their
   arguments permuted ([coreflector_op], [coreflector_op_adj]), and the
   hom-set isomorphism exchanges [to] and [from]; nothing is proved
   afresh.

   WHY FIELD BY FIELD, MEASURED.  The objects and the hom types of
   [Opposite (Sub C S)] and [Sub (Opposite C) (op_subcategory S)]
   convert, and so do the two [equiv] relations on a hom-set, but the
   two categories do not: stating their equality at [eq_refl] is
   refused with "cannot unify", and so is the equality of the two
   hom-SETOIDS, whose equivalence proofs are the different instances
   [Sub_obligation_1 C S x y] and [Sub_obligation_1 (C^op)
   (op_subcategory S) y x] of Construction/Subcategory.v's [Sub]
   ([Print Sub]).  Test/ProbeReflective370.v pins the two refusals
   beside the conversions of the objects, the hom types and the two
   [equiv] relations.  So no functor can be retyped from one side to
   the other, and handing the donor's [from] and [to] straight to
   [Build_Isomorphism Sets] is refused with a mismatch between the two
   [≊] statements; the two setoid morphisms are rebuilt around the
   donor's functions and respectfulness proofs instead.

   STRENGTHS, measured strict first.  All eight [Example]s hold at
   [eq_refl]:
   - the two halves are mutually inverse on the nose, on whole
   records and in both orders: [coreflector_roundtrip] (the
   functor), [coreflective_adj_roundtrip] (the adjunction),
   [coreflective_full_roundtrip] (the fullness witness) and
   [Coreflective_roundtrip] (the record), with the object and arrow
   parts [coreflector_obj_roundtrip] and
   [coreflector_fmap_roundtrip].  Under the project-wide primitive
   projections every record here has definitional eta, and that is
   what lets a rebuilt record convert with the one it was read
   from;
   - [coreflective_counit_is_op_unit]: the covariant counit IS the
   record's unit, and [coreflective_unit_is_op_counit]: the
   covariant unit IS the record's counit.
   [coreflective_unit_iso] is [reflective_counit_iso]'s isomorphism
   with its two inverse laws exchanged.  No constant is closed with
   [Qed].

   UNIVERSES, read by [About] under [Set Printing Universes] on all
   fifteen constants.  Each carries the binder [@{o h +}] with
   [C : Category@{o h h}], hom and proof identified; that
   identification is [Subcategory]'s own ([About Subcategory] reads
   [Category@{u u0 u0} → ...]).  The constants that mention
   [Coreflective] bind S at [Subcategory@{o h u4 h}], its fourth level
   identified with h; that is [Coreflective]'s own binder
   ([Subcategory@{u5 u6 u4 u6}]), while [coreflector_op] and
   [coreflector_op_adj] leave both of S's own levels free.  No
   constraint block carries an equation or mentions [Set].  Every
   global universe in the blocks is an upper bound and never a lower
   one: [Basics.compose.u0]-[u2], [ID.u0] and the standard library's
   [Projections.u0]/[u1] ([Sub] carries the last two in its own
   block).  The binders were measured not to narrow anything: against
   a copy of this file with every binder and annotation removed,
   compared under [Set Printing All], no constant has fewer distinct
   universes in its type (a block equation counting its two sides as
   one) or an identification the copy lacks, and one,
   [coreflector_op_adj], has one free level more.

   NOT DELIVERED.
   - Construction/Reflective.v is unchanged: [Coreflective] stays
   op-typed, and this file only reads and builds it.
   - No couniversal-arrow constructor for the record in THIS file,
   which builds a coreflection from an adjunction and does not
   require Theory/Universal/Arrow.v.  The constructor is
   Construction/Reflective/Universal.v's
   [Coreflective_of_CouniversalArrows]: Theory/Universal/Arrow/
   Dual.v's [AdjunctionFromCouniversalArrows] fed to
   [Coreflective_of_adjunction].
   - Nothing on the idempotent comonad of a coreflection beyond
   Construction/Reflective/FixedPoints.v's op-form
   [Coreflective_IdempotentMonad_op], and no co-Eilenberg–Moore
   reading.  CORRECTION (#463): at a preorder, and objectwise
   only, Instance/Proset/Monad/Interior.v's [wlocal_iff_open]
   with [wcoalgebra_iff_open] reads the coreflected objects of a
   comonad W as its coalgebras (W-local exactly when a
   W-coalgebra); no equivalence with a category of coalgebras is
   stated, so the item stands for every other category.
   - No uniqueness of the coreflector up to isomorphism. 

   --------
   * * 余反射子范畴，协变读取Mac Lane，《为在职数学家准备的范畴论》，第2版，Springer GTM 5, §IV.3, 印刷版第91页（PDF第100页），从页面图像阅读：“同理，当包含函子 A → B 有右伴随时，A ⊂ B 在 B 中是余反射的。（警告：Mitchell [1965] 交换了“反射”和“余反射”的含义。）” 
   印刷版第92页（PDF第101页）举的例子是挠子子群：“Ab 的一个余反射子范畴是所有挠阿贝尔群的满子范畴（如果群中所有元素的阶都是有限的，则该群是挠子的）；余反射函子将每个阿贝尔群 A 映射到 A 中所有有限阶元素组成的子群 TA。” 这个例子是 Instance/Ab/Torsion.v，该文件的第一个使用者。Riehl，《情境下的范畴论》，§4.6, 印刷版第169页（PDF第……）。189)、从页面图像读取：引理 4.6.11 列出了对于伴随 F ⊣ G，"(iii) 当且仅当 ε 是同构时，G 是满且忠实的"，以及对偶地 "(iii) 当且仅当 η 是同构时，F 是满且忠实的"；"每个列表中的第三个条件刻画了由反射子范畴或余反射子范畴定义的伴随关系。"
   nLab: https://ncatlab.org/nlab/show/coreflective+subcategory背景。nLab 将余反射子范畴定义为“一个包含函子具有右伴随 R（一个余自由函子）的满子范畴”，称反射子范畴为其对偶概念，并在此“参见更多细节”。Mac Lane 的警告指出，这两个词曾经用法相反，因此伴随所在的一侧就是定义的全部内容：反射子是包含函子的左伴随，余反射子是右伴随。nLab 的第一个等价表征是：当且仅当其单位为自然同构时，左伴随函子是完全忠实的，这是 Riehl 的第二个结论 (iii)；包含函子是完全忠实的，因此在余反射子范畴的一个对象上，单位是可逆的。即下面的 [coreflective_unit_iso]。这个文件存在的原因。Construction/Reflective.v 定义了 [Coreflective S] 为 [Reflective (C^op) (op_subcategory S)]：一个记录，其反射器的类型为 [C^op ⟶ Sub (C^op) (op_subcategory S)]，并且其伴随关系关联相反的范畴。树中没有任何内容以协变方式读取这样的记录，因此不能像 Mac Lane 所述那样声明一个共反射——包含具有一个右伴随——并同时成为该记录的成员。桥的两部分：

   - [Coreflective_of_adjunction full G A : Coreflective S] ，由协变数据构建：S 的充满性，一个函子 [G : C ⟶ Sub C S] 和一个伴随 [A : Incl C S ⊣ G]；
   - [coreflective_full] 、[coreflector] 和 [coreflective_adj]，它们将任何记录作为协变数据读取，伴随关系位于类型 [Incl C S ⊣ coreflector R]。每一个都是按字段逐个构建的。函子定律和 [Adjunction] 的四个自然性字段是捐赠者自身的，只是其参数被置换了（[coreflector_op]，[coreflector_op_adj]），同态集同构交换了 [to] 和 [from]；没有任何东西是重新证明的。为什么要逐字段测量。对象和同态类型 [Opposite (Sub C S)] 和 [Sub (Opposite C) (op_subcategory S)] 可以转换，两者在同态集合上的 [equiv] 关系也可以转换，但这两个范畴不行：在 [eq_refl] 上声明它们相等会被拒绝，并显示“无法统一”，两者的同态集合（hom-SETOIDS）的相等也同样被拒绝，它们的等价性证明是 Construction/Subcategory.v 的 [Sub]（[Print Sub]）的不同实例 [Sub_obligation_1 C S x y] 和 [Sub_obligation_1 (C^op) (op_subcategory S) y x]。Test/ProbeReflective370.v 将这两个拒绝与对象、同态类型及两个 [equiv] 关系的转换放在一起进行测试。因此，没有任何函子可以从一侧重新类型化到另一侧，并且将捐赠者的 [from] 和 [to] 直接传给 [Build_Isomorphism Sets] 会被拒绝，因为两个 [≊] 语句之间不匹配；这两个集合态射是围绕捐赠者的函数和尊重性证明重新构建的。优势，首先严格衡量。所有八个 [Example] 均保持在 [eq_refl]：
   - 两个部分在整个记录和两种顺序上完全互为逆：[coreflector_roundtrip]（函子）、[coreflective_adj_roundtrip]（伴随）、[coreflective_full_roundtrip]（充 fullness 证明）和 [Coreflective_roundtrip]（记录），对象和箭头部分为 [coreflector_obj_roundtrip] 和 [coreflector_fmap_roundtrip]。在整个项目范围的原始投影下，这里每个记录都具有定义性的 eta，这就是为什么重建的记录可以与其读取的记录转换；
   - [coreflective_counit_is_op_unit]：协变余单元是记录的单元，而 [coreflective_unit_is_op_counit]：协变单元是记录的余单元。[coreflective_unit_iso] 是 [reflective_counit_iso] 的同构，其两个逆律交换。没有常量是与 [Qed] 闭合的。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取，适用于所有十五个常量。每个常量都携带绑定器 [@{o h +}] 与 [C : Category@{o h h}]，hom 和证明已被标识；该标识是 [Subcategory] 自己的（[About Subcategory] 读取 [Category@{u u0 u0} → ...]）。提到 [Coreflective] 的常量在 [Subcategory@{o h u4 h}] 绑定 S，其第四层用 h 标识；这是 [Coreflective] 自己的绑定器（[Subcategory@{u5 u6 u4 u6}]），而 [coreflector_op] 和 [coreflector_op_adj] 保留 S 自己的所有层为空。不带任何约束块携带方程或提及 [Set]。块中的每个全局宇宙都是上界，而从不作为下界：[Basics.compose.u0] - [u2]，[ID.u0] 和标准库的 [Projections.u0] / [u1]（[Sub] 在其自己的块中携带最后两个）。这些绑定器的测量并不是为了缩小任何东西：与一份删除了所有绑定器和注释的文件副本相比，在 [Set Printing All] 下，没有任何常量在其类型中（将其两边视为一个整体的块方程）拥有的不同宇宙更少，或者拥有副本中缺少的识别，而 [coreflector_op_adj] 有一个额外的自由层。未交付。- Construction/Reflective.v 未更改：[Coreflective] 保持 op-typed，并且这个文件只读取并构建它。- 在此文件中没有该记录的 couniversal-arrow 构造函数，该文件从伴随构建核心反射，并且不需要 Theory/Universal/Arrow.v。构造函数是 Construction/Reflective/Universal.v 的 [Coreflective_of_CouniversalArrows]：Theory/Universal/Arrow/Dual.v 的 [AdjunctionFromCouniversalArrows] 输入到 [Coreflective_of_adjunction]。- 关于核心反射的幂等余代数之外没有其他内容，仅在 Construction/Reflective/FixedPoints.v 的 op-form [Coreflective_IdempotentMonad_op] 内，并且没有 co-Eilenberg–Moore 读取。更正 (#463)：在一个前序上，并且仅对对象，Instance/Proset/Monad/Interior.v 中的 [wlocal_iff_open] 与 [wcoalgebra_iff_open] 将一个余单子 W 的共反射对象读取为它的余代数（当且仅当一个 W-余代数时是 W-局部的）；未说明与余代数范畴的等价性，因此该条目适用于其他所有范畴。——共反射器不具有同构意义下的唯一性。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

Generalizable All Variables.

(* * ** From covariant data to the record / * ** 从协变数据到记录 *)

(*
 A covariant functor into the subcategory, read as a functor between
 the opposites.  Every field is the donor's own, with the two object
 arguments exchanged. 

 --------
 一个协变函子到子范畴，可读作对立范畴之间的函子。每个域都是出体自身的，两个对象参数交换。
*)
Definition coreflector_op@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) :
  C^op ⟶ Sub (C^op) (op_subcategory S).
Proof.
  refine (@Build_Functor (C^op) (Sub (C^op) (op_subcategory S))
            (fun x => fobj[G] x)
            (fun x y f => @fmap _ _ G y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ G y x f g E).
  - intros x. exact (@fmap_id _ _ G x).
  - intros x y z f g. exact (@fmap_comp _ _ G z y x g f).
Defined.

(*
 The covariant adjunction [Incl ⊣ G] read as [G^op ⊣ Incl^op].  The
 hom-set isomorphism is the donor's with [to] and [from] exchanged, and
 each of the four naturality fields is one of the donor's four with its
 arguments permuted: nothing is re-proved. 

 --------
 协变伴随 [Incl ⊣ G] 读作 [G^op ⊣ Incl^op]。
 同态集合同构是给体的同构，其中 [to] 和 [from] 互换，并且四个自然性域中的每一个都是给体的四个域之一，其参数被置换：没有什么被重新证明。
*)
Definition coreflector_op_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector_op G ⊣ Incl (C^op) (op_subcategory S).
Proof.
  unshelve refine
    (@Build_Adjunction (Sub (C^op) (op_subcategory S)) (C^op)
       (coreflector_op G) (Incl (C^op) (op_subcategory S))
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (from (@adj _ _ _ _ A y x)) f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ A y x) f) _).
      intros f g E. exact (proper_morphism (to (@adj _ _ _ _ A y x)) f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ A y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ A y x) f).
  - intros x y z f g. exact (@from_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@from_adj_nat_l _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_r _ _ _ _ A z y x g f).
  - intros x y z f g. exact (@to_adj_nat_l _ _ _ _ A z y x g f).
Defined.

(*
 Mac Lane's dual definition, built from covariant data: a full
 subcategory together with a right adjoint of its inclusion. 

 --------
 Mac Lane 的对偶定义，由协变数据构建：一个满子范畴及其包含函子的右伴随。
*)
Definition Coreflective_of_adjunction@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) : Coreflective S :=
  @Build_Reflective (C^op) (op_subcategory S)
    (fun x y ox oy f => full y x oy ox f)
    (coreflector_op G) (coreflector_op_adj G A).

(* * ** From the record back to covariant data / * ** 从记录回到协变数据 *)

Definition coreflective_full@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Construction.Subcategory.Full C S :=
  fun x y ox oy f => reflective_full R y x oy ox f.

Definition coreflector@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) : C ⟶ Sub C S.
Proof.
  refine (@Build_Functor C (Sub C S)
            (fun x => fobj[reflector R] x)
            (fun x y f => @fmap _ _ (reflector R) y x f) _ _ _).
  - intros x y f g E. exact (@fmap_respects _ _ (reflector R) y x f g E).
  - intros x. exact (@fmap_id _ _ (reflector R) x).
  - intros x y z f g. exact (@fmap_comp _ _ (reflector R) z y x g f).
Defined.

Definition coreflective_adj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Incl C S ⊣ coreflector R.
Proof.
  unshelve refine
    (@Build_Adjunction C (Sub C S) (Incl C S) (coreflector R)
       (fun x y => _) _ _ _ _).
  - unshelve refine (@Build_Isomorphism Sets _ _ _ _ _ _).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => from (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (from (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + refine (@Build_SetoidMorphism _ _ _ _
                (fun f => to (@adj _ _ _ _ (reflective_adj R) y x) f) _).
      intros f g E.
      exact (proper_morphism (to (@adj _ _ _ _ (reflective_adj R) y x))
               f g E).
    + intros f. exact (iso_from_to (@adj _ _ _ _ (reflective_adj R) y x) f).
    + intros f. exact (iso_to_from (@adj _ _ _ _ (reflective_adj R) y x) f).
  - intros x y z f g.
    exact (@from_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@from_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_r _ _ _ _ (reflective_adj R) z y x g f).
  - intros x y z f g.
    exact (@to_adj_nat_l _ _ _ _ (reflective_adj R) z y x g f).
Defined.

(** ** Round trips / ** 往返 *)

Example coreflector_obj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x : C) :
  fobj[coreflector (Coreflective_of_adjunction full G A)] x = fobj[G] x
  := eq_refl.

Example coreflector_fmap_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) (x y : C) (f : x ~> y) :
  fmap[coreflector (Coreflective_of_adjunction full G A)] f = fmap[G] f
  := eq_refl.

(*
 The whole functor, the whole adjunction, the fullness witness and the
 whole record all return on the nose. 

 --------
 整个函子、整个伴随、完全性证明以及整个记录都精确返回。
*)
Example coreflector_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflector (Coreflective_of_adjunction full G A) = G := eq_refl.

Example coreflective_adj_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_adj (Coreflective_of_adjunction full G A) = A := eq_refl.

Example coreflective_full_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (full : Construction.Subcategory.Full C S)
  (G : C ⟶ Sub C S) (A : Incl C S ⊣ G) :
  coreflective_full (Coreflective_of_adjunction full G A) = full
  := eq_refl.

Example Coreflective_roundtrip@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) :
  Coreflective_of_adjunction (coreflective_full R) (coreflector R)
    (coreflective_adj R) = R := eq_refl.

(* * ** Unit and counit, read across the bridge / * ** 单位与余单位，跨桥阅读 *)

(*
 The covariant counit at [x : C] IS the record's unit at [x], and the
 covariant unit at [s : Sub C S] IS the record's counit at [s]. 

 --------
 在 [x : C] 处的协变余单位是记录在 [x] 处的单位，而在 [s : Sub C S] 处的协变单位是记录在 [s] 处的余单位。
*)
Example coreflective_counit_is_op_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : C) :
  @counit _ _ _ _ (coreflective_adj R) x
    = @Category.Theory.Adjunction.unit _ _ _ _ (reflective_adj R) x
  := eq_refl.

Example coreflective_unit_is_op_counit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (s : Sub C S) :
  @Category.Theory.Adjunction.unit _ _ _ _ (coreflective_adj R) s
    = @counit _ _ _ _ (reflective_adj R) s
  := eq_refl.

(*
 The dual of [reflective_counit_iso]: at an object of a coreflective
 subcategory the unit is invertible, [x ≅ coreflector (Incl x)].  The
 two morphisms are [reflective_counit_iso]'s, and its two inverse laws
 are exchanged. 

 --------
 [reflective_counit_iso] 的对偶：在一个余反射子范畴的对象上，单位是可逆的，[x ≅ coreflector (Incl x)]。两个态射是 [reflective_counit_iso] 的，其两个逆律被交换。
*)
Definition coreflective_unit_iso@{o h +} {C : Category@{o h h}}
  {S : Subcategory C} (R : Coreflective S) (x : Sub C S) :
  x ≅[Sub C S] fobj[coreflector R] (fobj[Incl C S] x).
Proof.
  pose (i := reflective_counit_iso R x).
  unshelve refine (@Build_Isomorphism (Sub C S) _ _ (to i) (from i) _ _).
  - exact (iso_from_to i).
  - exact (iso_to_from i).
Defined.
