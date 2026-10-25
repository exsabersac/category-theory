Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Ens_V, the category of sets belonging to a set V / * * Ens_V，属于集合 V 的集合的类别 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §I.2 "Categories", printed p. 11 (PDF p. 21)
 nLab: https://ncatlab.org/nlab/show/category+of+sets
 nLab: https://ncatlab.org/nlab/show/full+subcategory
 nLab: https://ncatlab.org/nlab/show/type+universe

 Mac Lane's construction, as this repo's catalog summarizes it: for any set
 V of sets, Ens_V is
 the category with objects all sets X in V and arrows all functions
 f : X → Y with the usual composition; "Ens" then denotes any one of these
 categories. The point is the word ALL — the arrows carry no side condition
 whatever, so Ens_V is the FULL subcategory of the category of sets spanned by
 the members of V. What V buys is size: by choosing V one gets a category
 whose objects form a set rather than a proper class.

 Rendered type-theoretically, "a set V of sets" is a type of codes together
 with a decoding of each code into a type — a universe à la Tarski in the
 nLab's terminology, as opposed to a universe à la Russell where the codes
 *are* the types. So this file is parameterized by

 V  : Type          the codes, i.e. the members of Mac Lane's V
 El : V → Type      the decoding, i.e. "the set named by this code"

 and builds the category

 objects: the codes x : V
 arrows: x ~> y  :=  El x → El y      (ALL functions, no side condition)
 hom-setoid: f ≈ g  :=  ∀ a : El x, f a = g a
 identity: the identity function
 composition: ordinary function composition

 [EnsV_Sets] is the same construction over Instance/Sets.v instead: [El]
 decodes into [SetoidObject], an arrow is a setoid map, and two arrows are
 identified when they agree pointwise up to the codomain's own `≈`. Both are
 instances of one section, [Spanned], which spans a full subcategory of an
 arbitrary ambient category C along a family El : V → C. 

 --------
 书籍：Mac Lane，《Categories for the Working Mathematician》，第2版（GTM 5），§I.2 “Categories”，印刷版第11页（PDF第21页）
 nLab:  https://ncatlab.org/nlab/show/category+of+sets 
 nLab:  https://ncatlab.org/nlab/show/full+subcategory 
 nLab:  https://ncatlab.org/nlab/show/type+universe 

 Mac Lane 的构造，如本仓库的目录所总结：对于任何集合的集合 V，Ens_V 是一个范畴，其对象是 V 中的所有集合 X，箭头是所有函数 f : X → Y，具有通常的复合；“Ens”则表示这些范畴中的任意一个。关键在于“所有”一词——箭头没有任何附加条件，因此 Ens_V 是由 V 的成员生成的集合范畴的完整子范畴。V 的作用在于大小：通过选择 V，人们得到一个对象构成集合而非真正类的范畴。从类型理论的角度来看，“一个集合的集合 V”是一种代码类型，以及每个代码解码为一种类型——在 nLab 的术语中是一个 Tarski 式的宇宙，相对于 Russell 式的宇宙，其中代码本身就是类型。所以这个文件由以下参数化

 V  : Type          代码，即 Mac Lane 的 V 的成员
 El : V → Type      解码，即“这个代码所命名的集合”

 并构建类别

 对象：代码 x : V
 箭头：x ~> y  :=  El x → El y      （所有函数，无附加条件）
 同态集合：f ≈ g  :=  ∀ a : El x, f a = g a
 恒等式：恒等函数
 组合：普通函数组合[EnsV_Sets] 在 Instance/Sets.v 上的构造相同，只是变为：[El] 解码为 [SetoidObject]，箭头是一个集合等价映射，当两个箭头在每一点上与值域自身的 `≈` 一致时，它们被视为相同。两者都是一个截面 [Spanned] 的实例，该截面沿着一个族 El : V → C 扩展了一个任意环境范畴 C 的完整子范畴。
*)

(*
 How this file sits in the library, and what "recovers Coq" is measured to mean

 nLab: https://ncatlab.org/nlab/show/Grothendieck+universe
 Book: Mac Lane, CWM 2nd ed., §I.2, printed p. 11 (PDF p. 21)

 Three neighbours, and what distinguishes each.

 Instance/Ens.v is NOT this construction, despite the name. Its [Ens] has for
 objects the dependent pairs [∃ T : Type, Ensemble T] and for arrows the
 whole-carrier functions f : TA → TB satisfying ∀ x, x ∈ A ↔ f x ∈ B — that
 is, A = f⁻¹(B), membership preservation AND reflection. Its own header says
 so outright: "This file does NOT build that classical category directly."
 [EnsT], in the same file, is that idea with one carrier type fixed. (Those
 two are cited by name rather than by line, since the pointer comment this
 file's arrival adds to Instance/Ens.v moves them.) They are subobject-flavoured
 categories whose arrows are constrained; Mac Lane's Ens_V constrains nothing.
 Both files are kept, and neither construction subsumes the other.

 Instance/Coq.v ([Coq]) and Instance/Sets.v ([Sets]) are the
 "everything at one universe level" categories: objects are all of [Type@{o}],
 respectively all setoids at level o, and arrows are all functions,
 respectively all setoid maps. They are Ens_V with the bound fixed at a
 universe rather than at an arbitrary family — which is the set-theorist's
 Grothendieck universe (a transitive set closed under the usual operations,
 per the nLab) doing the job Mac Lane assigns to V. What this file adds is the
 arbitrary family: V may be any type at all, with no closure conditions, so a
 two-object Ens_V is as available as a universe-sized one.

 The relationship to [Coq] is measured, not asserted. At the tautological
 family (V := the objects of [Coq], El := the identity) the two categories
 are DEFINITIONALLY EQUAL: [EnsV_recovers_Coq] below is proved by [eq_refl],
 which is a conversion check on the whole [Category] record, subsuming
 agreement of every field — objects, homs, hom-setoids together with their
 [Equivalence] proofs, identity, composition, and all four laws. This is
 strictly stronger than an isomorphism in Cat. (It is not stronger than
 field-wise agreement: with definitional eta the two are equivalent.)

 The mechanism deserves a precise account, because an earlier draft got it
 wrong. For the two INSTANCE equalities below, eta is not what does the
 work: [Coq] and [Sets] are transparent constants whose bodies are literal
 records, so the check is constructor-against-constructor by delta, iota
 and beta alone. Where primitive-projection eta (Lib.v's [Primitive
 Projections]; the let-in fields [uhom], [dom], [cod] do not obstruct it on
 Rocq 9.1) becomes load-bearing is the GENERAL statement, where the ambient
 category is a variable and no delta is available:
 [Spanned_recovers_ambient] proves [@Spanned C (@obj C) (λ x, x) = C] for
 every C by the same one-line [eq_refl], and the two instance equalities
 are its corollaries. The same holds one universe over for [Sets]
 ([EnsV_Sets_recovers_Sets]). What is
 claimed is exactly what [eq_refl] checks: convertibility of the two
 [Category] values. Nothing is claimed about the two definitions' proof terms
 being syntactically the same, and the recovery is not vacuous — a family
 other than the identity is rejected by the same conversion check.

 On smallness. Mac Lane calls Ens_V a category of sets *within* a set
 precisely because its objects form a set. The corresponding in-tree fact is
 [EnsV_obj_is_V]: the object type of [EnsV El] is [V] on the nose, with no
 universe inflation and no packaging. So the size of Ens_V is exactly the size
 the caller chooses for V — [bool], a finite type, [nat], or the whole of
 [Type@{o}] — and [EnsV_two] below is a two-object witness that the small case
 is genuinely inhabited rather than vacuous. This is a remark about the shape
 of the definition, not a theorem: the library carries no internal notion of
 smallness or size, so "small" here means only "the codes are a type the
 caller picked", and nothing about cardinality is being claimed. 

 --------
 这个文件在图书馆中的位置，以及“恢复 Coq”被理解的含义

 nLab:  https://ncatlab.org/nlab/show/Grothendieck+universe 
 书籍: Mac Lane, CWM 第二版, §I.2, 印刷第11页（PDF第21页）

 三个邻居，以及区分每个邻居的特点。Instance/Ens.v 并不是这种结构，尽管名字如此。它的 [Ens] 的对象是依赖对 [∃ T : Type, Ensemble T]，而箭头则是满足 ∀ x, x ∈ A ↔ f x ∈ B 的全载函數 f : TA → TB——也就是说，A = f⁻¹(B)，既保留成员关系又反映成员关系。它自己的文件头明确说明了这一点：“该文件不直接构建那个经典范畴。”ZW3WZZ 在同一个文件中，是固定一个载体类型后的那个想法。（这两个是按名称引用，而不是按行，因为这个文件到达时的指针注释移动了它们在 Instance/Ens.v 中的位置。）它们是子对象风格的范畴，其箭头受到约束；而 Mac Lane 的 Ens_V 对箭头不作任何约束。两个文件都保留着，且彼此的构建设计并不包含对方。Instance/Coq.v ([Coq]) 和 Instance/Sets.v ([Sets]) 是“单一宇宙等级下的所有东西”类别：对象分别是 [Type@{o}] 的所有对象，以及 o 级的所有集合对象，箭头分别是所有函数，以及所有集合映射。它们是 Ens_V，其上界固定在一个宇宙中，而不是在任意族上——这是集合论者的 Grothendieck 宇宙（一个在通常操作下封闭的传递集，根据 nLab 的定义）完成 Mac Lane 指派给 V 的工作。这个文件增加了任意族：V 可以是任何类型，没有闭包条件，因此一个双对象 Ens_V 与一个宇宙大小的 Ens_V 一样可用。与 [Coq] 的关系是通过测量而不是断言来确定的。在自明的范畴族 (V := [Coq] 的对象，El := 恒等) 上，这两个范畴在定义上是相等的：下面的 [EnsV_recovers_Coq] 由 [eq_refl] 证明，它是对整个 [Category] 记录的转换检查，包括每个字段的一致性——对象、态射、态射集合及其 [Equivalence] 证明、恒等、复合以及所有四条定律。这严格强于 Cat 中的同构。（它不比字段级一致性更强：在定义性 eta 下，两者是等价的。）这个机制值得精确说明，因为早期的草稿对此理解错误。对于下面的两个 INSTANCE 等式，eta 并不是起作用的因素：[Coq] 和 [Sets] 是透明常量，其主体是字面记录，因此检查完全是通过 delta、iota 和 beta 的构造器对构造器的比较完成的。当原语投影 eta（Lib.v 的[原语投影]；let-in 字段 [uhom]、[dom]、[cod] 在 Rocq 9.1 上不会阻碍它）起到支撑作用时，是在 GENERAL 声明中，此时的环境类别是变量且没有可用的 delta：[Spanned_recovers_ambient] 对每个 C 通过同一行 [eq_refl] 证明 [@Spanned C (@obj C) (λ x, x) = C]，而这两个实例等式是它的推论。同样的情况也适用于高一层宇宙的 [Sets]（[EnsV_Sets_recovers_Sets]）。所主张的正是 [eq_refl] 所检查的内容：两个 [Category] 值的可转换性。对于两个定义的证明项在语法上是否相同，没有任何主张，并且恢复并非空洞——除了恒等式之外的其他族会被相同的转换检查拒绝。关于小性。Mac Lane 称 Ens_V 为一个集合中的集合的范畴，正是因为它的对象构成一个集合。相应的 in-tree 事实是 [EnsV_obj_is_V]：[EnsV El] 的对象类型恰好是 [V]，没有宇宙膨胀，也没有打包。因此，Ens_V 的大小正好是调用者为 V 选择的大小——[bool]，一个有限类型，[nat]，或者整个 [Type@{o}]——而下面的 [EnsV_two] 是一个有两个对象的例证，表明小的情况确实是有实例的，而不是空的。这是关于定义形状的一个备注，而不是定理：库中没有内部的小性或大小概念，所以这里的“小”仅意味着“代码是调用者选定的类型”，并不对基数作任何声明。
*)

(* * ** The full subcategory of C spanned by a family / * ** 由一个族生成的 C 的全子范畴 *)

(*
 nLab: https://ncatlab.org/nlab/show/full+subcategory

 Given any category C and any family El : V → C of its objects, [Spanned] has
 V for objects and, between codes x and y, exactly the C-morphisms
 El x ~> El y. Every field is the corresponding field of C read along El, so
 every law is C's law and nothing is reproved. El is not required to be
 injective: distinct codes may decode to the same object of C, in which case
 [Spanned] carries two copies of it. This is the general shape; Mac Lane's
 Ens_V is the case C = [Coq], and its setoid counterpart the case C = [Sets].

 The section is self-contained and does not mention [Coq] or [Sets]; should
 another development want it, it moves to Construction/ unchanged. 

 --------
 nLab：https://ncatlab.org/nlab/show/full+subcategory

 给定任意范畴 C 及其对象的任意族 El : V → C，[Spanned] 的对象是 V，在代码 x 和 y 之间正好有 C-态射 El x ~> El y。每个域都是沿着 El 读取的 C 的相应域，因此每条定律都是 C 的定律，没有什么需要重新证明。El 不要求是单射：不同的代码可能解码到同一个 C 的对象，在这种情况下 [Spanned] 携带其两个副本。这是一般的形式；Mac Lane 的 Ens_V 是 C = [Coq] 的情况，其集合同伴是 C = [Sets] 的情况。

 这一节是自包含的，不提及 [Coq] 或 [Sets]；如果其他发展需要它，它会移动到 Construction/ 中保持不变。
*)

Section Spanned.

Context {C : Category}.
Context {V : Type}.
Context (El : V → C).

Definition Spanned : Category := {|
  obj     := V;                                    (* objects are the codes / 对象是代码 *)
  hom     := λ x y, El x ~> El y;                  (* ALL C-arrows between decodings / 所有解码之间的 C 箭头 *)
  homset  := λ x y, @homset C (El x) (El y);       (* C's hom-setoid, unchanged / C 的同态集合，不变 *)
  id      := λ x, @id C (El x);                    (* C's identity / C的身份 *)
  compose := λ x y z f g, @compose C (El x) (El y) (El z) f g;  (* C's composition / C 的组成 *)

  compose_respects := λ x y z, @compose_respects C (El x) (El y) (El z);

  id_left  := λ x y, @id_left  C (El x) (El y);
  id_right := λ x y, @id_right C (El x) (El y);

  comp_assoc     := λ x y z w, @comp_assoc     C (El x) (El y) (El z) (El w);
  comp_assoc_sym := λ x y z w, @comp_assoc_sym C (El x) (El y) (El z) (El w)
|}.

(*
 The inclusion into the ambient category: decode on objects, and the identity
 on morphisms, since a [Spanned] morphism already IS a C-morphism. 

 --------
 包含到环境范畴中：在对象上解码，在态射上保持恒等，因为一个 [Spanned] 态射本身就是一个 C 态射。
*)
Program Definition Spanned_Incl : Spanned ⟶ C := {|
  fobj := El;
  fmap := λ _ _ f, f
|}.

(*
 It is full — the chosen preimage of a C-morphism is that morphism — which is
 the formal content of "spanned by El" being a FULL subcategory. 

 --------
 它是满的——C-态射的选定前像就是该态射——这就是“由 El 张成”是满子范畴的形式内容。
*)
#[export] Program Instance Spanned_Incl_Full : Full Spanned_Incl := {|
  prefmap := λ _ _ g, g
|}.

(*
 And faithful, since the hom-map is the identity function. Note that it is
 injective on objects only when El is; fullness and faithfulness are hom-level
 statements and hold for every family. 

 --------
 并且是忠实的，因为同态映射是恒等函数。注意，当 El 是时，它在对象上才是单射；充实性和忠实性是同态层面的陈述，并且对每一个族都成立。
*)
#[export] Program Instance Spanned_Incl_Faithful : Faithful Spanned_Incl := {|
  fmap_inj := λ _ _ _ _ H, H
|}.

End Spanned.

(* * ** Ens_V over [Coq]: objects are codes, arrows are all functions / * ** Ens_V 在 [Coq] 上：对象是代码，箭头都是函数 *)

(*
 Mac Lane's Ens_V. The decoding lands in bare types, so an arrow is an
 arbitrary function and morphism equivalence is pointwise Leibniz equality,
 exactly as in Instance/Coq.v. 

 --------
 Mac Lane 的 Ens_V。解码落在裸类型中，因此箭头是任意函数，态射等价是逐点的 Leibniz 等式，正如在 Instance/Coq.v 中一样。
*)
Definition EnsV {V : Type} (El : V → Type) : Category := @Spanned Coq V El.

(* The inclusion Ens_V ⟶ Set, full and faithful by the section above. / 通过上述部分，包含映射 Ens_V ⟶ Set 是满且忠实的。 *)
Definition EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  @Spanned_Incl Coq V El.

(* Statement fidelity, checked by conversion rather than argued. Objects are the members of V on the nose. / 声明的忠实性，通过转换而不是争论来检查。 对象就是 V 中的成员。 *)
Definition EnsV_obj_is_V {V : Type} (El : V → Type) : @obj (EnsV El) = V := eq_refl.

(*
 Arrows from x to y are ALL functions El x → El y: the right-hand side is the
 bare function type, carrying no membership condition and no other side
 condition. This is the clause the issue's reviewer note singles out. 

 --------
 从 x 到 y 的箭头是所有函数 El x → El y：右侧是裸函数类型，不带任何成员条件，也不带其他附加条件。这是问题的审阅者备注特别指出的条款。
*)
Definition EnsV_hom_is_all_functions {V : Type} (El : V → Type) (x y : V) :
  @hom (EnsV El) x y = (El x → El y) := eq_refl.

(* Two arrows are identified exactly when they agree pointwise. / 当两个箭头在各点上都相同时，它们被认为是完全相同的。 *)
Definition EnsV_equiv_is_pointwise {V : Type} (El : V → Type) (x y : V)
           (f g : @hom (EnsV El) x y) :
  (f ≈ g) = (∀ a : El x, f a = g a) := eq_refl.

(* Identity and composition are "the usual" ones, in Mac Lane's phrase. / 用麦克莱恩的话说，恒等式和组合是“通常的”那些。 *)
Definition EnsV_id_is_identity {V : Type} (El : V → Type) (x : V) (a : El x) :
  @id (EnsV El) x a = a := eq_refl.

Definition EnsV_compose_is_usual {V : Type} (El : V → Type) (x y z : V)
           (f : @hom (EnsV El) y z) (g : @hom (EnsV El) x y) (a : El x) :
  (f ∘ g) a = f (g a) := eq_refl.

(* * ** Ens_V over [Sets]: the setoid-flavoured variant / * ** Ens_V 在 [Sets] 上：集合类型风格的变体 *)

(*
 The same construction with the decoding landing in setoids. An arrow is a
 setoid map (a function together with its respectfulness certificate) and two
 arrows agree when they are pointwise `≈`-equal, exactly as in
 Instance/Sets.v. This variant is the one to use when Ens_V must serve as
 the codomain of a hom-functor or otherwise interact with the library's
 setoid-enriched machinery; the [Coq]-flavoured one above is the literal
 reading of Mac Lane, where a set is a bare type and equality of elements is
 Leibniz equality. 

 --------
 相同的构造在解码后落在集合等价类中。一个箭头是一个集合等价映射（一个函数以及其符合性证明），当它们在每一点上 `≈` -相等时，两箭头称为一致，正如在 Instance/Sets.v 中一样。当 Ens_V 必须作为同态函子（hom-functor）的余域或以其他方式与库中的集合等价增强机制交互时，应使用此变体；上面带有 [Coq] 风格的变体是 Mac Lane 的字面解读，其中集合只是一个裸类型，元素的等价是 Leibniz 等价。
*)
Definition EnsV_Sets {V : Type} (El : V → SetoidObject) : Category :=
  @Spanned Sets V El.

Definition EnsV_Sets_Incl {V : Type} (El : V → SetoidObject) : EnsV_Sets El ⟶ Sets :=
  @Spanned_Incl Sets V El.

Definition EnsV_Sets_obj_is_V {V : Type} (El : V → SetoidObject) :
  @obj (EnsV_Sets El) = V := eq_refl.

(*
 Arrows are ALL setoid maps between the decodings — again no side condition
 beyond the respectfulness that being a morphism of [Sets] already means. 

 --------
 箭头是解码之间的所有集合态射——再次强调，没有除了作为  [Sets]  的态射所已经意味着的尊重性之外的附加条件。
*)
Definition EnsV_Sets_hom_is_all_setoid_maps {V : Type} (El : V → SetoidObject)
           (x y : V) :
  @hom (EnsV_Sets El) x y = SetoidMorphism (El x) (El y) := eq_refl.

Definition EnsV_Sets_equiv_is_pointwise {V : Type} (El : V → SetoidObject)
           (x y : V) (f g : @hom (EnsV_Sets El) x y) :
  (f ≈ g) = (∀ a : El x, f a ≈ g a) := eq_refl.

(* * ** The tautological family recovers the ambient category / * ** 拓扑家族恢复环境范畴 *)

(*
 At V := the objects of [Coq] and El := the identity family, [EnsV] IS [Coq]:
 the two [Category] records are convertible, so [eq_refl] typechecks. Every
 field agrees definitionally — including the hom-setoids with their
 [Equivalence] proofs and all four category laws — because [Spanned] never
 builds a field, it only reads one off the ambient category.

 The measured strength is therefore definitional equality of the two
 categories, which is strictly stronger than an isomorphism in Cat and
 equivalent (under eta) to field-wise agreement: any statement whatever about
 [Coq] transports to [EnsV (λ T : Type, T)] by conversion alone. 

 --------
 在 V := [Coq] 的对象 和 El := 恒等族 的情况下，[EnsV] 是 [Coq]：
 这两个 [Category] 记录是可转换的，因此 [eq_refl] 类型检查通过。每个字段在定义上都一致——包括带其 [Equivalence] 证明的同态集和所有四条范畴定律——因为 [Spanned] 从不构建字段，它只从环境范畴中读取字段。

 因此测量的强度是两个范畴的定义性等价，这比 Cat 中的同构严格得多，并且在 eta 下等价于按字段一致：关于 [Coq] 的任何陈述都可以仅通过转换传输到 [EnsV (λ T : Type, T)]。
*)
(*
 The general form, for ANY ambient category: spanning C by its own objects
 along the identity family gives back C on the nose.  This is the statement
 for which definitional eta on [Category] is genuinely load-bearing -- C is
 a variable here, so no delta unfolding is available and the conversion
 must go record-against-eta-expansion.  The two named recoveries below are
 its instances (each also checkable by delta alone, their ambients being
 transparent constants). 

 --------
 一般形式，对于任何环境范畴：通过其自身对象沿着恒等族生成 C 会精确地返回 C。这就是在 [Category] 上定义性 η 真正起作用的陈述——C 在这里是一个变量，因此没有 δ 展开的可用性，转换必须通过记录对 η 展开的方式进行。下面两个命名的恢复是它的实例（每一个也可以仅通过 δ 检查，其环境都是透明常量）。
*)
Definition Spanned_recovers_ambient {C : Category} :
  @Spanned C (@obj C) (λ x, x) = C := eq_refl.

Definition EnsV_recovers_Coq : EnsV (λ T : Type, T) = Coq := eq_refl.

(* The same one universe over, for the setoid-flavoured variant and [Sets]. / 同一个宇宙，对于集合风味的变体和 [Sets]。 *)
Definition EnsV_Sets_recovers_Sets :
  EnsV_Sets (λ X : SetoidObject, X) = Sets := eq_refl.

(** ** A small Ens_V / ** 一个小的 Ens_V *)

(*
 Mac Lane's V is a SET of sets, and the interesting case is the one his
 notation is for: V small. Here is the two-member case, V = {1, 2}, a category
 with exactly two objects whose homs are honest function types. Its object
 type is [bool] and nothing has been enlarged, which is the whole content of
 the smallness remark in the header. 

 --------
 Mac Lane 的 V 是一组集合，有趣的情况是他的符号所针对的情况：V 很小。这里是一个有两个元素的例子，V = {1, 2}，这是一个恰好有两个对象的范畴，其同态是标准的函数类型。它的对象类型是 [bool]，且没有任何东西被放大，这就是标题中关于小规模的注释的全部内容。
*)
Definition EnsV_two_family (b : bool) : Type := if b then unit else bool.

Definition EnsV_two : Category := EnsV EnsV_two_family.

Definition EnsV_two_obj : @obj EnsV_two = bool := eq_refl.

(* The arrows from the one-element member to the two-element member are all functions unit → bool, and back again all functions bool → unit. / 从单元素成员到双元素成员的箭头全都是函数 unit → bool，而返回的箭头全都是函数 bool → unit。 *)
Definition EnsV_two_hom_up : @hom EnsV_two true false = (unit → bool) := eq_refl.

Definition EnsV_two_hom_down : @hom EnsV_two false true = (bool → unit) := eq_refl.
