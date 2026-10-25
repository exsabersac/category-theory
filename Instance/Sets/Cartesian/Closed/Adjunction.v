Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.

Generalizable All Variables.

(* * * The currying adjunction in [Sets], where the counit computes / * * 在 [Sets] 中的柯里化伴随，其中余单位计算 *)

(*
 nLab: https://ncatlab.org/nlab/show/exponential+object
 Book: Riehl, "Category Theory in Context", Dover 2016; §2.1
 (Representable functors), Example 2.1.6(iv)

 Structure/Cartesian/Closed/Adjunction.v builds (- × S) ⊣ (-)^S over an
 arbitrary cartesian closed category. This file instantiates it at [Sets],
 the category of setoids, through [Sets_Cartesian] and [Sets_Closed], and
 checks that the abstract packaging computes to the expected concrete maps.

 Because [Sets_Closed] takes the exponential y^S to be the setoid of
 ≈-respecting maps S → y and [uncurry] to be λp. f (fst p) (snd p), the
 counit — which the general file already identifies with [eval] — is
 function application:

 counit (h, s) = h s,

 which [Sets_counit_apply] proves by [reflexivity]: the two sides are
 convertible, not merely ≈-related. Note what kind of statement that is. It
 relates two ELEMENTS of the carrier of a setoid, not two morphisms, so
 [reflexivity] there is a claim about computation in this model; the variant
 [Sets_counit_apply_eq] states it with Leibniz =, which is strictly stronger
 than the ≈ form and is legitimate here only because both sides are carrier
 elements that happen to be convertible. Every = appearing in this file
 relates elements of a carrier type, and the one = in
 Structure/Cartesian/Closed/Adjunction.v relates two OBJECTS of a
 category (this library has no ≈ on objects), as that file says at the
 site. No morphism is compared with = in either file. This is a statement
 about these two files, not a claim about the rest of the library.

 The middle of the file discharges the vacuity worry. A hom-setoid whose ≈
 were trivial would make the equations below hold for uninteresting reasons,
 so a concrete non-identity morphism is transposed and its transpose is
 shown to be non-constant — a genuine inequality of setoid maps
 ([curry_plus_not_constant]). The witness is addition on [NatSet], the
 natural numbers under Leibniz equality; the transpose is n ↦ (m ↦ n + m),
 and the counit applied to (curry plus_map 2, 3) computes to 5.

 Finally [Sets_Curry_Representable] is Riehl's Example 2.1.6(iv) in literal
 form: "The functor Hom(− × A, B) : Set^op → Set that sends a set X to the
 set of functions X × A → B is represented by the set B^A of functions from
 A to B." Here Set is [Sets], so "set" means setoid and "function" means
 ≈-respecting map, and the natural bijection is an isomorphism in the
 functor category [Sets^op, Sets].

 One elaboration note, since it shapes how the statements below are
 written. Several equations are between elements of a carrier rather than
 between morphisms, and [Instance/Sets.v] exports a global [Setoid False]
 instance ([False_Setoid]); when the side of a ≈ that Coq elaborates first
 has a type still blocked on instance resolution, that global instance is
 picked and the statement is rejected. The remedy used throughout is to put
 the side whose type is immediately known on the left, or to name the arrow
 with its type ascribed first (as [Sets_counit] does). This is a matter of
 elaboration order only; no statement is weakened by it. 

 --------
 nLab: https://ncatlab.org/nlab/show/exponential+object
 书籍: Riehl, 《Category Theory in Context》，Dover 2016；§2.1
 （可表示函子），例2.1.6(iv)

 Structure/Cartesian/Closed/Adjunction.v 构建了 (- × S) ⊣ (-)^S 在任意笛卡尔闭类别上的对偶。这个文件在 [Sets] ，集合体分类（setoids）中，通过 [Sets_Cartesian] 和 [Sets_Closed] 进行实例化，并检查抽象包装计算是否符合预期的具体映射。

 因为 [Sets_Closed] 将指数 y^S 定义为保持≈关系的映射 S → y 的集合体，而 [uncurry] 定义为 λp. f (fst p) (snd p)，所以余单位——一般文件已经将其标识为 [eval]——就是函数应用：

 counit (h, s) = h s,[Sets_counit_apply] 通过 [reflexivity] 证明：两边是可转换的，而不仅仅是≈相关的。注意这是一个什么样的陈述。它关联的是集合体（setoid）载体的两个元素，而不是两个态射，因此 [reflexivity] 那里是在该模型中关于计算的声明；变体 [Sets_counit_apply_eq] 使用莱布尼茨等式（Leibniz =）来陈述，它严格强于≈形式，并且这里只因两边恰好是可转换的载体元素而合法。这个文件中出现的每个=都关联载体类型的元素，而 Structure/Cartesian/Closed/Adjunction.v 中的那个=关联的是一个范畴的两个对象（该库在对象上没有≈），正如该文件在相应位置所说明的。两个文件中都没有态射与=进行比较。这是关于这两个文件的声明，而不是对整个库的断言。文件的中间部分解决了虚无的担忧。一个其≈是平凡的同态集合（hom-setoid）会使下面的方程成立，且原因并不有趣，因此一个具体的非恒等态射被转置，其转置被证明是非恒定的——这是真正的集合态射不等式（[curry_plus_not_constant]）。见证是[NatSet]上的加法，即在莱布尼茨等式下的自然数；转置是 n ↦ (m ↦ n + m)，并且对 (curry plus_map 2, 3) 应用余单位计算为 5。最后 [Sets_Curry_Representable] 是 Riehl 的例 2.1.6(iv) 的字面形式：“函子 Hom(− × A, B) : Set^op → Set，将一个集合 X 发送到从 X × A 到 B 的函数集合，由从 A 到 B 的函数集合 B^A 表示。”这里 Set 是 [Sets]，因此“集合”意味着集合模，而“函数”意味着 ≈-保持映射，自然双射是在函子范畴 [Sets^op, Sets] 中的一个同构。一个展开说明的注释，因为它决定了下面语句的写法。几个方程式是作用于承载元素之间而不是态射之间，并且 [Instance/Sets.v] 导出了一个全局 [Setoid False] 实例（[False_Setoid]）；当 Coq 首先展开的 ≈ 一侧的类型仍然受实例解析阻塞时，将会选择该全局实例，并且语句会被拒绝。贯穿全文的解决方法是将类型立即已知的一侧放在左边，或者先给箭头命名并指定其类型（正如 [Sets_counit] 所做的）。这仅仅是展开顺序的问题；没有语句因为它而被削弱。
*)

(* * ** The counit computes to function application / * ** 协单位计算为函数应用 *)

(*
 The counit of the currying adjunction at [Sets], named with its type
 ascribed so that applications of it elaborate without further hints. 

 --------
 在 [Sets] 上的柯里化伴随的余单位，其类型被指定，以便对其的应用可以在不提供更多提示的情况下进行展开。
*)
Definition Sets_counit (S y : Sets) : (y ^ S) × S ~{Sets}~> y :=
  @counit _ _ _ _ (Curry_Adjunction S) y.

(* It is evaluation, as the general theory already says. / 正如一般理论已经说明的那样，这是评估。 *)
Lemma Sets_counit_eval (S y : Sets) : Sets_counit S y ≈ eval.
Proof. reflexivity. Qed.

(* And in the model it computes: the pair of a setoid map h : S → y and a point s of S is sent to h s. Both sides are elements of the carrier of y, compared with that setoid's ≈. / 在模型中，它计算：一对集合等价映射 h : S → y 和 S 的一个点 s 被发送到 h s。两边都是 y 的载体中的元素，并与该集合等价的 ≈ 进行比较。 *)
Lemma Sets_counit_apply (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) ≈ h s.
Proof. reflexivity. Qed.

(*
 The same fact with Leibniz equality. This is strictly stronger than
 [Sets_counit_apply], and it is stated only because both sides are elements
 of a carrier type — not morphisms — and are convertible in this model. It
 is not an equality of morphisms and licenses no such equality elsewhere. 

 --------
 与莱布尼茨等式相同的事实。这严格强于 [Sets_counit_apply]，并且它之所以被陈述，仅仅是因为两边都是承载类型的元素——而不是态射——并且在此模型中是可转换的。它不是态射的等式，并且在其他地方不允许这样的等式。
*)
Lemma Sets_counit_apply_eq
  (S y : Sets) (h : SetoidMorphism S y) (s : carrier S) :
  Sets_counit S y (h, s) = h s.
Proof. reflexivity. Qed.

(*
 The two transposes compute to the expected maps: currying fixes the first
 coordinate, uncurrying pairs the arguments. By [curry_adj_to] and
 [curry_adj_from] these are the adjunction's ⌊-⌋ and ⌈-⌉. Both are
 definitional unfoldings in this model ([reflexivity] closes them); their
 content is the identification of [Sets_Closed]'s transposes with λ-
 abstraction and application, not a new equation. 

 --------
 这两个转置计算得到预期的映射：柯里化固定第一个坐标，非柯里化将参数配对。通过 [curry_adj_to] 和 [curry_adj_from]，这些是伴随的 ⌊-⌋ 和 ⌈-⌉。在这个模型中，它们都是定义性的展开（[reflexivity] 将其封闭）；它们的内容是将 [Sets_Closed] 的转置识别为 λ-抽象和应用，而不是一个新的方程。
*)
Lemma Sets_curry_apply
  (S x y : Sets) (f : x × S ~{Sets}~> y) (a : carrier x) (s : carrier S) :
  f (a, s) ≈ curry f a s.
Proof. reflexivity. Qed.

Lemma Sets_uncurry_apply
  (S x y : Sets) (g : x ~{Sets}~> y ^ S) (p : carrier (x × S)) :
  g (fst p) (snd p) ≈ uncurry g p.
Proof. reflexivity. Qed.

(* * ** A concrete witness: addition on the natural numbers / * ** 一个具体的例子：自然数上的加法 *)

(*
 The natural numbers as a setoid, with ≈ taken to be Leibniz equality on
 [nat]. The hom-setoid (NatSet × NatSet ~> NatSet) is then pointwise
 equality of functions on pairs — a non-trivial relation, which is what
 makes the equations below carry content rather than hold vacuously. 

 --------
 作为集合类的自然数，其中≈被视为[nat]上的莱布尼茨等式。然后，hom-集合类 (NatSet × NatSet ~> NatSet) 是对函数在对上的逐点等式——这是一个非平凡关系，这正是使下面的方程有实际意义而非空洞成立的原因。
*)
Program Definition NatSet : Sets := {|
  carrier   := nat;
  is_setoid := {| equiv := fun n m : nat => n = m |}
|}.

(*
 Addition, as a morphism NatSet × NatSet ~> NatSet of [Sets]: a genuinely
 non-identity, non-projection arrow. 

 --------
 加法，作为 [Sets] 的一个态射 NatSet × NatSet ~> NatSet：一个真正的非恒等、非投影箭头。
*)
Program Definition plus_map : NatSet × NatSet ~{Sets}~> NatSet := {|
  morphism := fun p => (fst p + snd p)%nat
|}.

(*
 Its transpose is n ↦ (m ↦ n + m); at 2 and 3 that computes to 5. Leibniz
 equality is used between two ELEMENTS of [nat] (the carrier of NatSet),
 never between morphisms; the two sides are convertible. 

 --------
 它的转置是 n ↦ (m ↦ n + m)；在 2 和 3 上计算结果为 5。莱布尼茨等式用于 [nat]（自然数集合的载体）的两个元素之间，从不用于态射之间；两边是可转换的。
*)
Example curry_plus_compute : curry plus_map 2%nat 3%nat = 5%nat.
Proof. reflexivity. Qed.

(*
 The counit consumes the transpose again: it applies curry plus_map 2, that
 is (m ↦ 2 + m), to 3. Again an equality of elements of [nat]. 

 --------
 余单元再次消耗转置：它将 curry plus_map 2，即 (m ↦ 2 + m)，应用到 3。再次是 [nat] 元素的等式。
*)
Example counit_plus_compute :
  Sets_counit NatSet NatSet (curry plus_map 2%nat, 3%nat) = 5%nat.
Proof. reflexivity. Qed.

(*
 The round trip of the hom-set bijection on this concrete arrow. Here the
 comparison IS between morphisms of [Sets], so it is stated with ≈. 

 --------
 这个具体箭头上同态集双射的往返。在这里，比较是在 [Sets] 的态射之间进行的，因此用 ≈ 表示。
*)
Example uncurry_curry_plus : uncurry (curry plus_map) ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.

(*
 The same round trip taken through the adjunction's own transposes, using
 the general law ⌈⌊f⌋⌉ ≈ f of Theory/Adjunction.v. 

 --------
 通过伴随自身的转置进行的相同往返，使用 Theory/Adjunction.v 中的一般定律 ⌈⌊f⌋⌉ ≈ f。
*)
Example adj_roundtrip_plus :
  from (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet)
       (to (@adj _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet) plus_map)
    ≈ plus_map.
Proof.
  exact (@to_adj_comp_law _ _ _ _ (Curry_Adjunction NatSet) NatSet NatSet
                          plus_map).
Qed.

(*
 And the universal property in elementary form: evaluation after the
 transpose recovers the original arrow. 

 --------
 而在初等形式下的泛性质：转置之后的求值会恢复原来的箭头。
*)
Example eval_curry_plus :
  eval ∘ first (curry plus_map) ≈ plus_map.
Proof. exact (ump_exponents plus_map). Qed.

(* Non-vacuity as a genuine inequality: the transpose of addition is not a constant family, so the bijection above is not an identification of two one-element setoids. Concretely 2 + 0 and 0 + 0 differ. / 作为真正的不等式的非空性：加法的转置不是一个常量族，所以上面的双射并不是两个单元素集合的同一标识。具体来说，2 + 0 和 0 + 0 是不同的。 *)
Example curry_plus_not_constant :
  (curry plus_map 2%nat ≈ curry plus_map 0%nat) -> False.
Proof.
  intros HA.
  specialize (HA 0%nat).
  simpl in HA.
  discriminate.
Qed.

(* * ** Riehl's Example 2.1.6(iv), literally / * ** Riehl 的例子 2.1.6(iv)，逐字 *)

(* The functor Hom(− × A, B) : Sets^op ⟶ Sets ... / 函子 Hom(− × A, B) : Sets^op ⟶ Sets ... *)
Definition Sets_Curry_Presheaf (A B : Sets) : Sets^op ⟶ Sets :=
  Curry_Presheaf A B.

(* ... is represented by B^A, the setoid of ≈-respecting maps A → B. / ... 表示为 B^A，即尊重 ≈ 的映射 A → B 的集合体。 *)
Definition Sets_Curry_Representable (A B : Sets) :
  Representable (Sets_Curry_Presheaf A B) := Curry_Representable A B.

(*
 On the concrete witness: the representation carries the transpose of
 addition back to addition itself, an ≈ between morphisms of [Sets]. 

 --------
 关于具体的见证：表示将加法的转置带回加法本身，在 [Sets] 的态射之间是一个 ≈。
*)
Example Sets_repr_plus :
  transform (to (Curry_Representation NatSet NatSet)) NatSet (curry plus_map)
    ≈ plus_map.
Proof. exact (uncurry_curry plus_map). Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Mac Lane §V.4, exercise 4: X × − preserves all colimits / * ** Mac Lane §V.4，练习 4：X × − 保留所有余极限 *)

(*
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer 1998, §V.4, exercise 4

 The exercise asks for the fact that `X × −` on Set preserves all small
 colimits.  With the currying adjunction in place it is a corollary and
 not a construction: `− × X` is a left adjoint, and left adjoints
 preserve colimits — the in-tree [left_adjoint_preserves_colimits] of
 Adjunction/Continuity.v.

 It is recorded here rather than left implicit because, before this file,
 no tensor or exponential adjunction was instantiated anywhere in the
 tree, so no colimit-preservation witness of this kind existed to be
 consumed.  (An audit of the first commit observed that the issue asks
 for this in prose rather than in a checkbox, and that the first commit
 had passed over it while disclosing a different, unrequested corollary.
 Both corrections are made here.)

 The statement is for `− × X` rather than `X × −`; the two agree up to
 the symmetry of the product, which this library does not silently
 identify. 

 --------
 书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，Springer 1998，第V.4节，第4题

 该练习要求证明在集合范畴上 `X × −` 保留所有小余极限。有了柯里化的伴随关系，它就是一个推论而非构造：`− × X` 是左伴随，左伴随保留余极限——Adjunction/Continuity.v 中的树内 [left_adjoint_preserves_colimits]。这里之所以记录下来而不是隐含，是因为在此文件之前，树中任何地方都没有实例化张量或指数伴随，因此不存在可以被使用的此类余极限保持证明。（对首次提交的审查发现，该问题要求以文字形式而非复选框形式表达，并且首次提交在公开一个不同的、未请求的推论时忽略了它。这里对两者都进行了更正。）

 该声明适用于 `− × X` 而非 `X × −`；两者在乘积的对称性下是相同的，而该库不会默默地识别这一点。
*)

Definition Sets_prod_preserves_colimits (X : Sets) :
  PreservesAllColimits (Prod_Functor X) :=
  @left_adjoint_preserves_colimits _ _ _ _ (Curry_Adjunction X).

(*
 And the same corollary over an arbitrary cartesian closed category, since
 the adjunction was established there. 

 --------
 在任意笛卡尔闭范畴上也有同样的推论，因为对偶关系在那里已经建立。
*)
Definition CCC_prod_preserves_colimits
  {C : Category} `{@Cartesian C} `{@Closed C _} (S : C) :
  PreservesAllColimits (Prod_Functor S) :=
  @left_adjoint_preserves_colimits _ _ _ _ (Curry_Adjunction S).
