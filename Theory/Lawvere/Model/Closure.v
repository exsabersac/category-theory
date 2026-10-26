(** * Models are closed under product-preserving functors / * 模型在保持乘积的函子下是封闭的 *)

(*
nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   nLab:      https://ncatlab.org/nlab/show/product-preserving+functor
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   A model of a Lawvere theory [T] in a cartesian category [C] is a
   finite-product-preserving functor [law_cat T ⟶ C]
   (Theory/Lawvere/Model.v).  Composing one with a further
   finite-product-preserving functor [K : C ⟶ D] gives a model in [D],
   because preservation of finite products is closed under composition.
   That is the whole content of this file, stated once at the level of
   [Model] rather than per theory or per algebraic structure.

   PRIOR ART, MEASURED.  No such closure lemma exists anywhere in the
   tree.  Theory/Lawvere/Model.v has [Record Model], the category
   [Models], and the pack/unpack bridges, and nothing that composes a
   model with a product-preserving functor; and Functor/Structure/
   Cartesian.v and Functor/Structure/Terminal.v declare
   [CartesianFunctor] and [TerminalFunctor] with NO composition
   instance for either.  Read that narrowly: the tree DOES carry
   closure-under-composition results for a NEIGHBOURING notion --
   Structure/Limit/Preservation.v's [PreservesLimitCone_compose] and
   [continuous_compose] -- and they are cited here so the sentence above
   is not read as “nothing in the tree composes preservation”.  They
   concern a different class and do not supply either lemma built below.
   A name search over the whole tree for a
   composition of [CartesianFunctor] returns nothing.  The two
   composition results are therefore built here as well, and they are
   the reusable half:

     [CartesianFunctor_Compose] : [CartesianFunctor (K ◯ F)]
     [TerminalFunctor_Compose]  : [TerminalFunctor (K ◯ F)]

   They are stated for arbitrary [F : B ⟶ C] and [K : C ⟶ D], mention
   no Lawvere theory, and would sit equally well beside their donor
   classes; they live here because this file is their first consumer and
   because the brief for this work scoped the edit to a new file.

   HOW THE COMPARISONS COMPOSE.  Both are [iso_compose] of the outer
   functor's comparison with the image of the inner one under
   [fobj_iso] (Theory/Functor.v, which is [Defined], so its [to]
   reduces to [fmap[K] (to _)]).  For products the composite comparison
   is thus

       φ_{K◯F} = φ_K ∘ fmap[K] φ_F : K (F (x × y)) ~> K (F x) × K (F y),

   and for the terminal object, in the lax orientation
   [TerminalFunctor] uses,

       η_{K◯F} = fmap[K] η_F ∘ η_K : 1 ~> K (F 1).

   Every remaining field is then one [fmap_comp] and one associativity
   step.

   STRENGTH.  [Model_Compose_fun] records by [eq_refl] that the
   underlying functor of the composed model IS [K ◯ model_fun M] -- the
   composition is not up to isomorphism.  [Models_Compose_obj] is the
   same passage read at objects of the category [Models] via the
   existing pack/unpack bridges.

   NOT DELIVERED.  The composition is given only on OBJECTS: no functor
   [Models T C ⟶ Models T D] is built, so nothing is said about the
   action on morphisms of models (which would be left whiskering by [K])
   and no functoriality in [K] is claimed.  Neither composition instance
   is registered with [#[export] Instance] -- both are plain
   [Program Definition]s, so typeclass resolution is unperturbed; a
   consumer applies them by name.  There is no converse: nothing here
   says that if [K ◯ F] preserves finite products and [K] reflects
   isomorphisms then [F] does.  And no concrete instance is exhibited --
   the file is a conditional, like its donors.

   UNIVERSES.  All three exported results IDENTIFY the hom-and-proof
   universes of the three categories involved:
   [CartesianFunctor_Compose], [TerminalFunctor_Compose] and
   [Model_Compose] each carry [u0 = u2], [u0 = u4] and [u2 = u4] in their
   constraint blocks, over binders [B : Category@{u u0 u0}],
   [C : Category@{u1 u2 u2}], [D : Category@{u3 u4 u4}].  So a model can
   only be transported between categories sitting at the SAME hom level
   -- a real bound on what this file calls the reusable half, and one a
   consumer should know before reaching for it.  The cause is the DONOR:
   [Compose] (Theory/Functor.v) is declared
   [forall {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}}
            {E : Category@{u u3 u3}}], one shared hom-and-proof level
   across all three.  Nothing here adds to the identification and it is
   NOT claimed unavoidable; no re-annotated [Compose] was attempted, so
   “inherited rather than inherent” is an attribution, not a proof.  No
   [Set] appears in any block of this file.

   AXIOMS.  9/9 constants of this file are closed under the global
   context, counted by [Print Module] (which lists the [Program]
   obligations a [.glob] sweep does not) and queried by fully-qualified
   name.  This file declares no [Record], so there is no unlisted
   [Build_*] constructor to add -- unlike its sibling
   Structure/Group/Representable.v, whose count does need that
   correction.

--------
nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
nLab:      https://ncatlab.org/nlab/show/product-preserving+functor
维基百科: https://en.wikipedia.org/wiki/Lawvere_theory

在笛卡尔范畴 [C] 中，Lawvere 理论 [T] 的一个模型是一个保持有限积的函子 [law_cat T ⟶ C]（Theory/Lawvere/Model.v）。将其与一个进一步保持有限积的函子 [K : C ⟶ D] 组合，可以得到 [D] 中的一个模型，因为保持有限积在复合下是封闭的。这就是整个文件的全部内容，只是在 [Model] 层面上陈述，而不是针对每个理论或每个代数结构。

现有技术，已测量。在树的任何地方都不存在这样的闭合引理。Theory/Lawvere/Model.v 有 [Record Model]，范畴 [Models]，以及打包/解包桥梁，但没有将模型与保持乘积的函子组合的内容；而 Functor/Structure/Cartesian.v 和 Functor/Structure/Terminal.v 声明了 [CartesianFunctor] 和 [TerminalFunctor]，但都没有组合实例。从狭义上理解：树确实包含了针对一个相关概念的组合闭合结果——Structure/Limit/Preservation.v 的 [PreservesLimitCone_compose] 和 [continuous_compose]——它们在此引用，所以上面那句话不会被理解为“树中没有任何组合保持”。它们涉及不同的类，并没有提供下面构建的任何引理。在整个树中对 [CartesianFunctor] 的组合进行名称搜索没有返回任何结果。因此，这两个组合结果也在这里构建，并且它们是可重用的一部分：

[CartesianFunctor_Compose] : [CartesianFunctor (K ◯ F)]
[TerminalFunctor_Compose] : [TerminalFunctor (K ◯ F)]

它们是为任意的 [F : B ⟶ C] 和 [K : C ⟶ D] 规定的，没有提及任何 Lawvere 理论，也可以同它们的捐赠者类一起存在；它们出现在这里是因为这个文件是它们的第一个使用者，并且因为这项工作的简报将编辑范围限定在了一个新文件中。

比较是如何组成的。两者都是外部函子与在 [fobj_iso] 下的内部函子映像的比较的 [iso_compose]（Theory/Functor.v，它是 [Defined]，因此它的 [to] 归约为 [fmap[K]（到 _））。对于积而言，复合比较因此为

φ_{K◯F} = φ_K ∘ fmap[K] φ_F : K (F (x × y)) ~> K (F x) × K (F y),

对于终端对象，在宽松取向下 [TerminalFunctor] 使用,

η_{K◯F} = fmap[K] η_F ∘ η_K : 1 ~> K (F 1).

每个剩余的字段都是一个 [fmap_comp] 和一个关联步骤。

强度。[Model_Compose_fun] 通过 [eq_refl] 记录了复合模型的底层函子是 [K ◯ model_fun M] —— 这个复合不是按照同构来的。[Models_Compose_obj] 是通过现有的打包/解包桥在范畴 [Models] 的对象上读取的相同过程。

未交付。组合仅在对象上给出：没有函子 [Models T C ⟶ Models T D] 被构建，因此对于模型的态射的作用没有任何说明（这将是通过 [K] 的左鞭操作），并且没有宣称 [K] 的函子性。两个组合实例都没有在 [#[export] 实例中注册——两者都是普通的 [Program Definition]，因此类型类解析不受干扰；消费者通过名称应用它们。没有相反的情况：这里没有任何说明如果 [K ◯ F] 保留有限积且 [K] 反映同构，则 [F] 也具有此性质。而且没有展示具体实例——该文件是一个条件语句，就像它的提供者一样。

宇宙。 所有三个导出的结果都确定了三个相关范畴的同态和证明宇宙：[CartesianFunctor_Compose]、[TerminalFunctor_Compose] 和 [Model_Compose]，每个在其约束块中都包含 [u0 = u2]、[u0 = u4] 和 [u2 = u4]，绑定变量为 [B : Category@{u u0 u0}]、[C : Category@{u1 u2 u2}]、[D : Category@{u3 u4 u4}]。 因此，一个模型只能在位于相同同态级别的范畴之间传输——这是此文件所称的可重用部分的实际限制，并且是消费者在使用之前应该知道的。 原因在于捐赠者：[Compose]（Theory/Functor.v）被声明为 [forall {C : Category@{u0 u3 u3}} {D : Category@{u1 u3 u3}} {E : Category@{u u3 u3}}]，在这三个范畴中共享同一个同态和证明级别。 此处没有任何内容会增加识别能力，并且未声称这是不可避免的；没有尝试重新标注 [Compose]，因此“继承而非固有”是一种归属，而非证明。 此文件的任何块中都未出现 [Set]。

公理。本文件的 9/9 个常量在全局上下文下是封闭的，由 [Print Module] 计数（它列出了 [Program] 义务，而 [.glob] 扫描未列出这些义务），并通过完全限定名查询。本文件未声明任何 [Record]，因此没有未列出的 [Build_*] 构造函数需要添加——与其兄弟文件 Structure/Group/Representable.v 不同，后者的计数确实需要该修正。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.

Generalizable All Variables.

Section FunctorClosure.

Context {B C D : Category}.
Context `{CB : @Cartesian B}.
Context `{TB : @Terminal B}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.

Context (F : B ⟶ C) (K : C ⟶ D).
Context (FC : @CartesianFunctor B C F CB CC).
Context (KC : @CartesianFunctor C D K CC CD).

Program Definition CartesianFunctor_Compose :
  @CartesianFunctor B D (K ◯ F) CB CD := {|
  fobj_prod_iso := fun x y =>
    iso_compose (@fobj_prod_iso C D K CC CD KC (F x) (F y))
                (fobj_iso K _ _ (@fobj_prod_iso B C F CB CC FC x y))
|}.
Next Obligation.
  rewrite (@fmap_exl B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exl C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_exr B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_exr C D K CC CD KC).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite (@fmap_fork B C F CB CC FC).
  rewrite fmap_comp.
  rewrite (@fmap_fork C D K CC CD KC).
  now rewrite comp_assoc.
Qed.

Context (FT : @TerminalFunctor B C F TB TC).
Context (KT : @TerminalFunctor C D K TC TD).

Program Definition TerminalFunctor_Compose :
  @TerminalFunctor B D (K ◯ F) TB TD := {|
  fobj_one_iso :=
    iso_compose (fobj_iso K _ _ (@fobj_one_iso B C F TB TC FT))
                (@fobj_one_iso C D K TC TD KT)
|}.
Next Obligation.
  rewrite (@fmap_one B C F TB TC FT).
  rewrite fmap_comp.
  rewrite (@fmap_one C D K TC TD KT).
  now rewrite comp_assoc.
Qed.

End FunctorClosure.

Section ModelClosure.

Context (T : LawvereTheory).
Context {C D : Category}.
Context `{CC : @Cartesian C}.
Context `{TC : @Terminal C}.
Context `{CD : @Cartesian D}.
Context `{TD : @Terminal D}.
Context (K : C ⟶ D).
Context (KC : @CartesianFunctor C D K CC CD).
Context (KT : @TerminalFunctor C D K TC TD).

Definition Model_Compose (M : @Model T C CC TC) : @Model T D CD TD :=
  {| model_fun := K ◯ @model_fun T C CC TC M
   ; model_cartesian :=
       @CartesianFunctor_Compose (@law_cat T) C D (@law_cartesian T) CC CD
         (@model_fun T C CC TC M) K (@model_cartesian T C CC TC M) KC
   ; model_terminal :=
       @TerminalFunctor_Compose (@law_cat T) C D (@law_terminal T) TC TD
         (@model_fun T C CC TC M) K (@model_terminal T C CC TC M) KT |}.

Example Model_Compose_fun (M : @Model T C CC TC) :
  @model_fun T D CD TD (Model_Compose M) = K ◯ @model_fun T C CC TC M
  := eq_refl.

Definition Models_Compose_obj (x : @Models T C CC TC) : @Models T D CD TD :=
  @Model_pack T D CD TD (Model_Compose (@Model_unpack T C CC TC x)).

End ModelClosure.

