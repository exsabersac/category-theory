Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(**
The hom-action of a functor: [fmap] as one natural transformation of
    hom-bifunctors. 

--------
函子的 hom-action：[fmap] 作为 的一种自然变换
 同位双函子。 
*)

(*
nLab:      https://ncatlab.org/nlab/show/hom-functor
   nLab:      https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor
   Book:      Mac Lane, “Categories for the Working Mathematician”,
              2nd ed., Springer GTM 5, §II.5 Exercise 7 (printed p. 45)
              [maclane:II.5:ex7]

   A functor T : A ⟶ D carries, for each pair of objects (a, b), a map of
   hom-sets

     T_{a,b} : hom_A(a, b) → hom_D(T a, T b),   g ↦ fmap[T] g,

   and Mac Lane's exercise is to observe that this whole family is a single
   natural transformation. The two sides are bifunctors on one and the same
   index category A^op ∏ A: the source is the hom-bifunctor Hom A of
   Functor/Hom.v, and the target is Hom D with T inserted in BOTH slots —
   contravariantly in the first, covariantly in the second — that is,

     Hom D ◯ (T^op ∏⟶ T) : A^op ∏ A ⟶ Sets,   (a, b) ↦ hom_D(T a, T b).

   The transformation [hom_action] below has fmap[T] as its component at every
   pair, and its naturality square at a morphism (h, k) of A^op ∏ A — so
   h : a' ~{A}~> a and k : b ~{A}~> b' — reads

     fmap[T] k ∘ fmap[T] g ∘ fmap[T] h  ≈  fmap[T] (k ∘ g ∘ h).

   Naturality in the pair is therefore not an extra law: it is exactly two
   instances of [fmap_comp], with the two sides already associated alike. This
   is the precise sense in which “fmap is natural in both variables jointly”,
   and it is the two-variable packaging of the more familiar one-variable
   statements (naturality of T on hom(a, −) and on hom(−, b) separately).

   The composite [T^op ∏⟶ T] is new here, and the claim is a narrow one: every
   OTHER pullback of a hom-bifunctor ALONG A PRODUCT OF TWO FUNCTORS in the
   tree carries the IDENTITY in one of its two slots.  (The qualifier does
   work: [CoHom_Alt C := Hom C ◯ Swap], Functor/Hom.v, pulls a hom
   bifunctor back along the factor-exchange functor, which is not of the
   form F ∏⟶ G at all.)  Theory/Profunctor.v is the shape precedent,

     Repr_left F  := Hom D ◯ (F^op ∏⟶ Id),
     Repr_right U := Hom C ◯ (Id^op ∏⟶ U),

   and Adjunction/Hom.v pairs exactly those two, its [hom_adj] making an
   adjunction a natural isomorphism between them. A functor repeated in both
   slots is not by itself new — [(⨂) ◯ F ∏⟶ F] is the tensor comparison of a
   monoidal functor (Functor/Structure/Monoidal.v) — but that composite has
   no opposite slot and no hom-bifunctor. What the doubled T buys here is that
   the index category stays fixed at A^op ∏ A, so the hom-maps of a SINGLE
   functor become comparable to Hom A by an ordinary natural transformation,
   rather than by a comparison between two distinct profunctors.

   Componentwise readings of fullness and faithfulness follow (Mac Lane's
   “optional but natural” second half). Theory/Functor.v defines [Faithful]
 with the single field [fmap_inj], injectivity of fmap[T] with respect
   to ≈, and [Full] with a chosen preimage [prefmap] together with
   [fmap_sur] making it a section of fmap[T] — note that no functoriality of
   [prefmap] is demanded. Read through [hom_action], these say precisely that
   every component of the transformation is injective, respectively surjective
   as data. Both correspondences are stated as biconditionals with ↔, which in
   this library is Lib/Foundation.v's Type-valued [iffT]: the classes are
   Type-valued, and the [Full] direction genuinely transports data, [prefmap]
   being the first projection of the surjectivity witness. The four directions
   are also available as separately named lemmas. 

--------
nLab：https://ncatlab.org/nlab/show/hom-functor
 nLab：https://ncatlab.org/nlab/show/functor
 维基百科：https://en.wikipedia.org/wiki/Hom_functor
 书：Mac Lane，“工作数学家的类别”，
 第二版，Springer GTM 5，§II.5 练习 7（印刷第 45 页）
 保护0X

函子 T : A ⟶ D 对于每对对象 (a, b) 都有一个映射
 霍姆集

T_{a,b} : hom_A(a, b) → hom_D(T a, T b), g ↦ fmap[T] g,

麦克莱恩的练习是观察整个家庭都是一个人
 自然转变。 两侧是一侧的双函子且相同
 索引类别 A^op ∏ A：源是 hom-biunctor Hom A
 Functor/Hom.v，目标是 Hom D，两个槽中都插入了 T —
 第一个是逆变的，第二个是协变的——也就是说，

Hom D ◯ (T^op ∏⟶ T) : A^op ∏ A ⟶ 集合，(a, b) ↦ hom_D(T a, T b)。

下面的转换 [hom_action] 在每个位置都将 fmap[T] 作为其组件
 对，其自然性平方于 A^op ∏ A 的态射 (h, k) — 所以
 h : a' ~{A}~> a 和 k : b ~{A}~> b' — 读取

fmap[T] k ∘ fmap[T] g ∘ fmap[T] h ≈ fmap[T] (k ∘ g ∘ h)。

因此，配对的自然性并不是一个额外的法则：它恰好是两个
 [fmap_comp] 的实例，两侧已经关联相同。 这个
 是“fmap 在两个变量联合中是自然的”的精确含义，
 就是大家比较熟悉的一变量的二变量包装
 陈述（分别是 T 在 hom(a, −) 和 hom(−, b) 上的自然性）。

复合材料 [T^op ∏⟶ T] 是这里的新产品，其声明范围很窄：每个
 hom-biunctor 的其他回调以及两个函子的乘积
 树在其两个槽之一中携带 IDENTITY。 （预选赛确实
 工作：[CoHom_Alt C := Hom C ◯ Swap]，Functor/Hom.v，拉一个 hom
 双函子沿着因子交换函子返回，它不属于
 完全形成 F ∏⟶ G。）Theory/Profunctor.v 是形状先例，

Repr_left F := Hom D ◯ (F^op ∏⟶ Id),
 Repr_right U := Hom C ◯ (Id^op ∏⟶ U),

Adjunction/Hom.v 恰好将这两个配对，其 [hom_adj] 使
 它们之间存在着自然的同构。 函子在两者中重复
 slot 本身并不新鲜——[(⨂) ◯ F ∏⟶ F] 是一个张量比较
 幺半群函子 (Functor/Structure/Monoidal.v) — 但该复合体具有
 没有相反的槽，也没有 hom-biunctor。 双T在这里买的是
 索引类别固定为 A^op ∏ A，因此 SINGLE 的 hom-maps
 通过普通的自然变换，函子变得与 Hom A 相当，
 而不是通过两个不同的函子之间的比较。

完整度和忠实度的成分解读如下（Mac Lane 的
 “可选但自然”后半部分）。 Theory/Functor.v 定义 [Faithful]
 与单场 [fmap_inj] 相比，fmap[T] 的单射性
 到 ≈，[Full] 与选定的原像 [prefmap] 一起
 [fmap_sur] 使其成为 fmap[T] 的一部分 — 请注意，
 需要 [prefmap]。 通读 [hom_action]，这些恰恰说明了这一点
 变换的每个分量都是单射的，分别是满射的
 作为数据。 两个对应关系都被表述为带有 ↔ 的双条件，其中
 该库是 Lib/Foundation.v 的类型值 [iffT]：这些类是
 类型值，[Full]方向真正传输数据，[prefmap]
 是满射见证的第一个投影。 四个方向
 也可作为单独命名的引理使用。 
*)

Open Scope category_scope.

Section HomAction.

Context {A D : Category}.
Context (T : A ⟶ D).

(*
The Sets-morphism component at a pair p = (a, b) of objects: the hom-map
   g ↦ fmap[T] g, from hom_A(a, b) to hom_D(T a, T b). Its [proper_morphism]
   field is exactly [fmap_respects], supplied directly, so this is a plain
   [Definition] with no deferred obligation at all — which is what lets the
   component reduce, and hence [hom_action_component] below hold by eq_refl. 

--------
一对对象 p = (a, b) 处的集合态射分量：hom-map
 g ↦ fmap[T] g，从 hom_A(a, b) 到 hom_D(T a, T b)。 它的 [proper_morphism]
 字段正是 [fmap_respects]，直接提供，所以这是一个简单的
 [Definition] 完全没有递延义务——这就是让
 组件减少，因此 [hom_action_component] 低于 eq_refl 所保持的值。 
*)
Definition hom_action_at (p : A^op ∏ A) :
  Hom A p ~{Sets}~> (Hom D ◯ (T^op ∏⟶ T)) p := {|
  morphism := fun g => fmap[T] g;
  proper_morphism := fun g g' (eqv : g ≈ g') => fmap_respects _ _ g g' eqv
|}.

(*
Mac Lane §II.5 Exercise 7: the hom-maps of T assemble into one natural
   transformation between the hom-bifunctor of A and the hom-bifunctor of D
   pulled back along T in both variables. 

--------
Mac Lane §II.5 练习 7：T 的 hom-map 组装成一个自然的
 A 的同位双函子与 D 的同位双函子之间的变换
 两个变量都沿着 T 拉回。 
*)
Program Definition hom_action : Hom A ⟹ Hom D ◯ (T^op ∏⟶ T) := {|
  transform := hom_action_at
|}.
(* naturality: fmap[T] k ∘ fmap[T] g ∘ fmap[T] h ≈ fmap[T] (k ∘ g ∘ h)  / 自然性： fmap[T] k ∘ fmap[T] g ∘ fmap[T] h ≈ fmap[T] (k ∘ g ∘ h)*)
Next Obligation. now rewrite !fmap_comp. Qed.
(* naturality_sym: the same square in the opposite orientation  / natureity_sym：相反方向的同一个正方形*)
Next Obligation. now rewrite !fmap_comp. Qed.

(*
The component of [hom_action] at (a, b) IS the arrow function of T. This
   holds by [eq_refl]: the transformation stores [hom_action_at], whose
   [morphism] field is fmap[T] on the nose. Everything below is phrased through
   the transformation's components, and this lemma is what identifies those
   components with fmap[T]. 

--------
[hom_action] 在 (a, b) 处的分量是 T 的箭头函数。这
 [eq_refl] 成立：变换存储 [hom_action_at]，其
 [morphism] 场是鼻子上的 fmap[T]。 下面的所有内容都是通过
 转换的组成部分，这个引理就是识别那些
 带有 fmap[T] 的组件。 
*)
Lemma hom_action_component (a b : A) (f : a ~{A}~> b) :
  transform[hom_action] (a, b) f = fmap[T] f.
Proof. reflexivity. Qed.

(*
Faithfulness, read componentwise: every component of [hom_action] is
   injective with respect to ≈. 

--------
忠实地，逐个阅读：[hom_action] 的每个组件都是
 关于 ≈ 的单射。 
*)
Definition hom_action_injective : Type :=
  ∀ (a b : A) (f g : a ~{A}~> b),
    transform[hom_action] (a, b) f ≈ transform[hom_action] (a, b) g → f ≈ g.

(*
Fullness, read componentwise: every component of [hom_action] is surjective
   AS DATA — a preimage is produced, not merely asserted to exist. (In this
   library ∃ is [sigT], so the two readings coincide; see Lib/Foundation.v.) 

--------
完整性，按组件读取：[hom_action] 的每个组件都是满射的
 作为数据——原像被产生，而不仅仅是断言存在。 （在这个
 库∃是[sigT]，所以两个读数一致； 参见 Lib/Foundation.v.） 
*)
Definition hom_action_surjective : Type :=
  ∀ (a b : A) (g : T a ~{D}~> T b),
    ∃ (f : a ~{A}~> b), transform[hom_action] (a, b) f ≈ g.

Theorem Faithful_hom_action_injective : Faithful T → hom_action_injective.
Proof. intros F a b f g H; exact (fmap_inj f g H). Qed.

Theorem hom_action_injective_Faithful : hom_action_injective → Faithful T.
Proof. intros H; constructor; intros a b f g Hfg; exact (H a b f g Hfg). Qed.

(*
Faithful T ⟺ every component of [hom_action] is injective. Both directions
   are near-definitional: [Faithful]'s only field IS the implication, and the
   components are fmap[T] by [hom_action_component]. The two directions are
   [Qed] (following Functor/Hom.v's own [Yoneda_Faithful]), but the pair itself
   is a transparent [Definition], so projecting the biconditional gives back
   the named lemmas by conversion. 

--------
忠实的 T ⟺ [hom_action] 的每个组件都是单射的。 两个方向
 接近定义：[Faithful] 的唯一字段是含义，并且
 组件是 [hom_action_component] 的 fmap[T]。 两个方向是
 [Qed]（遵循 Functor/Hom.v 自己的 [Yoneda_Faithful]），但该对本身
 是一个透明的 [Definition]，因此投影双条件会返回
 通过转换命名的引理。 
*)
Definition hom_action_faithful_iff : Faithful T ↔ hom_action_injective :=
  (Faithful_hom_action_injective, hom_action_injective_Faithful).

Definition Full_hom_action_surjective : Full T → hom_action_surjective :=
  fun F a b g => (prefmap g; fmap_sur g).

Definition hom_action_surjective_Full : hom_action_surjective → Full T :=
  fun H => {| prefmap := fun a b g => `1 (H a b g)
            ; fmap_sur := fun a b g => `2 (H a b g) |}.

(*
Full T ⟺ every component of [hom_action] is surjective as data. Stated with
   ↔ = [iffT], since [Full] carries data: [prefmap] is recovered as the first
   projection of the surjectivity witness and [fmap_sur] as the second, so the
   backward direction is a repackaging rather than an implication between
   propositions. Both directions are given as terms, hence transparent, so the
   transported data reduces: prefmap of the round trip IS the original prefmap
   by conversion. 

--------
Full T ⟺ [hom_action] 的每个组件作为数据都是满射的。 陈述与
 ↔ = [iffT]，由于 [Full] 携带数据：[prefmap] 被恢复为第一个
 满射见证的投影和 [fmap_sur] 作为第二个，所以
 向后方向是重新包装而不是之间的暗示
 的建议。 两个方向都以术语形式给出，因此是透明的，因此
 传输的数据减少：往返的 prefmap 是原始 prefmap
 通过转换。 
*)
Definition hom_action_full_iff : Full T ↔ hom_action_surjective :=
  (Full_hom_action_surjective, hom_action_surjective_Full).

End HomAction.

(*
Acceptance: the transformation computes. At the identity functor every
   component is the identity on hom-sets, and at a composite it is the
   composite of the two arrow functions — both on the nose, by [eq_refl].
   These are the definitional [=] readings the house rule permits alongside ≈;
   they are labelled as such, and every statement about MORPHISMS above uses ≈. 

--------
接受：转换计算。 在恒等函子处，每
 分量是 hom 集上的恒等式，在复合体上它是
 两个箭头功能的组合——都在鼻子上，由 [eq_refl] 设计。 
这些是内部规则允许的 [=] 定义读数；
 它们被这样标记，并且上面关于形态的每个陈述都使用 ≈。 
*)

Example hom_action_Id (A : Category) (a b : A) (f : a ~{A}~> b) :
  transform[hom_action (@Id A)] (a, b) f = f.
Proof. reflexivity. Qed.

Example hom_action_Compose {A B D : Category} (F : B ⟶ D) (G : A ⟶ B)
        (a b : A) (f : a ~{A}~> b) :
  transform[hom_action (F ◯ G)] (a, b) f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.
