Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Strong.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.Monoidal.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(** * Costrong comonads / * Costrong comonads *)

(*
nLab:      https://ncatlab.org/nlab/show/strong+monad
   nLab:      https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   A costrong comonad on a monoidal category (C, ⨂, I) is a comonad
   (W, ε = extract, δ = duplicate) whose endofunctor carries a tensorial
   costrength: a family

     costrength : W (x ⨂ y) ~> x ⨂ W y

   natural in both variables and coherent with the left unitor λ and the
   associator α ([costrength_id_left], [costrength_assoc], both arriving in
   their inverse orientations, as dualization inverts the structural
   isomorphisms), and compatible with the comonad structure:

     - ε-compat ([costrength_extract]):
         (id ⨂ ε) ∘ costrength ≈ ε            at  W (x ⨂ y) ~> x ⨂ y
     - δ-compat ([costrength_duplicate]):
         (id ⨂ δ) ∘ costrength ≈ costrength ∘ W costrength ∘ δ
                                                at  W (x ⨂ y) ~> x ⨂ W (W y)

   The notion is the formal dual of a (left) strong monad: a costrength for
   W over (C, ⨂) is exactly a strength for W^op over (C^op, ⨂^op).  Duality
   is built into this library so that (C^op)^op = C and (W^op)^op = W hold
   by reflexivity, and Construction/Opposite/Monoidal.v transports monoidal
   structure to the opposite category, so [CostrongComonad] is DEFINED as
   the in-tree [StrongMonad] (Monad/Strong.v) instantiated at
   (C^op, Monoidal_op M) on W^op — no second axiomatization.  The covariant
   accessors and laws below are definitional op-reads of the [StrongMonad]
   fields, in the style of Comonad/Core.v, and [Build_CostrongComonad]
   assembles the bundled structure back out of covariant data, so the
   unfolding runs in both directions.

   Following the [Monoidal_op] precedent, [CostrongComonad] and all the
   transfers in this file are Definitions, not Instances: registering them
   would let instance resolution silently equip a category with a
   (co)strength, which is rarely what an unannotated goal means.  Callers
   select them explicitly.

   Double-op caveat (see Construction/Opposite/Monoidal.v): although the
   underlying category and functor round-trip on the nose, the transported
   monoidal structure does not — [Monoidal_op (Monoidal_op M)] is not
   definitionally M, because the transport rebuilds the functor-law and
   coherence fields as fresh Qed-opaque proof terms.  A strong monad on
   (C, M) and a costrong comonad on (C^op, Monoidal_op M) are therefore
   interchanged by rebuilding the record field by field (every data and law
   component IS convertible across the two monoidal structures), and the
   resulting round trips are stated up to ≈ on the structure maps rather
   than as record equalities: see [StrongMonad_to_op_CostrongComonad],
   [op_CostrongComonad_to_StrongMonad] and the round-trip lemmas at the end
   of this file.

--------
nLab:      https://ncatlab.org/nlab/show/strong+monad
nLab:      https://ncatlab.org/nlab/show/tensorial+strength
维基百科: https://en.wikipedia.org/wiki/Strong_monad

在一个单体范畴 (C, ⨂, I) 上的共强余单子是一个余单子 (W, ε = 提取, δ = 复制)，其自函子携带一个张量余强度：一个族

共强度：W (x ⨂ y) ~> x ⨂ W y

在两个变量中都是自然的，并且与左单位元 λ 和结合子 α 一致（[costrength_id_left]、[costrength_assoc] 都以其逆向到达，因为对偶化会反转结构同构），并且与余单子结构兼容：

- ε-兼容 ([costrength_extract]):
         (id ⨂ ε) ∘ 共强度 ≈ ε            在  W (x ⨂ y) ~> x ⨂ y
     - δ-兼容 ([costrength_duplicate]):
         (id ⨂ δ) ∘ 共强度 ≈ 共强度 ∘ W 共强度 ∘ δ
                                                在  W (x ⨂ y) ~> x ⨂ W (W y)

这个概念是（左）强单子的形式对偶：在 (C, ⨂) 上的 W 的余强正好是 W^op 在 (C^op, ⨂^op) 上的强。对偶性内建于这个库中，因此 (C^op)^op = C 和 (W^op)^op = W 都通过自反性成立，并且 Construction/Opposite/Monoidal.v 将幺半群结构传递到对偶范畴，所以 [CostrongComonad] 被定义为树内的 [StrongMonad] (Monad/Strong.v) 在 W^op 上以 (C^op, Monoidal_op M) 实例化——没有第二个公理化。下面的协变访问器和定律是 [StrongMonad] 字段的定义性对偶读取，风格类似 Comonad/Core.v，而 [Build_CostrongComonad] 则将捆绑结构从协变数据中重新组合，因此展开可以在两个方向上运行。

遵循 [Monoidal_op] 的先例，[CostrongComonad] 及此文件中的所有传输都是定义，而不是实例：注册它们会让实例解析静默地为一个范畴配备一个（共）强度，而这通常不是未标注目标的含义。调用者会明确选择它们。

双运算警告（见 Construction/Opposite/Monoidal.v）：尽管底层范畴和函子回绕是精确的，但传输的幺半群结构并不是——[Monoidal_op (Monoidal_op M)] 在定义上不是 M，因为传输会将函子律和相干性字段重新构建为新的 Qed 不透明证明项。在 (C, M) 上的强单子和在 (C^op, Monoidal_op M) 上的共强余单子因此通过逐字段重建记录来互换（每个数据和律的组成部分在两个幺半群结构之间是可转换的），并且生成的回绕是对结构映射上的 ≈ 而不是记录相等而言的：参见 [StrongMonad_to_op_CostrongComonad], [op_CostrongComonad_to_StrongMonad] 以及本文件末尾的回绕引理。
*)

(*
Why costrength matters

   nLab:  https://ncatlab.org/nlab/show/tensorial+costrength
   Paper: Blute, Cockett, Seely, J. Pure Appl. Algebra 116(1-3), 1997,
          pp. 49-98 (where the term "costrength" is introduced)
   Paper: Kock, Arch. Math. 23, 1972, pp. 113-120 (tensorial strength)

   Strength is what lets a functor travel through paired data.  In
   Moggi's semantics a bare monad cannot interpret programs with more
   than one free variable; the strength carries the ambient environment
   into the effectful computation, and Monad/Strong.v exists for that
   reason.  The comonadic situation is the mirror image: a context
   W (x ⨂ y) spanning a pair must be pushable onto a chosen factor,
   W (x ⨂ y) ~> x ⨂ W y, before a co-Kleisli program can consume the
   y-part in context while passing the x-part through.  That map is
   [costrength].  In Uustalu and Vene's account of dataflow the comonad
   plays the role that strong monads play in Moggi's semantics, with
   effects reintroduced through a distributive law of the comonad over
   a monad (APLAS 2005).

   Orientation deserves care, because the literature does not speak with
   one voice.  Dually to the left and right strengths
   x ⨂ F y ~> F (x ⨂ y), a left-costrength is F (x ⨂ y) ~> x ⨂ F y —
   the form of this file — and a right-costrength is
   F (x ⨂ y) ~> F x ⨂ y.  On a symmetric base either determines the
   other through the braiding, and one says simply "costrength"; on a
   non-symmetric base a full costrength further requires the two induced
   maps F (x ⨂ (y ⨂ z)) ~> (x ⨂ F y) ⨂ z to agree.  The term is due to
   Blute, Cockett and Seely (1997); nLab cautions that Power and
   Robinson (1997) use it for what is here a right-strength.

   Whether strength is data or property depends on the base.  For a
   closed monoidal V, a strength on an endofunctor of V is the same
   thing as a V-enrichment of it, so every endofunctor of Set carries a
   canonical strength; over a general monoidal base nothing of the sort
   holds, which is why the costrength here is data to be supplied
   ([Build_CostrongComonad] takes the family and its laws as inputs)
   rather than property to be derived.

   A final distinction separates strength from monoidality.  The
   programming face of comonads with monoidal structure is Haskell's
   ComonadApply, characterized in Kmett's Control.Comonad documentation
   as "a strong lax symmetric semi-monoidal comonad", under which
   extract and duplicate become symmetric monoidal natural
   transformations; it is the interface on which Foner's comonadic
   fixed point for spreadsheet-like recurrences is built (Haskell
   Symposium 2015).  Lax (semi)monoidal structure on the endofunctor is
   a further layer that this file does not axiomatize.

--------
为什么成本力量很重要

nLab：https://ncatlab.org/nlab/show/tensorial+costrength
   论文：Blute, Cockett, Seely, J. Pure Appl. Algebra 116(1-3), 1997，
          第49-98页（介绍“协强度”一词）
   论文：Kock, Arch. Math. 23, 1972，第113-120页（张量强度）

强度是让函子能够穿过成对数据的能力。在Moggi的语义中，一个裸单子无法解释具有多个自由变量的程序；强度将环境传递到有副作用的计算中，这就是Monad/Strong.v存在的原因。余单子的情况是镜像的：一个跨越一对的上下文W(x ⨂ y)必须能够推到选择的因子上，W(x ⨂ y) ~> x ⨂ W y，在余Kleisli程序能够在上下文中消耗y部分同时传递x部分之前。这个映射就是[costrength]。在Uustalu和Vene的数据流描述中，余单子扮演了强单子在Moggi语义中的角色，副作用通过余单子对单子的分配律重新引入（APLAS 2005）。

方向性值得关注，因为文献中并没有统一的说法。对应于左侧和右侧的强度 x ⨂ F y ~> F (x ⨂ y)，左余强度是 F (x ⨂ y) ~> x ⨂ F y——这是该文件的形式——而右余强度是 F (x ⨂ y) ~> F x ⨂ y。在对称基上，一个就能通过交错确定另一个，人们就简单地称之为“余强度”；在非对称基上，一个完整的余强度还要求由此诱导的两个映射 F (x ⨂ (y ⨂ z)) ~> (x ⨂ F y) ⨂ z 一致。这个术语归功于 Blute、Cockett 和 Seely（1997）；nLab 提醒，Power 和 Robinson（1997）在此使用该术语时其实指的是这里的右强度。

强度是数据还是属性取决于基。对于一个闭单模 V，V 的一个自函子上的强度与其 V-增强是同一回事，所以 Set 的每一个自函子都具有一个规范强度；在一般的单模基上，并不存在这种情况，这就是为什么这里的余强度是需要提供的数据（[Build_CostrongComonad] 将族及其定律作为输入）而不是需要推导的属性。

最后一个区别将强性与幺半群性分开。具有幺半群结构的余单子（comonads）的编程面是 Haskell 的 ComonadApply，在 Kmett 的 Control.Comonad 文档中被描述为“一个强松对称半幺半群余单子”，在这种结构下，extract 和 duplicate 成为对称幺半群自然变换；这是 Foner 为类似电子表格的递归构建余单子固定点接口的基础（Haskell 研讨会 2015）。对自同态函子（endofunctor）而言的松（半）幺半群结构是这一文件未公理化的进一步层次。
*)

Definition CostrongComonad {C : Category} (M : @Monoidal C) (W : C ⟶ C) : Type :=
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op).

(*
Mirroring [Existing Class Comonad] in Comonad/Core.v: [CostrongComonad]
   unfolds to the class [StrongMonad], but typeclass resolution keys on the
   head constant of a goal and does not look through this unfolding.
   Declaring [CostrongComonad] an existing class lets a costrong witness in
   scope be found when the accessors below insert their implicit argument.
   No instance of it is registered anywhere in this file, so no search space
   changes.

--------
在 Comonad/Core.v 中镜像 [Existing Class Comonad]：[CostrongComonad] 展开为类 [StrongMonad]，但类型类解析是基于目标的头部常量，而不会查看此展开。将 [CostrongComonad] 声明为已有类可以在访问器插入它们的隐式参数时找到在作用域中的强证人。这个文件中没有注册它的实例，因此搜索空间没有变化。
*)
Existing Class CostrongComonad.

(* ================================================================== *)
(** ** The covariant API: definitional op-reads of the bundled fields / ** 协变 API：捆绑字段的定义性操作读取  *)
(* ================================================================== *)

Section CostrongComonadAPI.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context {CS : CostrongComonad M W}.

(** The underlying comonad: the op-read of [strongmonad_is_monad]. / 底层的 comonad：[strongmonad_is_monad] 的 op-read。 *)
Definition costrong_is_comonad : @Comonad C W :=
  @strongmonad_is_monad (C^op) (@Monoidal_op C M) (W^op) CS.

(*
Let [extract] and [duplicate] from Comonad/Core.v resolve against the
   underlying comonad in the statements below.  The registration is
   section-local and is dropped when the section closes.

--------
让来自 Comonad/Core.v 的 [extract] 和 [duplicate] 在下面的语句中针对底层 comonad 进行解析。该注册是节级别的，并且在节关闭时会被删除。
*)
#[local] Existing Instance costrong_is_comonad.

(**
The underlying strong endofunctor over (C^op, Monoidal_op M): the
    op-read of [strongmonad_is_strong].

--------
在 (C^op, Monoidal_op M) 上的基础强 endofunctor：[strongmonad_is_strong] 的 op-read。
*)
Definition costrong_is_strong :
  @StrongFunctor (C^op) (@Monoidal_op C M) (W^op) :=
  @strongmonad_is_strong (C^op) (@Monoidal_op C M) (W^op) CS.

(**
The costrength W (x ⨂ y) ~> x ⨂ W y: the covariant reading of
    [strength] at (C^op, Monoidal_op M, W^op).

--------
余强 W (x ⨂ y) ~> x ⨂ W y：在 (C^op, Monoidal_op M, W^op) 上 [strength] 的协变解读。
*)
Definition costrength {x y : C} : W (x ⨂ y) ~> x ⨂ W y :=
  @strength (C^op) (@Monoidal_op C M) (W^op) costrong_is_strong x y.

(**
Joint naturality in both variables: the op-read of [strength_natural].
    The bundled field states the square with the two variables acted on
    separately (via the [Mapping] instances of Theory/Naturality.v); the
    bifunctor interchange law [bimap_id_right_left] merges the per-variable
    actions into the usual joint form.

--------
两个变量的联合自然性：[strength_natural] 的 op-read。捆绑字段表示正方形，其中两个变量被分别作用（通过 Theory/Naturality.v 的 [Mapping] 实例）；双函子交换律 [bimap_id_right_left] 将每个变量的作用合并为通常的联合形式。
*)
Lemma costrength_natural {x y z w : C} (f : x ~> y) (k : z ~> w) :
  costrength ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ costrength.
Proof.
  pose proof (@strength_natural (C^op) (@Monoidal_op C M) (W^op)
                costrong_is_strong y x f w z k) as SN.
  simpl in SN.
  rewrite <- fmap_comp in SN.
  rewrite bimap_id_right_left in SN.
  rewrite comp_assoc in SN.
  rewrite bimap_id_right_left in SN.
  exact SN.
Qed.

(**
Left-unitor coherence: the op-read of [strength_id_left].  Dualization
    inverts the unitor, so in C the law reads against λ⁻¹: precomposing the
    costrength with W (λ⁻¹) is λ⁻¹ at W x.

--------
左单位元相干性：[strength_id_left] 的 op-read。对偶化会反转单位元，因此在 C 中该定律针对 λ⁻¹：将代数强度与 W (λ⁻¹) 预组合时，就是 W x 处的 λ⁻¹。
*)
Lemma costrength_id_left {x : C} :
  costrength ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x)).
Proof.
  exact (@strength_id_left (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x).
Qed.

(**
Associator coherence: the op-read of [strength_assoc], with α likewise
    arriving in its inverse orientation.

--------
关联一致性：[strength_assoc] 的操作读取，同样 α 以其反向方向到达。
*)
Lemma costrength_assoc {x y z : C} :
  costrength ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ costrength) ∘ costrength.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_assoc (C^op) (@Monoidal_op C M) (W^op)
           costrong_is_strong x y z).
Qed.

(**
ε-compatibility, the dual of the Kock/Moggi η-compat law
    [strength_ret]: discarding the comonadic context of the right factor
    after applying the costrength is exactly extracting from the whole
    tensor.

--------
ε-兼容性，Kock/Moggi η-兼容定律的对偶
[strength_ret]：在应用共强度之后丢弃右因子的余单子上下文，正好是从整个张量中提取。
*)
Lemma costrength_extract {x y : C} :
  (id[x] ⨂ extract) ∘ costrength ≈ (extract : W (x ⨂ y) ~> x ⨂ y).
Proof.
  exact (@strength_ret (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

(**
δ-compatibility, the dual of the μ-compat law [strength_join]:
    duplicating the right factor after applying the costrength agrees with
    duplicating the whole tensor and sliding the costrength through both
    W-layers.

--------
δ-兼容性，μ-兼容律 [strength_join] 的对偶：在应用协强度后重复右边因子，与重复整个张量并将协强度通过两个 W 层滑动一致。
*)
Lemma costrength_duplicate {x y : C} :
  (id[x] ⨂ duplicate (x:=y)) ∘ costrength
    ≈ costrength ∘ fmap[W] costrength ∘ duplicate.
Proof.
  rewrite <- comp_assoc.
  exact (@strength_join (C^op) (@Monoidal_op C M) (W^op) CS x y).
Qed.

End CostrongComonadAPI.

(*
[costrength[W]] names the costrength of a given costrong comonad on W at
   implicit arguments, mirroring the [strength[F]] convention.

--------
[costrength[W]] 命名给定的 W 上共强余单子在隐式参数下的共强度，反映 [strength[F]] 的约定。
*)
Notation "costrength[ W ]" := (@costrength _ _ W%functor _ _ _)
  (at level 9, format "costrength[ W ]") : morphism_scope.

(* ================================================================== *)
(** ** Building the bundled structure from covariant data / ** 从协变数据构建打包结构              *)
(* ================================================================== *)

Section BuildCostrongComonad.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.

(*
Predictable obligation alignment (the Monad/Kleisli.v precedent): with
   [program_simpl] the unitor and counit compatibility obligations are
   discharged by the tactic itself — their op-statements are convertible
   to the supplied hypotheses [sigma_id_left] and [sigma_extract], so it
   closes them from the local context.  Exactly three obligations remain,
   in order: naturality, the associator law, and δ-compatibility, each a
   re-bracketing of the corresponding covariant hypothesis.

--------
可预测的义务对齐（Monad/Kleisli.v 先例）：使用 [program_simpl] 时，幺元算子和余元兼容性义务由策略自身解除——它们的 op-声明可转换为提供的假设 [sigma_id_left] 和 [sigma_extract]，因此它从本地上下文中关闭它们。确切地剩下三个义务，顺序为：自然性、结合子律和 δ-兼容性，每一个都是对相应协变假设的重新括号化。
*)
#[local] Obligation Tactic := program_simpl.

(**
[Build_CostrongComonad] assembles a [CostrongComonad] from a comonad
    together with a covariant costrength family satisfying the covariant
    laws — the inverse reading of the accessor layer above.  The data
    round trip is definitional: see [Build_CostrongComonad_costrength] and
    [Build_CostrongComonad_comonad] just below.

--------
[Build_CostrongComonad] 从一个 comonad 以及满足协变定律的协变共力族组装一个 [CostrongComonad] —— 这是上面访问器层的逆向解读。数据的往返是定义性的：参见下面的 [Build_CostrongComonad_costrength] 和 [Build_CostrongComonad_comonad]。
*)
Program Definition Build_CostrongComonad
  (H : @Comonad C W)
  (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y)
  (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
    sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z)
  (sigma_id_left : forall x : C,
    sigma I x ∘ fmap[W] (from (@unit_left C M x))
      ≈ from (@unit_left C M (W x)))
  (sigma_assoc : forall x y z : C,
    sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
      ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
          ∘ sigma x ((y ⨂ z)%object))
  (sigma_extract : forall x y : C,
    (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y))
  (sigma_duplicate : forall x y : C,
    (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
      ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate)
  : CostrongComonad M W :=
  @Build_StrongMonad (C^op) (@Monoidal_op C M) (W^op) H
    (@Build_StrongFunctor (C^op) (@Monoidal_op C M) (W^op)
       (fun x y => sigma x y) _ _ _)
    _ _.
Next Obligation.
  (*
strength_natural in C^op: merge the separated actions and apply the
     covariant naturality.

--------
C^op 中的 strength_natural：合并分离的动作并应用协变自然性。
*)
  rewrite <- fmap_comp.
  rewrite bimap_id_right_left.
  rewrite comp_assoc.
  rewrite bimap_id_right_left.
  apply sigma_natural.
Qed.
Next Obligation.
  (* strength_assoc in C^op: the op-read arrives right-bracketed. / C^op 中的 strength_assoc：op-read 到达时带有右括号。 *)
  rewrite comp_assoc.
  apply sigma_assoc.
Qed.
Next Obligation.
  (* strength_join in C^op: likewise a re-bracketing of δ-compat. / strength_join 在 C^op 中：同样是 δ-兼容性的重新括号化。 *)
  rewrite comp_assoc.
  apply sigma_duplicate.
Qed.

End BuildCostrongComonad.

Section BuildCostrongComonadAgreement.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).
Context (sigma : forall x y : C, W (x ⨂ y) ~> x ⨂ W y).
Context (sigma_natural : forall (x y z w : C) (f : x ~> y) (k : z ~> w),
  sigma y w ∘ fmap[W] (f ⨂ k) ≈ (f ⨂ fmap[W] k) ∘ sigma x z).
Context (sigma_id_left : forall x : C,
  sigma I x ∘ fmap[W] (from (@unit_left C M x))
    ≈ from (@unit_left C M (W x))).
Context (sigma_assoc : forall x y z : C,
  sigma ((x ⨂ y)%object) z ∘ fmap[W] (from (@tensor_assoc C M x y z))
    ≈ from (@tensor_assoc C M x y (W z)) ∘ (id[x] ⨂ sigma y z)
        ∘ sigma x ((y ⨂ z)%object)).
Context (sigma_extract : forall x y : C,
  (id[x] ⨂ extract) ∘ sigma x y ≈ (extract : W (x ⨂ y) ~> x ⨂ y)).
Context (sigma_duplicate : forall x y : C,
  (id[x] ⨂ duplicate (x:=y)) ∘ sigma x y
    ≈ sigma x (W y) ∘ fmap[W] (sigma x y) ∘ duplicate).

(**
Reading the costrength back off the assembled structure returns the
    supplied family on the nose.

--------
读取组装结构的回弹强度会直接返回所提供的家族。
*)
Lemma Build_CostrongComonad_costrength {x y : C} :
  @costrength C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) x y
    ≈ sigma x y.
Proof. reflexivity. Qed.

(** The underlying comonad passes through the assembly unchanged. / 底层的余单子在组装过程中保持不变。 *)
Lemma Build_CostrongComonad_comonad :
  @costrong_is_comonad C M W
    (Build_CostrongComonad H sigma sigma_natural sigma_id_left
       sigma_assoc sigma_extract sigma_duplicate) = H.
Proof. reflexivity. Qed.

End BuildCostrongComonadAgreement.

(* ================================================================== *)
(** ** Transfers: costrong comonads are strong monads on the opposite / ** 传递：共强余单子是在对偶范畴上的强单子  *)
(* ================================================================== *)

(*
On a FIXED base (C, M) the correspondence is definitional — a costrong
   comonad on (C, M) literally is a strong monad on (C^op, Monoidal_op M),
   so both passages are the identity and the round trips hold by
   reflexivity.

--------
在一个固定的基 (C, M) 上，对应关系是定义性的——在 (C, M) 上的一个共强 comonad 字面上是 (C^op, Monoidal_op M) 上的一个强 monad，因此两个传递都是恒等的，且往返由自反性成立。
*)

Definition CostrongComonad_to_op_StrongMonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (CS : CostrongComonad M W) :
  @StrongMonad (C^op) (@Monoidal_op C M) (W^op) := CS.

Definition op_StrongMonad_to_CostrongComonad
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad M W := S.

Lemma CostrongComonad_op_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C} (CS : CostrongComonad M W) :
  op_StrongMonad_to_CostrongComonad (CostrongComonad_to_op_StrongMonad CS)
    = CS.
Proof. reflexivity. Qed.

Lemma op_StrongMonad_roundtrip
  {C : Category} {M : @Monoidal C} {W : C ⟶ C}
  (S : @StrongMonad (C^op) (@Monoidal_op C M) (W^op)) :
  CostrongComonad_to_op_StrongMonad (op_StrongMonad_to_CostrongComonad S)
    = S.
Proof. reflexivity. Qed.

Section StrongMonadOpposite.

Context {C : Category}.
Context {M : @Monoidal C}.
Context {T : C ⟶ C}.

(*
The other direction of the duality — a strong monad on (C, M) as a
   costrong comonad on (C^op, Monoidal_op M) — is where the double-op
   caveat bites: the target type unfolds to a [StrongMonad] over
   [Monoidal_op (Monoidal_op M)], which is not definitionally M (its law
   fields are rebuilt Qed-opaque; see Construction/Opposite/Monoidal.v).
   The records are therefore rebuilt field by field.  Every field converts:
   the tensor's object and morphism actions, and the to/from components of
   the transported unitors and associator, all reduce to those of M, so
   each projection of S is accepted at the reindexed type as it stands.
   Only the record types themselves differ, which is why the round trips
   below are stated on the structure maps (up to ≈, or as the literal
   passthrough of the monad component) rather than as record equalities.

--------
二重性的另一个方向——（C, M）上的强单子作为（C^op, Monoidal_op M）上的共强余单子——是在双重-op 警告出现的地方：目标类型展开为 [StrongMonad] 上的 [Monoidal_op (Monoidal_op M)]，而这在定义上并不是 M（它的定律字段是重新构建的 Qed-opaque；参见 Construction/Opposite/Monoidal.v）。因此，这些记录是字段逐一重建的。每个字段都会被转换：张量的对象和态射作用，以及运输的单位子和结合子的 to/from 组件，都简化为 M 的对应元素，所以 S 的每个投影在重新索引的类型下都能直接被接受。只有记录类型本身不同，这也是下面的往返操作在结构映射上陈述的原因（在 ≈ 的意义下，或作为单子组件的字面透传），而不是作为记录等式。
*)

Definition StrongMonad_to_op_CostrongComonad (S : @StrongMonad C M T) :
  @CostrongComonad (C^op) (@Monoidal_op C M) (T^op) :=
  @Build_StrongMonad ((C^op)^op)
    (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
    (@strongmonad_is_monad C M T S)
    (@Build_StrongFunctor ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
       (fun x y => @strength C M T (@strongmonad_is_strong C M T S) x y)
       (@strength_natural C M T (@strongmonad_is_strong C M T S))
       (@strength_id_left C M T (@strongmonad_is_strong C M T S))
       (@strength_assoc C M T (@strongmonad_is_strong C M T S)))
    (@strength_ret C M T S)
    (@strength_join C M T S).

Definition op_CostrongComonad_to_StrongMonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @StrongMonad C M T :=
  @Build_StrongMonad C M T
    (@strongmonad_is_monad ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@Build_StrongFunctor C M T
       (fun x y => @strength ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S) x y)
       (@strength_natural ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_id_left ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S))
       (@strength_assoc ((C^op)^op)
          (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op)
          (@strongmonad_is_strong ((C^op)^op)
             (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)))
    (@strength_ret ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S)
    (@strength_join ((C^op)^op)
       (@Monoidal_op (C^op) (@Monoidal_op C M)) ((T^op)^op) S).

(**
Covariantly read, the costrength of the opposite costrong comonad IS
    the strength of the strong monad it came from.

--------
协变地阅读时，对应的余强余单子的余强度就是它所来源的强单子的强度。
*)
Lemma op_costrength_strength (S : @StrongMonad C M T) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad S) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

(**
Round trips.  The strength data survives both passages on the nose (so
    ≈ holds by reflexivity), and the underlying monad is passed through
    untouched; only the enclosing records differ, per the double-op caveat
    in the header.

--------
往返行程。强度数据在两次经过上都保留原样（所以≈通过自反性成立），底层的单子未经修改直接传递；只有外部的记录不同，根据标题中的双操作提示。
*)

Lemma StrongMonad_op_roundtrip_strength (S : @StrongMonad C M T) {x y : C} :
  @strength C M T
    (@strongmonad_is_strong C M T
       (op_CostrongComonad_to_StrongMonad
          (StrongMonad_to_op_CostrongComonad S))) x y
    ≈ @strength C M T (@strongmonad_is_strong C M T S) x y.
Proof. reflexivity. Qed.

Lemma StrongMonad_op_roundtrip_monad (S : @StrongMonad C M T) :
  @strongmonad_is_monad C M T
    (op_CostrongComonad_to_StrongMonad (StrongMonad_to_op_CostrongComonad S))
    = @strongmonad_is_monad C M T S.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_costrength
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) {x y : C} :
  @costrength (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    x y
    ≈ @costrength (C^op) (@Monoidal_op C M) (T^op) S x y.
Proof. reflexivity. Qed.

Lemma op_CostrongComonad_roundtrip_comonad
  (S : @CostrongComonad (C^op) (@Monoidal_op C M) (T^op)) :
  @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op)
    (StrongMonad_to_op_CostrongComonad (op_CostrongComonad_to_StrongMonad S))
    = @costrong_is_comonad (C^op) (@Monoidal_op C M) (T^op) S.
Proof. reflexivity. Qed.

End StrongMonadOpposite.
