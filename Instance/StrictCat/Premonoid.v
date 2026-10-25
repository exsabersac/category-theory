Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Construction.Funny.Unitors.
Require Import Category.Construction.Funny.Associator.
Require Import Category.Instance.StrictCat.Funny.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Binoidal.

Generalizable All Variables.

(*
   * * Strict premonoidal structures as monoid objects in (StrictCat, □)

   The funny bridge: a strict premonoidal structure on a category [c] is
   precisely a monoid object in the symmetric monoidal category
   [(StrictCat, □, 1)] of Instance/StrictCat/Funny.v.  This is the funny
   counterpart of the classical fact that a monoid in [(Cat, ∏, 1)] is a
   strict monoidal category:

   - the multiplication [mappend : c □ c ⟶ c] is a tensor that is
   functorial in each variable SEPARATELY — by the funny tensor's
   universal property (Construction/Funny.v: a functor out of [c □ c]
   is exactly a [SepFunctorial] assignment), with no interchange law
   relating the two partial actions.  This "separately functorial,
   jointly not" tensor is the binoidal core of a premonoidal category
   in the sense of Power–Robinson ("Premonoidal categories and notions
   of computation", MSCS 7(5), 1997); see also nLab, "funny tensor
   product" and "premonoidal category";
   - the unit [mempty : 1 ⟶ c] picks out the tensor unit object;
   - the monoid laws, read in StrictCat's strict hom-setoid
   [Functor_StrictEq_Setoid], say that unitality and associativity of
   the tensor hold on the nose, the comparison data being the funny
   unitors (Construction/Funny/Unitors.v) and the funny associator
   (Construction/Funny/Associator.v).  Strictness makes all of
   Power–Robinson's central coherence isomorphisms identities, so no
   centrality conditions need to be stated: this is the STRICT case of
   the premonoidal notion whose general, iso-weakened form lives in
   Structure/Premonoidal.v.

   The record [StrictPremonoidal] below spells out the three monoid laws in
   unfolded form (the field types ARE the types of [mempty_left],
   [mempty_right] and [mappend_assoc] at [(StrictCat, Funny_Monoidal, c)],
   up to definitional unfolding), so the two constructions

   [StrictPremonoidal_of_Monoid]  and  [Monoid_of_StrictPremonoidal]

   are pure repackagings, mutually inverse on the nose: the record-level
   round trips [roundtrip_monoid] and [roundtrip_strict_premonoidal] hold
   by [reflexivity].  The extractions [StrictPremonoidal_Binoidal] and
   [StrictPremonoidal_SepFunctorial] connect the multiplication to the
   [Binoidal] class of Structure/Binoidal.v and to the funny tensor's
   universal property, again definitionally on the generating steps.

   What is NOT built here: the bridge from [StrictPremonoidal] to the
   library's iso-weakened [Premonoidal] class (Structure/Premonoidal.v) —
   its coherence isomorphisms would be transported along the strict object
   equalities, with naturality via the StrictEq seam helpers — is deferred;
   the payoff sections below stop at the [Binoidal]/[SepFunctorial]
   fragment and the object-level strict laws.

   Universe scope.  [Funny_Monoidal@{u} : Monoidal@{u Set}] pins
   StrictCat's member categories to [Category@{Set Set Set}].  Re-declaring
   the instance at a rigid universe [v] is blocked: the compiled unitors of
   Construction/Funny/Unitors.v carry a minimized [Set] level, so
   [Build_Monoidal] at member level [v] reports "Cannot enforce Set = v" at
   the unitor field (checked-in probe: Test/ProbeFunnyPoly.v, whose [Fail]
   guards reproduce the failure).  Everything below therefore holds for
   [Set]-small carrier categories; lifting the restriction requires
   re-declaring the unitors with explicit universe binders in
   Construction/Funny/Unitors.v, which is left as future work. 

   --------
   * * 严格前单态结构作为 (StrictCat, □) 中的幺半群对象

   有趣的桥梁：在类别 [c] 上的严格前单态结构正是对称单态类别 [(StrictCat, □, 1)]（Instance/StrictCat/Funny.v 中的类别）的幺半群对象。这是经典事实的有趣对应：在 [(Cat, ∏, 1)] 中的幺半群就是严格单态类别。- 乘法 [mappend : c □ c ⟶ c] 是一个在每个变量上单独函子化的张量——根据这个有趣张量的普遍性质（Construction/Funny.v：从 [c □ c] 出发的函子恰好是一个 [SepFunctorial] 的分配），没有任何互换律将这两个部分作用联系起来。这个“分别函子化、联合不函子化”的张量是预单模范畴的双模核，在 Power–Robinson 的意义上（"Premonoidal categories and notions of computation", MSCS 7(5), 1997）；另见 nLab，"funny tensor product" 和 "premonoidal category"。
   - 单位 [mempty : 1 ⟶ c] 选取张量单位对象；
   - 在 StrictCat 的严格 Hom-setoid [Functor_StrictEq_Setoid] 中读取的幺半群律说明张量的单位律和结合律严格成立，其比较数据是有趣的单位子（Construction/Funny/Unitors.v）和有趣的结合子（Construction/Funny/Associator.v）。严格性使所有的 Power–Robinson 的中心一致性同构成为恒等式，因此不需要陈述任何中心性条件：这是前单体概念的严格情况，其一般的、同构弱化形式存在于 Structure/Premonoidal.v 中。

   下面的记录 [StrictPremonoidal] 展开了三条单体法则（字段类型是 [mempty_left]、[mempty_right] 和 [mappend_assoc] 在 [(StrictCat, Funny_Monoidal, c)] 处的类型，直至定义展开），所以两个构造

   [StrictPremonoidal_of_Monoid] 和 [Monoid_of_StrictPremonoidal]只是纯粹的重新打包，彼此完全互逆：记录级的往返  [roundtrip_monoid] 和 [roundtrip_strict_premonoidal] 由 [reflexivity] 成立。提取 [StrictPremonoidal_Binoidal] 和 [StrictPremonoidal_SepFunctorial] 将乘法与 Structure/Binoidal.v 中的 [Binoidal] 类以及有趣张量的普遍性性质连接起来，同样在生成步骤上是定义上的。

   这里没有构建的是：从 [StrictPremonoidal] 到库中 iso-弱化 [Premonoidal] 类（Structure/Premonoidal.v）的桥接 —— 它的一致性同构将沿严格对象等式传递，并通过 StrictEq 接缝辅助工具保持自然性 —— 被推迟；下面的收益部分只停在 [Binoidal] / [SepFunctorial] 碎片和对象级严格律上。宇宙范围。[Funny_Monoidal@{u} : Monoidal@{u Set}] 引脚
   严格猫的成员类别到 [Category@{Set Set Set}]。重新声明
   在刚性宇宙 [v] 的实例是被阻止的：Construction/Funny/Unitors.v 的已编译单元具有最小化的 [Set] 级别，因此
   在成员级别 [v] 的 [Build_Monoidal] 报告“无法在单元场强制执行 Set = v”（已登记探测器：Test/ProbeFunnyPoly.v，其 [Fail] 守卫重现了该失败）。因此，以下内容适用于 [Set] -小型载体类别；解除限制需要
   在 Construction/Funny/Unitors.v 中用显式宇宙绑定重新声明单元器，这将作为未来工作处理。
*)

(*
   * ** Strict premonoidal structures

   The three law fields are stated as strict equalities of functors, i.e.
   in [Functor_StrictEq_Setoid]: their right-hand sides are the funny
   unitors and associator, exactly as in the unfolded [MonoidObject] laws
   at [(StrictCat, Funny_Monoidal, c)].  In particular

   [to (@Funny_unit_left c)]  is definitionally [Funny_unit_left_to],
   [to (@Funny_unit_right c)] is definitionally [Funny_unit_right_to],
   [to (@Funny_assoc c c c)]  is definitionally [FunnyAssocTo],

   and [FunnyBimap F G] is definitionally [bimap[FunnyTensor] F G], so the
   types below convert to the [mempty_left]/[mempty_right]/[mappend_assoc]
   types on the nose.  The law fields are Type-valued (a
   [Functor_StrictEq_Setoid] equivalence is a sigma of an object-equality
   family and transported morphism agreement); projecting out the
   object-equality family at specific objects yields the object-level
   strict laws [StrictPremonoidal_unit_left_obj] etc. below. 

   --------
   * ** 严格前模结构

   这三个律域被表述为函子严格相等，即在 [Functor_StrictEq_Setoid] 中：它们的右侧是有趣的单位子和结合子，正如在展开的 [MonoidObject] 律中在 [(StrictCat, Funny_Monoidal, c)] 所示。特别是：

   [to (@Funny_unit_left c)] 定义上等于 [Funny_unit_left_to]，
   [to (@Funny_unit_right c)] 定义上等于 [Funny_unit_right_to]，
   [to (@Funny_assoc c c c)] 定义上等于 [FunnyAssocTo]，

   并且 [FunnyBimap F G] 定义上等于 [bimap[FunnyTensor] F G]，因此下面的类型直接转换为 [mempty_left] / [mempty_right] / [mappend_assoc] 类型。律域的类型是 Type 值（一个 [Functor_StrictEq_Setoid] 等价是一个对象等式族和传递的态射一致性的 σ 类型）；在特定对象上投影出对象等式族可以得到下面的对象层面严格律 [StrictPremonoidal_unit_left_obj] 等。
*)

Record StrictPremonoidal (c : Category) : Type := {
  sp_tensor : (c □ c) ⟶ c;
  sp_unit   : _1 ⟶ c;

  (* left unit law: tensoring with the unit on the left is the left funny unitor, strictly / 左单位律：在左边与单位张量化是左搞笑单位器，严格地 *)
  sp_unit_left :
    @equiv _ (@Functor_StrictEq_Setoid (_1 □ c) c)
      (sp_tensor ◯ FunnyBimap sp_unit Id[c])
      (to (@Funny_unit_left c));

  (* right unit law: tensoring with the unit on the right is the right funny unitor, strictly / 右单位律：在右边与单位张量化是右搞笑单元器，严格来说 *)
  sp_unit_right :
    @equiv _ (@Functor_StrictEq_Setoid (c □ _1) c)
      (sp_tensor ◯ FunnyBimap Id[c] sp_unit)
      (to (@Funny_unit_right c));

  (* associativity: the two reassociated double tensors agree across the funny associator, strictly / 结合性：两个重新结合的双张量在有趣的结合子作用下严格一致 *)
  sp_assoc :
    @equiv _ (@Functor_StrictEq_Setoid ((c □ c) □ c) c)
      (sp_tensor ◯ FunnyBimap sp_tensor Id[c])
      ((sp_tensor ◯ FunnyBimap Id[c] sp_tensor) ◯ to (@Funny_assoc c c c))
}.

Arguments sp_tensor {c} _.
Arguments sp_unit {c} _.
Arguments sp_unit_left {c} _.
Arguments sp_unit_right {c} _.
Arguments sp_assoc {c} _.

(*
   * ** The correspondence

   Both directions are pure repackagings: the record fields were stated as
   the unfolded monoid-object laws, so each construction is an explicit
   constructor application whose arguments typecheck by conversion alone. 

   --------
   * ** 对应关系

   两个方向都是纯粹的重新打包：记录字段被表述为展开的幺半群对象定律，因此每个构造都是一个显式的构造器应用，其参数仅通过转换就能进行类型检查。
*)

Definition StrictPremonoidal_of_Monoid {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) : StrictPremonoidal c :=
  @Build_StrictPremonoidal c
    mappend[m]
    mempty[m]
    (@mempty_left StrictCat Funny_Monoidal c m)
    (@mempty_right StrictCat Funny_Monoidal c m)
    (@mappend_assoc StrictCat Funny_Monoidal c m).

Definition Monoid_of_StrictPremonoidal {c : Category}
  (p : StrictPremonoidal c) : @MonoidObject StrictCat Funny_Monoidal c :=
  @Build_MonoidObject StrictCat Funny_Monoidal c
    (sp_unit p)
    (sp_tensor p)
    (sp_unit_left p)
    (sp_unit_right p)
    (sp_assoc p).

(*
   * ** Round trips

   The two constructions are mutually inverse — as whole records, not
   merely on the data.  [MonoidObject] and [StrictPremonoidal] both have
   primitive projections (Category.Lib exports [Set Primitive
   Projections]) and hence definitional eta, and each direction is a
   constructor application of the other's projections, so both composites
   are definitionally the identity and [reflexivity] closes the
   record-level equalities.  The four data-projection equalities that
   follow are immediate specializations, kept for direct reference. 

   --------
   * ** 往返操作

   这两种构造在整体记录层面上是互为逆操作的——不仅仅是在数据层面。[MonoidObject] 和 [StrictPremonoidal] 都有原始投影（Category.Lib 导出 [Set Primitive Projections]），因此具有定义性的 eta，并且每个方向都是另一个投影的构造器应用，因此两个复合操作在定义上都是恒等的，[reflexivity] 完成了记录级别的等式。随后的四个数据投影等式是直接特化结果，保留用于直接引用。
*)

Lemma roundtrip_monoid {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m) = m.
Proof. reflexivity. Qed.

Lemma roundtrip_strict_premonoidal {c : Category} (p : StrictPremonoidal c) :
  StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p) = p.
Proof. reflexivity. Qed.

Lemma roundtrip_mempty {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mempty[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mempty[m].
Proof. reflexivity. Qed.

Lemma roundtrip_mappend {c : Category}
  (m : @MonoidObject StrictCat Funny_Monoidal c) :
  mappend[Monoid_of_StrictPremonoidal (StrictPremonoidal_of_Monoid m)]
    = mappend[m].
Proof. reflexivity. Qed.

Lemma roundtrip_sp_unit {c : Category} (p : StrictPremonoidal c) :
  sp_unit (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_unit p.
Proof. reflexivity. Qed.

Lemma roundtrip_sp_tensor {c : Category} (p : StrictPremonoidal c) :
  sp_tensor (StrictPremonoidal_of_Monoid (Monoid_of_StrictPremonoidal p))
    = sp_tensor p.
Proof. reflexivity. Qed.

(*
   * ** Object-level strict laws

   The object-equality families of the three law fields, at specific
   objects: the tensor is strictly unital and associative on objects.
   [ttt] is the lone object of [_1], so [fobj[sp_unit p] ttt] is the tensor
   unit object; each statement converts to the projected component because
   the unitors' and associator's object actions compute on literal pairs. 

   --------
   * ** 对象级严格法律

   三个法律领域的对象相等族，在特定对象上：张量在对象上严格满足单位元和结合性。
   [ttt] 是 [_1] 的唯一对象，所以 [fobj[sp_unit p] ttt] 是张量单位对象；每个陈述都转换为投影分量，因为单位元和结合子的对象作用在字面对上计算。
*)

Corollary StrictPremonoidal_unit_left_obj {c : Category}
  (p : StrictPremonoidal c) (x : c) :
  fobj[sp_tensor p] (fobj[sp_unit p] ttt, x) = x.
Proof. exact (`1 (sp_unit_left p) (ttt, x)). Qed.

Corollary StrictPremonoidal_unit_right_obj {c : Category}
  (p : StrictPremonoidal c) (x : c) :
  fobj[sp_tensor p] (x, fobj[sp_unit p] ttt) = x.
Proof. exact (`1 (sp_unit_right p) (x, ttt)). Qed.

Corollary StrictPremonoidal_assoc_obj {c : Category}
  (p : StrictPremonoidal c) (x y z : c) :
  fobj[sp_tensor p] (fobj[sp_tensor p] (x, y), z)
    = fobj[sp_tensor p] (x, fobj[sp_tensor p] (y, z)).
Proof. exact (`1 (sp_assoc p) ((x, y), z)). Qed.

(*
   * ** The binoidal payoff

   A functor out of [c □ c] is exactly a separately-functorial tensor, so a
   strict premonoidal structure yields a [Binoidal] structure on its
   carrier: the two one-argument tensoring functors are the composites of
   [sp_tensor] with the funny injections [FunnyL]/[FunnyR].  Since
   [fobj[FunnyL d] x ≡ (x, d)] and [fmap[FunnyL d] f ≡ lstep f] hold
   definitionally (Construction/Funny.v), the [AFunctor] index of each
   injection matches [λ x, fobj[sp_tensor p] (x, y')] up to beta, and the
   whole instance is assembled with no proof obligations. 

   --------
   * ** 双态收益

   一个来自  [c □ c]  的函子恰好是一个单独函子化的张量，因此一个严格的预单调结构会在其承载上产生一个  [Binoidal]  结构：两个单参数的张量函子是  [sp_tensor]  与搞笑注入  [FunnyL] / [FunnyR]  的复合。由于  [fobj[FunnyL d]  x ≡ (x, d)] 和  [fmap[FunnyL d]  f ≡ lstep f] 在定义上成立（Construction/Funny.v），每个注入的  [AFunctor]  索引与  [λ x, fobj[sp_tensor p]  (x, y')] 在 beta 等价下匹配，并且整个实例在组装时无需证明义务。
*)

Definition StrictPremonoidal_Binoidal {c : Category}
  (p : StrictPremonoidal c) : @Binoidal c :=
  @Build_Binoidal c
    (fun x y : c => fobj[sp_tensor p] (x, y))
    (fun y' : c => ToAFunctor (sp_tensor p ◯ @FunnyL c c y'))
    (fun x' : c => ToAFunctor (sp_tensor p ◯ @FunnyR c c x')).

(*
 The extracted tensor is the object action of the multiplication, on the
 nose. 

 --------
 提取的张量是乘法的对象动作，正好如此。
*)
Corollary StrictPremonoidal_Binoidal_tensor {c : Category}
  (p : StrictPremonoidal c) (x y : c) :
  @tensor c (StrictPremonoidal_Binoidal p) x y = fobj[sp_tensor p] (x, y).
Proof. reflexivity. Qed.

(*
 The two partial tensoring functors act on morphisms as the multiplication
 acts on the generating steps of the funny tensor — definitionally. 

 --------
 这两个部分张量函子在态射上的作用就像乘法在滑稽张量的生成步骤上的作用一样——这是定义上的。
*)
Corollary StrictPremonoidal_inj_left_fmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (y' : c) :
  fmap[@inj_left c (StrictPremonoidal_Binoidal p) y'] f
    = @fmap (c □ c) c (sp_tensor p) (x, y') (y, y') (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_inj_right_fmap {c : Category}
  (p : StrictPremonoidal c) (x' : c) {x y : c} (f : x ~{c}~> y) :
  fmap[@inj_right c (StrictPremonoidal_Binoidal p) x'] f
    = @fmap (c □ c) c (sp_tensor p) (x', x) (x', y) (rstep f).
Proof. reflexivity. Qed.

(*
   * ** The universal-property payoff

   The same multiplication, restricted along the generating steps, is a
   [SepFunctorial] package for the funny tensor's universal property
   (Construction/Funny.v): separately functorial data with a shared object
   map and NO interchange condition. 

   --------
   * ** 通用性质的收益

   相同的乘法，沿生成步骤受限，是一个 
   [SepFunctorial] 包，用于有趣张量的通用性质
   (Construction/Funny.v)：具有共享对象映射且没有交换条件的单独函子数据。
*)

Definition StrictPremonoidal_SepFunctorial {c : Category}
  (p : StrictPremonoidal c) :
  @SepFunctorial c c c (fun x y : c => fobj[sp_tensor p] (x, y)) :=
  toSep (sp_tensor p).

(* Its actions are likewise the images of the generating steps, on the nose. / 它的动作同样是生成步骤的图像，正中要点。 *)
Corollary StrictPremonoidal_sf_lmap {c : Category}
  (p : StrictPremonoidal c) {x y : c} (f : x ~{c}~> y) (d : c) :
  sf_lmap (StrictPremonoidal_SepFunctorial p) f d
    = @fmap (c □ c) c (sp_tensor p) (x, d) (y, d) (lstep f).
Proof. reflexivity. Qed.

Corollary StrictPremonoidal_sf_rmap {c : Category}
  (p : StrictPremonoidal c) (x : c) {d d' : c} (g : d ~{c}~> d') :
  sf_rmap (StrictPremonoidal_SepFunctorial p) x g
    = @fmap (c □ c) c (sp_tensor p) (x, d) (x, d') (rstep g).
Proof. reflexivity. Qed.
