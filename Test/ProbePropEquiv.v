Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Cat.

(**
* Probe for [PropEquiv]: setoids whose equality is propositional

    The import list above is the union of the two target files' own lists --
    Lib/Setoid/Propositional.v and Instance/Sets/Propositional.v -- plus those
    two files themselves and Instance/Cat.v, whose own list is a subset of what
    is already here.  A shorter prefix is what makes a probe pass for no
    reason.

    WHAT THIS FILE PINS.  Four things, each a measurement rather than an
    assertion.

    (1) The library's `≈` cannot be truncated.  Cat's hom-setoid is
        [Functor_Setoid] (Theory/Functor.v, installed as Cat's [homset] at
        Instance/Cat.v) and an [F ≈ G] there IS a family of isomorphisms.
        Replacing it by [inhabited (F ≈ G)] and asking for the isomorphism at
        an object is refused -- NEGATIVE 1.  The same refusal, in the shape a
        would-be blanket instance takes, is NEGATIVE 3.  This is why
        [PropEquiv] is a PROPERTY of a setoid and not a change to
        [Class Setoid].

    (2) The property has to name its relation.  The sort ascription
        [(x ≈ y : Prop)] is refused even for [eq_Setoid], whose relation is
        Coq's [eq] -- NEGATIVE 2.  [PropEquiv_of_relation] is the constructor
        that takes the named relation instead.

    (3) The size fact the whole exercise rests on: a [Prop]-valued relation on
        a carrier in [Type@{u}] lands in [Type@{u}] itself, a [Type]-valued one
        lands in [Type@{u+1}].  Both halves are measured below, the second as
        NEGATIVE 4, and the contrast is repeated for [PropEquiv] against
        [Setoid] itself as NEGATIVE 5.

    (4) [PropEquiv] lands AT the carrier universe.  [PropEquiv_at_carrier]
        below is accepted with the measured signature quoted beside it.

    DISCIPLINE.  The messages quoted below are as this file produces them,
    with [Set Printing Universes] OFF -- which is why four of the five show a
    bare [Type] where a universe name would otherwise stand.  Exactly two
    edits are applied to the quotations and to nothing else: NEGATIVE 2's
    generated universe name, which is file-name dependent and would not
    survive a rename, is replaced by the readable [u_eq]; and Coq's line
    breaks are re-flowed to this comment's width, with trailing spaces
    trimmed.  Every other character is verbatim.  The SIGNATURES quoted beside
    the size measurements were taken separately, with [About] under
    [Set Printing Universes].  Every negative is paired with a positive control
    naming the same library constants; the instrument was checked (a refusal
    expected around a command that succeeds stops the file); and each negative
    was re-run with its guard stripped IN A COPY OF THE WHOLE FILE, so that the
    refusal kind is read off the message rather than guessed.  The refusal
    kinds recorded are ELIMINATION (two), SORT (one) and UNIVERSE (two),
    beside the instrument check, whose refusal is a missing NAME.

--------
* 探查 [PropEquiv]：其等式是命题性的集合对象

上面的导入列表是两个目标文件自身列表的并集 -- Lib/Setoid/Propositional.v 和 Instance/Sets/Propositional.v -- 加上这两个文件本身以及 Instance/Cat.v，其自身列表是这里已有内容的子集。一个更短的前缀会导致探测无故通过。

这个文件固定了什么。四件事，每件都是一种测量，而不是断言。

(1) 图书馆的 `≈` 不能被截断。Cat 的同态集合是 [Functor_Setoid]（Theory/Functor.v，安装为 Cat 的 [homset] 在 Instance/Cat.v），在那里确实存在一族同构。用 [inhabited (F ≈ G)] 替换它并请求在一个对象处的同构会被拒绝——NEGATIVE 1。以一个潜在的通用实例的形态被拒绝的情况是 NEGATIVE 3。这就是为什么 [PropEquiv] 是集合的一个属性，而不是对 [Class Setoid] 的改变。

(2) 该属性必须命名其关系。即使是对于 [eq_Setoid]，其关系是 Coq 的 [eq] —— NEGATIVE 2，也会拒绝作为 [(x ≈ y : Prop)] 的类型归属。[PropEquiv_of_relation] 是接收已命名关系的构造函数。

(3) 整个练习所依赖的大小事实：一个 [Prop] 值的关系在载体 [Type@{u}] 上映射到 [Type@{u}] 本身，一个 [Type] 值的关系映射到 [Type@{u+1}]。下面测量了两个部分，第二部分为负 4，并且对 [PropEquiv] 与 [Setoid] 本身的对比重复为负 5。

(4) [PropEquiv] 在载体宇宙着陆。[PropEquiv_at_carrier] 下方被接受，旁边附有引用的测量特征。

纪律。下面引用的消息是本文件生成时的内容，[Set Printing Universes] 处于关闭状态——这也是为什么五条消息中有四条显示的是裸露的 [Type]，而本应显示宇宙名称。对引用内容只应用了两处编辑，并且仅限于引用内容：NEGATIVE 2 生成的宇宙名称，它依赖于文件名且在重命名后无法保留，被可读的 [u_eq] 取代；Coq 的换行被重新调整以适应本评论宽度，并修剪了尾随空格。其他所有字符都保持逐字原样。在尺寸测量旁引用的 SIGNATURES 是单独采集的，使用 [About] 放在 [Set Printing Universes] 下。每个阴性都与一个正控配对，正控命名了相同的库常量；仪器已检查（在成功命令停止文件时会出现拒绝），并且每个阴性都在整个文件的副本中去掉其保护后重新运行，这样拒绝类型是从信息中读取而不是猜测的。记录的拒绝类型有 ELIMINATION（两个）、SORT（一个）和 UNIVERSE（两个），以及仪器检查，其拒绝类型是缺少 NAME。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A refusal expected around a name that is not there.  If the instrument were
   inert this line would pass silently and so would everything below it.

--------
对一个不存在的名字预期会有拒绝。如果工具是惰性的，这一行会悄无声息地通过，下面的所有内容也会如此。
*)
Fail Check zzz_no_such_constant_propequiv.

(** ** Positive controls: every constant the negatives sit beside / ** 阳性对照：每一个负对照旁边的常数 *)

Check @PropEquiv.
Check @pequiv.
Check @pequiv_to.
Check @pequiv_from.
Check @PropEquiv_of_relation.
Check @pequiv_Equivalence.
Check @pequiv_Equivalence_Prop.
Check @pequiv_Proper.
Check @pequiv_elim_inhabited.

Check @eq_PropEquiv.
Check @unit_PropEquiv.
Check @Fin_PropEquiv.
Check @funext_PropEquiv.
Check @fun_PropEquiv.
Check @prod_PropEquiv.
Check @sum_PropEquiv.
Check @option_PropEquiv.
Check @list_PropEquiv.
Check @nat_PropEquiv.

Check @PropEquivObj.
Check @hom_PropEquiv.
Check @product_PropEquiv.
Check @iprod_PropEquiv.
Check @limit_PropEquiv.
Check @LocallyPropositional.
Check @locally_prop.
Check @LocallyPropositional_of_relation.
Check @Morphism_equality_PropEquiv.
Check @LocallyPropositional_of_eq.

(*
The two [Cat] constants NEGATIVE 1 is about.  [Functor_Setoid] is Cat's
   hom-setoid, and the projection out of an UNTRUNCATED [F ≈ G] is accepted:
   the negative below is about the truncation, not about the projection.

--------
两个 [Cat] 常量 NEGATIVE 1 是关于……的。[Functor_Setoid] 是猫的同值集合，而一个未截断的 [F ≈ G] 的投影是被接受的：下面的负数是关于截断的，而不是关于投影的。
*)
Check @Functor_Setoid.

Definition cat_equiv_is_data {C D : Category} (F G : C ⟶ D)
  (H : F ≈ G) (x : C) : F x ≅ G x := `1 H x.

(*
[eq_PropEquiv] is registered, so instance resolution closes a [pequiv] goal
   at a discrete setoid with no explicit instance argument.

--------
[eq_PropEquiv] 已注册，因此实例解析会在没有显式实例参数的离散集合上关闭一个 [pequiv] 目标。
*)
Example c_resolution (A : Type) (x y : A) : Prop := @pequiv A (eq_Setoid A) _ x y.

(* ... and the relation it resolves to is Coq's [eq], on the nose. / ... 它解析到的关系正是 Coq 的 [eq]，恰恰如此。 *)
Example c_resolution_is_eq (A : Type) (x y : A) :
  @pequiv A (eq_Setoid A) (eq_PropEquiv A) x y = (x = y) := eq_refl.

(*
[pequiv_elim_inhabited] takes its [PropEquiv] implicitly, so the one
   elimination the class buys elaborates with instance resolution alone.

--------
[pequiv_elim_inhabited] 隐式地获取它的 [PropEquiv]，所以类所进行的一次消除仅通过实例解析就能详细说明。
*)
Example c_elim (A : Type) (x y : A)
  (h : inhabited (@equiv A (eq_Setoid A) x y)) : @equiv A (eq_Setoid A) x y :=
  pequiv_elim_inhabited x y h.

(**
** Control: [PropEquiv_of_relation] on a relation that is not [eq]

    A setoid on [nat] whose `≈` identifies numbers of the same parity.  Its
    relation is already [Prop]-valued, so [PropEquiv_of_relation] applies with
    both implications the identity -- which is the whole point of that
    constructor: the relation is handed over by NAME, since the ascription of
    NEGATIVE 2 is refused.

--------
** 控件：在非 [eq] 的关系上使用 [PropEquiv_of_relation]

    一个关于 [nat] 的集合，其 `≈` 用于识别相同奇偶性的数字。它的关系已经是 [Prop] 值，因此 [PropEquiv_of_relation] 适用，并且两种蕴含都是恒等——这正是该构造函数的全部意义：关系由 NAME 提供，因为拒绝了 NEGATIVE 2 的归属。
*)

Definition parity_rel (x y : nat) : Prop := Nat.even x = Nat.even y.

Definition parity_Equivalence : Equivalence parity_rel.
Proof.
  unfold parity_rel.
  constructor.
  - intro x; reflexivity.
  - intros x y H; symmetry; exact H.
  - intros x y z H1 H2; transitivity (Nat.even y); assumption.
Defined.

Definition parity_Setoid : Setoid nat :=
  {| equiv := parity_rel ; setoid_equiv := parity_Equivalence |}.

Definition parity_PropEquiv : PropEquiv parity_Setoid.
Proof.
  unshelve refine (PropEquiv_of_relation parity_rel _ _).
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

Example c_parity_pequiv (x y : nat) :
  @pequiv nat parity_Setoid parity_PropEquiv x y = parity_rel x y := eq_refl.

(** ** Controls: the pointwise and componentwise transports read back / ** 控制：逐点和逐分量传输回读 *)

(* The hom-setoid of [Sets]: pointwise into the target. / [Sets] 的同态等价类：逐点映射到目标。 *)
Example c_hom_pointwise {x y : SetoidObject} (Py : PropEquiv (is_setoid y))
  (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(* Indexed products: pointwise in the index. / 索引产品：索引中的逐点。 *)
Example c_iprod_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(* Limits: pointwise in the shape, the compatibility witness playing no part. / 极限：在形状上逐点，兼容性见证不发挥作用。 *)
Example c_limit_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(* The dependent-function setoid of Lib/Setoid.v. / Lib/Setoid.v 的依赖函数集合等价类。 *)
Example c_funext_pointwise {T : Type} (t : T -> Type) (a b : T)
  {Sb : Setoid (t b)} (Pb : PropEquiv Sb) (f g : t a -> t b) :
  @pequiv _ _ (funext_PropEquiv t a b Pb) f g
    = (forall x : t a, @pequiv _ _ Pb (f x) (g x)) := eq_refl.

(*
A [SetoidObject] that DOES have the property, as the control for
   NEGATIVE 3: the blanket instance is refused, individual ones are not.

--------
一个具有该属性的 [SetoidObject]，作为 NEGATIVE 3 的对照：整体实例被拒绝，单个实例则不被拒绝。
*)
Definition eq_SetoidObject (A : Type) : SetoidObject :=
  {| carrier := A ; is_setoid := eq_Setoid A |}.

Definition eq_SetoidObject_PropEquiv (A : Type) :
  PropEquiv (is_setoid (eq_SetoidObject A)) := eq_PropEquiv A.

(**
** Size measurements, and their controls

    The three-line size fact of Lib/Setoid/Propositional.v's header, measured.
    [PropRelSpace] is ACCEPTED at the carrier universe, with the constraint
    [Set < u] that the sort of [Prop] imposes:

      PropRelSpace@{u} : Type@{u} → Type@{u}
      (* u |= Set < u

--------
** 尺寸测量及其控制

    Lib/Setoid/Propositional.v 头部的三行尺寸事实，已测量。
    [PropRelSpace] 在承载宇宙中被接受，其约束条件是
    [Set < u]，由 [Prop] 的类型施加：

      PropRelSpace@{u} : Type@{u} → Type@{u}
      (* u |= Set < u* )
*)

    [PropEquiv] itself lands there too:

      PropEquiv_at_carrier@{u} : ∀ A : Type@{u}, Setoid@{u u} A → Type@{u}
      (* u |= Set < u *)

    NEGATIVE 4 and NEGATIVE 5 are the other half of the contrast. *)

Definition PropRelSpace@{u} (A : Type@{u}) : Type@{u} := A -> A -> Prop.

Definition PropEquiv_at_carrier@{u} (A : Type@{u}) (S : Setoid@{u u} A) :
  Type@{u} := PropEquiv@{u u} S.

(*
Control for NEGATIVE 4: one universe up, the [Type]-valued relation space
   is accepted.

--------
对 NEGATIVE 4 的控制：上升一个宇宙，[Type] 值关系空间被接受。
*)
Definition CRelSpace@{u v} (A : Type@{u}) : Type@{v} := A -> A -> Type@{u}.

(* Control for NEGATIVE 5: one universe up, [Setoid] is accepted. / 控制负5：向上一个宇宙，[Setoid] 被接受。 *)
Definition Setoid_above_carrier@{u v} (A : Type@{u}) : Type@{v} := Setoid@{u u} A.

(**
** NEGATIVE 1 (ELIMINATION): Cat's `≈` cannot be truncated

    Stripped and re-run in a copy of the whole file, the message is

      Incorrect elimination of "H" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type"
      because proofs can be eliminated only to build proofs.

    -- [inhabited] is [Prop]-valued and so eliminates only into [Prop], while
    the family of isomorphisms carried by an [F ≈ G] lands in [Type].  The
    control immediately above ([cat_equiv_is_data]) performs the same
    projection out of the UNTRUNCATED proof and is accepted, so the refusal is
    about the truncation alone.

--------
** 负面 1（消除）：猫的 `≈` 无法被截断

    在整个文件的副本中剥离并重新运行后，消息为

      在归纳类型 "inhabited" 中错误地消除了 "H"：
      返回类型的阶为 "Type"，而它应该是 SProp 或 Prop。
      不允许在 "Type" 阶的谓词上消除 Prop 阶的归纳对象，
      因为证明只能被消除用于构建其他证明。

    -- [inhabited] 的值为 [Prop]，因此只消除到 [Prop]，而
    [F ≈ G] 所携带的一族同构映射落在 [Type] 中。
    上面的控制（[cat_equiv_is_data]）执行了相同的
    从未截断的证明中投射出的操作并被接受，所以拒绝只与截断有关。
*)

Fail Definition cat_equiv_prop {C D : Category} (F G : C ⟶ D)
  (H : inhabited (F ≈ G)) (x : C) : F x ≅ G x :=
  match H with inhabits p => `1 p x end.

(**
** NEGATIVE 2 (SORT): [(x ≈ y : Prop)] is refused, even at [eq_Setoid]

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      x : A
      y : A
      The term "x ≈ y" has type "Type" while it is expected to have type
      "Prop" (universe inconsistency: Cannot enforce u_eq <= Prop).

    -- [equiv x y] is typed at [Type] whatever relation sits underneath, and
    [eq_Setoid]'s relation IS Coq's [eq].  No ascription narrows the sort after
    the fact; the relation has to be named, which is what
    [PropEquiv_of_relation] takes.  The control is [c_resolution_is_eq] above:
    naming [eq] and going through [eq_PropEquiv] is accepted and computes to
    [x = y].

--------
** 负 2（类型）：即使在 [eq_Setoid]，也拒绝 [(x ≈ y : Prop)]

去掉并在整个文件的副本中重新运行，消息是

  在环境中
  A : 类型
  x : A
  y : A
  项“x ≈ y”的类型是“类型”，而预期它的类型是“命题”
  （宇宙不一致性：无法强制 u_eq <= 命题）。

-- 无论底层关系是什么，[equiv x y] 在 [Type] 被类型化，并且 [eq_Setoid] 的关系确实是 Coq 的 [eq]。没有任何标注会在事实之后缩小类型；关系必须被命名，这正是 [PropEquiv_of_relation] 所采用的。上面的控制是 [c_resolution_is_eq]：命名 [eq] 并通过 [eq_PropEquiv] 是被接受的，并计算为 [x = y]。
*)

Fail Definition eq_equiv_ascribed (A : Type) (x y : A) : Prop :=
  (@equiv A (eq_Setoid A) x y : Prop).

(**
** NEGATIVE 3 (ELIMINATION): no blanket [PropEquiv] for [Sets]

    Stripped and re-run in a copy of the whole file, the message is

      Incorrect elimination of "H" in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type"
      because proofs can be eliminated only to build proofs.

    -- the same refusal as NEGATIVE 1, in the shape a blanket instance would
    take.  [pequiv_from] is fine ([inhabits]); [pequiv_to] is what is refused.
    This is why there is no [∀ X : SetoidObject, PropEquiv (is_setoid X)] in
    Instance/Sets/Propositional.v and no [LocallyPropositional Sets], and why
    the algebraic object records of the later phases CARRY the property as a
    field.  The control is [eq_SetoidObject_PropEquiv] above: a PARTICULAR
    [SetoidObject] can of course have it.

    Note what this does and does not measure.  It measures that THIS route --
    truncate `≈` and untruncate it again -- is refused.  For [Cat] the refusal
    is decisive, since the data projected out is a family of isomorphisms.  For
    an arbitrary [SetoidObject] it records the absence of a construction, not a
    proof that none exists.

--------
** 否定 3（消除）：没有针对 [Sets] 的通用 [PropEquiv]

在整个文件的副本中剥离并重新运行后，消息是

在归纳类型“inhabited”中错误地消除了“H”：返回类型的类型为“Type”，而它应该是 SProp 或 Prop。在“Type”类型的谓词上，不允许对 Prop 类型的归纳对象进行消除，因为证明只能用来构建其他证明。

-- 与 NEGATIVE 1 相同的拒绝，以一个通用实例可能采取的形式出现。 [pequiv_from] 是可以的（[inhabits]）；[pequiv_to] 是被拒绝的。这就是为什么在 Instance/Sets/Propositional.v 中没有 [∀ X : SetoidObject, PropEquiv (is_setoid X)]，也没有 [LocallyPropositional Sets]，以及为什么后期阶段的代数对象记录以字段的形式携带该属性。上面的控制是 [eq_SetoidObject_PropEquiv]：当然，一个特定的 [SetoidObject] 可以拥有它。

注意这一方法测量的内容和未测量的内容。它测量的是这条路径——截断 `≈` 然后再取消截断——被拒绝。对于 [Cat] 来说，这种拒绝是决定性的，因为所投射出的数据是一族同构。对于任意的 [SetoidObject]，它记录的是构造的缺失，而不是不存在构造的证明。
*)

Fail Definition sets_PropEquiv_generic (X : SetoidObject) :
  PropEquiv (is_setoid X) :=
  {| pequiv := fun x y => inhabited (@equiv _ (is_setoid X) x y)
   ; pequiv_to := fun x y H => match H with inhabits h => h end
   ; pequiv_from := fun x y h => inhabits h |}.

(**
** NEGATIVE 4 (UNIVERSE): a [Type]-valued relation space is one level up

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      The term "A → A → Type" has type "Type@{u+1}"
      while it is expected to have type "Type@{u}"
      (universe inconsistency: Cannot enforce u < u because u = u).

    -- against [PropRelSpace] above, which is accepted at [Type@{u}].  This is
    the size fact the solution-set argument of Mac Lane CWM §V.6-V.7 (printed
    p. 128) needs: an index built from relations on a carrier is carrier-sized
    only when those relations are [Prop]-valued.  The control is [CRelSpace],
    the same space at [Type@{v}] with [u < v].

--------
** 负 4 (宇宙)：一个 [Type] 值的关系空间是上一层级

去掉并在整个文件的副本中重新运行，消息是

  在环境中
  A : 类型
  术语 "A → A → 类型" 的类型为 "Type@{u+1}"
  而期望的类型是 "Type@{u}"
  （宇宙不一致：无法强制 u < u 因为 u = u）。

-- 针对上面的 [PropRelSpace]，它在 [Type@{u}] 被接受。这是 Mac Lane CWM §V.6-V.7（印刷页 128）解决方案集论证所需的大小事实：只有当这些关系是 [Prop] 值时，从载体上的关系构建的索引才是载体大小。控制是 [CRelSpace]，同一空间在 [Type@{v}] 时为 [u < v]。
*)

Fail Definition CRelSpace_small@{u} (A : Type@{u}) : Type@{u} :=
  A -> A -> Type@{u}.

(**
** NEGATIVE 5 (UNIVERSE): [Setoid] is one level up, [PropEquiv] is not

    Stripped and re-run in a copy of the whole file, the message is

      In environment
      A : Type
      The term "Setoid A" has type "Type@{u+1}" while it is expected to have
      type "Type@{u}"
      (universe inconsistency: Cannot enforce u < u because u = u).

    -- the same contrast one level of packaging up: the setoid RECORD does not
    fit at its own carrier's universe, while [PropEquiv] of that record does
    ([PropEquiv_at_carrier] above).  The control is [Setoid_above_carrier], the
    same record at [Type@{v}] with [u < v].

--------
** NEGATIVE 5（宇宙）：[Setoid] 提升了一个级别，而 [PropEquiv] 没有

在整个文件的副本中剥离后重新运行，消息是

  在环境中
  A : 类型
  术语 "Setoid A" 的类型是 "Type@{u+1}"，而预期类型是
  "Type@{u}"
  （宇宙不一致：无法强制 u < u 因为 u = u）。

-- 同样的对比在封装提升一个级别：setoid RECORD 不适合其自身载体的宇宙，而该记录的 [PropEquiv] 可以（上面的 [PropEquiv_at_carrier]）。控制是 [Setoid_above_carrier]，即在 [Type@{v}] 的同一记录与 [u < v]。
*)

Fail Definition Setoid_at_carrier@{u} (A : Type@{u}) : Type@{u} :=
  Setoid@{u u} A.
