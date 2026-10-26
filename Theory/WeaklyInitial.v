Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * From a weakly initial family to a genuine initial object / * 从弱初始范畴到真正的初始对象 *)

(*
nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   This file records the object-level input of Freyd's General Adjoint
   Functor Theorem: the passage from a *weakly* initial family to an actual
   initial object.  A family [wif_obj : wif_index -> C] is weakly initial
   when every object [c] is hit by some member, i.e. [wif_cover c] exhibits
   an index [i] and an arrow [wif_obj i ~> c] (existence, with no
   uniqueness).  The classical construction (Freyd, Mac Lane CWM V.6) forms
   the product [P] of the family — itself a single weakly initial object —
   and then carves out the joint equalizer of *all* endomorphisms of [P];
   that equalizer is genuinely initial.

   STATUS / hypothesis form.  The construction consumes exactly two limits
   over caller-chosen index [Type]s and a supply of binary equalizers:

     - [P]  : the product of the family [wif_obj] over [wif_index]
              (an indexed product = limit of a discrete diagram);
     - [Pe] : the product, over the hom-type of endomorphisms of that
              product object, of that object with itself — this is the
              [Type]-indexed limit whose universal cone lets a single
              parallel pair [P ~> Pe] “capture all endos” at once, so the
              wide equalizer of the endomorphism family reduces to one
              *binary* equalizer supplied by [E];
     - [E]  : binary equalizers for parallel pairs.

   Both products are passed as explicit hypotheses rather than harvested
   from a [Complete] / [HasIndexedProducts] instance.  This is deliberate
   (Risk (b)): the endomorphism-indexed product ranges over the hom-type
   [iprod .. ~> iprod ..], which sits at the hom universe [h]; routing it
   through a class that quantifies over every index [Type] would over-commit
   the ambient universes, whereas the explicit form leaves the smallness of
   the index (hence the relevant universe constraints) in the caller's
   hands.  Supplying [Pe] separately from [P] strengthens the hypotheses
   (an honest, leaner input) and never weakens the conclusion, which remains
   a full [Initial C].

   [Pe]'s family is CONSTANT -- [fun _ : P0 ~> P0 => P0] -- so [Pe] is a
   POWER of [P0] in the sense of Mac Lane III.3/III.4, and the proof below
   says so, through Structure/Limit/Power.v's [power_of_limit],
   [power_ev_of_limit] and [power_ump_of_limit].  Those are [iprod],
   [iprod_proj] and [iprod_ump] at the constant family, supplied by [:=], so
   the change is by conversion and the statement of the theorem is unaffected
   -- [Pe]'s type is written out in full above and is untouched.  [P]'s family
   [wif_obj W] genuinely varies and stays an indexed product.  Only
   Structure/Limit/Power.v is Required, not its Structure/Limit/Power/Hom.v
   satellite; [Instance/Sets] is in this file's closure anyway (measured:
   two hops since #435, Instance/Parallel → Instance/Sets; three before).

--------
nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件记录 Freyd 一般伴随函子定理的对象层输入：从*弱*初始族到真正初始对象的通路。
   族 [wif_obj : wif_index -> C] 弱初始，当每个对象 [c] 被某成员击中，即 [wif_cover c]
   展示指标 [i] 与箭头 [wif_obj i ~> c]（存在性，无唯一性）。经典构造（Freyd，
   Mac Lane CWM V.6）形成该族的积 [P]——本身是单个弱初始对象——再挖出 [P] *全部*
   自同态的联合等化子；该等化子真正初始。

   状态 / 假设形式。构造恰消耗两个在调用方选定指标 [Type] 上的极限，以及二元等化子供给：

     - [P]  ：族 [wif_obj] 在 [wif_index] 上的积
              （指标积 = 离散图的极限）；
     - [Pe] ：在该积对象自同态的 hom 类型上，该对象与自身的积——这是 [Type]-指标极限，
              其普遍锥使单个平行对 [P ~> Pe]「一次捕获全部自同态」，故自同态族的宽等化子
              归约为 [E] 供给的一个*二元*等化子；
     - [E]  ：平行对的二元等化子。

   两积作为显式假设传入，而非从 [Complete] / [HasIndexedProducts] 实例收获。这是刻意的
   （Risk (b)）：自同态指标积量化在 hom 类型 [iprod .. ~> iprod ..] 上，坐在 hom 宇宙 [h]；
   经量化每个指标 [Type] 的类路由会过度承诺环境宇宙，而显式形式把指标的小性（故相关宇宙约束）
   留给调用方。把 [Pe] 与 [P] 分开供给加强假设（诚实、更瘦的输入），从不削弱结论，结论仍是
   完整 [Initial C]。

   [Pe] 的族是常数——[fun _ : P0 ~> P0 => P0]——故 [Pe] 是 Mac Lane III.3/III.4 意义下
   [P0] 的幂，下文经 Structure/Limit/Power.v 的 [power_of_limit]、[power_ev_of_limit]、
   [power_ump_of_limit] 如此说明。它们是常数族上的 [iprod]、[iprod_proj]、[iprod_ump]，
   由 [:=] 供给，故变化靠转换，定理陈述不受影响——[Pe] 的类型上文写全且未动。[P] 的族
   [wif_obj W] 真正变化，仍是指标积。仅 Require Structure/Limit/Power.v，非其
   Structure/Limit/Power/Hom.v 卫星；[Instance/Sets] 本就在本文件闭包中（测得：自 #435
   起两跳，Instance/Parallel → Instance/Sets；此前三跳）。
*)

(*
A weakly initial family: an index [Type], a family of objects, and for
   every object [c] a *choice* of covering member together with an arrow
   into [c].  No uniqueness of the covering arrow is required — that is what
   makes the family only *weakly* initial.

--------
一个弱初始族：一个指标 [Type]，一族对象，对于每个对象 [c]，选择一个覆盖成员及一个指向 [c] 的箭头。覆盖箭头不要求唯一——这正是使该族仅为*弱*初始的原因。
*)
Record WeaklyInitialFamily (C : Category) := {
  wif_index : Type;
  wif_obj : wif_index -> C;
  wif_cover (c : C) : { i : wif_index & wif_obj i ~> c }
}.

Arguments wif_index {C} _.
Arguments wif_obj {C} _ _.
Arguments wif_cover {C} _ _.

(*
The product [P] of a weakly initial family, together with equalizers and
   the endomorphism-indexed product [Pe] over the product object, yields a
   genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial (a single
   object now).  The projections of [Pe] separate all endomorphisms of
   [P0]: there is a map [m : P0 ~> Pe] with [proj u ∘ m ≈ u] for every endo
   [u], and a map [d : P0 ~> Pe] with [proj u ∘ d ≈ id] for every [u].  The
   binary equalizer [e : I ~> P0] of [m] and [d] then satisfies
   [u ∘ e ≈ e] for *every* endomorphism [u] of [P0], and is monic.  This
   [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e], the weakly initial map post-
       composed with the equalizer inclusion;
     - uniqueness: given [f g : I ~> c], take the (binary) equalizer
       [k : K ~> I] of [f] and [g]; weak initiality gives [s : P0 ~> K], so
       [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi, and
       [f ∘ k ≈ g ∘ k] forces [f ≈ g].

--------
弱初族的产品 [P]，连同等化器以及在积对象上的以自同构为指标的积 [Pe]，共同产生一个真正的初对象。

构造。对于乘积对象 [iprod (wif_obj W) P]，写出 [P0]。
对于任何 [c]，覆盖箭头 [wif_cover c] 与匹配的投影组合会得到映射 [P0 ~> c]，因此 [P0] 是弱初的（现在是单个对象）。[Pe] 的投影分离 [P0] 的所有自同态：对于每个自同态 [u]，存在映射 [m : P0 ~> Pe] 使 [proj u ∘ m ≈ u] 成立；对于每个 [u]，存在映射 [d : P0 ~> Pe] 使 [proj u ∘ d ≈ id] 成立。[m] 和 [d] 的二值等化器 [e : I ~> P0] 随后满足对于 [P0] 的*每个*自同态 [u]，[u ∘ e ≈ e] 成立，并且是单射。这个 [I] 是初的：

- 存在性  [I ~> c]：将弱初始映射与等化器包含后复合得到 [wmap c ∘ e]；
- 唯一性：给定 [f g : I ~> c]，取 [f] 和 [g] 的（二元）等化器 [k : K ~> I]；弱初始性给出 [s : P0 ~> K]，因此 [e ∘ (k ∘ s)] 是 [P0] 的自同态，被 [e] 吸收；[e] 的单性然后使 [(k ∘ s) ∘ e ≈ id] 成立，即 [k] 是分割满射，且 [f ∘ k ≈ g ∘ k] 强制 [f ≈ g]。
*)
(*
THE BINDERS ARE WHERE FREYD'S SIZE CONDITION LIVES, so they are written
   out rather than inferred, and the two [Limit] instances are the whole
   point.

     [idx]  the weakly initial family's index universe,
     [obj]  the ambient category's object universe,
     [h]    its hom-and-proof universe,
     [lim]  the level of the first limit datum.

   The FIRST limit, [P], is over a discrete shape whose objects are the
   family index: [Limit@{lim idx h obj}], shape-object universe [idx],
   free.  The SECOND, [Pe], is over a discrete shape whose objects are the
   ENDOMORPHISM HOM-SET of [iprod (wif_obj W) P], so its shape-object
   universe is the ambient HOM universe: [Limit@{h h h obj}], written with
   [h] in the shape-object slot.  Nothing here forces [idx] up to [h] --
   the two limits are separate hypotheses and may be supplied separately.

   IT IS [Complete] THAT FUSES THEM, one caller out.  A [@Complete C]
   offers ONE shape-object universe for every shape at once, so a caller
   who discharges both hypotheses from a single [Complete] -- which is
   what Adjunction/GAFT.v does -- identifies [idx] with [h] and
   thereby puts the solution-set index at the ambient hom universe.  That
   is why [GAFT] carries [Complete@{h h h cobj}] and
   [SolutionSet@{h dobj cobj h}] in its own binders, and why an index
   strictly above [h] is refused there.

   Measured readback (the trailing [+] allows the level
   [DiscreteCat_Functor]'s [Program] obligations mint, printed last):

     initial_from_weakly_initial@{lim idx obj h u} :
     ∀ {C : Category@{obj h h}} (W : WeaklyInitialFamily@{idx obj h} C)
       (P : Limit@{lim idx h obj} (DiscreteCat_Functor (wif_obj W))),
       Limit@{h h h obj} (DiscreteCat_Functor (fun _ : … => iprod … ))
       → HasEqualizers C → Terminal C
     (* |= h < u / idx <= lim / h <= lim / … *)

--------
绑定器是弗雷德的大小条件所在，因此它们是明确写出的，而不是推断的，并且两个 [Limit] 实例就是关键所在。

[idx] 弱初始族的指标宇宙，
[obj] 环境范畴的对象宇宙，
[h] 它的同态与证明宇宙，
[lim] 第一个极限数据的层次。

第一个极限 [P] 是在一个离散形上，其对象是族索引：[Limit@{lim idx h obj}]，形对象宇宙 [idx]，自由的。第二个极限 [Pe] 是在一个离散形上，其对象是 [iprod (wif_obj W) P] 的 ENDOMORPHISM HOM-集，因此它的形对象宇宙是环境 HOM 宇宙：[Limit@{h h h obj}]，在形对象位置上写作 [h]。这里没有任何东西强制 [idx] 升到 [h]——这两个极限是独立的假设，可以单独提供。

正是 [Complete] 将它们融合，一个调用者输出。一个 [@Complete C] 为每个形状同时提供一个形状-对象宇宙，因此一个调用者如果从单个 [Complete] 排出两个假设——这正是 Adjunction/GAFT.v 所做的——会将 [idx] 与 [h] 识别起来，从而将解集索引放置在环境同类宇宙中。这就是为什么 [GAFT] 在它自己的绑定器中包含 [Complete@{h h h cobj}] 和 [SolutionSet@{h dobj cobj h}]，以及为什么高于 [h] 的索引会在这里被拒绝。

测量回读（尾随的 [+] 允许 [DiscreteCat_Functor] 的 [Program] 义务铸造，最后打印）：

initial_from_weakly_initial@{lim idx obj h u} :
     ∀ {C : Category@{obj h h}} (W : WeaklyInitialFamily@{idx obj h} C)
       (P : Limit@{lim idx h obj} (DiscreteCat_Functor (wif_obj W))),
       Limit@{h h h obj} (DiscreteCat_Functor (fun _ : … => iprod … ))
       → HasEqualizers C → Terminal C
     (* |= h < u / idx <= lim / h <= lim / … *)

   -- and, since Instance/Discrete.v's [DiscreteCat_Functor] was
   annotated in the PR “algebraic carriers are sets” (2026-09-17), with no
   literal [Set].  An earlier revision printed both [DiscreteCat_Functor]
   occurrences as [DiscreteCat@{_ Set Set}] and handed that [Set] on to
   [GAFT]. *)
Theorem initial_from_weakly_initial@{lim idx obj h +}
  {C : Category@{obj h h}} (W : WeaklyInitialFamily@{idx obj h} C)
  (P : Limit@{lim idx h obj} (DiscreteCat_Functor (wif_obj W)))
  (Pe : Limit@{h h h obj}
          (DiscreteCat_Functor
             (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
              => iprod (wif_obj W) P)))
  (E : HasEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object and fold it into [Pe]'s index. / 将产品对象缩写并折叠到 [Pe] 的索引中。 *)
  set (P0 := iprod (wif_obj W) P) in *.

  (*
Weak initiality of [P0]: a chosen map into every object.  [wif_obj W] is
     a genuinely varying family, so this stays an indexed PRODUCT; it is only
     [Pe] below whose family is constant.

--------
[P0] 的初始性较弱：是每个对象的一个选定映射。[wif_obj W] 是一个真正变化的族，所以它仍然是一个索引积；只有下面的 [Pe] 其族是恒定的。
*)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (*
The tupling of all endomorphisms, and of the constant identity family,
     through the endomorphism-indexed POWER [Pe] -- the family there is
     [fun _ : P0 ~> P0 => P0], constant, so Structure/Limit/Power.v's
     vocabulary applies and is used.  Every step below is the same term as
     before, read through that vocabulary: [power_of_limit],
     [power_ev_of_limit] and [power_ump_of_limit] are [iprod], [iprod_proj]
     and [iprod_ump] at the constant family, supplied by [:=].

--------
所有自同态的元组，以及常数恒等族，通过自同态索引的 POWER [Pe] —— 那里的族是 [fun _ : P0 ~> P0 => P0]，常数，因此 Structure/Limit/Power.v 的词汇适用并被使用。下面的每一步都是之前的相同项，通过该词汇来读取：[power_of_limit]、[power_ev_of_limit] 和 [power_ump_of_limit] 是在常数族下的 [iprod]、[iprod_proj] 和 [iprod_ump]，由 [:=] 提供。
*)
  destruct (power_ump_of_limit P0 Pe P0 (fun u => u)) as [m Hm0 _].
  destruct (power_ump_of_limit P0 Pe P0 (fun _ => id[P0])) as [d Hd0 _].
  (* beta-normalized reads of the two universal families / 两个通用家族的β归一化读数 *)
  assert (Hm : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ m ≈ u)
    by exact Hm0.
  assert (Hd : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ d ≈ id[P0])
    by exact Hd0.

  (* The binary equalizer of the two tuplings. / 两个元组的二进制均衡器。 *)
  destruct (@equalizer C E P0 (power_of_limit P0 Pe) m d) as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizer inclusion. / [P0] 的每个自同态都被等化子包含吸收。 *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    assert (Hu : power_ev_of_limit P0 Pe u ∘ (m ∘ e)
                   ≈ power_ev_of_limit P0 Pe u ∘ (d ∘ e)).
    { rewrite (fork_eq Eeq); reflexivity. }
    rewrite !comp_assoc in Hu.
    rewrite (Hm u) in Hu.
    rewrite (Hd u) in Hu.
    transitivity (id[P0] ∘ e).
    + exact Hu.
    + apply id_left. }

  (* The equalizer inclusion is monic. / 该等化器包含是单宿的。 *)
  pose proof (equalizer_monic m d Eeq) as Me.
  destruct Me as [mon].

  (* Assemble the initial object as a terminal object of [C^op]. / 将初始对象组装为 [C^op] 的终端对象。 *)
  unshelve refine (@Build_Terminal (C^op) I _ _).
  - (* existence: [I ~> x] via weak initiality post-composed with [e] / 存在：通过弱初始性与 [e] 后组合的 [I ~> x] *)
    intro x.
    exact (wmap x ∘ e).
  - (* uniqueness: any two [f g : I ~> x] agree / 唯一性：任意两个 [f g : I ~> x] 一致 *)
    intros x f g.
    (* read the goal in [C]: [f], [g] are [C]-morphisms [I ~> x] / 在 [C] 中阅读目标：[f]、[g] 是 [C]-态射 [I ~> x] *)
    change (unop f ≈ unop g).
    (* the binary equalizer of the competing pair / 竞争对的二进制均衡器 *)
    destruct (@equalizer C E I x f g) as [K [k Ek]].
    (* weak initiality supplies a map [P0 ~> K] / 弱初始性提供了一个地图 [P0 ~> K] *)
    pose (s := wmap K).
    (*
[e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then cancels it, exhibiting [s ∘ e] as a section of [k].

--------
[e ∘ (k ∘ s)] 是 [P0] 的一个自同态，被 [e] 吸收；然后 [e] 的单性抵消了它，显示 [s ∘ e] 作为 [k] 的一个截面。
*)
    assert (Habs : (e ∘ (k ∘ s)) ∘ e ≈ e ∘ id[I]).
    { transitivity e.
      - exact (endo_absorb (e ∘ (k ∘ s))).
      - symmetry; apply id_right. }
    assert (Hk : (k ∘ s) ∘ e ≈ id[I]).
    { apply (mon _ ((k ∘ s) ∘ e) (id[I])).
      transitivity ((e ∘ (k ∘ s)) ∘ e).
      - apply comp_assoc.
      - exact Habs. }
    (* hence [k ∘ (s ∘ e) ≈ id]: [k] is a split epimorphism / 因此 [k ∘ (s ∘ e) ≈ id]：[k] 是一个分裂表射 *)
    assert (Hkr : k ∘ (s ∘ e) ≈ id[I]).
    { transitivity ((k ∘ s) ∘ e).
      - apply comp_assoc.
      - exact Hk. }
    (* [k] equalizes [f] and [g] and is (split) epic, so [f ≈ g] / [k] 平衡 [f] 和 [g] 并且是（分裂的）史诗，所以 [f ≈ g] *)
    transitivity (unop f ∘ (k ∘ (s ∘ e))).
    + transitivity (unop f ∘ id[I]).
      * symmetry; apply id_right.
      * apply compose_respects; [ reflexivity | symmetry; exact Hkr ].
    + transitivity (unop g ∘ (k ∘ (s ∘ e))).
      * transitivity ((unop f ∘ k) ∘ (s ∘ e)).
        -- apply comp_assoc.
        -- transitivity ((unop g ∘ k) ∘ (s ∘ e)).
           ++ apply compose_respects; [ exact (fork_eq Ek) | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.

(**
* The characterization: both directions (Mac Lane §V.6 Theorem 1)

    Everything above this line is the original file (#158/#328's Freyd
    construction), byte-identical up to one corrected sentence (see
    below); the two external citations into it, from
    Instance/Sets/Products.v and from Structure/Limit/Power.v, still
    point at what they cite.  What follows is #435 (Mac Lane §V.6
    Theorem 1, book p. 120, `maclane:V.6:thm1`, with the Awodey §9.8 and
    Riehl §4.7 clauses appended to the issue): the theorem as a
    CHARACTERIZATION.  Mac Lane's statement is “a category with small
    hom-sets that is small-complete has an initial object iff it has a
    small weakly initial family”; the tree carries no size class, so
    smallness is universe levels exactly as [initial_from_weakly_initial]
    already has it — the index [Type@{u}] of the family and the two [Limit]
    hypotheses that mention it.

    NECESSITY, the direction that was missing.  [weakly_initial_of_initial
    (I : Initial C) : WeaklyInitialFamily C] is the singleton family at the
    initial object, indexed by Lib/Setoid.v's universe-polymorphic
    [poly_unit] — written DIRECTLY, not through [wif_of_weakly_initial]:
    the direct form has an EMPTY universe constraint block and one binder
    fewer than the composite (measured; [unit] or [bool] as the index would
    pin the index universe at [Set]).  Its three readbacks are at [eq_refl]:
    the index IS [poly_unit], the member IS [initial_obj], the covering
    arrow IS [zero] — the family is built from the initial object, as the
    issue's reviewer asks, and not by any other route.

    THE BICONDITIONAL.  A plain [iff] is impossible because Freyd's
    direction consumes two products and the second one's index depends on
    the first, so [FreydProducts C] packages them per family (for every
    [W], the product of [wif_obj W] and the product of the endomorphisms of
    that product), and [initial_iff_weakly_initial_family (Ps :
    FreydProducts C) (E : HasEqualizers C) : Initial C ↔ WeaklyInitialFamily
    C] — Lib/Foundation.v's Type-valued [iffT], so both directions are
    extractable with [fst]/[snd] — keeps smallness caller-chosen exactly as
    the original theorem does.  It is [Defined], not [Qed]: it carries data
    in both directions, and the readback [initial_iff_weakly_initial_family_fst]
    pins that the forward half IS [weakly_initial_of_initial] (flipping the
    [Defined] to [Qed] stops that readback).  Awodey §9.8's convenience
    form harvests the two products from [Complete] and keeps the equalizers
    an explicit supply — [initial_from_weakly_initial_complete] and
    [initial_iff_weakly_initial_family_complete] (likewise [Defined], with
    its own [_fst] readback).  The [Complete]-only variant is NOT here:
    [Complete_HasEqualizers] lives downstream, in Adjunction/GAFT.v,
    which [Require]s this file, and re-deriving it here would duplicate a
    downstream definition.  Read the universes of the [_complete] form:
    [Complete]'s first two levels are the family's index level (the
    biconditional prints [Complete@{u0 u0 Set u2}], the wrapper
    [Complete@{u u Set u1}]), so the shape's object universe is identified
    with the family's index universe and the caller's choice of [Complete]
    IS the choice of admissible index size — the honest reading of
    “small-complete”, with no size class.

    THE RIEHL CLAUSE.  [WeaklyInitial c : Type := ∀ x, c ~> x] (Definition
    4.7.4, the one-object form; the constant may take the module's own
    name — a structural replica of this file and of Wide.v using both was
    compiled to confirm the namespace does not clash), with
    [weakly_initial_obj_of_initial], [wif_of_weakly_initial] (the singleton
    family of a weakly initial object), and the relation lemma
    [weakly_initial_iprod : WeaklyInitial (iprod (wif_obj W) P)] — the
    [wmap] the proof above builds inline (and Wide.v likewise builds one
    inline), now named; the original theorem is [Qed]-opaque and is NOT
    re-proved through it, keeping docs/INDEX.md's “byte-identical” promise
    for the theorem.  Its converse — a family gives a weakly initial object
    at a chosen index — is FALSE without a singleton hypothesis, because
    [wif_cover] picks its own member per target: that is Riehl's
    distinction between weakly initial and jointly weakly initial, and
    probe N5 pins it.  Weak initiality is strictly weaker than initiality,
    proved rather than asserted, at Instance/Parallel.v's walking parallel
    pair (already in this file's closure): [Parallel_ParX_WeaklyInitial],
    [Parallel_ParX_not_initial] (two inequivalent arrows [ParX ~> ParY],
    [is_initial_unique] would identify them, [discriminate] closes it) and
    [Parallel_ParY_not_weakly_initial] (the separation is about the
    object, not the category).

    THE SOLUTION-SET VOCABULARY.  The issue's “hence the solution set
    condition” is Adjunction/GAFT.v's [sols_of_wif : WeaklyInitialFamily
    (=(d) ↓ U) → SolutionSet U d], the exact converse of [wif_of_sols] —
    same index, same members — with the special case
    [sols_of_comma_initial : Initial (=(d) ↓ U) → SolutionSet U d] defined
    as [sols_of_wif] of [weakly_initial_of_initial].  Both are appended at
    the END of that file so that nothing above them moves (eleven
    external citations point into it); the index of the
    general form and the index and member of the special case read back at
    [eq_refl].  (GAFT became a biconditional in #436, [GAFT_iff]; when
    this was written it had not.)

    THE WITNESS.  Theory/WeaklyInitial/Sets.v (a leaf satellite; its
    closure is 53, 25 more than this file's, which is why it is not here)
    runs the full round trip at [Sets]: [Sets_initial_characterization :=
    initial_iff_weakly_initial_family_complete Sets_Complete
    Sets_HasEqualizers], [Sets_wif := fst … Sets_Initial],
    [Sets_initial_recovered := snd … Sets_wif], and [Sets_roundtrip_iso :
    initial_obj Sets_initial_recovered ≅ initial_obj Sets_Initial] by
    [initial_unique]; the DERIVED singleton family's index and member read
    back at [eq_refl] (nothing about the recovered initial object does).
    It lands at [Sets@{Set u}], as Adjunction/GAFT/Sets.v's
    header already discloses for GAFT.  This turns the biconditional from a
    conditional into an inhabited result; docs/INHABITATION.md has the row.

    STALE PREMISES.  Every location in the issue's “Current state” is
    stale (they match commit 00fc744b, and 820201bc, “Powers and
    copowers”, shifted the file in TWO hunks): its pointers to
    [initial_from_weakly_initial], [Record WeaklyInitialFamily],
    [endo_absorb] and the uniqueness chase's [assert (Hk : …)] all miss,
    while two of them, one into this file and one into
    Adjunction/GAFT.v, happen to be right.  Every substantive absence
    claim is TRUE:
    [Build_WeaklyInitialFamily] has exactly one use tree-wide
    (Adjunction/GAFT.v; CORRECTION, #452: that was so when measured, and
    Adjunction/SAFT/InitialObject.v's [wif_of_cogenerator] is now a
    second), nothing built a family from an [Initial], no
    constant named [WeaklyInitial] existed (all 29 word hits over `*.v`,
    31 counting `_CoqProject`, were the module path).  Two sentences of
    the existing headers were FALSE and are
    corrected in place, line-count-preserving: this file's header said
    the [Power.v] choice “keeps [Instance/Sets] off this file's dependency
    closure” — [Instance/Sets] is in it, TWO hops now that this file
    [Require]s Instance/Parallel.v directly, three before through
    Structure/Equalizer/Fork.v (docs/INDEX.md's Power.v bullet records the
    one-hop route from Power.v itself, which is correct and is left alone);
    and Wide.v attributed the [Set] pin to [Terminal] and the
    equalizer supply — both
    have empty constraint blocks, and the pin was [iprod]'s:
    [DiscreteCat_Functor] put the discrete shape at [DiscreteCat@{u Set
    Set}] and [Limit] identifies the shape's hom universe with the
    ambient's.  (FURTHER CORRECTION: that pin is now GONE as well.  The
    donor was annotated in place at Instance/Discrete.v in the PR
    “algebraic carriers are sets” (2026-09-17), so [iprod] carries no
    literal [Set]; what [Limit] does to the shape's hom universe is
    unchanged.)

    UNIVERSES ([About] under `Set Printing Universes`).  No [Set] on the
    Riehl-side constants: [WeaklyInitial@{u u0 u1}] carries only the
    Π-type's `u0 <= u`, `u1 <= u`, and so do [wif_of_weakly_initial] and
    [weakly_initial_obj_of_initial], whose types mention it;
    [weakly_initial_of_initial@{u u0 u1}] alone carries an EMPTY block,
    where the composite through [wif_of_weakly_initial] would carry four
    binders and two constraints; the Parallel constants are at that small
    category's levels.
    RECORDED CORRECTION.  An earlier revision continued: “Everything that
    consumes [iprod] or a [Limit (DiscreteCat_Functor …)] —
    [weakly_initial_iprod], [FreydProducts], both biconditionals, the
    [_complete] wrapper and their readbacks — is over [C : Category@{_ Set
    Set}], the donor's pin, with the strict `Set < u` and the caps `JMeq`,
    `eq` and `Logic_lemmas.equality` the original theorem carries — and
    `Projections` on all of them but [FreydProducts].”  The donor's pin is
    gone: [DiscreteCat_Functor] was annotated in place at
    Instance/Discrete.v in the PR “algebraic carriers are sets”
    (2026-09-17), and measured after it [iprod@{u u0 u1 u2 u3}] is stated
    over [C : Category@{u1 u2 u2}] with no literal [Set].  The same
    constants' ambient categories are therefore free in their hom
    universe.  Where the old list read a strict `Set < u`, this file's own
    [initial_from_weakly_initial@{lim idx obj h +}] now reads `h < u`,
    with the ambient hom universe in the place the literal held; the
    stdlib caps are unaffected, being the [eq]-valued hom-setoid's own.
    The five other constants were NOT individually re-measured after the
    repair — re-run [About] on them rather than trusting either list.  A
    universe refutation at [Cat] was tried and does NOT refuse ([Cat]'s
    hom universe instantiates at [Set]); it is recorded here so it is not
    re-invented.

    MEASURED.  17 new `.glob` heads in this file (15 `def`, 2 `prf`; 22
    with the original five), 6 in Theory/WeaklyInitial/Sets.v, 5 in
    Adjunction/GAFT.v, no [Program] obligations, all 33 “Closed under the
    global context”, zero `Axioms:` lines; the `make print-assumptions`
    gate carries all 33, the original five of this file included (it
    carried none of those five before).  Four `Defined` — the two
    biconditionals here, [sols_of_wif] and [sols_of_comma_initial] — each
    LOAD-BEARING (flipped to `Qed` one at a time in a copy of the whole
    file, the matching [eq_refl] readback stops); two new `Qed` (the two
    Parallel negations).  Closure of this
    file 29 excluding self, one more than before (Structure/Complete.v, the
    only new module on the GAFT critical path; Instance/Parallel.v was
    already inside, 0 at the margin); Sets.v 53 (Adjunction/GAFT/Sets.v 15
    at the margin, its other six `Require`s 0); Sets.v has no droppable
    `Require` and both of this file's new ones are needed, though its
    PRE-EXISTING Theory/Functor.v and Theory/Morphisms.v lines are
    droppable and are kept so that the cited lines above do not move.
    Zero name collisions for the 28 new names
    (`grep -rlw --include='*.v'`).  Test/ProbeWeaklyInitial435.v mirrors
    this file's `Require` list plus the satellite, Adjunction/GAFT.v and
    their supplies, binds its category per command (a [Section] variable
    would fix the hom level the pinned [Limit]s need at [Set]), and carries
    6 refutation commands = 1 instrument + N1 TYPING (an object is not a
    family) + N2-N3 CONVERSION (the index is [poly_unit], not [bool]; a
    [Terminal] is not an [Initial] — “cannot unify λ x y, y ~> x and
    hom[C]”, the [C^op] pivot) + N4-N5 TYPING (the equalizer supply is not
    the second product; the cover does not make a chosen member weakly
    initial), each stripped one at a time in a copy of the whole file
    beside its accepted control; seven `eq_refl` readbacks; guard coverage
    34/27 with seven exhaustive exceptions (identifier tokens inside the
    six refutation commands / also named outside them, comments stripped:
    the two keywords, two bound variables, the two refuted names and the
    instrument's absent name); rename-simulated 15 library names —
    [WeaklyInitial], [WeaklyInitialFamily], [wif_index], [wif_obj],
    [wif_cover], [weakly_initial_of_initial], [initial_from_weakly_initial],
    [Terminal], [Limit], [DiscreteCat_Functor], [HasEqualizers], [Category],
    [eq_refl], [bool], [projT2] — every first break on a positive line.
    `make todo` grows by the 6 refutation lines only (2277 → 2283 over
    #434's tip), so the issue's “adds no new hits” box is not met as
    written (disclosed, as in #430-#434); Coq 8.19 and 8.20 are checked by
    nix source builds of the committed revision, which the PR records.

    NOT DELIVERED: any size class (smallness stays universe levels); any
    re-proof or restatement of [initial_from_weakly_initial] or of Wide.v's
    theorem (both stay [Qed] and byte-identical); a biconditional for the
    wide form, or a [HasWideEqualizers] instance; the [Complete]-only
    biconditional (see above); a witness at any category but [Sets]; an
    agreement proof between [Sets_wif] and a hand-built family, or an
    [eq_refl] reading of the round trip (only the canonical [≅]);
    [weakly_initial_of_wif] under a singleton hypothesis (contrived, and it
    drags in `eq_rect` caps); functoriality of anything here; GAFT as a
    biconditional; no edit to Structure/Complete.v, Structure/Limit/
    Product.v, Instance/Parallel.v, Instance/Sets/Complete.v or
    Adjunction/GAFT/Sets.v, and none to Adjunction/GAFT.v above its last
    line.

--------
* 该表征：双向（Mac Lane §V.6 定理 1）

此行以上内容为原始文件（#158/#328 的 Freyd 构造），字节上完全相同，仅有一句修正（见下文）；两个外部引用，分别来自 Instance/Sets/Products.v 和 Structure/Limit/Power.v，仍然指向它们所引用的内容。以下内容为 #435（Mac Lane §V.6 定理 1，书页 120，`maclane:V.6:thm1`，并附加 Awodey §9.8 和 Riehl §4.7 条款到该问题）：定理作为一个特征化。Mac Lane 的陈述是“一个具有小同态集的范畴如果小完备，则当且仅当它有一个小弱初族时，才有初对象”；树没有大小范畴，所以小性在宇宙层面上正好如 [initial_from_weakly_initial] 已经具有的那样——族的索引 [Type@{u}] 以及提到它的两个 [Limit] 假设。

必要性，缺失的方向。[weakly_initial_of_initial
    (I : Initial C) : WeaklyInitialFamily C] 是初始对象上的单例族，由 Lib/Setoid.v 的宇宙多态 [poly_unit] 索引 — 直接书写，而不是通过 [wif_of_weakly_initial]：
    直接形式有一个空的宇宙约束块，比复合形式少一个绑定器（测量过；[unit] 或 [bool] 作为索引会将索引宇宙固定在 [Set]）。它的三个回读值在 [eq_refl]：索引是 [poly_unit]，成员是 [initial_obj]，覆盖箭头是 [zero] — 该族是从初始对象构建的，正如问题的审查者所要求的，而不是通过任何其他途径。

双条件一个普通的 [iff] 是不可能的，因为 Freyd 的方向消耗两个积，而第二个积的索引依赖于第一个，因此 [FreydProducts C] 按家族打包它们（对于每一个 [W]，即 [wif_obj W] 的积以及该积的自同态的积），并且 [initial_iff_weakly_initial_family (Ps : FreydProducts C) (E : HasEqualizers C) : Initial C ↔ WeaklyInitialFamily C] — Lib/Foundation.v 的类型值 [iffT]，因此两个方向都可以用 [fst]/[snd] 提取 — 保持调用者选择的小型性，正如原始定理所做的那样。它是 [Defined]，而不是 [Qed]：它在两个方向上传输数据，并且回读的 [initial_iff_weakly_initial_family_fst] 引脚表明前半部分是 [weakly_initial_of_initial]（将 [Defined] 翻转为 [Qed] 会停止该回读）。Awodey §9.8 的便利形式从 [Complete] 收集两个产品，并保持均衡器的明确供给——[initial_from_weakly_initial_complete] 和 [initial_iff_weakly_initial_family_complete]（同样还有 [Defined]，以及它自己的 [_fst] 回读）。仅 [Complete] 的变体不在这里：
    [Complete_HasEqualizers] 在下游的 Adjunction/GAFT.v 中，
    [Require] 会影响此文件，在这里重新推导它将重复下游的定义。阅读 [_complete] 形式的宇宙：
    [Complete] 的前两级是家族的索引级（双条件打印 [Complete@{u0 u0 Set u2}]，包装器
    [Complete@{u u Set u1}]），所以该形状的对象宇宙被识别为家族的索引宇宙，而调用者选择的 [Complete]
    就是可接受索引大小的选择 — “小型完整”的诚实解读，没有大小范畴。

里尔条款。[WeaklyInitial c : Type := ∀ x, c ~> x]（定义 4.7.4，一元形式；常量可以使用模块自身的名称——使用该文件和 Wide.v 的结构副本同时编译以确认命名空间不冲突），以及 [weakly_initial_obj_of_initial]、[wif_of_weakly_initial]（弱初始对象的单例族），和关系引理 [weakly_initial_iprod : WeaklyInitial (iprod (wif_obj W) P)]——[wmap] 上述证明在线构建（Wide.v 同样在线构建一个），现在已命名；原定理是 [Qed]-不透明的，并未通过它重新证明，以保持 docs/INDEX.md 对定理的“字节相同”承诺。其逆命题——一个族在选定的指标处给出一个弱初对象——如果没有单元素假设是假的，因为 [wif_cover] 为每个目标选择它自己的成员：这就是 Riehl 在弱初与联合弱初之间的区分，而探针 N5 锁定了它。弱初始性严格弱于初始性，这是经过证明而非断言的，在 Instance/Parallel.v 的行走平行对（已在本文件的闭包中）：[Parallel_ParX_WeaklyInitial]，[Parallel_ParX_not_initial]（两个不等价箭头 [ParX ~> ParY]，[is_initial_unique] 会将它们认同，[discriminate] 闭合它）和 [Parallel_ParY_not_weakly_initial]（分离是关于对象，而不是范畴）。

解集词汇。该问题的“因此解集条件”是 Adjunction/GAFT.v 中的 [sols_of_wif : WeaklyInitialFamily (=(d) ↓ U) → SolutionSet U d]，它正好是 [wif_of_sols] 的逆——相同的索引，相同的成员——并且带有定义为 [weakly_initial_of_initial] 的 [sols_of_wif] 的特殊情况 [sols_of_comma_initial : Initial (=(d) ↓ U) → SolutionSet U d]。两者都被附加在该文件的末尾，以便其上面的内容不会移动（有十一条外部引用指向它）；一般形式的索引以及特殊情况的索引和成员在 [eq_refl] 处被读取。（GAFT 在 #436，[GAFT_iff] 中变为双条件；在写这篇文章时，它还不是双条件。）

证人。Theory/WeaklyInitial/Sets.v（一个叶子卫星；它的闭包是53，比这个文件多25，这就是它不在这里的原因）在 [Sets] 上运行完整的往返： [Sets_initial_characterization := initial_iff_weakly_initial_family_complete Sets_Complete Sets_HasEqualizers]，[Sets_wif := fst … Sets_Initial]，[Sets_initial_recovered := snd … Sets_wif]，以及 [Sets_roundtrip_iso : initial_obj Sets_initial_recovered ≅ initial_obj Sets_Initial] 由 [initial_unique]；在 [eq_refl] 处读取 DERIVED 单集合族的索引和成员（恢复的初始对象没有任何变化）。它降落在 [Sets@{Set u}]，因为 Adjunction/GAFT/Sets.v 的头文件已经为 GAFT 披露了这一点。这将双条件从一个条件转变为一个有具体内容的结果；docs/INHABITATION.md 有这一行。

陈旧的前提。该问题“当前状态”中的每个位置都是陈旧的（它们匹配提交 00fc744b 和 820201bc，“幂与余幂”，以两个片段移动了文件）：它指向 [initial_from_weakly_initial]、[Record WeaklyInitialFamily]、[endo_absorb] 以及唯一性追逐的 [assert (Hk : …)] 都找不到，而其中两个，一个指向此文件，一个指向 Adjunction/GAFT.v，恰好是正确的。每一个实质性的缺失声明都是真实的：
[Build_WeaklyInitialFamily] 在整个树中恰好有一个使用
（Adjunction/GAFT.v；更正，#452：测量时是这样，且
Adjunction/SAFT/InitialObject.v 的 [wif_of_cogenerator] 现在是第二个），没有任何东西从 [Initial] 构建过一个家族，没有任何名为 [WeaklyInitial] 的常量存在（`*.v` 上的 29 个词命中，算上 `_CoqProject` 是 31 个，都是模块路径）。现有头文件的两句话是错误的，已在原处更正，并保持行数不变：该文件的头文件说 [Power.v] 选项“保持 [Instance/Sets] 不在此文件的依赖闭包中”——[Instance/Sets] 已在其中，现在从该文件 [Require]s Instance/Parallel.v 直接两跳，以前通过 Structure/Equalizer/Fork.v 为三跳（docs/INDEX.md 的 Power.v 项记录了从 Power.v 本身的一跳路径，这是正确的，保持不变）；Wide.v 将 [Set] 引脚归属于 [Terminal] 和均衡器供电——两者的约束块都是空的，并且该引脚是 [iprod] 的：[DiscreteCat_Functor] 将离散形状放置在 [DiscreteCat@{u Set Set}]，[Limit] 将形状的同质宇宙标识为环境的同质宇宙。(进一步更正：那个引脚现在也消失了。捐赠者在 PR “代数承载是集合” (2026-09-17) 中已在 Instance/Discrete.v 中标注，所以 [iprod] 不携带任何字面上的 [Set]；[Limit] 对形状的 Hom 宇宙所做的改变保持不变。)

宇宙（[About] 在 `Set Printing Universes` 下）。Riehl 侧常数上没有 [Set]：[WeaklyInitial@{u u0 u1}] 仅携带 Π 型的 `u0 <= u`、`u1 <= u`，[wif_of_weakly_initial] 和 [weakly_initial_obj_of_initial] 也同样如此，它们的类型提到了它；[weakly_initial_of_initial@{u u0 u1}] 单独携带一个 EMPTY 块，而通过 [wif_of_weakly_initial] 的复合将携带四个绑定器和两个约束；并行常数位于该小范畴的层次。已记录更正。早期的修订继续写道：“所有消耗 [iprod] 或 [Limit (DiscreteCat_Functor …)] 的东西——[weakly_initial_iprod]、[FreydProducts]、两者的双条件、[_complete] 包装器及其回读——都在 [C : Category@{_ Set Set}] 上，供体的引脚，带有严格的 `Set < u` 以及大写 `JMeq`、`eq` 和 `Logic_lemmas.equality`，原定理所携带的——并且 `Projections` 在它们所有上，但 [FreydProducts] 除外。”供体的引脚已经消失：[DiscreteCat_Functor] 在 Instance/Discrete.v 的 PR “代数载体是集合” (2026-09-17) 中被注释到位，并在其之后测量的 [iprod@{u u0 u1 u2 u3}] 在 [C : Category@{u1 u2 u2}] 上被陈述，没有字面上的 [Set]。因此，相同常量的环境范畴在它们的同态宇宙中是自由的。旧列表中显示为严格的 `Set < u`，而该文件自身的 [initial_from_weakly_initial@{lim idx obj h +}] 现在显示为 `h < u`，其环境同态宇宙位于字面值所在的位置；stdlib 的上限不受影响，因为它们属于 [eq] 值的同态集体自身。其他五个常量在修复后没有单独重新测量 —— 对它们重新运行 [About]，而不要信任任一列表。在 [Cat] 尝试了一个宇宙反驳，并且没有被拒绝（[Cat] 的同类宇宙在 [Set] 实例化）；它记录在这里，以免被重新发明。

测量完成。在此文件中有 17 个新的 `.glob` 头（15 个 `def`，2 个 `prf`；加上原来的五个共 22 个），Theory/WeaklyInitial/Sets.v 中有 6 个，Adjunction/GAFT.v 中有 5 个，没有 [Program] 义务，全部 33 个“在全局上下文下闭合”，`Axioms:` 行数为零；`make print-assumptions` 门包含全部 33 个，包括该文件的原始五个（之前这些五个都未包含在内）。四个 `Defined` — 这里的两个双条件，[sols_of_wif] 和 [sols_of_comma_initial] — 每个承重（在整个文件的副本中一次翻转为 `Qed`，对应的 [eq_refl] 回读停止）；两个新的 `Qed`（两个平行否定）。关闭此文件29（不包括自身，比之前多一个，Structure/Complete.v，是GAFT关键路径上唯一的新模块；Instance/Parallel.v 已经在里面，边缘为0）；Sets.v 53（Adjunction/GAFT/Sets.v 边缘为15，它的其他六个 `Require` 为0）；Sets.v 没有可删除的 `Require`，并且这个文件的两个新 `Require` 都是必需的，尽管其预先存在的 Theory/Functor.v 和 Theory/Morphisms.v 行是可删除的，并且保留它们以使上述引用的行不移动。28 个新名称没有名称冲突 (`grep -rlw --include='*.v'`)。测试/ProbeWeaklyInitial435.v 镜像
 该文件的 `Require` 列表加上卫星、Adjunction/GAFT.v 和
 他们的供应，根据命令绑定其范畴（[Section] 变量
 将固定固定 [Limit]s 在 [Set] 上所需的 hom 电平），并携带
 6 个反驳命令 = 1 个仪器 + N1 打字（一个对象不是一个
 系列）+ N2-N3 CONVERSION（索引是 [poly_unit]，而不是 [bool]；a
 [Terminal] 不是 [Initial] —“无法统一 λ x y, y ~> x 和
 hom[C]”，[C^op] 枢轴）+ N4-N5 打字（均衡器电源不
 第二个产品； 封面不会使选定的成员变弱
 初始），每个在整个文件的副本中一次剥离一个
 除了其可接受的控制之外； 七个 `eq_refl` 读回； 警卫覆盖
 34/27，有七个详尽的例外（标识符标记在
 六个反驳命令/也在它们之外命名，注释被删除：
 两个关键字、两个绑定变量、两个被反驳的名称和
 仪器的缺席名称）； 重命名模拟的 15 个库名称 —
 [WeaklyInitial]、[WeaklyInitialFamily]、[wif_index]、[wif_obj]、
 XPTECT123X、[weakly_initial_of_initial]、[initial_from_weakly_initial]、
 [Terminal]、[Limit]、[DiscreteCat_Functor]、[HasEqualizers]、[Category]、
 [eq_refl]、[bool]、[projT2] — 正线上的每次首次突破。`make todo` 仅通过 6 条反驳行增长（2277 → 2283 超过 #434 的提示），因此按照原文，问题的“没有新增命中”框未满足（已披露，如 #430-#434 所示）；Coq 8.19 和 8.20 已通过对提交修订的 nix 源代码构建进行检查，这一点在 PR 中记录。

未交付：任何大小类（小型仍保持在宇宙级别）；对 [initial_from_weakly_initial] 或 Wide.v 的定理的任何重新证明或重述（两者保持 [Qed] 且字节相同）；宽形式的双条件，或 [HasWideEqualizers] 实例；仅 [Complete] 的双条件（见上文）；在除 [Sets] 之外的任何范畴中的见证；[Sets_wif] 与手工构建族之间的协议证明，或 [eq_refl] 对循环传输的解释（仅为规范 [≅]）；在单例假设下的 [weakly_initial_of_wif]（人为设计，并会引入 `eq_rect` 上限）；此处任何对象的函子性；将 GAFT 作为双条件；不修改 Structure/Complete.v、Structure/Limit/Product.v、Instance/Parallel.v、Instance/Sets/Complete.v 或 Adjunction/GAFT/Sets.v，以及不修改 Adjunction/GAFT.v 的最后一行以上内容。
*)

(*
[Structure.Complete] for the convenience wrapper; [Instance.Parallel]
   for the separator (already in this file's closure through
   Structure/Equalizer/Fork.v).

--------
[Structure.Complete] 用于便利封装；[Instance.Parallel] 用于分隔符（已经通过 Structure/Equalizer/Fork.v 在此文件的闭包中）。
*)
Require Import Category.Structure.Complete.
Require Import Category.Instance.Parallel.

(** ** A weakly initial object (Riehl Definition 4.7.4) / ** 弱初对象（Riehl 定义 4.7.4） *)

(*
One object with an arrow to every object, no uniqueness.  A weakly
   initial family is the jointly weakly initial version: [wif_cover] picks
   its own member per target.

--------
一个带箭头指向每个对象的对象，没有唯一性。弱初始族是共同弱初始版本：[wif_cover] 为每个目标选择自己的成员。
*)
Definition WeaklyInitial {C : Category} (c : C) : Type := ∀ x : C, c ~> x.

Definition weakly_initial_obj_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitial (@initial_obj C I) := fun x => @zero C I x.

Definition wif_of_weakly_initial {C : Category} {c : C} (w : WeaklyInitial c) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => c
   ; wif_cover := fun x => (ttt; w x) |}.

(*
The product of a weakly initial family is a weakly initial object: the
   [wmap] the proof above builds inline, now named.

--------
弱初族的积是弱初对象：上面的证明内联构建的 [wmap]，现在已命名。
*)
Definition weakly_initial_iprod {C : Category} (W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W))) :
  WeaklyInitial (iprod (wif_obj W) P) :=
  fun c => projT2 (wif_cover W c)
             ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c)).

(** ** Necessity: an initial object is a singleton weakly initial family / ** 必要性：初始对象是一个单例弱初始族 *)

(*
Written directly rather than through [wif_of_weakly_initial]: the direct
   form has an empty universe constraint block and one binder fewer.

--------
直接书写而不是通过 [wif_of_weakly_initial]：直接形式有一个空的宇宙约束块，并且少一个绑定器。
*)
Definition weakly_initial_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => @initial_obj C I
   ; wif_cover := fun x => (ttt; @zero C I x) |}.

(* The family is built from the initial object, on the nose. / 这个家族是从初始对象建立的，正中目标。 *)
Example weakly_initial_of_initial_index {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = poly_unit := eq_refl.

Example weakly_initial_of_initial_obj {C : Category} (I : @Initial C)
  (u : poly_unit) :
  wif_obj (weakly_initial_of_initial I) u = @initial_obj C I := eq_refl.

Example weakly_initial_of_initial_cover {C : Category} (I : @Initial C)
  (x : C) :
  projT2 (wif_cover (weakly_initial_of_initial I) x) = @zero C I x := eq_refl.

(** ** The biconditional / ** 双条件 *)

(*
The Freyd inputs, per family, so smallness stays caller-chosen: the
   product of the family and the product of the endomorphisms of that
   product (the second index depends on the first).

--------
Freyd 输入，对于每个范畴，因此小性保持由调用者选择：该范畴的积以及该积的自同构的积（第二个指标依赖于第一个）。
*)
Definition FreydProducts (C : Category) : Type :=
  ∀ W : WeaklyInitialFamily C,
    { P : Limit (DiscreteCat_Functor (wif_obj W))
    & Limit (DiscreteCat_Functor
               (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P
                => iprod (wif_obj W) P)) }.

(*
Transparent, so that each direction can be read back: the forward one
   IS [weakly_initial_of_initial].

--------
透明的，这样每个方向都可以回读：前向的是 [weakly_initial_of_initial]。
*)
Definition initial_iff_weakly_initial_family {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - intro W.
    destruct (Ps W) as [P Pe].
    exact (initial_from_weakly_initial W P Pe E).
Defined.

Example initial_iff_weakly_initial_family_fst {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family Ps E) I = weakly_initial_of_initial I
  := eq_refl.

(** ** The convenience wrapper: the two products from completeness / ** 便利包装：来自完整性的两种产品 *)

(*
Awodey §9.8's reading: harvest both products from [Complete] and keep
   the equalizers an explicit supply — [Complete_HasEqualizers] lives
   downstream, in Adjunction/GAFT.v, and is not re-derived here.

--------
Awodey §9.8 的解读：从 [Complete] 收获两种产品，并将均衡器保留为显式供应——[Complete_HasEqualizers] 位于下游，在 Adjunction/GAFT.v 中，不在此重新推导。
*)
Definition initial_from_weakly_initial_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (W : WeaklyInitialFamily C) :
  @Initial C :=
  initial_from_weakly_initial W
    (HC (DiscreteCat (wif_index W)) (DiscreteCat_Functor (wif_obj W)))
    (HC (DiscreteCat _)
        (DiscreteCat_Functor
           (fun _ : iprod (wif_obj W)
                      (HC (DiscreteCat (wif_index W))
                          (DiscreteCat_Functor (wif_obj W)))
                    ~> iprod (wif_obj W)
                         (HC (DiscreteCat (wif_index W))
                             (DiscreteCat_Functor (wif_obj W)))
            => iprod (wif_obj W)
                 (HC (DiscreteCat (wif_index W))
                     (DiscreteCat_Functor (wif_obj W))))))
    E.

Definition initial_iff_weakly_initial_family_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - exact (initial_from_weakly_initial_complete HC E).
Defined.

Example initial_iff_weakly_initial_family_complete_fst {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family_complete HC E) I
    = weakly_initial_of_initial I := eq_refl.

(** ** Weakly initial is strictly weaker than initial / ** 弱初始严格弱于初始 *)

(*
At the walking parallel pair: [ParX] reaches every object, is not
   initial (two inequivalent arrows to [ParY]), and [ParY] is not even
   weakly initial — the separation is about the object, not the category.

--------
在步行平行对：[ParX] 可以到达每个对象，不是初始对象（有两个不等价的箭头指向 [ParY]），而 [ParY] 甚至不是弱初始对象——这种区分是关于对象的，而不是关于范畴的。
*)
Definition Parallel_ParX_WeaklyInitial : @WeaklyInitial Parallel ParX :=
  fun x => match x with
           | ParX => (true; ParIdX)
           | ParY => (true; ParOne)
           end.

Theorem Parallel_ParX_not_initial : @IsInitialObj Parallel ParX → False.
Proof.
  intro H.
  pose proof (@is_initial_unique Parallel ParX H ParY
                (true; ParOne) (false; ParTwo)) as E.
  simpl in E.
  discriminate E.
Qed.

Theorem Parallel_ParY_not_weakly_initial :
  @WeaklyInitial Parallel ParY → False.
Proof.
  intro w.
  destruct (w ParX) as [b h].
  exact (ParHom_Y_X_absurd b h).
Qed.
