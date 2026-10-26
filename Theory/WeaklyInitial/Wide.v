Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Freyd's initial-object construction, through the wide-equalizer API / * 弗雷德的初始对象构造，通过宽等化器 API *)

(*
nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   [Theory/WeaklyInitial.v] proves [initial_from_weakly_initial]: a weakly
   initial family, a product of it, an endomorphism-indexed POWER of that
   product, and a supply of BINARY equalizers together yield a genuine
   initial object (Freyd; Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.6).  The power is there for one reason,
   which that file states in terms: it is the device by which “the wide
   equalizer of the endomorphism family reduces to one *binary*
   equalizer”.  With wide equalizers available the device is unnecessary,
   and this file says so — [initial_from_weakly_initial_wide] equalizes
   ALL endomorphisms of the product directly, which is the form Freyd's
   argument is usually presented in.

   WHAT THIS FILE IS AND IS NOT.  It is ADDITIVE.  [Theory/WeaklyInitial.v]
   is untouched: [initial_from_weakly_initial] keeps its statement, its
   proof and its universe constraints, and [Adjunction/GAFT.v],
   [Adjunction/SAFT.v] and the two GAFT example files keep consuming it
   unchanged.  Nothing here is claimed to supersede it, and the two are not
   related by any passage — neither theorem is derived from the other.

   THE TRADE, STATED PLAINLY.  The wide form drops one hypothesis (the
   power [Pe]) and needs no separate binary-equalizer supply, since the
   two-element family [fun b : bool => if b then f else g] is a wide family
   like any other.  What it costs is the shape of the remaining hypothesis:
   [HasWideEqualizers] is a CLASS whose index [Type] is a universe
   parameter, and the endomorphism family forces that parameter to sit at
   or above the ambient hom universe.  [Theory/WeaklyInitial.v] avoids
   exactly this by passing both limits as explicit hypotheses, on the
   stated ground that a class quantifying over index [Type]s would
   over-commit the ambient universes; that reasoning is not withdrawn here.
   A caller who wants the leaner input keeps the original theorem, and a
   caller who has wide equalizers uses this one.

   WHERE THE PROOF ACTUALLY GETS SHORTER.  In the original, absorption of
   endomorphisms ([endo_absorb]) is four rewrites through the two tuplings
   [m] and [d] and their defining families.  Here it is one instance of the
   wide fork condition at [u] and [id], followed by [id_left]: the wide
   equalizer's defining equation IS “every endomorphism agrees with the
   identity after [e]”.  Monicity of the equalizing map, which supplies the
   uniqueness half, comes from [wide_equalizer_monic] exactly as it came
   from [equalizer_monic].  The endgame — a weakly initial map into the
   equalizer of a competing pair, exhibited as a section, then cancellation
   — is the original's, transcribed.

   UNIVERSES, measured (reproduce with [Set Printing Universes. About
   initial_from_weakly_initial. About initial_from_weakly_initial_wide.]).
   RECORDED CORRECTION.  An earlier revision read: “Both theorems are over
   [C : Category@{u2 Set Set}] — the pin at [Set] is the DONOR's, from
   [iprod] and not from [Terminal] or the equalizers (both unpinned;
   measured in #435).  The binder COUNT is the same — both are
   [@{u u0 u1 u2}], so there is no extra binder: the wide form replaces the
   power's binder with the class's index binder, which is itself
   unconstrained, appearing free in [HasWideEqualizers@{u1 u2 Set} C].”
   The attribution to the donor was right, and the donor has been
   repaired: [iprod] inherited its [Set] from Instance/Discrete.v's
   unannotated [DiscreteCat_Functor], annotated in place there in the
   PR “algebraic carriers are sets” (2026-09-17).  Measured after it,

     initial_from_weakly_initial_wide@{u u0 u1 u2 u3} :
       ∀ {C : Category@{u2 u3 u3}} (W : WeaklyInitialFamily@{u1 u2 u3} C),
       Limit@{u0 u1 u3 u2} (DiscreteCat_Functor@{u1 u3 u3 u2 u3 u3 u} …)
       → HasWideEqualizers@{u3 u2 u3} C → Terminal@{u2 u3}   (* u3 < u *)

--------
nLab：https://ncatlab.org/nlab/show/adjoint+functor+theorem
维基百科：https://en.wikipedia.org/wiki/Adjoint_functor_theorem

[Theory/WeaklyInitial.v] 证明了 [initial_from_weakly_initial]：一个弱初始簇，其一个积，该积的自同态索引幂，以及一组二元等化器，结合起来产生一个真正的初始对象（Freyd；Mac Lane，《为应用数学家讲述的范畴论》，第二版，第V.6节）。引入幂的原因只有一个，该文件用术语说明：它是使“自同态簇的广义等化器归约为一个*二元*等化器”的工具。由于有宽频均衡器可用，这个设备是多余的，这个文件也这么说——[initial_from_weakly_initial_wide] 直接均衡产品的所有自同态，这是 Freyd 的论证通常呈现的形式。

这个文件是什么以及不是什么。它是附加性的。[Theory/WeaklyInitial.v]保持不变：[initial_from_weakly_initial]保留其陈述、证明及其宇宙约束，[Adjunction/GAFT.v]、[Adjunction/SAFT.v]以及两个GAFT示例文件继续不变地使用它。这里没有任何内容声称要取代它，而且两者之间没有任何章节相关——两个定理都不是由对方推导出的。

交易，直白地说。广义形式放弃了一个假设（幂 [Pe]），且不需要单独的二进制均衡器供电，因为双元素族 [fun b : bool => if b then f else g] 是像其他任何族一样的广义族。其代价是剩余假设的形式：[HasWideEqualizers] 是一个类，其索引 [Type] 是一个宇宙参数，而自同态族强制该参数位于或高于环境同构宇宙。[Theory/WeaklyInitial.v] 避免了完全相同的问题，通过将两个界限作为明确的假设传递，其理由是量化索引 [Type] 的类会过度承诺当前的宇宙；这里并没有撤回这一推理。希望更精简输入的调用者保持使用原定理，而拥有广泛等化器的调用者则使用这个定理。

证明实际上变得更简短。在原文中，幂自同态的吸收（[endo_absorb]）通过两个对偶 [m] 和 [d] 及其定义的族进行了四次重写。在这里，它是在 [u] 和 [id] 处广叉条件的一个实例，然后是 [id_left]：广等化器的定义方程是“每个幂自同态在 [e] 之后与恒等映射一致”。等化映射的单性，提供了唯一性的一半，来源于 [wide_equalizer_monic]，就像它来源于 [equalizer_monic] 一样。最后阶段——一个弱初始映射进入竞争对的等化器，表现为一个截面，然后是消去——是原文的，已被转录。

宇宙，通过[设置打印宇宙。关于 initial_from_weakly_initial。关于 initial_from_weakly_initial_wide。]测量（再现）。记录的更正。早期的修订版本写道：“两个定理都涉及 [C : Category@{u2 Set Set}] —— [Set] 的针是捐赠者的，来源于 [iprod]，而不是 [Terminal] 或均衡器（两者未固定；在 #435 中测量）。绑定器 COUNT 相同 —— 都是 [@{u u0 u1 u2}]，所以没有额外的绑定器：宽形式用类的索引绑定器替代了 power 的绑定器，该绑定器本身不受约束，在 [HasWideEqualizers@{u1 u2 Set} C] 中自由出现。对捐赠者的归属是正确的，并且捐赠者已被修复：[iprod] 从 Instance/Discrete.v 的未标注 [DiscreteCat_Functor] 继承了其 [Set]，该绑定器在 PR “代数承载体是集合”（2026-09-17）中已在原位标注。之后测量,

initial_from_weakly_initial_wide@{u u0 u1 u2 u3} :
       ∀ {C : Category@{u2 u3 u3}} (W : WeaklyInitialFamily@{u1 u2 u3} C),
       Limit@{u0 u1 u3 u2} (DiscreteCat_Functor@{u1 u3 u3 u2 u3 u3 u} …)
       → HasWideEqualizers@{u3 u2 u3} C → Terminal@{u2 u3}   (* u3 < u *)

   -- no literal [Set], the ambient hom universe [u3] free, and FIVE
   binders where the old reading counted four (the annotated donor's
   auxiliary level is the extra one).  [HasWideEqualizers] now reads
   [@{u3 u2 u3}] where the old text quoted [@{u1 u2 Set}]; whether its
   index slot is still free of the ambient's levels has NOT been
   re-measured, and the old claim that it is should not be repeated
   without re-running [About].  The
   constraint-block difference runs the other way: the DONOR carries two
   extra stdlib bounds ([u0 <= eq.u0], [u0 <= Logic_lemmas.equality.u0])
   from the power's discrete diagram, which the wide form drops.

   NOT DELIVERED.  No [HasWideEqualizers] instance, so this theorem has no
   in-tree application and is a conditional exactly as its donor is; in
   particular [Adjunction/GAFT.v] is NOT rerouted through it.  No wide
   analogue of [Structure/Limit/Product.v]'s indexed products (the product
   [P] is still an ordinary discrete-diagram limit).  No claim that the two
   theorems have the same universe constraints — they do not, and the
   difference is the donor's two extra bounds described above. *)

(*
A weakly initial family, a product of it, and a supply of wide
   equalizers yield a genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial.  Take the
   wide equalizer [e : I ~> P0] of the family of ALL endomorphisms of [P0],
   indexed by the hom-type itself.  Its fork condition instantiated at an
   endomorphism [u] and at [id] says [u ∘ e ≈ id ∘ e], i.e. [e] absorbs
   every endomorphism; and [e] is monic.  This [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e];
     - uniqueness: given [f g : I ~> c], take the wide equalizer [k : K ~> I]
       of the two-element family {f, g}; weak initiality gives [s : P0 ~> K],
       so [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e];
       monicity of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi,
       and [f ∘ k ≈ g ∘ k] forces [f ≈ g].

--------
一个弱初始范畴、它的一个积和一组广义均衡器提供了一个真正的初始对象。

构造。对于对象 [iprod (wif_obj W) P] 的乘积对象，写 [P0]。对于任何 [c]，覆盖箭头 [wif_cover c] 与匹配的投影复合得到映射 [P0 ~> c]，因此 [P0] 是弱初始的。取 [P0] 所有自射的族的广义等化子 [e : I ~> P0]，索引由同态类型本身给出。在自射 [u] 处以及在 [id] 处实例化其叉条件表示 [u ∘ e ≈ id ∘ e]，即。[e] 吸收每个自同态；并且 [e] 是单射。这个 [I] 是初始对象：

- 存在性 [I ~> c]: [wmap c ∘ e]；
- 唯一性：给定 [f g : I ~> c]，取二元族 {f, g} 的广义等化器 [k : K ~> I]；弱初始性给出 [s : P0 ~> K]，因此 [e ∘ (k ∘ s)] 是 [P0] 的自同态，被 [e] 吸收；[e] 的单态性于是得到 [(k ∘ s) ∘ e ≈ id]，即 [k] 是分裂的满射，而 [f ∘ k ≈ g ∘ k] 强制 [f ≈ g]。
*)
Theorem initial_from_weakly_initial_wide `(W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W)))
  (E : HasWideEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object. / 缩写产品对象。 *)
  set (P0 := iprod (wif_obj W) P) in *.

  (* Weak initiality of [P0]: a chosen map into every object. / [P0] 的弱初始性：一个映射到每个对象的选定映射。 *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (*
The wide equalizer of the family of ALL endomorphisms of [P0].  The
     index type is the hom-type [P0 ~> P0] and the family is the identity
     assignment, so “the i-th member” IS the endomorphism [i].

--------
[P0] 的所有自同态族的广义等化器。索引类型是同态类型 [P0 ~> P0]，族是恒等映射，所以“第 i 个成员”就是自同态 [i]。
*)
  destruct (@wide_equalizer C E (P0 ~> P0) P0 P0 (fun u => u))
    as [I [e Eeq]].

  (*
Every endomorphism of [P0] is absorbed by the equalizing map.  This is
     one instance of the wide fork condition — at [u] and at [id] — where
     the original needed the two tuplings through the power.

--------
[P0] 的每一个自同态都被等化映射吸收。这是宽叉条件的一个实例——在 [u] 和 [id]——其中原本需要通过幂的两个配对。
*)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    transitivity (id[P0] ∘ e).
    - exact (wfork_eq Eeq u id[P0]).
    - apply id_left. }

  (* The equalizing map is monic. / 该平衡映射是单射的。 *)
  pose proof (wide_equalizer_monic (fun u : P0 ~> P0 => u) Eeq) as Me.
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
    (*
the wide equalizer of the two-element family {f, g}; no separate
       binary-equalizer supply is needed

--------
由二元函数族 {f, g} 的广义等化器；不需要单独提供二元等化器
*)
    destruct (@wide_equalizer C E bool I x
                (fun b : bool => if b then unop f else unop g))
      as [K [k Ek]].
    assert (Hfg : unop f ∘ k ≈ unop g ∘ k)
      by exact (wfork_eq Ek true false).
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
           ++ apply compose_respects; [ exact Hfg | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.
