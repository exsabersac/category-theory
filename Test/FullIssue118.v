(**
* Regression test for issue #118: the [Full] type class.

    https://github.com/jwiegley/category-theory/issues/118

    The [Full] type class must express the *standard* notion of a full
    functor: a section [prefmap] of the hom-map [fmap[F]] together with the
    surjectivity witness [fmap_sur] — and nothing more.  No functoriality may
    be demanded of [prefmap].  The previous definition additionally carried
    [prefmap_respects], [prefmap_id] and [prefmap_comp]; those three fields
    were extraneous and have been removed, leaving exactly:

      Class Full `(F : C ⟶ D) := {
        prefmap {x y} (g : F x ~> F y) : x ~> y;
        fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g
      }.

    This file pins that two-field shape.  It constructs a [Full] instance
    using *only* [prefmap] and [fmap_sur]:

      - [Id_Full_build] applies the generated constructor [Build_Full] to
        exactly those two values.  Under the old five-field class this is a
        partial application whose type still expects the three dropped fields,
        so it is rejected; under the corrected class it has type [Full Id[C]].

      - [Full_from_section] does the same via a record literal that lists only
        the two surviving fields.  Under the old class the omitted fields turn
        into unresolved implicit arguments (a hard error); under the corrected
        class the literal is complete.

    Either construction therefore compiles only against the corrected
    definition and fails against the old one.  Finally we reference
    [FullyFaithful] — the lemma whose proof previously relied on the removed
    [prefmap_comp] / [prefmap_id] — to confirm it still typechecks under the
    leaner class.

--------
* 针对问题 #118 的回归测试：[Full] 类型类。

https://github.com/jwiegley/category-theory/issues/118

[Full] 类型类必须表达一个*标准*的满函子概念：在同态映射 [fmap[F] 上的一个截面 [prefmap]，以及满射性证明 [fmap_sur] —— 不需要更多。不能要求 [prefmap] 具有函子性。之前的定义还包含了 [prefmap_respects]、[prefmap_id] 和 [prefmap_comp]；这三个字段是多余的，已被移除，现在留下的正好是：

类 Full `(F : C ⟶ D) := {
        prefmap {x y} (g : F x ~> F y) : x ~> y;
        fmap_sur {x y} (g : F x ~> F y) : fmap[F] (prefmap g) ≈ g
      }.

该文件固定了那个两字段的结构。它仅使用 [prefmap] 和 [fmap_sur] 构造一个 [Full] 实例：

- [Id_Full_build] 将生成的构造函数 [Build_Full] 应用于恰好这两个值。在旧的五字段类下，这是一个部分应用，其类型仍然期望三个被省略的字段，因此会被拒绝；在修正后的类下，它的类型是 [Full Id[C]。

- [Full_from_section] 通过一个只列出两个幸存字段的记录字面量实现相同的功能。在旧类中，被省略的字段会变成未解析的隐式参数（一个严重错误）；在修正后的类中，该字面量是完整的。

因此，任一构造只能针对已更正的定义进行编译，而针对旧定义则会失败。最后，我们引用 [FullyFaithful] —— 该引理的证明之前依赖于已移除的 [prefmap_comp] / [prefmap_id] —— 以确认它在精简后的类下仍然类型检查通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(**
** Constructor form.

    [Build_Full] is the constructor generated for the [Full] class.  We feed
    it exactly the two fields of the corrected definition.  The identity
    functor's hom-map is the identity on [x ~> y], so the chosen preimage is
    [g] itself and [fmap_sur] holds by reflexivity (recall that [fmap[Id[C]] g]
    reduces to [g]).

--------
** 构造函数形式。

[Build_Full] 是为 [Full] 类生成的构造函数。我们将修正定义中的恰好两个字段提供给它。恒等函子（identity functor）的同态映射是 [x ~> y] 上的恒等映射，因此选择的原像是 [g] 本身，并且 [fmap_sur] 通过自反性成立（回想 [fmap[Id[C]] g] 归约为 [g]）。
*)
Definition Id_Full_build (C : Category) : Full (Id[C]) :=
  Build_Full _ _ Id[C]
    (fun x y (g : Id[C] x ~> Id[C] y) => g)
    (fun x y (g : Id[C] x ~> Id[C] y) => reflexivity g).

(**
** Record-literal form.

    The same two-field shape, expressed as a section of an arbitrary functor's
    hom-map.  The literal mentions only [prefmap] and [fmap_sur]; under the old
    class the missing functoriality fields would be unresolved implicits.

--------
** 记录-字面形式。

相同的双字段形状，表示为任意函子同态映射的一部分。字面上只提到 [prefmap] 和 [fmap_sur]；在旧类下，缺失的函子性字段将是未解析的隐式项。
*)
Definition Full_from_section
  `(F : C ⟶ D)
  (pre : ∀ x y, F x ~> F y → x ~> y)
  (sec : ∀ x y (g : F x ~> F y), fmap[F] (pre x y g) ≈ g) : Full F :=
  {| prefmap x y g := pre x y g
   ; fmap_sur x y g := sec x y g |}.

(**
The identity functor is full: every hom-map is the identity, hence its own
    section.  The witness is exhibited through [Full_from_section], with the
    section law closed explicitly by [reflexivity] rather than left to the
    ambient [Program] obligation tactic — so the test states its own proof.

--------
恒等函子是满的：每个同态映射都是恒等的，因此它自身就是其截面。通过 [Full_from_section] 展示了该证据，截面律由 [reflexivity] 明确封闭，而不是留给环境中的 [Program] 义务策略——因此测试陈述了它自己的证明。
*)
Definition Id_Full {C : Category} : Full (@Id C) :=
  Full_from_section Id (fun _ _ g => g) (fun _ _ g => reflexivity g).

(** Register an instance so resolution of the leaner class is exercised too. / 注册一个实例，以便也能够使用精简类的解析。 *)
#[local] Existing Instance Id_Full.

(**
The two surviving projections, with their expected types under the
    corrected definition.

--------
根据修正后的定义，两个幸存的投影及其预期类型。
*)
Check @prefmap.
Check @fmap_sur.

(**
** [FullyFaithful] under the leaner class.

    The identity functor is trivially faithful; combined with fullness this
    lets us instantiate [FullyFaithful] and confirm the lemma — whose proof no
    longer has access to [prefmap_comp] / [prefmap_id] — still elaborates.

--------
** [FullyFaithful] 在精简类下。

恒等函子显然是忠实的；结合丰满性，这让我们可以实例化 [FullyFaithful] 并确认引理——其证明不再访问 [prefmap_comp] / [prefmap_id]——仍然可以展开。
*)
#[local] Program Instance Id_Faithful (C : Category) : Faithful (Id[C]) := {|
  fmap_inj := fun x y (f g : x ~> y) (H : f ≈ g) => H
|}.

Definition FullyFaithful_under_lean_Full
  `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y := FullyFaithful F.

(** Pin a concrete instantiation as well, independent of implicit inference. / 也要固定一个具体的实例，与隐式推理无关。 *)
Check (fun C : Category =>
         @FullyFaithful C C Id[C] (Id_Full_build C) (Id_Faithful C)).
