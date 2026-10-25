Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The arrows-only presentation of natural transformations / 自然变换的仅箭头表示 *)

(*
nLab: https://ncatlab.org/nlab/show/natural+transformation
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer 1998, §I.4 (printed p. 19), exercise 5

   A natural transformation τ : S ⟹ T between functors S T : C ⟶ D is
   ordinarily a family indexed by the OBJECTS of C — one component
   τ_c : S c ~> T c for each c — subject to one naturality square per arrow
   (Theory/Natural/Transformation.v).  Mac Lane's exercise gives the
   object-free reading of the same data: index instead by the ARROWS of C.
   To each f : c ~> c' assign a single morphism τ f : S c ~> T c', subject
   to the chain

       fmap[T] g ∘ τ f  ≈  τ (g ∘ f)  ≈  τ g ∘ fmap[S] f

   for every composable pair g, f.  [ArrowTransform] below is that record,
   its two equations being the fields [τ_arr_left] and [τ_arr_right].  The
   correspondence with [Transform] is [Transform_to_Arrows] and
   [Arrows_to_Transform]; they are mutually inverse up to ≈
   ([Transform_to_Arrows_to_Transform], [Arrows_to_Transform_to_Arrows]),
   each respects the relevant setoid ([Transform_to_Arrows_respects],
   [Arrows_to_Transform_respects]), and the pair is packaged as an
   isomorphism of setoids in Sets ([Transform_Arrows_iso]).

--------
nLab: https://ncatlab.org/nlab/show/natural+transformation
   书籍: Mac Lane，《为实践数学家准备的范畴》，第2版，
         Springer 1998，第I.4节（印刷页19），练习5

在函子 S, T : C ⟶ D 之间的自然变换 τ : S ⟹ T 通常是由 C 的对象索引的一族——对每个对象 c 有一个分量 τ_c : S c ~> T c——并且对于每条箭头满足一个自然性方格（Theory/Natural/Transformation.v）。Mac Lane 的练习给出了同一数据的无对象表述：改为以 C 的箭头为索引。对于每条 f : c ~> c' 分配一个单一的态射 τ f : S c ~> T c'，并满足链式条件。

fmap[T] g ∘ τ f  ≈  τ (g ∘ f)  ≈  τ g ∘ fmap[S] f

对于每一对可组合的 g、f。下面的 [ArrowTransform] 是该记录，其两个方程分别是字段 [τ_arr_left] 和 [τ_arr_right]。与 [Transform] 的对应是 [Transform_to_Arrows] 和 [Arrows_to_Transform]；它们在 ≈ ([Transform_to_Arrows_to_Transform], [Arrows_to_Transform_to_Arrows]) 下互为逆，每个都尊重相关的集合等价关系 ([Transform_to_Arrows_respects], [Arrows_to_Transform_respects])，这对被作为集合中集合等价同构打包 ([Transform_Arrows_iso])。
*)

(*
Where the naturality square went

   Given τ : S ⟹ T there are two ways to turn f : c ~> c' into a morphism
   S c ~> T c': travel by S and then transform, τ_{c'} ∘ fmap[S] f, or
   transform and then travel by T, fmap[T] f ∘ τ_c.  The naturality square
   says precisely that the two agree, so the pair collapses into one
   operation on arrows — and that operation is the arrow family.  This is
   the point of the exercise, and it is recorded here as
   [Transform_to_Arrows_alt]: the family built from τ by the first formula
   satisfies the second, the proof being [naturality] and nothing else.
   In the reverse direction the components are read off the identities,
   τ_c := τ (id[c]), and the naturality square is recovered as
   [τ_arr_diagonal_naturality].

   Object-free presentations run through the library one level further
   down.  Theory/Metacategory/ArrowsOnly.v carries Mac Lane's arrows-only
   axiomatization of a CATEGORY (CWM §I.1): there is no sort of objects at
   all, an object being recovered as an identity arrow, and
   [Category_from_Metacategory] builds a [Category] whose objects are the
   identity arrows [{i | is_identity i}] of a [Metacategory].  The move
   made here is the same move one dimension up — the components of a
   transformation are its values at the identity arrows — and the
   machinery is entirely separate: that file's partial composition on
   [N]-indexed arrows shares no constant with this one.

   A third reading of the same fusion is the interval category.  As
   Instance/Two.v records, a natural transformation between two functors
   C ⟶ D is a functor C ∏ 2 ⟶ D, a directed homotopy; the arrow family is
   what such a functor does to the arrows of C ∏ 2 that cross the
   interval, namely (f, TwoXY) ↦ τ f.  The walking arrow 2 reappears below
   as the base of the independence countermodels.

--------
自然广场去了哪里

给定 τ : S ⟹ T，有两种方法可以将 f : c ~> c' 转化为态射
   S c ~> T c'：先通过 S 传递然后变换，τ_{c'} ∘ fmap[S] f，或者
   先变换然后通过 T 传递，fmap[T] f ∘ τ_c。自然性方形准确地表示两者相等，因此这一对会简化为箭头上的一个操作——而这个操作就是箭头族。这就是练习的要点，它在这里被记录为 [Transform_to_Arrows_alt]：通过第一个公式由 τ 构建的族满足第二个公式，证明是 [naturality]，仅此而已。
   在反向方向上，分量直接从恒等式中读取，τ_c := τ (id[c])，自然性方形则可以恢复为 [τ_arr_diagonal_naturality]。

无对象的表示在库中进一步向下运行一级。Theory/Metacategory/ArrowsOnly.v 包含 Mac Lane 对 CATEGORY 的仅箭头公理化 (CWM §I.1)：根本不存在任何对象，对象是通过恒等箭头恢复出来的，而 [Category_from_Metacategory] 构建了一个 [Category]，其对象是 [Metacategory] 的恒等箭头 [{i | is_identity i}]。这里所采取的步骤与上一维度相同——变换的分量是其在恒等箭头处的值——并且机制完全独立：该文件中对 [N] 索引箭头的部分组合与此文件没有任何共享常数。

同一融合的第三种理解是区间范畴。正如 Instance/Two.v 所记录的，两个函子 C ⟶ D 之间的自然变换是一个函子 C ∏ 2 ⟶ D，即一种有向同伦；箭头族是这样的函子对 C ∏ 2 中跨越区间的箭头所做的映射，即 (f, TwoXY) ↦ τ f。下文中，行走箭头 2 再次出现，作为独立性反例的基础。
*)

(*
Two equations, both of which carry content

   The tree's [Transform] carries [naturality] together with
   [naturality_sym], but those are one equation in two orientations, kept
   apart so that duality holds definitionally; the comment above
   [Transform] says so, and [Build_Transform'] derives the second from the
   first by [symmetry].  The two splice laws here are not of that kind.
   Neither implies the other, and section [Independence] below proves it
   with two concrete families over the walking arrow 2 (Instance/Two.v)
   and the walking parallel pair (Instance/Parallel.v), whose two arrows
   ParX ~> ParY are non-equivalent: [dom_family], which reads only the
   domain of its argument, satisfies the left law ([dom_family_left]) and
   refutes the right one ([dom_family_not_right]); [cod_family], which
   reads only the codomain, does the reverse.  Both are respectful
   ([dom_family_respects], [cod_family_respects]), so the independence is
   not an artifact of dropping respectfulness.

   What the two laws jointly buy is respectfulness itself.  A family that
   respects ≈ in its argument is what the tree's setoid discipline
   normally has to require as a field, but here it is a consequence:
   [τ_arr_from_left] proves τ f ≈ fmap[T] f ∘ τ (id[c]) by rewriting once
   with each law — the left law supplies fmap[T] f ∘ τ (id) ≈ τ (f ∘ id),
   the right law supplies τ (f ∘ id) ≈ τ f ∘ fmap[S] (id) — and the
   right-hand side depends on f only through fmap[T] f, which respects ≈
   already.  [τ_arr_respects] is that argument, and the record therefore
   has no [Proper] field.  Each law alone reaches only one half of the
   detour: the equations constrain the family at terms literally of the
   form g ∘ f, so passing between τ f and τ (f ∘ id) is itself an appeal
   to a law, and it is the other one.

   The dual reading [τ_arr_from_right], τ f ≈ τ (id[c']) ∘ fmap[S] f, is
   available on the same footing, and the equality of the two right-hand
   sides is the naturality square of the diagonal family c ↦ τ (id[c]).
   That is the whole content of the reverse direction of the
   correspondence, and it is what [Arrows_to_Transform] is built from.

--------
两个方程，都包含内容

这棵树的 [Transform] 携带了 [naturality] 和 [naturality_sym]，但它们是两个方向的同一个方程，被分开以便定义上保持对偶性；[Transform] 上方的注释说明了这一点，而 [Build_Transform'] 通过 [symmetry] 从第一个推导出第二个。这里的两个拼接律不是那种类型。它们彼此并不蕴含，下文第 [Independence] 节通过在步行箭头 2（Instance/Two.v）和步行平行对（Instance/Parallel.v）上的两个具体族证明了这一点，其中的两条箭头 ParX ~> ParY 非等价：[dom_family] 仅读取其参数的定义域，满足左律（[dom_family_left]）并否定右律（[dom_family_not_right]）；[cod_family] 仅读取余域，则相反。两者都是尊重性的（[dom_family_respects], [cod_family_respects]），因此独立性并非因为放弃尊重性而产生的现象。

两条定律共同购买的是敬重本身。一个在论证中尊重≈的家族，是树的集合体范式通常必须要求作为字段的，但在这里它是一个结果：[τ_arr_from_left] 通过用每条定律各重写一次证明 τ f ≈ fmap[T] f ∘ τ (id[c])——左边的定律提供 fmap[T] f ∘ τ (id) ≈ τ (f ∘ id)，右边的定律提供 τ (f ∘ id) ≈ τ f ∘ fmap[S] (id)——右侧仅通过 fmap[T] f 依赖 f，而 fmap[T] f 已经尊重≈了。[τ_arr_respects] 就是这个论证，因此该记录没有 [Proper] 字段。单独每条定律只到达绕道的一半：方程式约束家族在字面形式为 g ∘ f 的项上，所以在 τ f 和 τ (f ∘ id) 之间的转换本身就是对定律的调用，而使用的是另一条定律。

双重阅读 [τ_arr_from_right]，τ f ≈ τ (id[c']) ∘ fmap[S] f，在相同基础上是可用的，并且两个右侧的等式是对角族 c ↦ τ (id[c]) 的自然性方形。这就是对应关系反向方向的全部内容，也是 [Arrows_to_Transform] 的构建基础。
*)

Section ArrowTransform.

Context {C : Category}.
Context {D : Category}.
Context {S : C ⟶ D}.
Context {T : C ⟶ D}.

(*
An arrow-indexed family: one morphism S c ~> T c' for each f : c ~> c',
   with the two splice laws.  [τ_arr_left] absorbs a post-composition into
   the family through T, [τ_arr_right] absorbs a pre-composition through
   S; together they are Mac Lane's displayed chain, and [τ_arr_splice]
   below states that chain as the single equation it is usually written
   as.

   A universe note, since the parent file is careful about this and a
   reader comparing the two will notice the difference.  Where
   Theory/Natural/Transformation.v declares its six universes up front and
   keeps the hom and proof levels of each category independent, the record
   below lets them be inferred, and inference collapses the hom level onto
   the proof level in both categories.  So [Transform] applies at strictly
   more instantiations than [ArrowTransform] does.  Nothing here needs the
   extra generality, and the correspondence theorems below are stated at
   the shared instantiation, but the asymmetry is real and is recorded
   rather than papered over.

--------
箭头索引的族：为每个 f : c ~> c' 有一个态射 S c ~> T c'，并满足两个拼接律。[τ_arr_left] 通过 T 吸收后组合进族中，[τ_arr_right] 通过 S 吸收前组合；它们一起构成了 Mac Lane 的显示链，而下面的 [τ_arr_splice] 则以通常书写的单一方程形式表示这个链。

一个关于宇宙的说明，因为源文件对此很谨慎，而一个比较两者的读者会注意到差异。 其中 Theory/Natural/Transformation.v 在开头声明了它的六个宇宙，并保持每个范畴的 hom 和 proof 级别独立，而下面的记录允许它们被推断，并且推断会将两个范畴中的 hom 级别折叠到 proof 级别上。因此 [Transform] 在严格意义上应用于的实例比 [ArrowTransform] 多。这里没有任何内容需要额外的泛化，并且下面的对应定理在共享实例上陈述，但这种不对称是真实存在的，并且被记录下来，而不是掩盖。
*)

(*
   【Record ArrowTransform 展开】/ Walkthrough（薄）
   自然变换入口见 Theory/Natural/Transformation.v（已有完整展开）。

   箭头视角：给每个基态射 f : c ~> c' 一条「对角线」τ_arr f : S c ~> T c'，
   满足与 S/T 的函子作用相容的正方形（自然性的箭头形式）。
   Arrow-form of a natural transformation: a family of diagonals for each f.
*)

Record ArrowTransform := {
  τ_arr {c c' : C} (f : c ~> c') : S c ~> T c';

  (* post-composition splices in through T / 通过 T 的后期拼接 *)
  τ_arr_left {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    fmap[T] g ∘ τ_arr f ≈ τ_arr (g ∘ f);

  (* pre-composition splices in through S / 通过 S 的预构图拼接 *)
  τ_arr_right {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    τ_arr (g ∘ f) ≈ τ_arr g ∘ fmap[S] f
}.

(*
The two fields chained, i.e. the exercise's displayed equation with its
   middle term elided.

--------
两个字段被链接，即练习中显示的方程及其中间项被省略。
*)

Lemma τ_arr_splice (A : ArrowTransform) {c c' c'' : C}
      (g : c' ~> c'') (f : c ~> c') :
  fmap[T] g ∘ τ_arr A f ≈ τ_arr A g ∘ fmap[S] f.
Proof.
  rewrite τ_arr_left.
  apply τ_arr_right.
Qed.

(*
The family is determined by its values at the identities, in two ways.
   Each derivation uses BOTH laws: the detour through the padded term
   f ∘ id[c] is legitimized by one law and removed by the other.

--------
家庭由其恒等下的价值决定，有两种方式。每个推导都使用两条定律：通过填充项 f ∘ id[c] 的迂回路径由一条定律合法化，并由另一条定律移除。
*)

Lemma τ_arr_from_left (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ fmap[T] f ∘ τ_arr A (id[c]).
Proof.
  rewrite (τ_arr_left A f (id[c])).       (* fmap[T] f ∘ τ id ≈ τ (f ∘ id) / fmap[T] f ∘ τ id ≈ τ (f ∘ id) *)
  rewrite (τ_arr_right A f (id[c])).      (* τ (f ∘ id) ≈ τ f ∘ fmap[S] id / τ (f ∘ id) ≈ τ f ∘ fmap[S] id *)
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Lemma τ_arr_from_right (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- (τ_arr_right A (id[c']) f).  (* τ id ∘ fmap[S] f ≈ τ (id ∘ f) / τ id ∘ fmap[S] f ≈ τ (id ∘ f) *)
  rewrite <- (τ_arr_left A (id[c']) f).   (* τ (id ∘ f) ≈ fmap[T] id ∘ τ f / τ (id ∘ f) ≈ fmap[T] id ∘ τ f *)
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* Respectfulness is a consequence of the two laws, not a further field. / 尊重是这两条律法的结果，而不是另一个领域。 *)

#[export]
Instance τ_arr_respects (A : ArrowTransform) {c c'} :
  Proper (equiv ==> equiv) (@τ_arr A c c').
Proof.
  intros f f' Hf.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left A f').
  now rewrite Hf.
Qed.

(*
The naturality square of the diagonal family c ↦ τ (id[c]), obtained by
   reading the previous two lemmas in opposite directions.

--------
通过反向解读前两个引理所得到的对角族 c ↦ τ (id[c]) 的自然性平方。
*)

Lemma τ_arr_diagonal_naturality (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  fmap[T] f ∘ τ_arr A (id[c]) ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- τ_arr_from_left.
  apply τ_arr_from_right.
Qed.

(*
Arrow families form a setoid under pointwise ≈ at every arrow, exactly
   as transformations form one under pointwise ≈ at every object
   ([Transform_Setoid]).  The correspondence below is an equivalence of
   these two setoids, not merely a bijection of their carriers.

--------
箭族在每个箭头处按逐点≈形成一个集合族，就像变换在每个对象处按逐点≈形成一个集合族一样（[Transform_Setoid]）。下面的对应关系是这两个集合族的等价，而不仅仅是它们载体的一一对应。
*)

#[export]
Program Instance ArrowTransform_Setoid : Setoid ArrowTransform := {|
  equiv := fun A B => ∀ (c c' : C) (f : c ~> c'), τ_arr A f ≈ τ_arr B f
|}.
Next Obligation.
  constructor.
  - intros A c c' f.
    reflexivity.
  - intros A B H c c' f.
    symmetry.
    apply H.
  - intros A B E H1 H2 c c' f.
    transitivity (τ_arr B f).
    + apply H1.
    + apply H2.
Qed.

(*
From a transformation to its arrow family: transport along S, then
   transform.  Both laws are then instances of naturality and
   functoriality.

--------
从一个变换到它的箭头族：沿着 S 传送，然后进行变换。两个规律随后都是自然性和函子性的实例。
*)

Program Definition Transform_to_Arrows (N : S ⟹ T) : ArrowTransform := {|
  τ_arr := fun c c' f => transform[N] c' ∘ fmap[S] f
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  now rewrite <- fmap_comp.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

(*
The other formula for the same family: transform, then transport along
   T.  That the two agree IS the naturality square of N — the proof is
   [naturality] alone — and it is the observation the exercise turns on.

--------
同一族的另一个公式：先变换，然后沿 T 运输。二者一致就是 N 的自然性方格——证明仅靠 [naturality]——这正是练习所依据的观察。
*)

Lemma Transform_to_Arrows_alt (N : S ⟹ T) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows N) f ≈ fmap[T] f ∘ transform[N] c.
Proof.
  simpl.
  symmetry.
  apply naturality.
Qed.

(*
From an arrow family back to a transformation: the components are the
   values at the identities, and the naturality square is
   [τ_arr_diagonal_naturality].  [Build_Transform'] supplies the symmetric
   orientation, so nothing further is proved here.

--------
从一个箭头族回到一个变换：组成部分是在恒等上的值，自然性方形是 [τ_arr_diagonal_naturality]。[Build_Transform'] 提供了对称的方向，因此这里没有进一步的证明。
*)

Definition Arrows_to_Transform (A : ArrowTransform) : S ⟹ T :=
  Build_Transform' (fun c => τ_arr A (id[c]))
                   (fun c c' f => τ_arr_diagonal_naturality A f).

(* Both composites are the identity up to ≈. / 两个复合都是恒等映射，直到 ≈。 *)

Theorem Transform_to_Arrows_to_Transform (N : S ⟹ T) :
  Arrows_to_Transform (Transform_to_Arrows N) ≈ N.
Proof.
  intros c.
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Arrows_to_Transform_to_Arrows (A : ArrowTransform) :
  Transform_to_Arrows (Arrows_to_Transform A) ≈ A.
Proof.
  intros c c' f.
  simpl.
  now rewrite <- τ_arr_from_right.
Qed.

(* Both directions respect the two setoids. / 两个方向都尊重这两个集合拓扑。 *)

#[export]
Instance Transform_to_Arrows_respects :
  Proper (equiv ==> equiv) Transform_to_Arrows.
Proof.
  intros N M H c c' f.
  simpl.
  now rewrite (H c').
Qed.

#[export]
Instance Arrows_to_Transform_respects :
  Proper (equiv ==> equiv) Arrows_to_Transform.
Proof.
  intros A B H c.
  simpl.
  apply H.
Qed.

(*
Uniqueness, in the four forms one wants of it.

   [Transform_determined_by_arrows]: a natural transformation is determined
   by its arrow family, so the assignment is injective up to ≈.
   [Arrows_determined_by_transform]: an arrow family is determined by the
   transformation it induces, i.e. by its diagonal.
   [Arrows_unique_transform]: the transformation inducing a given family is
   unique — with [Arrows_to_Transform_to_Arrows] for existence, this is
   Mac Lane's "arises from a unique natural transformation".
   [Transform_unique_arrows]: and the family induced by a transformation is
   unique.

   These four are COROLLARIES, not four independent facts: each follows
   mechanically from the two round trips together with the two
   respectfulness instances, as an audit of the first commit verified by
   re-deriving all of them.  They are stated separately because each is
   the form some downstream argument will want, and because
   [Arrows_unique_transform] is literally the uniqueness clause of Mac
   Lane's exercise.

--------
独特性，以人们所希望的四种形式存在。

[Transform_determined_by_arrows]：一个自然变换由它的箭头族决定，因此该赋值在≈下是单射的。
[Arrows_determined_by_transform]：一个箭头族由它所引起的变换决定，即由它的对角线决定。
[Arrows_unique_transform]：引起给定箭头族的变换是唯一的——结合[Arrows_to_Transform_to_Arrows]的存在性，这是Mac Lane所说的“由唯一的自然变换产生”。
[Transform_unique_arrows]：并且由一个变换引起的箭头族是唯一的。

这四个是推论，而不是四个独立的事实：每一个都是从两次往返加上两次尊重实例机械推导出来的，就像对第一次提交的审计通过重新推导它们所有内容所验证的一样。它们被分别列出是因为每一个都是某些下游论证所需要的形式，并且因为 [Arrows_unique_transform] 实际上就是 Mac Lane 练习中的唯一性条款。
*)

Theorem Transform_determined_by_arrows (N M : S ⟹ T) :
  Transform_to_Arrows N ≈ Transform_to_Arrows M → N ≈ M.
Proof.
  intros H c.
  pose proof (H c c (id[c])) as Hc.
  simpl in Hc.
  rewrite !fmap_id in Hc.
  now rewrite !id_right in Hc.
Qed.

Theorem Arrows_determined_by_transform (A B : ArrowTransform) :
  Arrows_to_Transform A ≈ Arrows_to_Transform B → A ≈ B.
Proof.
  intros H c c' f.
  simpl in H.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left B f).
  now rewrite (H c).
Qed.

Theorem Arrows_unique_transform (A : ArrowTransform) (N : S ⟹ T) :
  Transform_to_Arrows N ≈ A → N ≈ Arrows_to_Transform A.
Proof.
  intros H c.
  simpl.
  rewrite <- (H c c (id[c])).
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Transform_unique_arrows (N : S ⟹ T) (A : ArrowTransform) :
  Arrows_to_Transform A ≈ N → A ≈ Transform_to_Arrows N.
Proof.
  intros H c c' f.
  simpl.
  rewrite (τ_arr_from_right A f).
  now rewrite (H c').
Qed.

(*
The correspondence as an isomorphism of setoids in Sets, in the manner
   of [classifier_classifies] (Structure/SubobjectClassifier.v): the
   underlying maps are the two directions above, and the two round trips
   are the two theorems above.

--------
作为集合中的集合同构的对应关系，方式如 [classifier_classifies]（Structure/SubobjectClassifier.v）：底层映射是上述两个方向，而两个往返是上述两个定理。
*)

Theorem Transform_Arrows_iso :
  @Isomorphism Sets {| carrier := S ⟹ T |} {| carrier := ArrowTransform |}.
Proof.
  unshelve econstructor.
  - (*
to: a transformation to its arrow family; the setoid-map obligation
       is discharged by [Transform_to_Arrows_respects]

--------
到：变换为它的箭头族；集合映射义务由 [Transform_to_Arrows_respects] 解除
*)
    simpl.
    unshelve refine {| morphism := Transform_to_Arrows |}.
  - (* from: an arrow family to the transformation on the identities / 从：一个箭头家族到恒等的变换 *)
    simpl.
    unshelve refine {| morphism := Arrows_to_Transform |}.
  - (* to ∘ from ≈ id, pointwise / 到 ∘ 从 ≈ 恒等映射，逐点 *)
    intros A.
    apply Arrows_to_Transform_to_Arrows.
  - (* from ∘ to ≈ id, pointwise / 从 ∘ 到 ≈ id，逐点 *)
    intros N.
    apply Transform_to_Arrows_to_Transform.
Defined.

End ArrowTransform.

Arguments ArrowTransform {C D} S T.

(*
The identity transformation's arrow family is the functorial action of
   the functor itself: a functor is its own arrow family, which is the
   arrows-only counterpart of the identity arrows standing in for the
   objects.  This also witnesses that [ArrowTransform] is inhabited for
   every endo-pair (F, F).

--------
恒等变换的箭头族是函子本身的函子作用：一个函子是它自己的箭头族，这对应于用于对象的恒等箭头的仅箭头对应物。这也证明了对于每个自我对 (F, F)，[ArrowTransform] 都是有定义的。
*)

Lemma Transform_to_Arrows_nat_id `(F : C ⟶ D) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (@nat_id C D F)) f ≈ fmap[F] f.
Proof.
  simpl.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(*
Non-triviality in general: distinct transformations have distinct arrow
   families.  This is [Transform_determined_by_arrows] contraposed, and a
   concrete pair of witnesses appears below.

--------
一般的非平凡性：不同的变换具有不同的箭头族。这是 [Transform_determined_by_arrows] 的逆否命题，下面给出了一个具体的证据对。
*)

Corollary distinct_Transforms_distinct_Arrows {C D : Category}
      {S T : C ⟶ D} (N M : S ⟹ T) :
  ¬ (N ≈ M) → ¬ (Transform_to_Arrows N ≈ Transform_to_Arrows M).
Proof.
  intros H HA.
  apply H.
  now apply Transform_determined_by_arrows.
Qed.

(*
The remaining sections need two concrete small categories and the
   constant functors between them; the requires are placed here to keep
   the development above free of them.

--------
剩下的部分需要两个具体的小范畴以及它们之间的恒等函子；将这些要求放在这里，是为了让上面的发展不受它们的影响。
*)

Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Parallel.

(*
The functorial action of a constant functor is an identity; every
   computation in the two sections below reduces through this lemma.

--------
常数函子的函子作用是恒等的；下面两节中的每一个计算都通过这个引理进行归约。
*)

Lemma diagonal_fmap {C J : Category} (x : C) {c c' : J} (f : c ~> c') :
  fmap[Δ[J](x)] f ≈ id[x].
Proof. reflexivity. Qed.

(*
Parallel (Instance/Parallel.v) has exactly two arrows ParX ~> ParY, and
   they are not equivalent: its hom-setoid compares the boolean tags that
   index the arrows.  The two objects are named again at the type
   [Parallel] so that the ambient category is available to inference in
   every statement below.

--------
Parallel (Instance/Parallel.v) 恰好有两个箭头 ParX ~> ParY，并且它们不等价：它的同态集合通过比较标记箭头的布尔标签。 这两个对象再次在类型 [Parallel] 中命名，以便在下面的每个语句中都可以用于推断的环境范畴。
*)

Definition parX : Parallel := ParX.
Definition parY : Parallel := ParY.

Definition par_one : parX ~> parY := (true; ParOne).
Definition par_two : parX ~> parY := (false; ParTwo).

Lemma par_one_par_two_distinct : ¬ (par_one ≈ par_two).
Proof.
  intros H.
  unfold par_one, par_two in H.
  simpl in H.
  discriminate.
Qed.

(*
The two constant functors 2 ⟶ Parallel that carry every example and
   every countermodel below: one sending all of 2 to parX, the other
   sending all of 2 to parY.  Their functorial actions are identities, by
   [diagonal_fmap].

--------
将每个例子和每个反模型都携带到下面的两个恒定函子 2 ⟶ Parallel：一个将 2 的所有元素发送到 parX，另一个将 2 的所有元素发送到 parY。它们的函子作用是恒等的，由 [diagonal_fmap]。
*)

Local Notation ConstX := (Δ[_2](parX)).
Local Notation ConstY := (Δ[_2](parY)).

Section ConcreteArrows.

(*
A concrete non-identity example: the constant arrow family at
   h : parX ~> parY, taken between ConstX and ConstY.  Both splice laws
   hold because both functorial actions are identities.  Nothing here is
   an identity transformation — the source and target functors differ —
   and the record is thereby shown non-vacuous over a pair of distinct
   functors as well as over the pairs (F, F) covered by
   [Transform_to_Arrows_nat_id].

--------
一个具体的非同一例子：在 h : parX ~> parY 的常量箭头族，取在 ConstX 和 ConstY 之间。两个拼接律都成立，因为两个函子作用都是恒等的。这里没有任何是恒等变换——源函子和目标函子不同——因此该记录显示在一对不同的函子上是非空的，同时也适用于由 [Transform_to_Arrows_nat_id] 涵盖的 (F, F) 对。
*)

Definition const_arrows (h : parX ~> parY) : ArrowTransform ConstX ConstY.
Proof.
  unshelve refine
    (@Build_ArrowTransform _2 Parallel ConstX ConstY (fun c c' f => h) _ _).
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_left.
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_right.
Defined.

(*
The correspondence computes on it: the induced transformation has h at
   every component (by conversion alone), and the family recovered from
   that transformation is again the constant family.

--------
对应在其上进行计算：诱导的变换在每个分量上都有 h（仅通过转换），从该变换恢复的族再次是常数族。
*)

Lemma const_arrows_transform (h : parX ~> parY) (c : _2) :
  transform[Arrows_to_Transform (const_arrows h)] c ≈ h.
Proof. reflexivity. Qed.

Lemma const_arrows_roundtrip (h : parX ~> parY) {c c' : _2} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (Arrows_to_Transform (const_arrows h))) f ≈ h.
Proof.
  rewrite (Arrows_to_Transform_to_Arrows (const_arrows h) c c' f).
  reflexivity.
Qed.

(*
Non-triviality, concretely: the two constant families at the two arrows
   of Parallel are distinct, hence so are the transformations they induce
   — the latter by [Arrows_determined_by_transform], i.e. through the
   round trip rather than by inspection.

--------
非平凡性，具体来说：平行的两个箭头上的两个常量族是不同的，因此它们引起的变换也是不同的——后者通过 [Arrows_determined_by_transform]，即通过往返而不是通过检查。
*)

Lemma const_arrows_distinct :
  ¬ (const_arrows par_one ≈ const_arrows par_two).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  exact (H TwoX TwoY TwoXY).
Qed.

Lemma const_transforms_distinct :
  ¬ (Arrows_to_Transform (const_arrows par_one)
       ≈ Arrows_to_Transform (const_arrows par_two)).
Proof.
  intros H.
  apply const_arrows_distinct.
  now apply Arrows_determined_by_transform.
Qed.

End ConcreteArrows.

Section Independence.

(*
The two splice laws are independent: neither follows from the other,
   with or without respectfulness.  Both countermodels live over the same
   pair of constant functors ConstX, ConstY : 2 ⟶ Parallel, where both
   functorial actions are identities, so that the left law reads
   τ f ≈ τ (g ∘ f) and the right law reads τ (g ∘ f) ≈ τ g.  The first
   constrains the family only along the domain of its argument, the second
   only along the codomain, and in the walking arrow 2 the two come apart
   at the non-identity arrow TwoXY : TwoX ~> TwoY.

--------
这两个拼接定律是独立的：一个都不能从另一个推导出来，无论是否考虑尊重性。两个反例模型都基于同一对常量函子 ConstX、ConstY : 2 ⟶ Parallel，其中两个函子作用都是恒等的，因此左边的定律可以写作 τ f ≈ τ (g ∘ f)，右边的定律可以写作 τ (g ∘ f) ≈ τ g。第一个定律仅在其参数的定义域上约束函数族，第二个定律仅在其余域上约束，而在“行箭”(walking arrow) 2 中，这两者在非恒等箭头 TwoXY : TwoX ~> TwoY 上发生分离。
*)

(*
A LIMITATION of these two countermodels, disclosed because an audit of
   the first commit called it out: their respectfulness lemmas below hold
   for a reason that has nothing to do with the families.  The hom-setoid
   of the walking arrow is Leibniz equality (Instance/Two.v's
   Morphism_equality), so EVERY function out of one of its hom-types
   respects `≈` automatically.  The two lemmas therefore establish that
   independence survives the presence of a respectfulness field, which is
   what they are for, but they are not evidence that these particular
   families are well behaved.  The closing section of this file supplies
   countermodels over a hom-setoid that genuinely quotients, where
   respectfulness is a real constraint.

--------
这两个反例的一个限制，被发现是因为对第一个提交的审计指出了它们：下面的尊重性引理成立的原因与这些族无关。行箭的同构集道（hom-setoid）是莱布尼茨等式（Instance/Two.v 中的 Morphism_equality），所以从它的某个同构类型出的每一个函数都自动满足 `≈`。因此，这两个引理确立了独立性在存在尊重性字段时仍然保持，这正是它们的用途，但它们并不能证明这些特定的族是良好行为的。本文件的最后部分提供了一个真正进行商化的同构集道上的反例，其中尊重性是一个真实的约束。
*)

Definition dom_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c with
  | TwoX => par_one
  | TwoY => par_two
  end.

Definition cod_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c' with
  | TwoX => par_one
  | TwoY => par_two
  end.

(* Both families respect ≈, ignoring their argument outright. / 两家都尊重≈，完全忽视他们的争论。 *)

Lemma dom_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@dom_family c c').
Proof. intros f g Hf; reflexivity. Qed.

Lemma cod_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@cod_family c c').
Proof. intros f g Hf; reflexivity. Qed.

(* Reading the domain satisfies the left law and refutes the right one. / 读取域满足左边定律并否定右边定律。 *)

Lemma dom_family_left {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  fmap[ConstY] g ∘ dom_family f ≈ dom_family (g ∘ f).
Proof. now rewrite diagonal_fmap, id_left. Qed.

Lemma dom_family_not_right :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       dom_family (g ∘ f) ≈ dom_family g ∘ fmap[ConstX] f).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_right par_two).
  exact (H TwoX TwoY TwoY (@id _2 TwoY) TwoXY).
Qed.

(* Reading the codomain satisfies the right law and refutes the left one. / 读取陪域满足右律并否定左律。 *)

Lemma cod_family_right {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  cod_family (g ∘ f) ≈ cod_family g ∘ fmap[ConstX] f.
Proof. now rewrite diagonal_fmap, id_right. Qed.

Lemma cod_family_not_left :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       fmap[ConstY] g ∘ cod_family f ≈ cod_family (g ∘ f)).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_left par_one).
  exact (H TwoX TwoX TwoY TwoXY (@id _2 TwoX)).
Qed.

End Independence.

(* ------------------------------------------------------------------------ *)
(** ** Neither law alone implies respectfulness / ** 仅靠法律并不意味着尊重 *)

(*
[τ_arr_respects] above derives respectfulness of the family from the two
   splice laws TOGETHER, and the derivation visibly uses both: each law
   supplies one leg of the detour through the padded term `f ∘ id`.  That
   left open whether one law alone might already suffice by some other
   route.  It does not, in either direction, and this section settles it
   with countermodels.  (The first commit of this file left the question
   open; an audit resolved it and the argument is integrated here.)

   The question cannot even be POSED over the walking arrow used above,
   because its hom-setoid is Leibniz equality and respectfulness there is
   free.  What is needed is a base category whose hom-setoid genuinely
   quotients — two arrows that Rocq can tell apart but that the setoid
   identifies.  The blur categories below are the minimal such thing: one
   object, two arrows, ALL arrows equivalent.  Their composition is chosen
   degenerate in the two possible ways, which is exactly what makes one
   splice law hold trivially while respectfulness collapses.

--------
上文的 [τ_arr_respects] 从两个拼接定律一起推导出家庭的尊重性，并且推导明显使用了两者：每个定律提供了通过填充项 `f ∘ id` 的绕行之一条路。这仍然没有说明单独一个定律是否可能通过其他途径已经足够。事实上，无论哪个方向都不够，本节用反例解决了这一问题。（此文件的第一次提交时该问题尚未解决；经过审计之后问题得到了解决，并且论证已整合在此处。）

上述使用的步行箭头甚至无法提出这个问题，因为它的同态集合是莱布尼茨等式，并且在那里保持性是免费的。所需要的是一个基范畴，其同态集合真正进行商化——两个 Rocq 能区分的箭头，但集合同态会将它们认同。下面的模糊范畴是最小的这种情况：一个对象，两个箭头，所有箭头都等价。它们的组合在两种可能的方式中被选择为退化的，这正是使一个拼接法则平凡成立而保持性崩溃的原因。
*)

Program Definition BlurRight : Category := {|
  obj     := unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ g f => f          (* right-zero: the composite is f / 右零：复合是 f *)
|}.

Program Definition BlurLeft : Category := {|
  obj     := unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ g f => g          (* left-zero: the composite is g / 左零：复合是 g *)
|}.

(*
The separating pair is the same one the independence countermodels use:
   the two distinct arrows ParX ~> ParY of the parallel-pair category.

--------
分离对正是独立性反例所使用的那一个：平行对范畴中的两个不同箭头 ParX ~> ParY。
*)
Lemma par_one_two_distinct : ¬ (par_one ≈ par_two).
Proof. intros H; unfold par_one, par_two in H; simpl in H; discriminate. Qed.

Section LeftLawAlone.

Notation SR := (Δ[BlurRight](parX)).
Notation TR := (Δ[BlurRight](parY)).

Definition blur_right_family {c c' : BlurRight} (f : c ~> c') : SR c ~> TR c' :=
  if f then par_one else par_two.

(*
It satisfies the LEFT splice law in full generality: with right-zero
   composition the law reads τ f ≈ τ f.

--------
它在完全一般性下满足左拼接律：对于右零组合，该律写作 τ f ≈ τ f。
*)
Lemma blur_right_left {c c' c'' : BlurRight} (g : c' ~> c'') (f : c ~> c') :
  fmap[TR] g ∘ blur_right_family f ≈ blur_right_family (g ∘ f).
Proof. apply id_left. Qed.

(*
Yet it is not respectful: the two arrows are `≈` and their images are
   not.  So the LEFT law alone does not imply respectfulness.

--------
然而，这并不表示尊重：两个箭头是 `≈`，而它们的图像不是。因此，仅左侧的法律并不意味着尊重。
*)
Theorem left_law_alone_gives_no_respect :
  ¬ (∀ c c' : BlurRight, Proper (equiv ==> equiv) (@blur_right_family c c')).
Proof.
  intros H.
  apply par_one_two_distinct.
  exact (H tt tt true false I).
Qed.

End LeftLawAlone.

Section RightLawAlone.

Notation SL := (Δ[BlurLeft](parX)).
Notation TL := (Δ[BlurLeft](parY)).

Definition blur_left_family {c c' : BlurLeft} (f : c ~> c') : SL c ~> TL c' :=
  if f then par_one else par_two.

(*
The mirror image: with left-zero composition the RIGHT law reads
   τ g ≈ τ g.

--------
镜像：在左零组合下，右侧定律表述为
   τ g ≈ τ g。
*)
Lemma blur_left_right {c c' c'' : BlurLeft} (g : c' ~> c'') (f : c ~> c') :
  blur_left_family (g ∘ f) ≈ blur_left_family g ∘ fmap[SL] f.
Proof. symmetry; apply id_right. Qed.

Theorem right_law_alone_gives_no_respect :
  ¬ (∀ c c' : BlurLeft, Proper (equiv ==> equiv) (@blur_left_family c c')).
Proof.
  intros H.
  apply par_one_two_distinct.
  exact (H tt tt true false I).
Qed.

End RightLawAlone.

(*
The countermodels are non-degenerate in the way that matters: the two
   arrows really are identified by the setoid, and really are distinguished
   by the family.

--------
反例在重要的方面是非退化的：这两个箭头确实被集合类型识别，并且确实被族区分。
*)
Example blur_arrows_equivalent :
  (true : @hom BlurRight tt tt) ≈ (false : @hom BlurRight tt tt).
Proof. exact I. Qed.

Example blur_family_separates :
  blur_right_family (c:=tt) (c':=tt) true
    <> blur_right_family (c:=tt) (c':=tt) false.
Proof. simpl; unfold par_one, par_two; discriminate. Qed.
