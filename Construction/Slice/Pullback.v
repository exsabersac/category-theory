Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   * Functors between slice categories induced by a base morphism. 

   --------
   * 由基态态射引起的切片范畴之间的函子。
*)

(*
 nLab: https://ncatlab.org/nlab/show/base+change
 nLab: https://ncatlab.org/nlab/show/dependent+sum
 nLab: https://ncatlab.org/nlab/show/over+category
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., Springer GTM 5, 1998, SS IV.5, printed p. 97,
 Exercise 3 (catalog id maclane:IV.5:ex3)

 Mac Lane's Exercise 3 reads, verbatim from the printed page:

 “For C a category with pullbacks, each arrow f : a→a' defines a
 functor (C↓f) = f_*: (C↓a)→(C↓a') which carries each object
 x→a of (C↓a) to the composite x→a→a'.  Show that f_* has a
 right adjoint f* with f*(x'→a') = y→a, where y is the vertex
 of the pullback of a→a'←x'.”

 A NOTE ON HIS NOTATION, since it collides with this file's.  He
 writes f_* for POST-COMPOSITION, where this file and the nLab
 write f_! or Σ_f -- that is [Bang_Functor] below -- while his f*
 is this file's [Star_Functor].  So his displayed conclusion, that
 f_* has a right adjoint f*, IS [Base_Functor_Adjunction] with the
 names translated, and his “y is the vertex of the pullback” is
 [Pull].

 A morphism f : a ~> b in C induces two functors between the slice
 categories C ̸ a and C ̸ b:

 - Bang_Functor f : C ̸ a ⟶ C ̸ b is the dependent sum Σ_f (also
 written f_!, “lower shriek”), defined by post-composition with f:
 it sends an object (o; h) with h : o ~> a to (o; f ∘ h), an object
 over b.  This needs no extra structure on C.

 - Star_Functor f : C ̸ a ⟶ C ̸ c is the base change (pullback)
 functor f*, defined by pulling back along f: given f : c ~> a, it
 sends an object (o; h) with h : o ~> a to (Pull h f;
 pullback_snd h f), the fiber product o ×_a c equipped with its
 projection to c.  This requires that the relevant pullbacks exist
 in C, which is assumed below as the Hypothesis [pullbacks].

 The theorem of this file is that the two are adjoint, dependent sum
 on the LEFT and base change on the RIGHT: for a single f : a ~> b,
 [Base_Functor_Adjunction] inhabits

 Bang_Functor f ⊣ Star_Functor f,   i.e.   Σ_f ⊣ f*

 with the class of Theory/Adjunction.v, so the left adjoint is the
 functor C ̸ a ⟶ C ̸ b and the right adjoint is the functor
 C ̸ b ⟶ C ̸ a obtained by instantiating [Star_Functor] at the same
 f (its declared shape `(f : c ~> a) : C ̸ a ⟶ C ̸ c reads, at our
 f : a ~> b, as C ̸ b ⟶ C ̸ a).  The orientation matters, and the
 opposite reading Star_Functor f ⊣ Bang_Functor f -- which an earlier
 commented sketch in this file proposed -- is NOT ill formed: both
 functors have the shapes the class wants once the roles are swapped,
 so it is a well typed statement that is simply not true in general.
 Test/ProbeBaseChange387.v measures both halves of that: it records
 the reversed statement as formable, and [reversed_orientation_refuted]
 there compiles a counterexample over Sets along the unique morphism
 ∅ ~> 1, where the unit such an adjunction would supply is a map from
 the singleton into a setoid with uninhabited carrier -- the pullback
 object, whose carrier is a sub-setoid of 1 × ∅.

 The hom-set bijection is the universal property of the chosen
 pullback, read twice.  For x = (o; h) over a and y = (p; k) over b, a
 slice morphism Σ_f x ~> y is a C-morphism g : o ~> p with
 k ∘ g ≈ f ∘ h, and that equation is precisely the square condition of
 the competing cone ⟨g, h⟩ over the pullback square of k along f; the
 mediator it produces is the transposed morphism x ~> f* y, its
 [pullback_snd] leg equation being the slice condition over a.
 Conversely a morphism into the pullback is turned back by
 post-composing with [pullback_fst].  Because the slice hom-setoid of
 Construction/Slice.v compares only the underlying C-morphism, both
 round trips, both respectfulness obligations and both naturality
 clauses are equations in C alone, and each is one appeal to the
 uniqueness half of the universal property.

 Unit and counit are named.  [bang_star_unit] at (o; h) is the
 comparison of o into the pullback of f ∘ h along f -- the mediator of
 the cone ⟨id, h⟩, whose square condition is (f ∘ h) ∘ id ≈ f ∘ h.
 [bang_star_counit] at (p; k) is the pullback projection
 [pullback_fst k f], whose slice condition k ∘ fst ≈ f ∘ snd IS
 [pullback_commutes] verbatim, with no proof of its own.  Read their
 identification with the class's η and ε at the strength measured, not
 the one hoped for: the class's counit IS this projection composed
 with a residual [id], on the nose ([bang_star_counit_strict]), and
 the class's unit IS [base_to_mor] of the slice identity, on the nose
 ([bang_star_unit_strict]), while against [bang_star_unit_mor] and
 [bang_star_counit_mor] themselves only ≈ holds.  On the unit side
 that is not the residual [id] but the PROOF argument: both sides are
 mediators of the same cone ⟨id, h⟩, and [ump_pullbacks] takes the
 square condition as an argument on which the mediator depends, so
 feeding it the slice identity's own witness and feeding it
 [id_right (f ∘ h)] give two mediators related by [uniqueness] and not
 by conversion.

 What is NOT built here.  When C is locally cartesian closed, f*
 itself has a further right adjoint Π_f (the dependent product),
 giving the string Σ_f ⊣ f* ⊣ Π_f.  Π_f is not constructed, and the
 reason is measured rather than guessed: no class of local cartesian
 closure is declared anywhere in this tree (the phrase occurs only in
 prose, in Structure/Pullback.v, Construction/Slice.v and
 Instance/Sets.v), and Structure/Cartesian/Closed.v's [Closed] is a
 structure on C over a [Cartesian C], while no [Cartesian] instance
 for a slice category is declared either -- so the dependent product
 would have to be built from scratch.  That is left for a later
 effort, and nothing below depends on it.  Also not delivered: no
 Beck-Chevalley condition, no comparison of this adjunction with the
 codomain fibration of Construction/Displayed/Codomain.v, no
 monad or comonad from the adjunction, and no statement about when the
 unit or counit is an isomorphism. 

 --------
 nLab:  https://ncatlab.org/nlab/show/base+change 
 nLab:  https://ncatlab.org/nlab/show/dependent+sum 
 nLab:  https://ncatlab.org/nlab/show/over+category 
 维基百科:  https://en.wikipedia.org/wiki/Pullback_(category_theory) 
 书籍:      Mac Lane, 《为工作数学家准备的范畴论》,  
 第二版, Springer GTM 5, 1998, 第 IV.5 节, 印刷页 97, 
 练习 3 (目录编号 maclane:IV.5:ex3)

 Mac Lane 的练习 3 原文如下（逐字从印刷页）：

 “对于具有拉回的范畴 C，每个箭头 f : a→a' 定义了一个函子
 (C↓f) = f_*: (C↓a)→(C↓a')，将 (C↓a) 中的每个对象
 x→a 映射为复合箭头 x→a→a'。证明 f_* 具有右伴随函子 f*，
 其中 f*(x'→a') = y→a，y 是 a→a'←x' 的拉回顶点。”关于他的符号的说明，由于它与本文件的符号冲突。他用 f_* 表示后合成（POST-COMPOSITION），而本文件和 nLab 则写作 f_! 或 Σ_f——也就是下文的 [Bang_Functor]——而他的 f* 对应本文件的 [Star_Functor]。因此，他展示的结论，即 f_* 有右伴随 f*，用翻译后的名称是 [Base_Functor_Adjunction]，他所说的“y 是拉回的顶点”是 [Pull]。

 在范畴 C 中的一个态射 f : a ~> b 会在切范畴 C ̸ a 和 C ̸ b 之间诱导出两个函子：

 - Bang_Functor f : C ̸ a ⟶ C ̸ b 是依赖和 Σ_f（也写作 f_! ，即“下感叹号”），通过与 f 的后合成定义：它将一个对象 (o; h)，其中 h : o ~> a，映射为 (o; f ∘ h)，一个位于 b 上的对象。这个过程不需要 C 具有额外的结构。- Star_Functor f : C ̸ a ⟶ C ̸ c 是基变（拉回）函子 f*，通过沿 f 拉回来定义：给定 f : c ~> a，它将一个对象 (o; h) 与 h : o ~> a 映射为 (Pull h f; pullback_snd h f)，即带有投影到 c 的纤维积 o ×_a c。这要求相关的拉回在 C 中存在，下文假设为假设 [pullbacks]。

 本文件的定理是，两者是伴随的，依赖和在左侧，基变在右侧：对于单个 f : a ~> b，[Base_Functor_Adjunction] 属于

 Bang_Functor f ⊣ Star_Functor f，即 Σ_f ⊣ f*使用 Theory/Adjunction.v 类，所以左伴随是函子 C ̸ a ⟶ C ̸ b，而右伴随是通过在相同的 f 上实例化 [Star_Functor] 得到的函子 C ̸ b ⟶ C ̸ a（其声明的形状 `(f : c ~> a) : C ̸ a ⟶ C ̸ c` 在我们的 f : a ~> b 上读作 C ̸ b ⟶ C ̸ a）。方向很重要，而相反的读法 Star_Functor f ⊣ Bang_Functor f —— 该文件早期注释草图中提出的 —— 并非格式错误：一旦交换角色，这两个函子的形状都符合类的要求，所以这是一条类型正确的语句，只是通常情况下不成立。Test/ProbeBaseChange387.v 测量了两方面：它将反向语句记录为可形成的，并且 [reversed_orientation_refuted] 在集合上沿着唯一态射 ∅ ~> 1 编译了一个反例，其中该伴随提供的单位是从单例映射到具有空载体的集合构的映射——拉回对象，其载体是 1 × ∅ 的子集合构。同态集双射是所选拉回的广义性质，读两次。对于 x = (o; h) 位于 a 之上以及 y = (p; k) 位于 b 之上，一个切片态射 Σ_f x ~> y 是一个 C-态射 g : o ~> p，使得 k ∘ g ≈ f ∘ h，而这个方程恰恰是 k 沿 f 的拉回方格上竞争圆锥 ⟨g, h⟩ 的方格条件；它产生的中介态射是转置态射 x ~> f* y，其 [pullback_snd] 分支方程是 a 上的切片条件。反过来，进入拉回的态射通过后合成 [pullback_fst] 来还原。因为 Construction/Slice.v 的切片同态集只比较底层的 C-态射，所以两次往返、两次尊重性义务以及自然性条款都是仅在 C 中的方程，每一个都是对广义性质惟一性半边的应用。

 单位和余单位被命名。在 (o; h) 处的 [bang_star_unit] 是将 o 映入 f ∘ h 沿 f 的拉回的比较——锥 ⟨id, h⟩ 的中介，其方形条件是 (f ∘ h) ∘ id ≈ f ∘ h。在 (p; k) 处的 [bang_star_counit] 是拉回投影 [pullback_fst k f]，其切片条件 k ∘ fst ≈ f ∘ snd 正是 [pullback_commutes]，完全照搬，无需自证。将它们与类的 η 和 ε 在已测量的强度下的识别进行阅读，而不是希望的那种：类的余单位就是此投影与残留 [id] 的复合，精确无误（[bang_star_counit_strict]）；类的单位正是切片恒等的 [base_to_mor]，精确无误（[bang_star_unit_strict]），而针对 [bang_star_unit_mor] 和 [bang_star_counit_mor] 本身，仅保持 ≈ 成立。在单位的一侧
 那不是残余的 [id]，而是 PROOF 论证：双方都是相同圆锥 ⟨id, h⟩ 的中介，而 [ump_pullbacks] 将平方条件作为中介依赖的参数，因此将切片恒等的自身证明传给它，并将 [id_right (f ∘ h)] 传给它，会得到两个通过 [uniqueness] 相关的中介，而不是通过转换。这里没有构建什么。当 C 是局部笛卡尔封闭时，f* 本身还有一个进一步的右伴随 Π_f（依赖积），形成串 Σ_f ⊣ f* ⊣ Π_f。Π_f 没有被构建，其原因是经过测量而非猜测：在这棵树的任何地方都没有声明局部笛卡尔封闭类（这个短语仅出现在文字描述中，如 Structure/Pullback.v、Construction/Slice.v 和 Instance/Sets.v 中），而 Structure/Cartesian/Closed.v 的 [Closed] 是 C 上的一个结构，而 [Cartesian C] 上没有为切片范畴声明 [Cartesian] 实例——所以依赖积必须从零开始构建。那将留待以后的工作，目前下面的内容不依赖它。也没有实现：没有 Beck-Chevalley 条件，没有将此伴随与 Construction/Displayed/Codomain.v 的余域纤维进行比较，没有从伴随中得到单子或余单子，也没有关于何时单位或余单位为同构的说明。
*)

Section SliceFunctors.

Context `{C : Category}.

#[local] Set Transparent Obligations.

(*
 Dependent sum Σ_f (= f_!): post-compose the structure morphism with f. 

 --------
 依赖和 Σ_f (= f_!): 将结构态射与 f 后合成。
*)
Program Definition Bang_Functor `(f : a ~> b) : @Slice C a ⟶ @Slice C b := {|
  fobj := λ '(o; h), (o; f ∘ h);
  fmap := λ x y f, (_; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  now rewrite X.
Qed.

(*
 Postfix notation for Σ_f, mirroring the standard f_! (“lower shriek”). 

 --------
 Σ_f 的后缀表示法，类似于标准的 f_!（“下惊叹号”）。
*)
Notation "f !" := (Bang_Functor f) (at level 90) : category_scope.

(*
 C has all binary pullbacks; this is what makes base change f* below total. 

 --------
 C 拥有所有二元拉回；这就是使下面的基变换 f* 成为全函数的原因。
*)
Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g.

(*
 Base change f*: pull the structure morphism back along f, taking the
 resulting projection onto c as the new structure morphism over c. 

 --------
 基变换 f*：沿着 f 拉回结构态射，将所得的投影到 c 作为 c 上的新结构态射。
*)
Program Definition Star_Functor `(f : c ~> a) :
  @Slice C a ⟶ @Slice C c := {|
  fobj := λ '(_; h),
            let pull : Pullback h f := pullbacks h f in
            (Pull h f pull; pullback_snd h f pull);
  fmap := λ '(a; x) '(b; y) '(g; H),
            let ypb : Pullback y f := pullbacks y f in
            let xpb : Pullback x f := pullbacks x f in
            let uniq :=
                  ump_pullbacks
                    _ _ ypb _
                    (g ∘ pullback_fst x f xpb)
                    (pullback_snd x f xpb)
                    ltac:(rewrite comp_assoc, H;
                          exact (pullback_commutes x f xpb)) in
            (unique_obj uniq; snd (unique_property uniq))
|}.
Next Obligation.
  proper; simpl in *.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  intuition eauto.
  now rewrites.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  now cat.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  repeat (destruct (ump_pullbacks1 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  split.
  - rewrite comp_assoc.
    rewrite a1.
    now comp_left.
  - rewrite comp_assoc.
    now rewrite b0.
Qed.

(** ** The base change adjunction Σ_f ⊣ f* / ** 基变换伴随 Σ_f ⊣ f* *)

Section BaseChange.

Context `(f : a ~> b).

(*
 The universal property of the chosen pullback of k along f, read at
 the competing cone that a slice morphism Σ_f (o; h) ~> (p; k)
 supplies: its two legs are the morphism itself and h, and the square
 condition IS that morphism's slice condition. 

 --------
 沿 f 选取的 k 的拉回的普遍性质，在竞争锥 Σ_f (o; h) ~> (p; k) 提供的情况下读取：它的两个边是该态射本身和 h，并且该方形条件就是该态射的切片条件。
*)
Definition base_ump {o p : C} (h : o ~> a) (k : p ~> b)
      (g : o ~> p) (Hg : k ∘ g ≈ f ∘ h) :
  ∃! u : o ~> Pull k f (pullbacks k f),
      pullback_fst k f (pullbacks k f) ∘ u ≈ g ∧
      pullback_snd k f (pullbacks k f) ∘ u ≈ h :=
  ump_pullbacks k f (pullbacks k f) o g h Hg.

(*
 The arrow action of f* is itself a pullback mediator; its underlying
 C-morphism is named here so that its two leg equations can be stated
 with the pullback objects already in reduced form. 

 --------
 f* 的箭头作用本身就是一个拉回调解器；其底层的 C-态射在此被命名，以便可以使用已经简化形式的拉回对象来表述其两个支腿方程。
*)
Definition star_fmap_mor {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  Pull k1 f (pullbacks k1 f) ~> Pull k2 f (pullbacks k2 f) :=
  `1 (fmap[Star_Functor f] g).

Lemma star_fmap_fst {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_fst k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ `1 g ∘ pullback_fst k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (fst (unique_property U))
  end.
Qed.

Lemma star_fmap_snd {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_snd k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ pullback_snd k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (snd (unique_property U))
  end.
Qed.

(* The forward transpose, on underlying C-morphisms. / 在基础 C-态射上的前向转置。 *)
Definition base_to_mor {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  o ~> Pull k f (pullbacks k f) :=
  unique_obj (base_ump h k (`1 g) (`2 g)).

Lemma base_to_fst {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_fst k f (pullbacks k f) ∘ base_to_mor g ≈ `1 g.
Proof. exact (fst (unique_property (base_ump h k (`1 g) (`2 g)))). Qed.

Lemma base_to_snd {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_snd k f (pullbacks k f) ∘ base_to_mor g ≈ h.
Proof. exact (snd (unique_property (base_ump h k (`1 g) (`2 g)))). Defined.

(*
 Every competitor satisfying the two leg equations IS the transpose.
 This single lemma discharges respectfulness, one round trip and both
 naturality clauses. 

 --------
 每一个满足两条腿方程的竞争者都是转置。
 这个单一引理消除了尊重性、一轮往返以及两个自然性条款。
*)
Lemma base_to_mor_unique {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k))
      (u : o ~> Pull k f (pullbacks k f)) :
  pullback_fst k f (pullbacks k f) ∘ u ≈ `1 g →
  pullback_snd k f (pullbacks k f) ∘ u ≈ h →
  base_to_mor g ≈ u.
Proof.
  intros H1 H2.
  exact (uniqueness (base_ump h k (`1 g) (`2 g)) u (H1, H2)).
Qed.

Definition base_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  (o; h) ~{@Slice C a}~> Star_Functor f (p; k) :=
  (base_to_mor g; base_to_snd g).

(*
 The backward transpose: post-compose with the pullback projection.
 Its slice condition over b is [pullback_commutes] followed by the
 argument's own slice condition over a. 

 --------
 向后转置：与拉回投影后组合。它在 b 上的切片条件是 [pullback_commutes]，随后是参数自身在 a 上的切片条件。
*)
Lemma base_from_ok {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  k ∘ (pullback_fst k f (pullbacks k f) ∘ `1 u) ≈ f ∘ h.
Proof.
  pose proof (`2 u) as Hu; simpl in Hu.
  rewrite comp_assoc.
  rewrite (pullback_commutes k f (pullbacks k f)).
  rewrite <- comp_assoc.
  now rewrite Hu.
Defined.

Definition base_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  (o; f ∘ h) ~{@Slice C b}~> (p; k) :=
  (pullback_fst k f (pullbacks k f) ∘ `1 u; base_from_ok u).

Lemma base_to_respects {o p : C} {h : o ~> a} {k : p ~> b}
      (g1 g2 : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 g1 ≈ `1 g2 → base_to_mor g1 ≈ base_to_mor g2.
Proof.
  intro Hg.
  apply base_to_mor_unique.
  - rewrite base_to_fst.
    now symmetry.
  - apply base_to_snd.
Qed.

(*
 Round trip: the transpose of a morphism into the pullback recovers
 it, by uniqueness of the mediator. 

 --------
 往返：将一个态射转置到拉回中会恢复它，这是通过中介的唯一性实现的。
*)
Lemma base_to_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  base_to_mor (base_from u) ≈ `1 u.
Proof.
  apply base_to_mor_unique.
  - reflexivity.
  - exact (`2 u).
Qed.

(*
 The other round trip is the FIRST leg equation of the mediator, with
 no further argument. 

 --------
 另一个往返是调解者的第一段方程，没有进一步的论证。
*)
Lemma base_from_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 (base_from (base_to g)) ≈ `1 g.
Proof. exact (base_to_fst g). Qed.

Program Definition base_adj_to (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    ~{Sets}~>
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  morphism := @base_to o p h k
|}.
Next Obligation. proper; now apply base_to_respects. Qed.

Program Definition base_adj_from (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |}
    ~{Sets}~>
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |} := {|
  morphism := @base_from o p h k
|}.

Program Definition base_adj_at (o p : C) (h : o ~> a) (k : p ~> b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
     ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  to   := base_adj_to o p h k;
  from := base_adj_from o p h k
|}.
Next Obligation. apply base_to_from. Qed.
Next Obligation. apply base_from_to. Qed.

Definition base_adj (x : @Slice C a) (y : @Slice C b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f x ~{@Slice C b}~> y
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f x) y |}
    {| carrier   := x ~{@Slice C a}~> Star_Functor f y
     ; is_setoid := @homset (@Slice C a) x (Star_Functor f y) |}.
Proof.
  destruct x as [o h], y as [p k].
  exact (base_adj_at o p h k).
Defined.

(*
 The two leg equations the [to_adj_nat_r] clause needs, stated at
 arguments whose slice types are already in pullback form, so that the
 rewriting below has the shape it expects. 

 --------
 [to_adj_nat_r] 条款所需的两个腿方程，已在其切片类型已处于拉回形式的参数下说明，以便下面的重写具有其预期的形状。
*)
Lemma base_nat_r_fst {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_fst k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u)
    ≈ `1 g ∘ `1 u.
Proof.
  rewrite comp_assoc, star_fmap_fst, <- comp_assoc, base_to_fst.
  reflexivity.
Qed.

Lemma base_nat_r_snd {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_snd k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u) ≈ h.
Proof.
  rewrite comp_assoc, star_fmap_snd.
  apply base_to_snd.
Qed.

(*
   * The base change adjunction: dependent sum is left adjoint to
   pullback along the same morphism. 

   --------
   * 基础变换伴随性：依赖和是沿相同态射的拉回的左伴随。
*)
Definition Base_Functor_Adjunction : Bang_Functor f ⊣ Star_Functor f.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C b) (@Slice C a)
                     (Bang_Functor f) (Star_Functor f) base_adj).
  - intros [ox hx] [oy hy] [p k] g u; simpl.
    apply base_to_mor_unique.
    + rewrite comp_assoc, base_to_fst.
      reflexivity.
    + rewrite comp_assoc, base_to_snd.
      exact (`2 u).
  - intros [o h] [p1 k1] [p2 k2] g u.
    change (@base_to_mor o p2 h k2 (g ∘ u)
              ≈ star_fmap_mor g ∘ @base_to_mor o p1 h k1 u).
    apply base_to_mor_unique.
    + apply (base_nat_r_fst g u).
    + apply (base_nat_r_snd g u).
Defined.

(** ** Unit and counit / ** 单位和余单位 *)

(*
 The unit at (o; h) is the comparison of o into the pullback of f ∘ h
 along f: the mediator of the cone ⟨id, h⟩, whose square condition is
 (f ∘ h) ∘ id ≈ f ∘ h. 

 --------
 位于 (o; h) 的单位是 o 与沿 f 的 f ∘ h 的拉回的比较：锥 ⟨id, h⟩ 的中介，其方形条件是 (f ∘ h) ∘ id ≈ f ∘ h。
*)
Definition bang_star_unit_mor (o : C) (h : o ~> a) :
  o ~> Pull (f ∘ h) f (pullbacks (f ∘ h) f) :=
  unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))).

Definition bang_star_unit (o : C) (h : o ~> a) :
  (o; h) ~{@Slice C a}~> Star_Functor f (Bang_Functor f (o; h)) :=
  (bang_star_unit_mor o h;
   snd (unique_property (base_ump h (f ∘ h) id (id_right (f ∘ h))))).

(*
 The counit at (p; k) is the pullback projection itself; its slice
 condition k ∘ fst ≈ f ∘ snd IS [pullback_commutes]. 

 --------
 在 (p; k) 处的余单位是拉回投影本身；它的切片条件 k ∘ fst ≈ f ∘ snd 是 [pullback_commutes]。
*)
Definition bang_star_counit_mor (p : C) (k : p ~> b) :
  Pull k f (pullbacks k f) ~> p := pullback_fst k f (pullbacks k f).

Definition bang_star_counit (p : C) (k : p ~> b) :
  Bang_Functor f (Star_Functor f (p; k)) ~{@Slice C b}~> (p; k) :=
  (bang_star_counit_mor p k; pullback_commutes k f (pullbacks k f)).

(* * *** How the named unit and counit relate to the class / * *** 命名的单位和余单位如何与类相关 *)

(*
 The class's unit at (o; h) IS the forward transpose of the identity,
 on the nose. 

 --------
 该类在 (o; h) 的单元正是单位矩阵的前向转置，完全准确。
*)
Example bang_star_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = base_to_mor (id[Bang_Functor f (o; h)]) := eq_refl.

(*
 The residue is exhibited rather than described: both sides are the
 mediator of the cone whose legs are [id] and [h], and they differ in
 nothing but the proof of that cone's square condition. 

 --------
 残余部分是展示出来的，而不是描述的：两边都是锥体的中介，其边分别是 [id] 和 [h]，它们唯一的不同之处只是该锥体平方条件的证明。
*)
Example bang_star_unit_residue (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = unique_obj (base_ump h (f ∘ h) id
                  (`2 (id[Bang_Functor f (o; h)]))) := eq_refl.

Example bang_star_unit_mor_residue (o : C) (h : o ~> a) :
  bang_star_unit_mor o h
  = unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))) := eq_refl.

(*
 Against [bang_star_unit_mor] the identification holds up to ≈ and not
 on the nose: both are mediators of the SAME cone ⟨id, h⟩, but the
 mediator is produced from a proof of the square condition and the two
 sides feed it different proofs -- the slice identity's own commuting
 witness on the class side, [id_right (f ∘ h)] on the named side. 

 --------
 针对 [bang_star_unit_mor]，该识别成立约等于 ≈，而不是严格相等：两者都是同一个圆锥 ⟨id, h⟩ 的中介，但这个中介是从平方条件的证明中产生的，而两个方面提供了不同的证明 —— 在类侧是切片恒等式自身的交换见证，在命名侧是 [id_right (f ∘ h)]。
*)
Lemma bang_star_unit_is_mediator (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
    ≈ bang_star_unit_mor o h.
Proof.
  symmetry.
  apply (uniqueness (base_ump h (f ∘ h) id (id_right (f ∘ h)))).
  split.
  - apply (base_to_fst (id[Bang_Functor f (o; h)])).
  - apply (base_to_snd (id[Bang_Functor f (o; h)])).
Qed.

Lemma bang_star_unit_is_unit (o : C) (h : o ~> a) :
  @unit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (o; h)
    ≈ bang_star_unit o h.
Proof. exact (bang_star_unit_is_mediator o h). Qed.

(*
 The class's counit at (p; k) is the pullback projection with one
 residual identity, which is exactly what ε := ⌈id⌉ produces. 

 --------
 在 (p; k) 上的类余单元是带有一个剩余恒等的拉回投影，这正是 ε := ⌈id⌉ 所产生的。
*)
Example bang_star_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
  = bang_star_counit_mor p k ∘ id := eq_refl.

Lemma bang_star_counit_is_fst (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
    ≈ bang_star_counit_mor p k.
Proof. apply id_right. Qed.

Lemma bang_star_counit_is_counit (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (p; k)
    ≈ bang_star_counit p k.
Proof. exact (bang_star_counit_is_fst p k). Qed.

End BaseChange.

End SliceFunctors.
