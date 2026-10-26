Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/local+object
 https://ncatlab.org/nlab/show/reflective+subcategory
 https://ncatlab.org/nlab/show/localization

 Orthogonal-subcategory localization.  Fix a category C and a class W of
 morphisms (a [MorphismClass C], from Theory/Morphisms/Classes.v).  An object
 x of C is *W-local* when it “sees every W-map as invertible”: for every
 w : a ~> b in W the precomposition map on hom-sets

 (- ∘ w) : Hom(b, x) ⟶ Hom(a, x)

 is an isomorphism of setoids.  This precomposition map is exactly the action
 of the contravariant hom-functor [Hom ─, x] = Curried_CoHom C x on the arrow
 w (read as an arrow b ~{C^op}~> a), so we state W-locality directly as an
 [IsIsomorphism] in [Sets] of [fmap[[Hom ─, x]] w].  See Functor/Hom.v for
 the presheaf [Hom ─, x] and Instance/Sets.v for isomorphisms in [Sets].

 The W-local objects span a *full* subcategory [C_W W] of C (built on
 Construction/Subcategory.v with [shom] retaining every morphism, so the
 fullness witness is trivial).  When this subcategory is reflective
 (Construction/Reflective.v) the reflector *inverts W*: it carries every W-map
 to an isomorphism.  The proof runs entirely through the reflection
 adjunction's hom-set transposes together with W-locality of the reflections
 [Iota (reflector _ a)] and [Iota (reflector _ b)]; it needs neither a
 calculus of fractions nor any classical or extensionality principle.  We also
 record the companion fact on which localizations rest, that the reflection
 unit at a W-local object is an isomorphism ([unit_at_local_iso]) — the dual,
 for the unit, of the counit-iso lemma [reflective_counit_iso]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/local+object 
 https://ncatlab.org/nlab/show/reflective+subcategory 
 https://ncatlab.org/nlab/show/localization 

 正交子范畴定位。固定一个范畴 C 和一个态射类 W（一个  [MorphismClass C] ，来自 Theory/Morphisms/Classes.v）。C 的对象 x 当 “将每个 W-映射视为可逆” 时被称为 *W-局部对象*：对于 W 中的每个 w : a ~> b，抽象同态集上的前复合映射

 (- ∘ w) : Hom(b, x) ⟶ Hom(a, x)

 是集合同构。这个前复合映射正是反变 Hom 函子 [Hom ─, x] = Curried_CoHom C x 在箭头 w 上的作用（将其读作箭头 b ~{C^op}~> a），因此我们直接将 W-局部性表述为 [IsIsomorphism] 在 [Sets] 的 [fmap[[Hom ─, x] ] w] 中。参见 Functor/Hom.v 了解预层 [Hom ─, x] ，以及 Instance/Sets.v 了解 [Sets] 中的同构。W-局部对象张成了 C 的一个*完全*子范畴 [C_W W]（基于 Construction/Subcategory.v 构建，[shom] 保留每一个态射，因此完全性见证是平凡的）。当这个子范畴是反射的（Construction/Reflective.v）时，反射子范畴*将 W 反转*：它把每个 W-映射转为同构。证明完全通过反射伴随的同集换位以及反射的 W-局部性 [Iota (reflector _ a)] 和 [Iota (reflector _ b)] 进行；它既不需要分数演算，也不需要任何经典或外延原则。我们还记录关于本地化所依赖的伴随事实，即在 W-局部对象处的反射单位是同构（[unit_at_local_iso]）——这是余单位同构引理 [reflective_counit_iso] 的对偶，对单位而言。
*)

(*
 Where localization comes from, and what it is for

 nLab:  https://ncatlab.org/nlab/show/localization
 https://ncatlab.org/nlab/show/reflective+localization
 https://ncatlab.org/nlab/show/orthogonal+subcategory+problem
 Wikipedia:
 https://en.wikipedia.org/wiki/Localization_(commutative_algebra)

 Localization universally inverts a chosen class of morphisms.  Given
 W it is the initial way to pass from C to a category C[W⁻¹] in which
 every W-map becomes an isomorphism, so that any functor carrying W to
 isomorphisms factors, essentially uniquely, through it.  It lets a
 family of maps be turned into isomorphisms — the weak equivalences of
 spaces, the quasi-isomorphisms of chain complexes, a multiplicative
 system in a ring — so that work proceeds in the setting where that
 identification holds, while a universal comparison back to C is kept
 (nLab, “localization”; Gabriel–Zisman, “Calculus of Fractions and
 Homotopy Theory”, Springer 1967).

 The vocabulary descends from commutative algebra, where the ring of
 fractions S⁻¹R adjoins formal inverses to a multiplicative set and is
 universal among ring maps sending it to units.  Øystein Ore gave the
 corresponding condition for non-commutative rings, and the categorical
 calculus of fractions is its direct analogue, whence both the names
 “localization” and “fractions” (Wikipedia; nLab, “calculus of
 fractions”).

 The general categorical construction is due to Gabriel and Zisman,
 whose 1967 monograph localized a category at an arbitrary class of
 morphisms and built the category of fractions C[W⁻¹] — its morphisms
 finite zig-zags modulo relations, or explicit spans under the
 Ore-style calculus — with the homotopy category, spaces localized at
 the weak homotopy equivalences, as its headline application.  The
 motivating case from homological algebra is Verdier's derived
 category: in his thesis under Grothendieck in the 1960s he built D(A)
 by formally inverting the quasi-isomorphisms of chain complexes and
 introduced triangulated categories and the Verdier quotient, the first
 published account being Hartshorne, “Residues and Duality” (Springer
 Lecture Notes in Mathematics 20, 1966).

 This file takes the reflective, rather than the syntactic, reading,
 whose theory is due to Freyd and Kelly.  Rather than the zig-zag
 category the localization is identified with the full subcategory of
 W-local objects [C_W], and Freyd and Kelly (“Categories of continuous
 functors, I”, Journal of Pure and Applied Algebra 2, 1972) studied
 exactly this orthogonal subcategory problem — when such a subcategory
 is reflective — as the mechanism behind reflective localizations.
 Passing to W-local objects sidesteps the size questions and the Ore
 hypotheses the syntactic construction carries, which is why
 [reflector_inverts_W] needs neither.

 The applications span the mathematics the construction was built for.
 The homotopy category of spaces is Top[W⁻¹] at the weak homotopy
 equivalences; the derived category is chain complexes localized at
 quasi-isomorphisms, pervasive in sheaf cohomology and duality; and the
 sheaves on a site are the reflective subcategory of presheaves
 orthogonal to the covering sieves, sheafification being the reflector
 — the prototypical Freyd–Kelly orthogonality example, whose full
 subcategory inclusion Theory/Sheaf/Category.v realizes in-tree, with
 sheafification, the reflector, a named deferral there.  More generally
 every reflective subcategory is a reflective localization at the class
 its reflector inverts, so abelianizations, completions and idempotent
 reflections are all instances, the homotopical form being left
 Bousfield localization (nLab, “reflective localization”).

 Computationally a reflective localization is an idempotent monad.  The
 round trip [Incl] ∘ [reflector] is a monad on C whose multiplication
 is invertible, its algebras are exactly the local objects, and to be
 local is to be a fixed point while to localize is to apply the monad:
 idempotent normalization into the full subcategory of already
 saturated objects, where the inverted maps are isomorphisms.  This is
 the correspondence of Construction/Reflective/Idempotent.v (reflective
 subcategory if and only if idempotent monad, with the Eilenberg–Moore
 equivalence), and the same structure homotopy type theory studies as a
 reflective modality (Rijke, Shulman, Spitters, “Modalities in homotopy
 type theory”, arXiv:1706.07526, 2020).  The universal property that
 makes the reflector the localization is established separately in
 Construction/Localization/Universal.v. 

 --------
 本地化的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/localization 
 https://ncatlab.org/nlab/show/reflective+localization 
 https://ncatlab.org/nlab/show/orthogonal+subcategory+problem 
 维基百科:
 https://en.wikipedia.org/wiki/Localization_(commutative_algebra) 

 本地化会普遍地逆转所选择的某类态射。给定 W，它是从 C 到一个范畴 C [W⁻¹] 的初始方式，在该范畴中每个 W-映射都变为同构，因此任何将 W 映射为同构的函子，基本上唯一地通过它进行分解。它可以将一族映射转变为同构——空间的弱等价，链复形的拟同构，环中的乘法系统——从而在这种识别成立的情境下进行工作，同时保持回到 C 的普遍比较（nLab，“localization”；Gabriel–Zisman，《分数演算与同伦理论》，Springer 1967）。这一术语来源于交换代数，其中分数环 S⁻¹R 向一个乘法集合引入形式逆元，并且在将其映射为单位元的环映射中具有普遍性。Øystein Ore 给出了非交换环的相应条件，而分数的范畴演算则是其直接对应，因此有了“局部化”和“分数”这两个名称（维基百科；nLab，“分数演算”）。一般的范畴构造由加布里埃尔和齐斯曼提出，
 其1967年的专著将范畴局域化为任意类
 态射，构造了分式 C [W⁻¹] 范畴——其态射
 有限之字形模关系，或在
 矿石式演算——同伦范畴，空间局部化于
 弱同伦等价，作为其主要应用。该
 同调代数的动机格是韦尔迪耶导出的
 类别：在1960年代格罗滕迪克指导下的论文中，他建立了D（A）
 通过形式反演链复形的拟同构和
 引入了三角范畴和韦尔迪耶商，这是第一个
 出版的记载是哈特肖恩，《残余与二元性》（施普林格出版社）
 《数学讲义》20期，1966年）。这个文件采取的是反射的，而不是句法的，理解方式，其理论归功于 Freyd 和 Kelly。局部化不是通过锯齿形范畴，而是被识别为 W-局部对象 [C_W] 的完全子范畴，而 Freyd 和 Kelly（“连续函子范畴 I”，《纯粹与应用代数杂志》 2, 1972）正是研究了这个正交子范畴问题——当这样的子范畴是反射的——作为反射局部化背后的机制。转向 W-局部对象绕过了语法构造所带来的大小问题和 Ore 假设，这就是 [reflector_inverts_W] 不需要它们的原因。这些应用涵盖了该构造所建立的数学领域。空间的同伦范畴是 Top [W⁻¹]，在弱同伦等价下；导出范畴是链复形在拟同构下的局部化，这在层上同调和对偶性中普遍存在；而一个站点上的层是正则子范畴中与覆盖筛正交的预层的反射子范畴，层化是该反射子——这是典型的 Freyd–Kelly 正交性例子，其完整子范畴包含 Theory/Sheaf/Category.v，在树中实现，并且通过层化实现反射子，这是那里命名的延迟。更一般地，
 每一个反射子范畴都是其反射器逆转的类上的反射局部化，所以阿贝尔化、完备化和幂等反射都是实例，其同伦形式是左 Bousfield 局部化（nLab，“反射局部化”）。从计算的角度来看，一个反射局部化是一个幂等单子。往返 [Incl] ∘ [reflector] 是 C 上的一个单子，其乘法是可逆的，其代数正是局部对象，而成为局部意味着成为一个不动点，而局部化意味着应用该单子：幂等归一化到已饱和对象的全子范畴，其中被反转的映射是同构。这对应于 Construction/Reflective/Idempotent.v（反射子范畴当且仅当幂等单子，并且具有 Eilenberg–Moore 等价），与同类型理论研究的相同结构作为反射模态（Rijke, Shulman, Spitters, “Modalities in homotopy type theory”, arXiv:1706.07526, 2020）。在 Construction/Localization/Universal.v 中，单独建立了使反射器成为局部化的通用性质。
*)

(*
 [WLocal W x]: the object x is local with respect to the class W.  The
 morphism [fmap[[Hom ─, x]] w] is the [Sets]-map [Hom b x -> Hom a x] sending
 g to g ∘ w (precomposition by w); W-locality asserts it is invertible in
 [Sets] for every w selected by W. 

 --------
 [WLocal W x]：对象 x 对类 W 是局部的。态射 [fmap[[Hom ─, x] ] w] 是 [Sets]-映射 [Hom b x -> Hom a x]，将 g 发送到 g ∘ w（通过 w 的前合成）；W-局部性断言，对于 W 选择的每个 w，它在 [Sets] 中都是可逆的。
*)

Definition WLocal {C : Category} (W : MorphismClass C) (x : C) : Type :=
  ∀ (a b : C) (w : a ~> b), W a b w →
    IsIsomorphism (@fmap (C^op) Sets (Curried_CoHom C x) b a w).

(*
 From W-locality, the two elementary hom-set facts used downstream: the
 precomposition [(- ∘ w)] into a W-local object is split-surjective ... 

 --------
 从 W-局部性出发，下游使用的两个基本同态集事实：将 [(- ∘ w)] 预组合到一个 W-局部对象是分裂满射 ...
*)

Lemma WLocal_surj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (p : a ~> x) :
  { q : b ~> x & q ∘ w ≈ p }.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  exists (phi p).
  exact (Hr p).
Qed.

(* ... and injective. / ... 且为单射。 *)

Lemma WLocal_inj {C : Category} {W : MorphismClass C} {x : C} (Hx : WLocal W x)
      {a b : C} (w : a ~> b) (Hw : W a b w) (g1 g2 : b ~> x) :
  g1 ∘ w ≈ g2 ∘ w → g1 ≈ g2.
Proof.
  destruct (Hx a b w Hw) as [phi Hr Hl].
  intro Heq.
  transitivity (phi (g1 ∘ w)).
  - symmetry. exact (Hl g1).
  - transitivity (phi (g2 ∘ w)).
    + apply (proper_morphism phi). exact Heq.
    + exact (Hl g2).
Qed.

(*
 The full subcategory of W-local objects.  Objects are the W-local ones;
 every C-morphism between them is retained ([shom := True]), so composition
 and identities are closed trivially. 

 --------
 W-局部对象的完整子范畴。对象是 W-局部的；它们之间的每个 C-态射都被保留（[shom := True]），因此合成和恒等映射是平凡封闭的。
*)

Definition C_W {C : Category} (W : MorphismClass C) : Subcategory C :=
  {| sobj  := fun x => WLocal W x
   ; shom  := fun x y ox oy f => True
   ; scomp := fun x y z ox oy oz f g _ _ => I
   ; sid   := fun x ox => I |}.

(*
 The subcategory C_W is full: every morphism between W-local objects is in it
 (the [shom] witness is [I]). 

 --------
 子类别 C_W 是满的：每个 W-局部对象之间的态射都属于它（[shom] 的证据是 [I]）。
*)

Definition Full_C_W {C : Category} (W : MorphismClass C) :
  Construction.Subcategory.Full C (C_W W) :=
  fun x y ox oy f => I.

(*
 The reflection unit at a W-local object is an isomorphism.  For any object s
 of the reflective subcategory C_W, the unit η : Iota s ~> Iota (reflector s)
 is invertible in C, with inverse [fmap[Iota] (counit s)].  This is the dual,
 for the unit, of [reflective_counit_iso]; the two triangle identities supply
 both inverse laws, the second one after transporting the subcategory-level
 [zeta ∘ counit ≈ id] along the inclusion functor. 

 --------
 一个 W-局部对象的反射单位是一个同构。对于反射子范畴 C_W 的任意对象 s，单位 η : Iota s ~> Iota (reflector s) 在 C 中是可逆的，其逆是 [fmap[Iota]（counit s）。这是单元的对偶，对应于 [reflective_counit_iso]；两个三角形恒等式提供了两个逆律，第二个逆律是在沿包含函子传输子范畴级别的 [zeta ∘ counit ≈ id] 之后得到的。
*)

Lemma unit_at_local_iso {C : Category} {W : MorphismClass C}
      (R : Reflective (C_W W)) (s : Sub C (C_W W)) :
  IsIsomorphism
    (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
       (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)).
Proof.
  (*
 zeta : the unit at [Incl s], lifted into the subcategory by fullness. 

 --------
 zeta：在 [Incl s] 的单位，通过丰度被提升到子类别中。
*)
  pose (zeta := (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                   (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)
                 ; reflective_full R (Incl C (C_W W) s)
                     (Incl C (C_W W) (reflector R (Incl C (C_W W) s)))
                     (`2 s) (`2 (reflector R (Incl C (C_W W) s)))
                     (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
                        (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)))
                : s ~{Sub C (C_W W)}~> reflector R (Incl C (C_W W) s)).
  (*
 zeta ∘ counit ≈ id in the subcategory (the [from ∘ to] triangle). 

 --------
 zeta ∘ counit ≈ id 在子范畴中（[from ∘ to] 三角形）。
*)
  assert (Hlaw2 : zeta ∘ (@counit (Sub C (C_W W)) C (reflector R)
                            (Incl C (C_W W)) (reflective_adj R) s) ≈ id).
  { rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s)). }
  unshelve econstructor.
  - (* the inverse: the inclusion of the counit / 逆：含有余单位 *)
    exact (fmap[Incl C (C_W W)]
             (@counit (Sub C (C_W W)) C (reflector R)
                (Incl C (C_W W)) (reflective_adj R) s)).
  - (* is_right_inverse: η ∘ fmap[Incl] counit ≈ id / is_right_inverse: η ∘ fmap [Incl] counit ≈ id *)
    change (@Category.Theory.Adjunction.unit (Sub C (C_W W)) C (reflector R)
              (Incl C (C_W W)) (reflective_adj R) (Incl C (C_W W) s))
      with (fmap[Incl C (C_W W)] zeta).
    rewrite <- fmap_comp.
    rewrite Hlaw2.
    apply fmap_id.
  - (* is_left_inverse: fmap[Incl] counit ∘ η ≈ id, a triangle identity / is_left_inverse：fmap [Incl] counit ∘ η ≈ id，一个三角恒等式 *)
    apply (@fmap_counit_unit (Sub C (C_W W)) C (reflector R)
             (Incl C (C_W W)) (reflective_adj R) s).
Qed.

(*
 The localization theorem: when C_W is reflective, the reflector inverts every
 W-map.  For w : a ~> b in W, [fmap[reflector R] w] is an isomorphism of the
 subcategory.  The inverse is [⌈q⌉], where q : b ~> Iota (reflector a) is any
 filler of the unit η_a through [(- ∘ w)] (available by W-locality of the
 reflection Iota (reflector a)); both inverse laws are then discharged through
 the adjunction transposes and W-locality of Iota (reflector b). 

 --------
 本地化定理：当 C_W 是反射类时，反射子会反转每一个 W 图。对于 w : a ~> b 属于 W，[fmap[reflector R]  w] 是子范畴的一个同构。其逆是 [⌈q⌉]，其中 q : b ~> Iota (reflector a) 是单位 η_a 通过 [(- ∘ w)] 的任意填充（可由反射 Iota (reflector a) 的 W-局部性得到）；然后，通过伴随变换和 Iota (reflector b) 的 W-局部性，可以验证两个逆定律。
*)

Section Inverts.
Context {C : Category} {W : MorphismClass C}.
Context (R : Reflective (C_W W)).

(*
 Parse-time abbreviations: these expand to the full terms, keeping the goal
 and every adjunction-transpose lemma instance in the same syntactic form
 (a [set]-folded form would not match the lemmas' unfolded functor). 

 --------
 解析时缩写：这些会扩展为完整的术语，保持目标和每个附加-换位词元实例在相同的句法形式（一个 [set] 折叠形式将无法匹配词元的展开函子）。
*)
Local Notation Su   := (Sub C (C_W W)).
Local Notation Iota := (Incl C (C_W W)).
Local Notation Refl := (reflector R).
Local Notation A    := (reflective_adj R).

Theorem reflector_inverts_W {a b : C} (w : a ~> b) (Hw : W a b w) :
  IsIsomorphism (fmap[Refl] w).
Proof.
  (*
 fill the unit η_a through precomposition by w, using W-locality of the
 reflection Iota (Refl a). 

 --------
 通过用 w 进行前合成填充单位 η_a，使用反射 Iota (Refl a) 的 W-局部性。
*)
  destruct (WLocal_surj (`2 (Refl a)) w Hw
              (@Category.Theory.Adjunction.unit Su C Refl Iota A a)) as [q Hq].
  (* the candidate inverse, transposed back into the subcategory / 候选逆，转置回子类别 *)
  assert (Hli : from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w ≈ id).
  { transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a))
           (from (@adj Su C Refl Iota A b (Refl a)) q ∘ fmap[Refl] w))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    transitivity
      (from (@adj Su C Refl Iota A a (Refl a))
        (to (@adj Su C Refl Iota A a (Refl a)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A a (Refl a)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A a (Refl a)))).
    rewrite (@to_adj_nat_l Su C Refl Iota A a b (Refl a)
               (from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite (@from_adj_comp_law Su C Refl Iota A b (Refl a) q).
    exact Hq. }
  unshelve refine {| two_sided_inverse := from (@adj Su C Refl Iota A b (Refl a)) q |}.
  - (* is_right_inverse: fmap[Refl] w ∘ ⌈q⌉ ≈ id / is_right_inverse: fmap [Refl] w ∘ ⌈q⌉ ≈ id *)
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b))
           (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q))).
    { symmetry. apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    transitivity
      (from (@adj Su C Refl Iota A b (Refl b))
        (to (@adj Su C Refl Iota A b (Refl b)) id)).
    2:{ apply (@to_adj_comp_law Su C Refl Iota A b (Refl b)). }
    apply (proper_morphism (from (@adj Su C Refl Iota A b (Refl b)))).
    apply (WLocal_inj (`2 (Refl b)) w Hw).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b)
                 (fmap[Refl] w ∘ from (@adj Su C Refl Iota A b (Refl a)) q) w).
    rewrite <- (@to_adj_nat_l Su C Refl Iota A a b (Refl b) id w).
    apply (proper_morphism (to (@adj Su C Refl Iota A a (Refl b)))).
    rewrite id_left.
    rewrite <- comp_assoc.
    rewrite Hli.
    rewrite id_right.
    reflexivity.
  - (* is_left_inverse: ⌈q⌉ ∘ fmap[Refl] w ≈ id / is_left_inverse: ⌈q⌉ ∘ fmap [Refl] w ≈ id *)
    exact Hli.
Qed.

End Inverts.
