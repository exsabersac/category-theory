(*
   * * Functors into the arrow category classify natural transformations 

   --------
   * * 指向箭头范畴的函子分类自然变换
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Instance.Sets.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §II.4, printed pp. 40–42 (PDF 50–52) —
 maclane:II.4:construction1, maclane:II.4:ex7
 Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
 Example 7.15, printed p. 171 (PDF p. 180) —
 awodey:7.7:example15
 nLab:      https://ncatlab.org/nlab/show/arrow+category

 Mac Lane's Exercise II.4.7: a functor into the arrow category is
 exactly a natural transformation.  From H : C ⟶ Arrow B one reads
 off two functors — the domain and codomain of the arrows H picks
 out — and the arrows themselves assemble into a natural
 transformation between them, BECAUSE the morphism part of H is a
 commuting square; conversely a natural transformation τ : S ⟹ T
 materializes as the functor c ↦ (τ c), naturality supplying the
 squares.  The two passages are mutually inverse, and this file
 states the bijection at the strength the library supports: a
 setoid isomorphism in Sets between functors C ⟶ Arrow B under
 [Functor_Setoid] (natural isomorphism) and transformation triples
 (S, T, τ) under componentwise natural isomorphism intertwining τ.

 - [ArrowTriple]/[triple_dom]/[triple_cod]/[triple_nat]: the
 bundle (S, T, τ : S ⟹ T) with its boundary accessors
 - [Arrow_dom]/[Arrow_cod]: the boundary functors of a functor
 into the arrow category, and [Arrow_generic H] — the arrows H
 picks out, assembled into a transformation (Ex. 7 forward);
 [Arrow_dom_boundary]/[Arrow_cod_boundary] record that the
 generic arrow's components have the projected boundaries
 - [Arrow_intro (S, T, τ)]: the classifying functor H_τ with
 object action c ↦ τ c and morphism action the naturality
 square (Ex. 7 inverse)
 - [ArrowTriple_Setoid]: triples up to componentwise natural
 isomorphism intertwining the transformations
 - [Arrow_classification]: the bijection, as an isomorphism in
 Sets between the functor setoid and the triple setoid

 Design:

 1. THE COMPARISON WITH [_2, B] IS ALREADY IN THE TREE, AND IS NOT
 REBUILT.  Theory/Shapes.v proves
 [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C] (with the strict half
 [Arrow_Fun_Arrow_strict]), for [C : Category@{o Set Set}] — a
 restriction [_2]'s Set-level homs force through [Fun].  This
 file is the OTHER half of Mac Lane's §II.4 story, and it is
 free of that Set-level pin: the classification never mentions
 [_2], only the comma presentation [Arrow B := Id ↓ Id], so hom
 and proof universes may sit strictly above [Set] (the
 library's ambient h = p constraint that [Functor] imposes
 still applies, as it does to every functor statement).
 Awodey's Example 7.15 reads C^1 = C, C^2 = the arrow category,
 C^I = powers: the first is Theory/Shapes.v's [One_Fun_iso]
 (itself under the same Set-level restriction as
 [Two_Fun_Arrow], for the same reason), the second is
 [Two_Fun_Arrow], and the discrete third is issue #276's
 Instance/Fun/Discrete.v.

 2. THE TRIPLE SETOID MIRRORS [Functor_Setoid].  Two triples are
 identified when their boundary functors are naturally
 isomorphic AND the isomorphisms intertwine the two
 transformations (ρ c ∘ τ c ≈ τ' c ∘ σ c).  This is forced:
 the functor side identifies H ≈ H' by natural isomorphisms
 whose components are commuting squares of [Arrow B], and a
 square's two legs are exactly the σ/ρ components while the
 square condition is exactly the intertwining.  The explicit
 symmetric/transitive witnesses [fs_sym]/[fs_trans] for
 [Functor_Setoid] are built by hand (iso_sym/iso_compose
 families) so their component families stay transparent — the
 instance's own Equivalence proof is opaque and cannot be
 computed through.

 3. ROUND TRIPS.  Extraction after introduction is definitional on
 every component (identity isomorphism families); introduction
 after extraction differs from the original functor only by
 sigT/pair eta — H c is ((p, h)) while the rebuilt object is
 ((fst p, snd p), h) — repaired by the identity-legged square,
 the same pair-eta phenomenon Construction/Product/Special.v
 documents. 

 --------
 书籍：      Mac Lane，《为工作的数学家准备的范畴论》，第2版，§II.4，印刷页 40–42（PDF 50–52）——
 maclane:II.4:construction1, maclane:II.4:ex7
 书籍：      Awodey，《范畴论》（第一版，2005年预印本），§7.7，
 示例 7.15，印刷页 171（PDF 页 180）——
 awodey:7.7:example15
 nLab:       https://ncatlab.org/nlab/show/arrow+categoryMac Lane 的练习 II.4.7：一个指向箭头范畴的函子恰好是一个自然变换。从 H : C ⟶ Arrow B 可以读出两个函子——H 选出的箭头的定义域和陪域——并且这些箭头本身组装成它们之间的自然变换，因为 H 的态射部分是一个交换方形；反过来，一个自然变换 τ : S ⟹ T 体现为函子 c ↦ (τ c)，自然性提供方形。两者的转换是相互逆的，并且这个文件陈述了在库支持的强度下的双射：Sets 中在函子 C ⟶ Arrow B 下的集合同构（自然同构）与分量自然同构互相交织 τ 的变换三元组 (S, T, τ) 之间的集合同构。-  [ArrowTriple] / [triple_dom] / [triple_cod] / [triple_nat]：带有边界访问器的丛 (S, T, τ : S ⟹ T)  
 -  [Arrow_dom] / [Arrow_cod]：映入箭头范畴的函子的边界函子，以及 [Arrow_generic H] — H 选出的箭头，组合成一个变换（例 7 正方向）；  
 [Arrow_dom_boundary] / [Arrow_cod_boundary] 记录了通用箭头的分量具有投射边界  
 -  [Arrow_intro (S, T, τ)]：分类函子 H_τ，作用于对象 c ↦ τ c，作用于态射为自然性正方形（例 7 逆方向）  
 -  [ArrowTriple_Setoid]：至分量自然同构的三元组，交织变换  
 -  [Arrow_classification]：作为集合中的同构，函子同伦类与三元组同伦类之间的双射  

 设计：1. 与 [_2, B] 的比较已经在树中，并未重新构建。Theory/Shapes.v 证明 [Two_Fun_Arrow : [_2, C] ≅ [Cat] 箭头 C]（与严格的一半 [Arrow_Fun_Arrow_strict]），对于 [C : Category@{o Set Set}] — [_2] 的限制其集合级的同态通过 [Fun] 强制应用。该文件是 Mac Lane §II.4 故事的另一半，而且它不受该集合级限制的影响：分类从未提及 [_2]，只提及逗号表示 [Arrow B := Id ↓ Id]，因此同态和证明宇宙可以严格位于 [Set] 之上（库的环境约束 h = p 对 [Functor] 施加的限制仍然适用，就像对每个函子声明一样）。Awodey 的例子 7.15 写道 C^1 = C，C^2 = 箭头范畴，C^I = 幂：第一个是 Theory/Shapes.v 的 [One_Fun_iso]（其自身在与 [Two_Fun_Arrow] 相同的 Set 级别限制下，原因相同），第二个是 [Two_Fun_Arrow]，离散的第三个是 issue #276 的 Instance/Fun/Discrete.v。2. 三重集合镜像 [Functor_Setoid]。 当两个三重体的边界函子自然同构且这些同构互相交织两个变换（ρ c ∘ τ c ≈ τ' c ∘ σ c）时，这两个三重体被认为是相同的。这是强制的：函子一侧通过自然同构识别 H ≈ H'，其组件是 [Arrow B] 的交换方块，而一个方块的两条边恰好是 σ/ρ 组件，方块条件恰好是交织条件。用于 [Functor_Setoid] 的显式对称/传递见证 [fs_sym] / [fs_trans] 是手工构建的（iso_sym/iso_compose 家族），因此它们的组件家族保持透明——实例自身的等价性证明是不透明的，无法通过计算获得。3. 往返转换。在每个组件上（同一性同构族），提取在引入之后是定义性的；而引入在提取之后与原来的函子仅在 sigT/pair eta 上有所不同——H c 是 ((p, h))，而重建的对象是 ((fst p, snd p), h)——通过具有同一性支的方形修复，这与 Construction/Product/Special.v 文档中描述的相同的 pair-eta 现象一致。
*)

(** ** Transformation triples / ** 变换三元组 *)

(*
 The data Ex. 7 classifies: two functors and a transformation. 

 --------
 例 7 的数据分类：两个函子和一个变换。
*)
Definition ArrowTriple (C B : Category) : Type :=
  { S : C ⟶ B & { T : C ⟶ B & S ⟹ T } }.

Definition triple_dom {C B : Category} (t : ArrowTriple C B) : C ⟶ B := `1 t.
Definition triple_cod {C B : Category} (t : ArrowTriple C B) : C ⟶ B :=
  `1 (`2 t).
Definition triple_nat {C B : Category} (t : ArrowTriple C B) :
  triple_dom t ⟹ triple_cod t := `2 (`2 t).

(*
   * ** Transparent equivalence witnesses for [Functor_Setoid] 

   --------
   * ** [Functor_Setoid] 的透明等价证明
*)

(*
 [Functor_Setoid]'s own Equivalence proof is opaque; the
 classification needs to compute with the component families of
 symmetric and transitive witnesses, so they are rebuilt here with
 transparent families and opaque (Qed) naturality parts. 

 --------
 [Functor_Setoid] 自身的等价性证明是不透明的；分类需要与对称和传递见证的分量族一起计算，因此这里使用透明的族并带有不透明（Qed）自然性部分重新构建它们。
*)

Lemma fs_sym_nat {C D : Category} {F G : C ⟶ D} (σ : F ≈ G) :
  ∀ x y (f : x ~{C}~> y),
    fmap[G] f ≈ from (iso_sym (`1 σ y)) ∘ fmap[F] f ∘ to (iso_sym (`1 σ x)).
Proof.
  intros x y f; simpl.
  rewrite (`2 σ x y f).
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- !comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Definition fs_sym {C D : Category} {F G : C ⟶ D} (σ : F ≈ G) : G ≈ F :=
  existT _ (fun c => iso_sym (`1 σ c)) (fs_sym_nat σ).

Lemma fs_trans_nat {C D : Category} {F G K : C ⟶ D}
      (σ : F ≈ G) (σ' : G ≈ K) :
  ∀ x y (f : x ~{C}~> y),
    fmap[F] f ≈ from (iso_compose (`1 σ' y) (`1 σ y)) ∘ fmap[K] f
                  ∘ to (iso_compose (`1 σ' x) (`1 σ x)).
Proof.
  intros x y f; simpl.
  rewrite (`2 σ x y f).
  rewrite (`2 σ' x y f).
  rewrite !comp_assoc.
  reflexivity.
Qed.

Definition fs_trans {C D : Category} {F G K : C ⟶ D}
           (σ : F ≈ G) (σ' : G ≈ K) : F ≈ K :=
  existT _ (fun c => iso_compose (`1 σ' c) (`1 σ c)) (fs_trans_nat σ σ').

Lemma fs_refl_nat {C D : Category} (F : C ⟶ D) :
  ∀ x y (f : x ~{C}~> y),
    fmap[F] f ≈ from (@iso_id D (F y)) ∘ fmap[F] f ∘ to (@iso_id D (F x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Definition fs_refl {C D : Category} (F : C ⟶ D) : F ≈ F :=
  existT _ (fun c => iso_id) (fs_refl_nat F).

(** ** The triple setoid / ** 三重等价类 *)

Program Definition ArrowTriple_Setoid {C B : Category} :
  Setoid (ArrowTriple C B) := {|
  equiv := fun t u =>
    { σ : triple_dom t ≈ triple_dom u
    & { ρ : triple_cod t ≈ triple_cod u
      & ∀ c, @equiv _ (@homset B (triple_dom t c) (triple_cod u c))
               (to (`1 ρ c) ∘ triple_nat t c)
               (triple_nat u c ∘ to (`1 σ c)) } }
|}.
Next Obligation.
  intros C B; constructor.
  - (* reflexivity / 反身性 *)
    intro t.
    exists (fs_refl _), (fs_refl _).
    intro c; simpl; cat.
  - (* symmetry / 对称 *)
    intros t u (σ & ρ & compat).
    exists (fs_sym σ), (fs_sym ρ).
    intro c; simpl.
    rewrite <- id_right.
    rewrite <- (iso_to_from (`1 σ c)); simpl.
    rewrite comp_assoc.
    rewrite <- (comp_assoc _ (triple_nat u c)).
    rewrite <- compat.
    rewrite !comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - (* transitivity / 及物性 *)
    intros t u v (σ & ρ & compat) (σ' & ρ' & compat').
    exists (fs_trans σ σ'), (fs_trans ρ ρ').
    intro c; simpl.
    rewrite <- comp_assoc.
    rewrite compat.
    rewrite comp_assoc.
    rewrite compat'.
    rewrite comp_assoc.
    reflexivity.
Qed.

(*
   * ** Ex. 7 forward: reading a triple off a functor into [Arrow B] 

   --------
   * ** 示例 7 及以后：将三元组从函子读取到 [Arrow B]
*)

Definition Arrow_dom {C B : Category} (H : C ⟶ @Arrow B) : C ⟶ B :=
  comma_proj1 ◯ H.

Definition Arrow_cod {C B : Category} (H : C ⟶ @Arrow B) : C ⟶ B :=
  comma_proj2 ◯ H.

(*
 The arrows H picks out, assembled into a transformation: the
 component at c is the arrow part of the object H c, and naturality
 is exactly the square that is the morphism part of H.  This is the
 whiskering of Construction/Comma.v's [comma_proj_nat] along H — the
 two agree componentwise — built directly because [comma_proj_nat]'s
 transform is a tactic-synthesized match on the destructured comma
 object, which does not reduce at an opaque [H c]. 

 --------
 箭头 H 所选择的部分，组装成一个变换：在 c 处的分量是对象 H c 的箭头部分，而自然性正好是 H 的态射部分的方形。这是 Construction/Comma.v 中 [comma_proj_nat] 沿 H 的鞭状操作——两者在各分量上相互一致——直接构建，因为 [comma_proj_nat] 的变换是对解构的逗号对象进行策略合成匹配，而在不透明的 [H c] 上不会化简。
*)
Program Definition Arrow_generic {C B : Category} (H : C ⟶ @Arrow B) :
  Arrow_dom H ⟹ Arrow_cod H := {|
  transform := fun c => `2 (H c)
|}.
Next Obligation.
  intros C B H x y f; simpl.
  symmetry.
  exact (`2 (fmap[H] f)).
Qed.
Next Obligation.
  intros C B H x y f; simpl.
  exact (`2 (fmap[H] f)).
Qed.

(*
 Boundary lemmas: the generic arrow's component at c runs from the
 projected domain to the projected codomain, definitionally. 

 --------
 边界引理：通用箭头在 c 处的分量从投影域到投影陪域，本质上是定义的。
*)
Lemma Arrow_dom_boundary {C B : Category} (H : C ⟶ @Arrow B) (c : C) :
  Arrow_dom H c = fst (`1 (H c)).
Proof. reflexivity. Qed.

Lemma Arrow_cod_boundary {C B : Category} (H : C ⟶ @Arrow B) (c : C) :
  Arrow_cod H c = snd (`1 (H c)).
Proof. reflexivity. Qed.

Definition Arrow_extract {C B : Category} (H : C ⟶ @Arrow B) :
  ArrowTriple C B :=
  (Arrow_dom H; (Arrow_cod H; Arrow_generic H)).

(*
   * ** Ex. 7 inverse: the classifying functor of a transformation 

   --------
   * ** 示例 7 逆：变换的分类函子
*)

(*
 A natural transformation materializes as a functor into the arrow
 category: objects go to components, morphisms to naturality
 squares. 

 --------
 自然变换表现为箭头范畴中的函子：对象映射到分量，态射映射到自然性方格。
*)
Program Definition Arrow_intro {C B : Category} (t : ArrowTriple C B) :
  C ⟶ @Arrow B := {|
  fobj := fun c => ((triple_dom t c, triple_cod t c); triple_nat t c);
  fmap := fun x y f =>
    ((fmap[triple_dom t] f, fmap[triple_cod t] f); _)
|}.
Next Obligation.
  intros C B t x y f; simpl.
  symmetry.
  apply (naturality[triple_nat t]).
Qed.
Next Obligation.
  intros C B t x y f g Hfg; simpl; split.
  - now rewrite Hfg.
  - now rewrite Hfg.
Qed.
Next Obligation.
  intros C B t c; simpl; split.
  - apply fmap_id.
  - apply fmap_id.
Qed.
Next Obligation.
  intros C B t x y z f g; simpl; split.
  - apply fmap_comp.
  - apply fmap_comp.
Qed.

(* * ** Component isomorphisms for the classification / * ** 组件同构用于分类 *)

(*
 An isomorphism of arrow objects projects to isomorphisms of the two
 boundaries; its to-square is the intertwining.  (Cf.
 Construction/Comma.v's [comma_proj_mor_iso], which packages the
 same content as a single isomorphism in the product category.) 

 --------
 箭头对象的同构投射到两个边界的同构上；其 to-方阵就是交织。（参见 Construction/Comma.v 的 [comma_proj_mor_iso]，它将相同的内容打包为乘积范畴中的单个同构。）
*)
Program Definition Arrow_proj_dom_iso {B : Category} {a b : @Arrow B}
        (i : a ≅ b) : fst (`1 a) ≅ fst (`1 b) := {|
  to   := fst (`1 (to i));
  from := fst (`1 (from i))
|}.
Next Obligation.
  intros B a b i; exact (fst (iso_to_from i)).
Qed.
Next Obligation.
  intros B a b i; exact (fst (iso_from_to i)).
Qed.

Program Definition Arrow_proj_cod_iso {B : Category} {a b : @Arrow B}
        (i : a ≅ b) : snd (`1 a) ≅ snd (`1 b) := {|
  to   := snd (`1 (to i));
  from := snd (`1 (from i))
|}.
Next Obligation.
  intros B a b i; exact (snd (iso_to_from i)).
Qed.
Next Obligation.
  intros B a b i; exact (snd (iso_from_to i)).
Qed.

Lemma Arrow_extract_dom_nat {C B : Category} {H H' : C ⟶ @Arrow B}
      (Θ : ∀ c, H c ≅ H' c)
      (Θnat : ∀ x y (f : x ~{C}~> y),
          fmap[H] f ≈ from (Θ y) ∘ fmap[H'] f ∘ to (Θ x)) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_dom H] f
      ≈ from (Arrow_proj_dom_iso (Θ y)) ∘ fmap[Arrow_dom H'] f
          ∘ to (Arrow_proj_dom_iso (Θ x)).
Proof.
  intros x y f; exact (fst (Θnat x y f)).
Qed.

Lemma Arrow_extract_cod_nat {C B : Category} {H H' : C ⟶ @Arrow B}
      (Θ : ∀ c, H c ≅ H' c)
      (Θnat : ∀ x y (f : x ~{C}~> y),
          fmap[H] f ≈ from (Θ y) ∘ fmap[H'] f ∘ to (Θ x)) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_cod H] f
      ≈ from (Arrow_proj_cod_iso (Θ y)) ∘ fmap[Arrow_cod H'] f
          ∘ to (Arrow_proj_cod_iso (Θ x)).
Proof.
  intros x y f; exact (snd (Θnat x y f)).
Qed.

(*
 Boundary isomorphisms intertwining the transformations assemble into
 an isomorphism of the classifying functors' values. 

 --------
 把交错这些变换的边界同构组合起来，就形成了分类函子值的同构。
*)
Program Definition Arrow_intro_component_iso {C B : Category}
        {t u : ArrowTriple C B}
        (σ : triple_dom t ≈ triple_dom u) (ρ : triple_cod t ≈ triple_cod u)
        (compat : ∀ c, @equiv _ (@homset B (triple_dom t c) (triple_cod u c))
                    (to (`1 ρ c) ∘ triple_nat t c)
                    (triple_nat u c ∘ to (`1 σ c)))
        (c : C) :
  @Isomorphism (@Arrow B) (Arrow_intro t c) (Arrow_intro u c) := {|
  to   := ((to (`1 σ c), to (`1 ρ c)); _);
  from := ((from (`1 σ c), from (`1 ρ c)); _)
|}.
Next Obligation.
  intros C B t u σ ρ compat c; simpl.
  symmetry; apply compat.
Qed.
Next Obligation.
  (*
 the reverse square, by conjugating the intertwining with inverses 

 --------
 反平方，通过将纠缠与逆运算结合
*)
  intros C B t u σ ρ compat c; simpl.
  transitivity ((`1 ρ c)⁻¹ ∘ ((`1 ρ c ∘ triple_nat t c) ∘ (`1 σ c)⁻¹)).
  - rewrite !comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - rewrite (compat c).
    rewrite <- (comp_assoc (triple_nat u c)).
    rewrite iso_to_from, id_right.
    reflexivity.
Qed.
Next Obligation.
  intros C B t u σ ρ compat c; split; simpl.
  - apply (iso_to_from (`1 σ c)).
  - apply (iso_to_from (`1 ρ c)).
Qed.
Next Obligation.
  intros C B t u σ ρ compat c; split; simpl.
  - apply (iso_from_to (`1 σ c)).
  - apply (iso_from_to (`1 ρ c)).
Qed.

(*
 Introduction after extraction differs from the original only by
 sigT/pair eta, repaired by the identity-legged square. 

 --------
 提取后的引入与原始内容的区别仅在于 sigT/对 eta，通过恒等腿平方修复。
*)
Program Definition Arrow_eta_iso {C B : Category} (H : C ⟶ @Arrow B)
        (c : C) :
  @Isomorphism (@Arrow B) (Arrow_intro (Arrow_extract H) c) (H c) := {|
  to   := ((id, id); _);
  from := ((id, id); _)
|}.
Next Obligation.
  intros C B H c; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; split; simpl; cat.
Qed.
Next Obligation.
  intros C B H c; split; simpl; cat.
Qed.

(** ** The classification / ** 分类 *)

(*
 Ex. 7 as a bijection: functors into the arrow category, up to
 natural isomorphism, are exactly transformation triples up to
 componentwise natural isomorphism intertwining the
 transformations. 

 --------
 例 7 作为双射：进入箭头范畴的函子，在自然同构意义下，正好是变换三元组，在分量自然同构意义下交织这些变换。
*)
Program Definition Arrow_classification (C B : Category) :
  ({| carrier := C ⟶ @Arrow B;
      is_setoid := @Functor_Setoid C (@Arrow B) |} : SetoidObject)
    ≅[Sets]
  {| carrier := ArrowTriple C B;
     is_setoid := @ArrowTriple_Setoid C B |} := {|
  to   := {| morphism := fun H => Arrow_extract H |};
  from := {| morphism := fun t => Arrow_intro t |}
|}.
Next Obligation.
  (*
 to respects ≈: a natural iso of functors into Arrow B projects to
 boundary isos, and its squares are the intertwining 

 --------
 关于 respects ≈：把函子自然同构到 Arrow B 投影到边界同构，并且它的方形是交织的
*)
  intros C B H H' (Θ & Θnat).
  exists (existT _ (fun c => Arrow_proj_dom_iso (Θ c))
                 (Arrow_extract_dom_nat Θ Θnat)).
  exists (existT _ (fun c => Arrow_proj_cod_iso (Θ c))
                 (Arrow_extract_cod_nat Θ Θnat)).
  intro c; simpl.
  exact (symmetry (`2 (to (Θ c)))).
Qed.
Next Obligation.
  (*
 from respects ≈: boundary isos with intertwining assemble into a
 natural iso of classifying functors, componentwise squares 

 --------
 从尊重 ≈：带交织的边界同构组装成分类函子的一种自然同构，按分量的平方
*)
  intros C B t u (σ & ρ & compat).
  exists (fun c => Arrow_intro_component_iso σ ρ compat c).
  intros x y f; split; simpl.
  - exact (`2 σ x y f).
  - exact (`2 ρ x y f).
Qed.
Next Obligation.
  (*
 to ∘ from ≈ id on triples: extraction after introduction is
 definitional on every component 

 --------
 在三元组上：引入后的提取在每个组件上都是定义性的
*)
  intros C B t.
  exists (fs_refl _), (fs_refl _).
  intro c; simpl; cat.
Qed.
Next Obligation.
  (*
 from ∘ to ≈ id on functors: introduction after extraction differs
 only by sigT/pair eta, repaired by identity-legged squares 

 --------
 从 ∘ 到 ≈ id 在函子上：提取后的引入仅在 sigT/对偶 η 上有所不同，由带有恒等腿的方形修复
*)
  intros C B H.
  exists (fun c => Arrow_eta_iso H c).
  intros x y f; split; simpl; cat.
Qed.
