Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
   * * The centrality closure kit for binoidal categories

   nLab: https://ncatlab.org/nlab/show/premonoidal+category
   (centrality and the centre are discussed there; bare binoidal
   categories have no dedicated nLab page and are covered under
   premonoidal categories)

   Structure/Binoidal.v defines when a morphism [f : x ~> y] of a
   binoidal category is [central]: tensoring [f] with any morphism [f']
   in either order gives the same composite, on both the [x ⊗ x'] and
   the [x' ⊗ x] side.  This file develops the closure properties of that
   predicate that are available in a BARE binoidal category — no unit,
   no associator:

   - [central_id]        : identities are central;
   - [central_respects]  : centrality respects ≈;
   - [central_comp]      : central morphisms compose;
   - [central_iso_from]  : the inverse of a central isomorphism is
   central;

   together with the interaction of [composite_ff'] with identities
   ([composite_id_left] / [composite_id_right]) and with composition
   under a single centrality hypothesis ([composite_ff'_comp_l] /
   [composite_ff'_comp_r]).  The last two isolate the exact “middle
   interchange” that one-sided functoriality of the tensor needs; both
   reduce to the same square, read off one conjunct of the centrality of
   [f] or of [g'].

   The closure properties package the central morphisms as the centre
   Z(C) — here [Centre] — a wide subcategory of [C] built through
   Construction/Subcategory.v, mirroring the deterministic subcategory
   [Det] of Structure/Monoidal/CopyDiscard/Deterministic.v.

   What is deliberately NOT here: closure of centrality under the tensor
   [composite_ff'] itself.  For central [f] and [f'], commuting
   [composite_ff' f f'] past a right-tensored morphism is a square at
   the nested tensor [(x ⊗ x') ⊗ a], and a bare binoidal category
   carries no morphism relating the two nesting levels, so that square
   is unreachable from the single-level centrality data.  Once an
   associator is present the chase goes through; the closure lemma
   [composite_ff'_central] therefore lives in
   Structure/Premonoidal/Centre.v, where Z(C) is also shown to be
   monoidal ([Centre_Monoidal]), discharging the promise recorded in the
   comment above [central] in Structure/Binoidal.v. 

   --------
   * * 双模范畴的中心闭包工具包

   nLab: https://ncatlab.org/nlab/show/premonoidal+category 
   （在那里讨论了中心性和中心；纯双模范畴没有专门的nLab页面，涵盖在前模范畴下）

   Structure/Binoidal.v 定义了何时双模范畴中的一个态射 [f : x ~> y] 是 [central] ：与任意态射 [f'] 张量 [f]，无论顺序如何，都产生相同的复合，在 [x ⊗ x'] 和 [x' ⊗ x] 两边都成立。该文件发展了在纯双模范畴中该谓词可用的闭包性质——没有单位元，没有结合子：-  [central_id]         ：恒等式是核心的；
   -  [central_respects]   ：中心性尊重≈；
   -  [central_comp]       ：中心态射可以复合；
   -  [central_iso_from]   ：中心同构的逆也是中心的；

   并且考虑  [composite_ff']  与恒等式的相互作用
   ( [composite_id_left]  /  [composite_id_right] ) 以及在单一中心性假设下的复合
   ( [composite_ff'_comp_l]  /  [composite_ff'_comp_r] )。最后两者 isolates 精确的“中间交换”，这是张量的单边函子性所需要的；两者都归结为相同的方形，可从  [f]  或  [g'] 的中心性中的一个合取抽取。闭包性质将中心态射打包为中心 Z(C) —— 在这里是 [Centre] —— 一个由 Construction/Subcategory.v 构建的宽子范畴 [C]，类似于 Structure/Monoidal/CopyDiscard/Deterministic.v 中的确定性子范畴 [Det]。这里故意没有提及的是：张量 [composite_ff'] 本身下的中心性闭包。对于中心元素 [f] 和 [f']，将 [composite_ff' f f'] 在右张量态态的态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态态態[嵌套张量 [(x ⊗ x') ⊗ a] 处为一个方形]，而一个裸二元范畴不携带任何态态之间的态态态关系态，因此这个方形无法用单级中心性数据访问。一旦存在结合子，追踪就可以进行；因此闭包引理 [composite_ff'_central] 位于 Structure/Premonoidal/Centre.v 中，其中也显示 Z(C) 是单态范畴（[Centre_Monoidal]），履行了在 Structure/Binoidal.v 中位于 [central] 上方注释中记录的承诺。
*)

Section CentralKit.

Context {C : Category}.
Context `{@Binoidal C}.

(* * ** Closure properties of centrality / * ** 中心性的封闭性 *)

(* Identities are central: both defining squares reduce by [fmap_id] and the unit laws to a triviality. / 恒等式是核心：两个定义平方通过 [fmap_id] 和单位律约简为平凡。 *)
Lemma central_id {x : C} : central (@id C x).
Proof.
  intros x' y' f'; split.
  - rewrite !fmap_id; cat.
  - rewrite !fmap_id; cat.
Qed.

(*
 Centrality is a property of the ≈-class of a morphism: both defining
 squares mention [f] only through [fmap], which respects ≈. 

 --------
 中心性是态射≈-类的一个属性：两个定义方形都仅通过[fmap]提到[f]，而[fmap]遵循≈。
*)
Lemma central_respects {x y : C} {f g : x ~> y} :
  f ≈ g → central f → central g.
Proof.
  intros E cf x' y' f'.
  destruct (cf x' y' f') as [sq1 sq2].
  split.
  - rewrite <- E; exact sq1.
  - rewrite <- E; exact sq2.
Qed.

(*
 Central morphisms compose: expand [fmap] over the composite with
 [fmap_comp], then paste [g]'s square followed by [f]'s square.  Each
 conjunct is a single-level pasting of two commuting squares. 

 --------
 中心态射的复合：在与[fmap_comp]的复合上展开[fmap]，然后粘贴[g]的方格，接着是[f]的方格。每个合取项都是两个可交换方格的单层粘贴。
*)
Lemma central_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  central f → central g → central (f ∘ g).
Proof.
  intros cf cg x' y' f'.
  destruct (cf x' y' f') as [f1 f2].
  destruct (cg x' y' f') as [g1 g2].
  split.
  - rewrite !fmap_comp.
    rewrite !comp_assoc_sym.
    rewrite g1.
    rewrite !comp_assoc.
    now rewrite f1.
  - rewrite !fmap_comp.
    rewrite !comp_assoc.
    rewrite f2.
    rewrite !comp_assoc_sym.
    now rewrite g2.
Qed.

(*
 The inverse of a central isomorphism is central: conjugate each
 to-square by the tensored inverse on both sides and cancel via
 [fmap_comp], the isomorphism laws, and [fmap_id].  The auxiliary
 equation [E] expresses the tensored [f'] as the to-square composite
 flanked by one inverse; substituting it into the goal leaves only the
 other cancellation. 

 --------
 中心同构的逆也是中心的：通过在两边用张量化的逆对每个 to-square 进行共轭，并通过 [fmap_comp]、同构律 和 [fmap_id] 进行消去。辅助方程 [E] 将张量化的 [f'] 表示为一个 to-square 复合体，左右夹着一个逆；将其代入目标后，仅剩下另一次消去。
*)
Lemma central_iso_from {x y : C} (i : x ≅ y) :
  central (to i) → central (from i).
Proof.
  intros ci x' y' f'.
  destruct (ci x' y' f') as [sq1 sq2].
  split.
  - assert (E : fmap[inj_right y] f'
                  ≈ fmap[inj_left y'] (to i)
                      ∘ (fmap[inj_right x] f' ∘ fmap[inj_left x'] (from i))).
    { rewrite !comp_assoc.
      rewrite sq1.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
  - assert (E : fmap[inj_left y] f'
                  ≈ fmap[inj_right y'] (to i)
                      ∘ (fmap[inj_left x] f' ∘ fmap[inj_right x'] (from i))).
    { rewrite !comp_assoc.
      rewrite <- sq2.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
Qed.

(* * ** [composite_ff'] against identities / * ** [composite_ff'] 针对身份 *)

(* Tensoring the identity on the left leaves the right tensoring of [g]. / 在左边张量恒等式会留下右边张量的 [g]。 *)
Lemma composite_id_left {x y : C} (w : C) (g : x ~> y) :
  composite_ff' (id[w]) g ≈ fmap[inj_right w] g.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

(* Tensoring the identity on the right leaves the left tensoring of [f]. / 在右边张量恒等式会保持左边张量 [f]。 *)
Lemma composite_id_right {x y : C} (w : C) (f : x ~> y) :
  composite_ff' f (id[w]) ≈ fmap[inj_left w] f.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(*
   * ** One-sided bifunctoriality

   In a monoidal category [bimap] is functorial in both variables
   jointly.  For the binoidal [composite_ff'] the analogous interchange

   composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'

   needs exactly one middle swap,

   fmap[inj_right z] g' ∘ fmap[inj_left x'] f
   ≈ fmap[inj_left y'] f ∘ fmap[inj_right y] g',

   and a SINGLE centrality hypothesis supplies it: this square is
   conjunct 1 of [central f] instantiated at [g'], and equally conjunct 2
   of [central g'] instantiated at [f].  [composite_ff'_comp_swap] is
   keyed on the bare square and pastes the swap between the [fmap_comp]
   expansions once; the two variants below each read the square off one
   conjunct. 

   --------
   * ** 单边双函子性

   在一个幺半群范畴中  [bimap]  在两个变量上是联合函子的。对于双物体范畴  [composite_ff'] ，类似的交换性

   composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'

   只需要一个中间交换，

   fmap [inj_right z]  g' ∘ fmap [inj_left x']  f
   ≈ fmap [inj_left y']  f ∘ fmap [inj_right y]  g'

   而单个中心性假设足以提供它：这个方形是  [central f] 
   在  [g'] 上实例化的合取 1，同时也是  [central g'] 
   在  [f] 上实例化的合取 2。[composite_ff'_comp_swap] 以裸方形为关键，并在 [fmap_comp] 展开间粘贴一次交换；下面的两个变体各自从一个合取中读取该方形。
*)

Lemma composite_ff'_comp_swap {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  fmap[inj_left y'] f ∘ fmap[inj_right y] g'
    ≈ fmap[inj_right z] g' ∘ fmap[inj_left x'] f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof.
  intros sq.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite !comp_assoc_sym.
  rewrite (comp_assoc (fmap[inj_right z] g')).
  rewrite <- sq.
  now rewrite !comp_assoc_sym.
Qed.

Lemma composite_ff'_comp_l {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cf; exact (composite_ff'_comp_swap (fst (cf x' y' g'))). Qed.

Lemma composite_ff'_comp_r {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central g' →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cg'; exact (composite_ff'_comp_swap (snd (cg' y z f))). Qed.

(*
   * ** The centre Z(C) as a wide subcategory

   [central_id] and [central_comp] are exactly the closure conditions
   Construction/Subcategory.v asks of a subcollection of morphisms, so
   the central morphisms over ALL objects form a wide subcategory, the
   centre of the binoidal category (Power–Robinson, “Premonoidal
   categories and notions of computation”, 1997).  The packaging
   mirrors [DeterministicSub]/[Det] of
   Structure/Monoidal/CopyDiscard/Deterministic.v. 

   --------
   * ** 作为广义子范畴的中心 Z(C)

   [central_id] 和 [central_comp] 恰好是闭合条件
   Construction/Subcategory.v 询问一个态射的子集合，因此
   作用在所有对象上的中心态射形成一个广义子范畴，即
   双算子范畴的中心（Power–Robinson，《Premonoidal
   categories and notions of computation》，1997）。该封装
   类似于 Structure/Monoidal/CopyDiscard/Deterministic.v 中的 [DeterministicSub] / [Det]。
*)

Program Definition CentralSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => central f;
  scomp := fun _ _ _ _ _ _ _ _ cf cg => central_comp cf cg;
  sid   := fun _ _ => central_id
|}.

Lemma Centre_wide : Wide C CentralSub.
Proof. intro x; exact ttt. Qed.

(*
 The inclusion Z(C) ⟶ C is the generic faithful [Incl C CentralSub]
 from Construction/Subcategory.v.  Note that [Sub]'s homset compares
 first projections — [fun f g => `1 f ≈ `1 g] — so every equation
 between morphisms of the centre is literally an equation between the
 underlying morphisms of [C]; Structure/Premonoidal/Centre.v relies on
 this when it transports the coherence laws of a premonoidal [C] to
 its (monoidal) centre. 

 --------
 包含 Z(C) ⟶ C 是 Construction/Subcategory.v 中的通用忠实 [Incl C CentralSub]。注意 [Sub] 的同态集合比较的是第一投影 — [fun f g => `1 f ≈ `1 g] — 因此中心之间的每一个态射方程实际上都是 [C] 的底层态射之间的方程；Structure/Premonoidal/Centre.v 在将一个前单态 [C] 的相干律传输到其（单态）中心时依赖于此。
*)

End CentralKit.

(*
 The centre as a category, with the base category explicit so that
 downstream files can write [Centre C] for the centre of [C].  Its
 objects are those of [C] tagged with the trivial [poly_unit] witness,
 and its morphisms are the central morphisms. 

 --------
 中心作为一个范畴，其中基范畴是显式的，以便下游文件可以为 [C] 的中心写 [Centre C]。它的对象是带有平凡 [poly_unit] 证人的 [C] 的对象，其态射是中心态射。
*)
Definition Centre (C : Category) `{H : @Binoidal C} : Category :=
  Sub C (@CentralSub C H).
