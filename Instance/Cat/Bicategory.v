Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/Cat

 Cat is the motivating bicategory: its 0-cells are categories, the hom-
 category `bicat C D` is the functor category `[C, D]` (objects = functors,
 2-cells = natural transformations, vertical composition = `nat_compose`),
 horizontal composition is functor composition `◯` extended to natural
 transformations by the Godement/horizontal composite `nat_hcompose`, and the
 unitors and associator are the coherence isomorphisms of `Instance/Fun.v`.
 Following `Instance/Cat.v`, `bi0cell := Category` sits one universe level up;
 `Cat_Bicategory` is a registration-free `Definition`, never an `Instance`
 (there is no bicategory of bicategories).

 RECONCILING THE REVERSED NAMING OF Instance/Fun.v.  The unitor isomorphisms
 in `Instance/Fun.v` are named against the usual monoidal convention (its own
 comment flags this):

 nat_λ F : F ◯ Id ≅ F   is the RIGHT-unit isomorphism (Id on the right),
 nat_ρ F : Id ◯ F ≅ F   is the LEFT-unit  isomorphism (Id on the left).

 The bicategory's `bi1id` is the identity functor `Id`, so `bi1id ∘∘∘ f` is
 `Id ◯ f` and `f ∘∘∘ bi1id` is `f ◯ Id`.  Hence the CROSSED assignment:

 hunit_left  f : bi1id ∘∘∘ f = Id ◯ f ≅ f   :=  nat_ρ f   (Fun's “ρ”),
 hunit_right f : f ∘∘∘ bi1id = f ◯ Id ≅ f   :=  nat_λ f   (Fun's “λ”).

 For the associator, `nat_α F G H : H ◯ (G ◯ F) ≅ (H ◯ G) ◯ F` runs in the
 `h ◯ (g ◯ f) → (h ◯ g) ◯ f` direction, whereas `hassoc h g f` must run
 `(h ∘∘∘ g) ∘∘∘ f → h ∘∘∘ (g ∘∘∘ f)`, i.e. `(h ◯ g) ◯ f → h ◯ (g ◯ f)`.  So
 `hassoc h g f` is the INVERSE of `nat_α f g h`: `iso_sym (nat_α f g h)`, whose
 `to` is `from (nat_α f g h)` (mind the factor order `f g h`).

 PERFORMANCE / DEFINITIONAL-EQUALITY NOTE (a deliberate deviation from the
 `Build_Bicategory'` route).  The `hcompose` field wants a functor of type
 `bicat D E ∏ bicat C D ⟶ bicat C E`, and `Cat_Hcompose` has the type
 `[D, E] ∏ [C, D] ⟶ [C, E]`.  For Coq to accept it cheaply, the manifest
 hom-category `bicat C D` must be *definitionally* the functor category
 `[C, D]`; otherwise unifying two non-convertible `Category` records churns.
 We obtain that definitional equality by feeding the structural fields of the
 bicategory from `[C, D]`'s own projections (record eta then gives
 `bicat C D ≡ [C, D]`).  Record eta breaks if `comp_assoc_sym` is the
 `symmetry`-derived form of `Build_Bicategory'`, so `Cat_Bicategory` is built
 with the raw `Build_Bicategory`, supplying `[C, D]`'s `comp_assoc_sym`
 projection directly.  `Build_Bicategory'` remains available (and type-checked)
 in `Theory/Bicategory.v`; it is simply not the constructor used here. 

 --------
 nLab：https://ncatlab.org/nlab/show/Cat

 Cat 是激励的二范畴：其 0-胞为范畴，Hom 范畴 `bicat C D` 是函子范畴 ` [C, D]ZZ `（对象 = 函子，2-胞 = 自然变换，垂直组合 = `nat_compose`），水平组合为函子组合 `◯`，通过 Godement/水平复合扩展至自然变换 `nat_hcompose`，单位子同构与结合子同构是 `Instance/Fun.v` 的相容性同构。遵循 `Instance/Cat.v`，`bi0cell := Category` 位于一个更高的宇宙层级；`Cat_Bicategory` 是一个无需注册的 `Definition`，从不成为 `Instance`（不存在二范畴的二范畴）。

 调和 Instance/Fun.v 的命名顺序相反。在 `Instance/Fun.v` 中，单位子同构的命名与通常的单范畴惯例相反（其自身的注释指出了这一点）：nat_λ F : F ◯ Id ≅ F 是右单位同构（右侧的 Id），
 nat_ρ F : Id ◯ F ≅ F 是左单位同构（左侧的 Id）。

 该双范畴的 `bi1id` 是恒等函子 `Id`，所以 `bi1id ∘∘∘ f` 是
 `Id ◯ f`，且 `f ∘∘∘ bi1id` 是 `f ◯ Id`。因此交叉赋值：

 hunit_left  f : bi1id ∘∘∘ f = Id ◯ f ≅ f   :=  nat_ρ f   （函子的 “ρ”），
 hunit_right f : f ∘∘∘ bi1id = f ◯ Id ≅ f   :=  nat_λ f   （函子的 “λ”）。

 对于结合子，`nat_α F G H : H ◯ (G ◯ F) ≅ (H ◯ G) ◯ F` 沿着 `h ◯ (g ◯ f) → (h ◯ g) ◯ f` 方向，而 `hassoc h g f` 必须沿着
 `(h ∘∘∘ g) ∘∘∘ f → h ∘∘∘ (g ∘∘∘ f)`，亦即 `(h ◯ g) ◯ f → h ◯ (g ◯ f)`。因此
 `hassoc h g f` 是 `nat_α f g h` 的逆：`iso_sym (nat_α f g h)`，其 `to` 是 `from (nat_α f g h)`（注意因子顺序 `f g h`）。性能 / 定义相等性备注（有意偏离 `Build_Bicategory'` 路线）。`hcompose` 字段需要类型为 `bicat D E ∏ bicat C D ⟶ bicat C E` 的函子，而 `Cat_Hcompose` 的类型是 ` [D, E]ZZ  ∏  [C, D]ZZ  ⟶  [C, E]ZZ `。为了让 Coq 低成本接受它，显性同态范畴 `bicat C D` 必须在*定义上*是函子范畴 ` [C, D]ZZ `；否则统一两个不可转换的 `Category` 记录会引起大量处理。我们通过将 ` [C, D]ZZ ` 本身投影的结构字段输入，得到这种定义上的相等性（记录 eta 然后给出 `bicat C D ≡  [C, D]ZZ `）。如果 `comp_assoc_sym` 是 `Build_Bicategory'` 的 `symmetry` 派生形式，则记录 eta 会崩溃，因此 `Cat_Bicategory` 是用原始的 `Build_Bicategory` 构建的，直接提供 ` [C, D]ZZ ` 的 `comp_assoc_sym` 投影。`Build_Bicategory'` 在 `Theory/Bicategory.v` 中仍然可用（并且类型已检查）；它只是这里没有被用作构造函数。
*)

(*
 Horizontal composition as a bifunctor `[D, E] ∏ [C, D] ⟶ [C, E]`: on objects
 it composes functors, on 2-cells it takes the Godement horizontal composite
 `nat_hcompose`.  `fmap_id` is `fmap id` juggling; `fmap_comp` is the middle-
 four interchange law, discharged from naturality of the outer transformation.
 Being the underlying functor of the bicategory's `hcompose` field, its `fmap`
 is exactly what `hcomp2` computes to. 

 --------
 作为双函子的水平组合  ` [D, E]ZZ  ∏  [C, D]ZZ  ⟶  [C, E]ZZ ` ：在对象上它组合函子，在 2-胞上它取 Godement 水平组合  `nat_hcompose` 。`fmap_id` 是 `fmap id` 的杂耍；`fmap_comp` 是中间四交换律，由外部变换的自然性引出。作为双范畴 `hcompose` 场的基础函子，其 `fmap` 正是 `hcomp2` 所计算的内容。
*)
#[local] Obligation Tactic := idtac.
Program Definition Cat_Hcompose {C D E : Category} :
  ([D, E] ∏ [C, D]) ⟶ [C, E] := {|
  fobj := fun p => fst p ◯ snd p;
  fmap := fun p q m => nat_hcompose (fst m) (snd m)
|}.
Next Obligation.
  intros C D E [P1 P2] [Q1 Q2] [α β] [α' β'] [Hα Hβ]; simpl; intro o.
  now rewrite (Hα (Q2 o)), (Hβ o).
Qed.
Next Obligation.
  intros C D E [P1 P2]; simpl; intros; cat.
Qed.
Next Obligation.
  intros C D E [P1 P2] [Q1 Q2] [R1 R2] [α β] [α' β']; simpl; intros.
  rewrite fmap_comp, !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  symmetry; apply naturality.
Qed.

(*
 The bicategory coherence laws for Cat, proven componentwise in the functor
 category `[C, D]`.  Under the crossed dictionary the unitor naturalities, the
 triangle and the pentagon all reduce to `fmap id` bookkeeping closed by `cat`;
 the associator naturality additionally needs `fmap_comp`.  These are exactly
 the field statements of `Bicategory` with `hcomp2 = nat_hcompose`,
 `hunit_left = nat_ρ`, `hunit_right = nat_λ`, `hassoc = (nat_α …)⁻¹`. 

 --------
 Cat 的双范畴相容性定律，在函子范畴 ` [C, D]ZZ ` 中逐分量证明。在交叉词典下，单位子自然性、三角和五边形都简化为由 `cat` 关闭的 `fmap id` 的记账；同时，结合子自然性还需要 `fmap_comp`。这正是带有 `hcomp2 = nat_hcompose`、`hunit_left = nat_ρ`、`hunit_right = nat_λ`、`hassoc = (nat_α …)⁻¹` 的 `Bicategory` 的场陈述。
*)

Lemma Cat_hunit_left_natural (C D : Category) (f f' : C ⟶ D) (η : f ⟹ f') :
  nat_compose η (to (nat_ρ f))
  ≈ nat_compose (to (nat_ρ f')) (nat_hcompose (nat_id (F:=Id)) η).
Proof. simpl; intros; cat. Qed.

Lemma Cat_hunit_right_natural (C D : Category) (f f' : C ⟶ D) (η : f ⟹ f') :
  nat_compose η (to (nat_λ f))
  ≈ nat_compose (to (nat_λ f')) (nat_hcompose η (nat_id (F:=Id))).
Proof. simpl; intros; cat. Qed.

Lemma Cat_hassoc_natural (W X Y Z : Category)
  (h h' : Y ⟶ Z) (g g' : X ⟶ Y) (f f' : W ⟶ X)
  (θ : h ⟹ h') (γ : g ⟹ g') (η : f ⟹ f') :
  nat_compose (nat_hcompose θ (nat_hcompose γ η)) (from (nat_α f g h))
  ≈ nat_compose (from (nat_α f' g' h')) (nat_hcompose (nat_hcompose θ γ) η).
Proof. simpl; intros; rewrite !fmap_id, fmap_comp; cat. Qed.

Lemma Cat_triangle (X Y Z : Category) (g : Y ⟶ Z) (f : X ⟶ Y) :
  nat_hcompose (to (nat_λ g)) (nat_id (F:=f))
  ≈ nat_compose (nat_hcompose (nat_id (F:=g)) (to (nat_ρ f))) (from (nat_α f Id g)).
Proof. simpl; intros; cat. Qed.

Lemma Cat_pentagon (V W X Y Z : Category)
  (k : Y ⟶ Z) (h : X ⟶ Y) (g : W ⟶ X) (f : V ⟶ W) :
  nat_compose (nat_compose (nat_hcompose (nat_id (F:=k)) (from (nat_α f g h)))
                           (from (nat_α f (h ◯ g) k)))
              (nat_hcompose (from (nat_α g h k)) (nat_id (F:=f)))
  ≈ nat_compose (from (nat_α (g ◯ f) h k)) (from (nat_α f g (k ◯ h))).
Proof. simpl; intros; cat. Qed.

(*
 Cat as a bicategory.  The structural fields are `[C, D]`'s own projections
 (so `bicat C D ≡ [C, D]` definitionally), `hcompose := Cat_Hcompose`, the
 unitors/associator come from `nat_ρ`/`nat_λ`/`(nat_α)⁻¹`, and the coherence
 laws are the lemmas above.  `bi1id := Id`; `bi2id/vcompose/…` project from
 `[C, D]`.  A `Definition`, one universe level up, never registered. 

 --------
 作为二范畴的 Cat。结构字段是 ` [C, D]ZZ ` 自己的投影（因此 `bicat C D ≡  [C, D]ZZ ` 是定义上的），`hcompose := Cat_Hcompose`，单位子/结合子来自 `nat_ρ` / `nat_λ` / `(nat_α)⁻¹`，协调律是上面的引理。`bi1id := Id`；`bi2id/vcompose/…` 从 ` [C, D]ZZ ` 投影。一个 `Definition`，比上一个宇宙层级高，从未注册。
*)
Definition Cat_Bicategory : Bicategory :=
  Build_Bicategory
    Category
    (fun C D => @obj (@Fun C D))                 (* bi1cell   *)
    (fun C D => @hom (@Fun C D))                 (* bi2cell   *)
    (@Id)                                        (* bi1id     *)
    (fun C D => @homset (@Fun C D))              (* bi2homset / 同志 *)
    (fun C D => @id (@Fun C D))                  (* bi2id     *)
    (fun C D => @compose (@Fun C D))             (* vcompose / vcompose *)
    (fun C D => @compose_respects (@Fun C D))    (* vcompose_respects / vcompose_尊重 *)
    (fun C D => @id_left (@Fun C D))             (* bi2id_left / bi2id_左 *)
    (fun C D => @id_right (@Fun C D))            (* bi2id_right / bi2id_右 *)
    (fun C D => @comp_assoc (@Fun C D))          (* vcompose_assoc / vcompose_结合 *)
    (fun C D => @comp_assoc_sym (@Fun C D))      (* vcompose_assoc_sym / v组合_结合_对称 *)
    (@Cat_Hcompose)                              (* hcompose / 组合 *)
    (fun C D f => nat_ρ f)                        (* hunit_left / 左单位 *)
    (fun C D f => nat_λ f)                        (* hunit_right / 右单位 *)
    (fun W X Y Z h g f => iso_sym (nat_α f g h))  (* hassoc *)
    Cat_hunit_left_natural
    Cat_hunit_right_natural
    Cat_hassoc_natural
    Cat_triangle
    Cat_pentagon.
