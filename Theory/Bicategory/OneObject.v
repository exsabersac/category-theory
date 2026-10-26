Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/bicategory (§ “Examples”, delooping)
   nLab: https://ncatlab.org/nlab/show/delooping

   A monoidal category is exactly a one-object bicategory.  Delooping the single
   0-cell, the 1-cells become the objects of the monoidal category, the 2-cells
   its morphisms, vertical composition its composition, horizontal composition
   its tensor product, and the unitors/associator of the bicategory the
   unitors/associator of the monoidal structure.  This is the routine sanity
   check that every field added to [Bicategory] in Theory/Bicategory.v was
   shaped to mirror the corresponding field of [Structure/Monoidal.v]: here the
   mirror is *exact*, so the entire bicategory is assembled by directly
   projecting the monoidal data, with no wrapper on a single field.

   Dictionary (Bicategory field  ←  Monoidal field):

       bi0cell               ←  unit          (the single delooped 0-cell)
       bicat tt tt           ←  C             (the one hom-category is C itself)
       hcompose              ←  tensor
       bi1id                 ←  I
       hunit_left            ←  unit_left     (λ)
       hunit_right           ←  unit_right    (ρ)
       hassoc                ←  tensor_assoc  (α, same orientation)
       hunit_left_natural    ←  to_unit_left_natural
       hunit_right_natural   ←  to_unit_right_natural
       hassoc_natural        ←  to_tensor_assoc_natural
       hcoherence_triangle   ←  triangle_identity
       hcoherence_pentagon   ←  pentagon_identity

   DEFINITIONAL-EQUALITY NOTE (the same technique as Instance/Cat/Bicategory.v).
   The [hcompose] field wants a functor `bicat tt tt ∏ bicat tt tt ⟶ bicat tt tt`,
   whereas [tensor] has type `C ∏ C ⟶ C`.  For Coq to accept it cheaply the
   manifest hom-category `bicat tt tt` must be *definitionally* C; otherwise
   unifying two non-convertible `Category` records churns.  We obtain that
   convertibility by feeding the structural fields of the bicategory from C's own
   projections (record eta then gives `bicat tt tt ≡ C`), i.e. we build with the
   raw [Build_Bicategory], supplying C's own `comp_assoc_sym` projection directly
   (record eta breaks under the `symmetry`-derived form of [Build_Bicategory']).
   With `bicat tt tt ≡ C` in place, every coherence field type reduces to the
   corresponding monoidal axiom verbatim, so the monoidal proof plugs straight in.
   (`hcomp2 θ η` is the manifest `fmap[hcompose] (θ, η)`, which is exactly
   `bimap θ η` for `hcompose := tensor`, so the naturality and coherence
   statements land on the nose.)

--------
nLab：https://ncatlab.org/nlab/show/bicategory（§“示例”，解环）
 nLab：https://ncatlab.org/nlab/show/delooping

幺半群范畴实际上是一个单对象双范畴。 解除单曲循环
 0-细胞，1-细胞成为幺半群范畴的对象，2-细胞
 它的态射，垂直组合 它的组合，水平组合
 它的张量积，以及二范畴的单位器/关联器
 幺半群结构的单位元/缔合元。 这就是日常理智
 检查 Theory/Bcategory.v 中添加到 [Bicategory] 的每个字段是否为
 形状为镜像 [Structure/Monoidal.v] 的相应场：此处
 镜像是*精确*的，所以整个二范畴是直接组装的
 投影幺半群数据，单个字段上没有包装器。

字典（二类字段←单类字段）：

bi0cell ← 单元（单个解环 0 单元）
 bicat tt tt ← C （唯一的 hom 范畴是 C 本身）
 hcompose ← 张量
 bi1id ← 我
 hunit_left ←unit_left (λ)
 hunit_right ←unit_right (ρ)
 hassoc ←tensor_assoc（α，相同方向）
 hunit_left_natural ← to_unit_left_natural
 hunit_right_natural ← to_unit_right_natural
 hassoc_natural ← to_tensor_assoc_natural
 hcoherence_triangle ← triangle_identity
 hcoherence_pentagon ← pentagon_identity

定义相等注释（与 Instance/Cat/Bcategory.v 相同的技术）。 
[hcompose] 字段需要一个函子 `bicat tt tt ∏ bicat tt tt ⟶ bicat tt tt`，
 而 [tensor] 的类型为 `C ∏ C ⟶ C`。 为了让 Coq 便宜地接受它
 清单 hom-category `bicat tt tt` 必须*明确地* C； 否则
 统一两个不可转换的 `Category` 记录改动。 我们得到的是
 通过从 C 自身提供二范畴的结构字段来实现可转换性
 投影（记录 eta 然后给出 `bicat tt tt ≡ C`），即我们使用
 raw [Build_Bicategory]，直接提供C自己的`comp_assoc_sym`投影
 （[Build_Bicategory'] 的 `symmetry` 派生形式下的 eta 打破记录）。 
有了 `bicat tt tt ≡ C`，每种相干场类型都简化为
 逐字对应的幺半群公理，因此幺半群证明可以直接插入。 
（`hcomp2 θ η` 是清单 `fmapXPROTECT6X (θ, η)`，它恰好是
 `bimap θ η` 为 `hcompose := tensor`，因此自然性和连贯性
 陈述落在鼻子上。）
*)

Definition Monoidal_OneObject_Bicategory
    (C : Category) `{M : @Monoidal C} : Bicategory :=
  Build_Bicategory
    unit                             (* bi0cell   : one delooped 0-cell / bi0cell ：一个去环的 0-胞   *)
    (fun _ _ => @obj C)              (* bi1cell   := objects of C / bi1cell := C 的对象         *)
    (fun _ _ => @hom C)              (* bi2cell   := morphisms of C / bi2cell := C 的态射       *)
    (fun _ => @I C M)                (* bi1id     := I / bi1id     := 我                    *)
    (fun _ _ => @homset C)           (* bi2homset := hom-setoids of C / bi2homset := C 的同构集     *)
    (fun _ _ => @id C)               (* bi2id     := identities of C / bi2id := C 的恒等      *)
    (fun _ _ => @compose C)          (* vcompose  := composition of C / vcompose := C 的组合     *)
    (fun _ _ => @compose_respects C) (* vcompose_respects / vcompose_尊重                 *)
    (fun _ _ => @id_left C)          (* bi2id_left / bi2id_左                        *)
    (fun _ _ => @id_right C)         (* bi2id_right / bi2id_右                       *)
    (fun _ _ => @comp_assoc C)       (* vcompose_assoc / vcompose_结合                    *)
    (fun _ _ => @comp_assoc_sym C)   (* vcompose_assoc_sym (raw form) / vcompose_assoc_sym（原始形式）     *)
    (fun _ _ _ => @tensor C M)       (* hcompose  := tensor / hcompose  := 张量               *)
    (fun _ _ => @unit_left C M)      (* hunit_left  := λ / hunit_left  := λ                  *)
    (fun _ _ => @unit_right C M)     (* hunit_right := ρ / hunit_right := ρ                  *)
    (fun _ _ _ _ => @tensor_assoc C M)            (* hassoc := α / hassoc := α          *)
    (fun _ _ => @to_unit_left_natural C M)        (* hunit_left_natural / hunit_left_natural   *)
    (fun _ _ => @to_unit_right_natural C M)       (* hunit_right_natural / hunit_right_natural  *)
    (fun _ _ _ _ => @to_tensor_assoc_natural C M) (* hassoc_natural / hassoc_自然       *)
    (fun _ _ _ => @triangle_identity C M)         (* hcoherence_triangle / H相干三角  *)
    (fun _ _ _ _ _ => @pentagon_identity C M).    (* hcoherence_pentagon / hcoherence_五角大楼  *)

(*
Kelly's unit-coincidence, transported.  A monoidal category satisfies
   λ_I ≈ ρ_I ([unit_identity] in Structure/Monoidal/Proofs.v, a derived
   consequence of the triangle and pentagon axioms).  Under the delooping this
   is precisely the statement that the left and right unitors of the one-object
   bicategory agree on the identity 1-cell.  Because `bicat tt tt ≡ C`, the two
   unitors-at-`bi1id` are the very isomorphisms `unit_left`/`unit_right` at I, so
   the corollary is [unit_identity] lifted from the `to`-level to an equivalence
   of isomorphisms by [to_equiv_implies_iso_equiv].

--------
凯利的单位重合，被转移。一个幺半范畴满足 λ_I ≈ ρ_I（见 Structure/Monoidal/Proofs.v 中的 [unit_identity]，这是三角形公理和五边形公理的推导结果）。在退圈（delooping）下，这恰好说明单对象双范畴的一左一右单子变换在恒等 1-态射上是一致的。因为 `bicat tt tt ≡ C`，这两个在 `bi1id` 的单子变换正是 I 上的 `unit_left`/`unit_right` 的同构，因此推论是由 [to_equiv_implies_iso_equiv] 将 [unit_identity] 从 `to` 级提升为同构等价。
*)

Corollary Monoidal_OneObject_unit_coincidence
    (C : Category) `{M : @Monoidal C} :
  @hunit_left  (Monoidal_OneObject_Bicategory C) tt tt
               (@bi1id (Monoidal_OneObject_Bicategory C) tt)
    ≈ @hunit_right (Monoidal_OneObject_Bicategory C) tt tt
                   (@bi1id (Monoidal_OneObject_Bicategory C) tt).
Proof.
  apply to_equiv_implies_iso_equiv, unit_identity.
Qed.
