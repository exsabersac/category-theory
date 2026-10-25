(**
* Probe for Instance/Sets/NoAdjoint.v and Adjunction/Continuity/Finite.v
      (issue #432)

    Pins the measured boundaries of the two non-existence results with
    negatives of two kinds, kept lexically apart: CONVERSION (N1: even at
    [X = 1], [fixed_product_functor 1] is NOT the identity functor as a
    record — its objects are [1 × x] — so the converse of Exercise 1 is a
    construction, not [Id ⊣ Id] read through a conversion); TYPING (N2:
    the converse's adjoint sits on the LEFT, [Id ⊣ X × −], and the other
    ascription is refused; N3: the refutation is about [Sets^op] — read at
    [Sets], whose cartesian structure IS closed, the ascription is refused
    while [Sets_Closed] is accepted as the control).  The [eq_refl]
    readbacks are positive controls: the duality scaffolding is
    conversion, the two injections of [1 + 1] are apart definitionally,
    and the fixed-product functor's arrow action is [second].  Each
    refutation was stripped one at a time in a copy of the whole file;
    the import list mirrors the target's.  UNIVERSE (N4): the four
    obstruction corollaries identify the hom levels of the two categories;
    the identification is the adjunction's own — a functor may not go DOWN
    the hom levels (Theory/Functor.v's [h1 <= h2]) — not this file's.

--------
* 探针用于 Instance/Sets/NoAdjoint.v 和 Adjunction/Continuity/Finite.v（问题 #432）

以两种类型的否定将两个不存在结果的测量边界钉住，词汇上保持分开：转换 (N1：即使在 [X = 1]，[fixed_product_functor 1] 也不是作为记录的恒等函子——它的对象是 [1 × x]——因此习题 1 的逆是一个构造，而不是通过转换读取的 [Id ⊣ Id])；类型 (N2：逆的伴随位于左侧，[Id ⊣ X × −]，而另一个归属被拒绝；N3：反驳是关于 [Sets^op]——在 [Sets] 读取时，其笛卡尔结构是闭合的，归属被拒绝，而 [Sets_Closed] 被接受作为控制)。[eq_refl] 读回是正控制：对偶支架是转换，[1 + 1] 的两个注入在定义上分开，固定积函子的箭头作用是 [second]。
每一个反驳都在整个文件的副本中一次性地被剥离；导入列表与目标的相同。UNIVERSE (N4)：四个阻塞推论识别两个范畴的同态层次；该识别是结合自身的——函子不能下降同态层次（Theory/Functor.v 的 [h1 <= h2]）——而不是这个文件的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Product.Fixed.
Require Import Category.Adjunction.Continuity.Finite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.NoAdjoint.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe432_absent_name.

(** ** A: CONVERSION — the converse is a construction / ** A: 互换 — 相反的情况是一种结构 *)

Section NotIdentity.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

(* control: the adjoint exists at [X := 1] / 控制：伴随在 [X := 1] 存在 *)
Check (Id_adj_fixed_product (1 : C) iso_id : Id ⊣ fixed_product_functor 1).

(* N1 CONVERSION: [1 × −] is not [Id] as a functor record / N1 转换：[1 × −] 作为函子记录不是 [Id] *)
Fail Example p432_fixed_product_one_not_Id :
  fixed_product_functor (1 : C) = Id := eq_refl.

End NotIdentity.

(** ** B: TYPING — sides and categories / ** B：打字——边和类别 *)

Section Sides.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.
Context (X : C) (HX : X ≅ 1).

(* control *)
Check (Id_adj_fixed_product X HX : Id ⊣ fixed_product_functor X).

(*
N2 TYPING: the identity is the LEFT adjoint of [X × −], not its right
   adjoint

--------
N2 打字：该恒等式是 [X × −] 的左伴随，而不是它的右伴随
*)
Fail Check (Id_adj_fixed_product X HX : fixed_product_functor X ⊣ Id).

End Sides.

(* control: Sets itself IS cartesian closed / 控制：设置自身为笛卡尔封闭 *)
Check (Sets_Closed : @Closed Sets Sets_Cartesian).
Check (Sets_op_not_cartesian_closed
         : ∀ CC : @Cartesian (Sets^op), @Closed (Sets^op) CC → False).

(*
N3 TYPING: the refutation is about [Sets^op]; it does not ascribe at
   [Sets]

--------
N3 打字：反驳是关于 [Sets^op] 的；它并没有归因于 [Sets]
*)
Fail Check (Sets_op_not_cartesian_closed
              : ∀ CC : @Cartesian Sets, @Closed Sets CC → False).

(** ** C: UNIVERSE — an adjunction identifies the two hom levels / ** C: 宇宙 — 一个伴随关系识别两个同态层 *)

Monomorphic Universe co ch do dh.
Monomorphic Constraint ch < dh.

Section HomLevels.

Context (Cw : Category@{co ch ch}).
Context (Dw : Category@{do dh dh}).

(* controls: the two categories, and a functor UP the hom levels / 控制：两个类别，以及上的霍姆水平的函子 UP *)
Check Cw.
Check Dw.
Check (Cw ⟶ Dw).

(*
N4 UNIVERSE: a functor DOWN the hom levels is refused (Theory/Functor.v's
   [h1 <= h2]), so an adjunction between [Cw] and [Dw] needs [ch = dh] —
   the identification the four corollaries carry is the adjunction's,
   not this file's

--------
N4 宇宙：从同态层下降的函子被拒绝（Theory/Functor.v 的 [h1 <= h2]），因此 [Cw] 与 [Dw] 之间的伴随需要 [ch = dh]——四个推论所带的识别是伴随的，而不是这个文件的
*)
Fail Check (Dw ⟶ Cw).

End HomLevels.

(** ** D: readbacks / ** D：复读 *)

Example p432_op_initial_is_terminal :
  @initial_obj (Sets^op) Sets_op_Initial = @terminal_obj Sets Sets_Terminal
  := eq_refl.

Example p432_injections_apart : (pt_inl ttt ≈ pt_inr ttt) = False := eq_refl.

Example p432_fixed_product_fmap {C : Category} `{@Cartesian C}
  (X : C) {x y : C} (g : x ~> y) :
  fmap[fixed_product_functor X] g = second g := eq_refl.

(*
the converse's transpose computes: it is pairing with the unique arrow
   to [X] — this makes [Id_adj_fixed_product]'s [Defined] load-bearing

--------
逆运算的转置计算：它与唯一的箭头配对到 [X] —— 这使得 [Id_adj_fixed_product] 的 [Defined] 承重
*)
Example p432_transpose_is_pairing {C : Category} `{CC : @Cartesian C}
  `{T : @Terminal C} (X : C) (HX : X ≅ 1) (x y : C) (f : x ~> y) :
  to (@adj _ _ _ _ (Id_adj_fixed_product X HX) x y) f = to_X X HX x △ f
  := eq_refl.

Check @right_adjoint_preserves_terminal.
Check @right_adjoint_preserves_binary_products.
Check @left_adjoint_preserves_initial.
Check @left_adjoint_preserves_binary_coproducts.
Check @times_X_has_left_adjoint_iff_terminal.
Check @fixed_product_left_adjoint_iff_terminal.

(** ** Guard block / ** 防守格挡 *)

Check @fixed_product_functor.
Check @Id_adj_fixed_product.
Check @Sets_op_not_cartesian_closed.
Check @Sets_Closed.
Check @Sets_Cartesian.
Check @Sets_op_Initial.
Check @pt_inl.
Check @pt_inr.
Check @Closed.
Check @Cartesian.
Check @Terminal.
Check @Adjunction.
Check @Id.
Check @iso_id.
Check @Sets.
Check @Category.
Check @ttt.
