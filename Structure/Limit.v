Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   Wikipedia：「设 F : J ⟶ C 是范畴 C 中形状为 J 的图。到 F 的锥是 C 的对象 N 连同
   由 J 的对象 X 指标的态射族 ψX : N ⟶ F(X)，使得对 J 中每个态射 f : X ⟶ Y，
   有 F(f) ∘ ψX = ψY。

   「图 F : J ⟶ C 的极限是到 F 的锥 (L, φ)，使得对到 F 的任意其他锥 (N, ψ) 存在
   唯一态射 u : N ⟶ L 满足对所有 X ∈ J 有 φX ∘ u = ψX。

   「称锥 (N, ψ) 经锥 (L, φ) 以唯一分解 u 分解。态射 u 有时称为中介态射。」

   等价地，极限是 F 上锥范畴的终对象：每个其他锥经其唯一分解的普遍锥（nLab）。
   锥 (L, φ) 此处记为 [Cone F]（见 [Structure/Cone.v]）；[Limit] 把此类终锥与其普遍性质
   捆绑。库记号中普遍性质读作：

       ∀ N : Cone F, ∃! u : vertex_obj[N] ~> vertex_obj[L],
         ∀ x : J, φ_x ∘ u ≈ ψ_x,

   其中 φ = vertex_map[L] 是极限的腿，ψ = vertex_map[N] 是竞争锥的腿。（同一预层可表性
   视角见 [Structure/UniversalProperty/Limit.v]，证明表示 [ConePresheaf F] 等价于是极限。） *)

(*
   关于极限的来源与用途

   nLab:  https://ncatlab.org/nlab/show/colimit
   Paper: Kan, "Adjoint functors", Transactions of the American

   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Limit `(F : J ⟶ C) := {
  (* 相关说明。 （已译） *)
  limit_cone : Cone F;

  (* Universal 性质: every cone N factors through 极限 cone a
 唯一 mediating 态射 u apexes, satisfying φ_x ∘ u ≈ ψ_x for
 every x J. Here [N ~> limit_cone] is, via [vertex_obj] coercion,
 态射 vertex_obj[N] ~> vertex_obj[limit_cone] C.（已译） *)
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x
}.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class IsALimit `(F : J ⟶ C) (c : C) := {
    (* 相关说明。 （已译） *)
    limit_acone : ACone c F;
    (*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    ump_limit : ∀ N : Cone F, ∃! u : N ~> c, ∀ x : J,
    vertex_map _ ∘ u ≈ vertex_map x
  }.

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition LimitSetoid `(F : J ⟶ C) (c : C) : Setoid (IsALimit F c) :=
  {| equiv := fun l1 l2 => @limit_acone _ _ _ _ l1 ≈ @limit_acone _ _ _ _ l2 |}.
Next Obligation.
  abstract(equivalence;
           specialize X with j; specialize X0 with j;
           exact (Equivalence_Transitive _ _ _ X X0)).
Defined.

Coercion limit_cone : Limit >-> Cone.

Require Import Category.Functor.Opposite.

(* The colimit F dual notion: limit opposite diagram
 F^op, i.e. universal cocone / 始对象 范畴 of
 cocones over F (nLab, Wikipedia). （已译） *)
Definition Colimit `(F : J ⟶ C) := Limit (F^op).
