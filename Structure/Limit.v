Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   图 F : J ⟶ C 的极限 = 「到 F 的锥」范畴里的终对象：普遍锥 (L, φ)，
   使得任意竞争锥 (N, ψ) 经唯一 u : N ~> L 分解，且 φ_x ∘ u ≈ ψ_x。
   A limit of F is a terminal cone over F: every other cone factors
   uniquely through it.
*)

(*
   关于极限 / On limits

   Haskell 直觉：积、等化子、拉回都是极限的特例——「用一组方程粘合数据」。
   形状 J 决定粘合方式（空图→终对象；两点无边→积；平行对→等化子）。
   Haskell intuition: products, equalizers, pullbacks are special limits —
   "glue data by equations"; shape J picks the pattern.
*)

(*
   【Class Limit 语法与字段展开】/ Syntax & field walkthrough

   1) Class Limit (F : J ⟶ C)：对固定图 F 打包「极限锥 + UMP」。
      Packages a limiting cone for a fixed diagram F.

   2) 数据 / Data
      - limit_cone : Cone F  —— 极限锥（顶点 + 腿族）；见 Cone.v
        / the limiting cone (apex + legs); see Cone.v

   3) 普遍性质 / UMP
      - ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone,
          ∀ x, vertex_map[limit_cone] ∘ u ≈ vertex_map[N] x
        每个竞争锥经唯一中介态射分解。
        Every competing cone factors via a unique mediator.

   4) 对偶：Colimit F := Limit (F^op)（余极限 = 对偶图的极限）。
      Dual: Colimit F := Limit (F^op).

   阅读顺序：先 Cone.v（ACone/Cone）→ Limit → 特例 Equalizer/Pullback。
   Read Cone.v first, then Limit, then special cases.
*)

Class Limit `(F : J ⟶ C) := {
  limit_cone : Cone F;  (* 极限锥 / limiting cone *)

  (* UMP：竞争锥经唯一 u 分解 / every cone factors via unique u *)
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x
}.

(* 指定对象 c 为 F 的极限顶点 / Designate c as limit apex of F *)
Class IsALimit `(F : J ⟶ C) (c : C) := {
    limit_acone  (* 以 c 为顶点的锥 / cone with apex c *) : ACone c F;
    (* UMP at designated apex c / UMP at c *)
    ump_limit : ∀ N : Cone F, ∃! u : N ~> c, ∀ x : J,
    vertex_map _ ∘ u ≈ vertex_map x
  }.

(* IsALimit 的 Setoid（腿点态 ≈）/ Setoid on IsALimit *)
Program Definition LimitSetoid `(F : J ⟶ C) (c : C) : Setoid (IsALimit F c) :=
  {| equiv := fun l1 l2 => @limit_acone _ _ _ _ l1 ≈ @limit_acone _ _ _ _ l2 |}.
Next Obligation.
  abstract(equivalence;
           specialize X with j; specialize X0 with j;
           exact (Equivalence_Transitive _ _ _ X X0)).
Defined.

Coercion limit_cone : Limit >-> Cone.

Require Import Category.Functor.Opposite.

(* 余极限 = 对偶图的极限 / Colimit = limit of opposite diagram *)
Definition Colimit `(F : J ⟶ C) := Limit (F^op).
