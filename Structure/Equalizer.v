Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Parallel.

Generalizable All Variables.

(* nLab:      https://ncatlab.org/nlab/show/equalizer
   Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   平行对 f,g : x ~> y 的等化子 = 使 f∘i ≈ g∘i 的普遍对象 e（i : e ~> x）。
   本库定义为图形状 Parallel 上的极限：Equalizer F := Limit F。
   Equalizer of parallel pair = limit of shape Parallel.
*)

(*
   关于等化子 / On equalizers

   Haskell 直觉：`{a | f a == g a}` —— 用方程切出子类型/子集。
   与积、拉回同属「极限家族」。
   Haskell intuition: `{a | f a == g a}`; same family as products/pullbacks.
*)

(*
   【Equalizer 定义展开】/ Definition walkthrough

   1) 不新开 Class：Equalizer F := Limit F，其中 F : Parallel ⟶ C。
      No new Class — specialize Limit to the Parallel shape.

   2) 形状 Parallel（Instance/Parallel.v）：两对象 ParX/ParY，两平行箭头。
      极限锥在 ParX 上的腿 = 等化映射 i；连贯性强制 f∘i ≈ g∘i；
      ump_limits 给出竞争锥的唯一中介。
      Leg at ParX is the equalizing map i; coherence forces f∘i ≈ g∘i.

   3) Coequalizer F := Colimit F（对偶）。
      Dual: coequalizer = colimit of the same shape.

   阅读：Cone → Limit → 本文件；用 APair f g 把具体平行对变成图 F。
   Read Cone → Limit → here; use APair f g to build F.
*)

Definition Equalizer {C : Category} (F : Parallel ⟶ C) := Limit F.
  (* 等化子 = Parallel 形状的极限 / equalizer as limit *)

(* 余等化子 = 同形状的余极限 / Coequalizer = colimit of same shape *)
Definition Coequalizer {C : Category} (F : Parallel ⟶ C) := Colimit F.
