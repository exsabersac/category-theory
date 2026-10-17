Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.FCoalg.

Generalizable All Variables.

(** * Catamorphisms and anamorphisms *)

(* nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Catamorphism
              https://en.wikipedia.org/wiki/Anamorphism

   当自函子 [F : C ⟶ C] 有初始 F-代数 [(μ, inα)]——[FAlg F] 的初始对象
   （Construction/FAlg.v）——其普遍性质恰是结构递归原理。对每个 F-代数 [(a, β)]
   存在唯一载体映射 [cata β : μ ~> a] 使方块

       F μ --inα--> μ
        |           |
     F(cata β)   cata β
        |           |
        v           v
       F a ---β----> a

   交换；该中介即 *catamorphism*（「fold」）。唯一性与融合律由初始对象中介 [zero]
   的唯一性推出。

   对偶地，终结 F-余代数 [(ν, outγ)]——[FCoalg F] 的终对象（Construction/FCoalg.v）——
   给出结构余递归：每个余代数 [(a, γ)] 有唯一 [ana γ : a ~> ν]（「unfold」）。
   因库把 [FCoalg F] 建为 [(FAlg (F^op))^op]，故 [@Terminal (FCoalg F)] 定义上等于
   [@Initial (FAlg (F^op))]，anamorphism 包纯由 [F^op] 的 catamorphism 包经 op-对偶得到，
   复合与 [fmap] 在表面上反向。 *)

Section Catamorphism.

Context {C : Category}.
Context (F : C ⟶ C).
Context (I : @Initial (FAlg F)).

(* The initial F-algebra: its carrier [μ] is the least fixed point of [F] and
   its structure map [inα : F μ ~> μ] is the initial structure (Lambek makes it
   an isomorphism, Theory/Lambek.v). *)
Let iobj : FAlg F := @initial_obj (FAlg F) I.
Let μ : C := `1 iobj.
Let inα : F μ ~> μ := `2 iobj.

(* The catamorphism (fold) into an F-algebra [(a, β)] is the carrier of the
   unique F-algebra mediator [iobj ~> (a; β)] provided by initiality. *)
Definition cata {a : C} (β : FAlgebra F a) : μ ~> a :=
  falg_hom[ @zero (FAlg F) I (a ; β) ].

(*
   The defining square: the mediator is an F-代数 同态, so its

   本节说明相关定义、性质与动机。 carrier commutes initial structure [inα] target structure [β].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cata_commutes {a : C} (β : FAlgebra F a) :
  cata β ∘ inα ≈ β ∘ fmap[F] (cata β).
Proof.
  exact (@falg_commutes _ _ _ _ _ _ (@zero (FAlg F) I (a ; β))).
Qed.

(*
   本节说明相关定义、性质与动机。 Uniqueness: any carrier [h] commuting same square is catamorphism.. Package [h] F-代数 同态 [iobj ~> (a;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cata_unique {a : C} (β : FAlgebra F a) (h : μ ~> a)
      (Hh : h ∘ inα ≈ β ∘ fmap[F] h) : h ≈ cata β.
Proof.
  exact (@zero_unique (FAlg F) I (a ; β)
           (@Build_FAlgHom _ F μ a inα β h Hh)
           (@zero (FAlg F) I (a ; β))).
Qed.

(*
   Fusion: a carrier map [g] of F-代数 absorbs into the fold.  The

   本节说明相关定义、性质与动机。 复合 [g ∘ cata β] is again F-代数 mediator [iobj ~> (b;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cata_fusion {a b : C} (β : FAlgebra F a) (γ : FAlgebra F b)
      (g : a ~> b) (Hg : g ∘ β ≈ γ ∘ fmap[F] g) :
  g ∘ cata β ≈ cata γ.
Proof.
  exact (@zero_unique (FAlg F) I (b ; γ)
           ((@Build_FAlgHom _ F a b β γ g Hg : (a ; β) ~{FAlg F}~> (b ; γ))
              ∘ @zero (FAlg F) I (a ; β))
           (@zero (FAlg F) I (b ; γ))).
Qed.

End Catamorphism.

Section Anamorphism.

Context {C : Category}.
Context (F : C ⟶ C).
Context (T : @Terminal (FCoalg F)).

(*
   The final F-余代数: its carrier [ν] is the greatest fixed point of [F]

   本节说明相关定义、性质与动机。 and its structure map [outγ : ν ~> F ν] is final structure.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Let tobj : FCoalg F := @terminal_obj (FCoalg F) T.
Let ν : C := `1 tobj.
Let outγ : ν ~> F ν := `2 tobj.

(* The anamorphism (unfold) out of a coalgebra [(a, γ)] is the catamorphism for
   [F^op], read back through the definitional identity of the two categories. *)
Definition ana {a : C} (γ : FCoalgebra F a) : a ~> ν :=
  @cata (C^op) (F^op) T a γ.

(* The defining square, with composition and [fmap] reversed relative to the
   algebra side; it is [cata_commutes] for [F^op] whose op-composition unfolds
   to the C-composition displayed here. *)
Lemma ana_commutes {a : C} (γ : FCoalgebra F a) :
  outγ ∘ ana γ ≈ fmap[F] (ana γ) ∘ γ.
Proof.
  exact (@cata_commutes (C^op) (F^op) T a γ).
Qed.

(* Uniqueness of the unfold, dual to [cata_unique]. *)
Lemma ana_unique {a : C} (γ : FCoalgebra F a) (h : a ~> ν)
      (Hh : outγ ∘ h ≈ fmap[F] h ∘ γ) : h ≈ ana γ.
Proof.
  exact (@cata_unique (C^op) (F^op) T a γ h Hh).
Qed.

(* Fusion for the unfold, dual to [cata_fusion]. *)
Lemma ana_fusion {a b : C} (γ : FCoalgebra F a) (δ : FCoalgebra F b)
      (g : b ~> a) (Hg : γ ∘ g ≈ fmap[F] g ∘ δ) :
  ana γ ∘ g ≈ ana δ.
Proof.
  exact (@cata_fusion (C^op) (F^op) T a b γ δ g Hg).
Qed.

End Anamorphism.
