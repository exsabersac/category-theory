Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/closed+category
   nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

   本文件是 Eilenberg–Kelly 意义下「闭范畴」的进行中草稿：范畴 C 配备内部 hom 双函子

       [-, -] : C^op ∏ C ⟶ C,

   单位对象 I、自然同构 x ≅ [I, x]、恒等元 I ~> [x, x]，以及复合态射
   [y, z] ~> [[x, y], [x, z]]，服从连贯公理。与闭*幺半*范畴不同，闭范畴不必携带张量积；
   内部 hom 是原始的，不假定张量-hom 伴随 Hom(x ⊗ y, z) ≅ Hom(x, [y, z])。

   捕捉该结构的 [Closed] 类已草拟但下文注释掉（见 jww TODO）；仅两助手函子 [Curry]
   与 [Flip] 可用。完整开发的闭*幺半*范畴——带张量、求值态射 eval[a, b] : (a ⇒ b) ⊗ a ~> b
   以及 curry 普遍性质——在 [Structure.Monoidal.Closed]。 *)

(*
   关于closed categories的来源与用途

   https://ncatlab.org/nlab/show/Proceedings+of+the+Conference+on+Categorical+Algebra+-+La+Jolla+1965
   Wikipedia:
   https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
   Wikipedia: https://en.wikipedia.org/wiki/Currying
   Paper: Eilenberg, Kelly, "Closed Categories", in Proceedings of the
   Paper: Kelly, "Basic Concepts of Enriched Category Theory", LMS Lecture

   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

#[local] Set Transparent Obligations.

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

(*
   本节说明hom、同构、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End Closed.
