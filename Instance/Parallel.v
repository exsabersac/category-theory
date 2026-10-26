Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The walking parallel pair / 步行平行对 *)

(*
 nLab: https://ncatlab.org/nlab/show/parallel+morphisms
 nLab: https://ncatlab.org/nlab/show/walking+parallel+pair
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

 This is the “walking parallel pair” (also called the free quiver), the
 category with two objects and two parallel non-identity arrows between them
 (plus the two identity morphisms):

 --- f --->
 x            y
 --- g --->

 There are no arrows y → x, and no non-identity arrows x → x or y → y, so
 composition is trivial: composing the only non-identity arrows f, g : x → y
 with an identity yields that same arrow.

 A functor [Parallel ⟶ C] is exactly a parallel pair of morphisms in C; its
 limit is their equalizer and its colimit their coequalizer.  This is the
 shape category used to build the diagrams that identify (co)equalizers. 

 --------
 nLab: https://ncatlab.org/nlab/show/parallel+morphisms
 nLab: https://ncatlab.org/nlab/show/walking+parallel+pair
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

 这是“行走的平行对”（也称自由箭簇），这是一个有两个对象且在它们之间有两条平行非恒等箭头的范畴（还有两条恒等态射）：

 --- f --->
 x            y
 --- g --->

 没有从 y → x 的箭头，也没有非恒等的 x → x 或 y → y 箭头，所以复合是平凡的：将唯一的非恒等箭头 f, g : x → y 与恒等箭头复合会得到那条相同的箭头。

 一个函子 [Parallel ⟶ C] 正好是 C 中的一对平行态射；它的极限是它们的等化器，余极限是它们的余等化器。这是建立识别（余）等化器的图所使用的形状范畴。
*)

Inductive ParObj : Set := ParX | ParY.

Inductive ParHom : bool → ParObj → ParObj → Set :=
  | ParIdX : ParHom true ParX ParX
  | ParIdY : ParHom true ParY ParY
  | ParOne : ParHom true ParX ParY
  | ParTwo : ParHom false ParX ParY.

Definition ParHom_inv_t : ∀ b x y, ParHom b x y → Prop.
Proof.
  intros [] [] [] f.
  - exact (f = ParIdX).
  - exact (f = ParOne).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = ParIdY).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact (f = ParTwo).
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
  - exact False.          (* Unused, any Prop is ok here / 未使用，这里任何道具都可以 *)
Defined.

Corollary ParHom_inv b x y f : ParHom_inv_t b x y f.
Proof. destruct f; reflexivity. Qed.

Lemma ParHom_Id_false_absurd : ∀ x, ParHom false x x → False.
Proof. inversion 1. Qed.

#[local] Hint Extern 4 =>
  match goal with
    [ H : ParHom false ?X ?X |- _ ] =>
    contradiction (ParHom_Id_false_absurd X H)
  end : parallel_laws.

Lemma ParHom_Y_X_absurd : ∀ b, ParHom b ParY ParX → False.
Proof. inversion 1. Qed.

#[local] Hint Extern 4 =>
  match goal with
    [ H : ParHom ?B ParY ParX |- _ ] =>
    contradiction (ParHom_Y_X_absurd B H)
  end : parallel_laws.

#[local] Ltac reduce :=
  repeat match goal with
  | [ H : ParObj |- _ ] => destruct H
  | [ H : bool   |- _ ] => destruct H
  end; auto.

Set Transparent Obligations.

Local Set Warnings "-intuition-auto-with-star".

Program Definition Parallel : Category := {|
  obj     := ParObj;
  hom     := fun x y => ∃ b : bool, ParHom b x y;
  (* Any hom that typechecks is valid. / 任何能够类型检查的同质都是有效的。 *)
  homset  := fun x y =>
    {| equiv := fun (f g : ∃ b : bool, ParHom b x y) => ``f = ``g |};
  id      := fun x => match x with
    | ParX => (true; ParIdX)
    | ParY => (true; ParIdY)
    end;
  compose := fun x y z (f : ∃ b : bool, ParHom b y z)
                       (g : ∃ b : bool, ParHom b x y) =>
    match x, y, z with
    | ParX, ParX, ParX => (true; ParIdX)
    | ParY, ParY, ParY => (true; ParIdY)
    | ParX, ParY, ParY => _
    | ParX, ParX, ParY => _
    | _,    _,    _    => _
    end
|}.
Next Obligation. equivalence; reduce. Qed.
Next Obligation. exact (f; X0). Defined.
Next Obligation. reduce; intuition; auto with *. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  proper.
  destruct x, y, z; simpl in *; intuition; auto with *.
Defined.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  destruct f; intuition; auto with *.
Qed.

Require Import Category.Theory.Functor.

Program Definition APair {C : Category} {x y : C} (f g : x ~> y) :
  Parallel ⟶ C := {|
  fobj := fun z => match z with
    | ParX => x
    | ParY => y
    end;
  fmap := fun z w h => match z, w with
    | ParX, ParX => id[x]
    | ParY, ParY => id[y]
    | ParX, ParY =>
      match ``h with
      | true  => f
      | false => g
      end
    | ParY, ParX => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
    end
|}.
Next Obligation. proper; reduce; simpl; intuition; auto with *. Qed.
Next Obligation. destruct x0; simpl; cat. Qed.
Next Obligation.
  destruct x0, y0, z; simpl; auto with parallel_laws; cat.
Qed.

(*
 A presheaf on this category, i.e. a contravariant functor [Parallel^op ⟶
 Sets], is given by a pair of sets G0, G1 and a pair of functions source,
 target : G1 → G0.  Identities are sent to identities.

 nLab: https://ncatlab.org/nlab/show/quiver
 Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)

 In other words, a presheaf on the parallel-pair category x ⇉ y is a graph
 (quiver): G0 is the set of vertices, G1 the set of edges, and the two arrows
 send an edge to its source and target. 

 --------
 该范畴上的一个预层，即一个逆变函子 [Parallel^op ⟶ Sets]，由一对集合 G0、G1 以及一对函数 source、target : G1 → G0 给出。恒等映射被映射到恒等映射。

 nLab: https://ncatlab.org/nlab/show/quiver
 Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)

 换句话说，平行对范畴 x ⇉ y 上的一个预层是一个图（箭图）：G0 是顶点集，G1 是边集，而两个箭头将边映射到它的起点和终点。
*)

Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Program Definition Presheaf_Graph : Parallel^op ⟶ Sets := {|
  fobj := fun z => match z with
    | ParX => {| carrier := nat |}       (* vertices / 顶点 *)
    | ParY => {| carrier := nat * nat |} (* edges *)
    end;
  fmap := fun z w h => match z, w with
    | ParX, ParX => id
    | ParY, ParY => id
    | ParX, ParY => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
    | ParY, ParX =>
      match ``h with
      | true  => {| morphism := fst |} (* source *)
      | false => {| morphism := snd |} (* target *)
      end
    end
|}.
Next Obligation.
  construct.
  - exact eq.
  - exact eq_equivalence.
Defined.
Next Obligation.
  construct.
  - exact eq.
  - exact eq_equivalence.
Defined.
Next Obligation.
  proper.
  simpl in H; subst.
  destruct x, y; simpl; auto.
  exfalso.
  now apply ParHom_Y_X_absurd in e.
Qed.
Next Obligation.
  destruct x; simpl; auto.
Qed.
Next Obligation.
  destruct x, y, z; simpl; auto.
  - exfalso.
    now apply ParHom_Y_X_absurd in X0.
  - exfalso.
    now apply ParHom_Y_X_absurd in X.
  - exfalso.
    now apply ParHom_Y_X_absurd in X.
  - exfalso.
    now apply ParHom_Y_X_absurd in X0.
Qed.
