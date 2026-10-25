(*
 Strict initiality at the
 concrete categories Sets and FinSet (Seven Sketches §1.2.1 Exercise 1.25). 

 --------
 在具体范畴 Sets 和 FinSet 中的严格初性（《七个草图》第1.2.1节练习1.25）。
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.

Generalizable All Variables.

(* ---- Sets ---- *)

(*
 Seven Sketches §1.2.1 Exercise 1.25, at [Sets]: a setoid carrying a
 morphism into the empty setoid is itself isomorphic to it. 

 --------
 七个素描 §1.2.1 练习 1.25，在 [Sets]：一个承载到空集合的同态的集合自身与它同构。
*)
Definition Sets_initial_strict {x : Sets}
  (f : x ~{Sets}~> @initial_obj Sets Sets_Initial) :
  x ≅ @initial_obj Sets Sets_Initial :=
  @initial_strict Sets Sets_Cartesian Sets_Closed Sets_Initial x f.

(*
 The concrete reading Fong & Spivak give the exercise: a set with a function
 to the empty set is itself empty.  Unfolded to elements this needs no
 isomorphism at all -- the morphism's own action lands in [False] -- and
 that is exactly why the exercise is an exercise. 

 --------
 Fong 和 Spivak 给出的具体阅读练习是：一个带有指向空集的函数的集合本身是空的。展开到元素级时，这根本不需要同构 —— 该态射本身的作用落在 [False] 中 —— 这正是这个练习被称为练习的原因。
*)
Lemma Sets_initial_strict_empty {x : Sets}
  (f : x ~{Sets}~> @initial_obj Sets Sets_Initial) : carrier x -> False.
Proof. intro a; exact (f a). Qed.

(* ---- FinSet ---- *)

Definition FinSet_initial_strict {x : FinSet}
  (f : x ~{FinSet}~> @initial_obj FinSet FinSet_Initial) :
  x ≅ @initial_obj FinSet FinSet_Initial :=
  @initial_strict FinSet FinSet_Cartesian FinSet_Closed FinSet_Initial x f.

(*
 Concretely in the skeletal model: an object of [FinSet] is a natural
 number, the initial object is [0], and a morphism [x ~> 0] is a function
 [Fin.t x -> Fin.t 0].  Strictness says [x] must itself be [0], which we can
 state as a genuine equality of objects because [FinSet] is skeletal
 ([FinSet_Skeletal], Instance/FinSet/Skeleton.v). 

 --------
 在骨架模型中具体来说：[FinSet] 的一个对象是一个自然数，初始对象是 [0]，一个态射 [x ~> 0] 是一个函数 [Fin.t x -> Fin.t 0]。严格性意味着 [x] 本身必须是 [0]，我们可以将其作为对象的真正相等来陈述，因为 [FinSet] 是骨架的 ([FinSet_Skeletal]，Instance/FinSet/Skeleton.v)。
*)
Lemma FinSet_initial_strict_zero (x : nat)
  (f : x ~{FinSet}~> @initial_obj FinSet FinSet_Initial) : x = 0%nat.
Proof.
  destruct x as [|n]; [ reflexivity | ].
  exact (Fin.case0 (fun _ => S n = 0%nat) (f Fin.F1)).
Qed.
