Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Tuple.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** 本节：Law proofs pair/tuple [A * B] instances （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma fst_snd : forall a b (z : a * b),
  (let '(x, y) := z in (x, y)) = (fst z, snd z).
Proof. intros ? ? [?]; auto. Qed.

(* The same η law lifted through [map]: since [fun x => (fst x, snd x)] the
 恒等 pairs, 映射 it over list 恒等. （已译） *)
Lemma unsplit : forall a b (xs : list (a * b)),
  map (fun x => (fst x, snd x)) xs = xs.
Proof.
  intros.
  induction xs as [|x xs IHxs]; auto; simpl.
  rewrite IHxs.
  destruct x; auto.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Tuple_Functor {x} : IsFunctor (Tuple_Functor x) := {|
  a_fmap := Tuple_Functor x;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
