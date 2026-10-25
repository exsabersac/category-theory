Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** Monadic do-notation and combinators in COQ. / COQ 中的单子 do-记法和组合子。 *)

(*
 nLab: https://ncatlab.org/nlab/show/Kleisli+category
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)

 This file is not a catalogue of concrete monads (identity, option, list,
 …). It is the generic Haskell-style surface syntax and combinator library
 for an *arbitrary* monad [M] on COQ, fixed by the section variables [m] and
 [M] below. Everything here is parametric in that monad, so it specialises to
 any concrete monad over COQ once one is supplied.

 The categorical monad (Theory/Monad.v) is presented in the join/return
 style; here we expose the equivalent bind/Kleisli surface:

 - bind          x >>= f  :=  join (fmap f x)        (m a → (a → m b) → m b)
 - Kleisli comp  f >=> g  :=  fun x => f x >>= g     ((a → m b)→(b → m c)→…)
 - reverse comp  f <=< g  :=  g >=> f

 in the value-first argument order used by Haskell (the categorical [bind]
 of Theory/Monad.v is the function-first [join ∘ fmap f]). The Kleisli laws
 ret >=> g ≈ g, f >=> ret ≈ f and (f >=> g) >=> h ≈ f >=> (g >=> h) are the
 bind-form of the monad laws and follow from the [Monad] class fields; the
 four corollaries at the end restate those fields pointwise (∀ x, _ x = _ x).

 This layer lives over Instance/Coq.v, whose function equivalence is pointwise
 Leibniz equality; reasoning that collapses functions extensionally relies on
 the pre-existing functional_extensionality axiom of that layer (the combinators
 and corollaries here add none). 

 --------
 nLab:  https://ncatlab.org/nlab/show/Kleisli+category
 Wikipedia:  https://en.wikipedia.org/wiki/Monad_(functional_programming)

 该文件不是具体单子（identity、option、list 等）的目录。它是 Haskell 风格的通用表面语法和组合子库，适用于 COQ 上的*任意*单子 [M]，由下面的段落变量 [m] 和 [M] 确定。这里的一切都是关于该单子的泛型，因此一旦提供具体单子，它可以专门化为 COQ 上的任意具体单子。

 范畴单子（Theory/Monad.v）以 join/return 风格呈现；这里我们暴露等价的 bind/Kleisli 表面形式：

 - bind          x >>= f  :=  join (fmap f x)        (m a → (a → m b) → m b)
 - Kleisli comp  f >=> g  :=  fun x => f x >>= g     ((a → m b)→(b → m c)→…)
 - reverse comp  f <=< g  :=  g >=> f在 Haskell 使用的以值为先的参数顺序中（Theory/Monad.v 的范畴形式是以函数为先）。Kleisli 定律 ret >=> g ≈ g、f >=> ret ≈ f 和 (f >=> g) >=> h ≈ f >=> (g >=> h) 是单子定律的绑定形式，并且可以从类字段推导出来；最后的四个推论以点值方式重述这些字段（∀ x, _ x = _ x）。

 这一层位于 Instance/Coq.v 之上，其函数等价性是逐点 Leibniz 相等；通过扩展性地折叠函数的推理依赖于该层预先存在的 functional_extensionality 公理（这里的组合子和推论没有增加任何新的公理）。
*)

Section Monad.

Context {m : Coq ⟶ Coq}.
Context {M : @Monad Coq m}.

Notation "()" := Datatypes.unit : category_scope.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Open Scope monad_scope.

Notation "x >>= f" :=
  (@bind Coq m _ _ _ f x) (at level 42, right associativity) : monad_scope.
Notation "x >> y" :=
  (x >>= fun _ => y)%monad (at level 81, right associativity) : monad_scope.

Definition bind {a b : Type} (x : m a) (f : a → m b) := x >>= f.

Definition kleisli_compose `(f : a → m b) `(g : b → m c) :
  a → m c := fun x => (f x >>= g)%category.

Infix ">=>" := kleisli_compose (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ f _ g) (at level 42, right associativity,
                                    format "f >=[ m ]=> g") : monad_scope.
Notation "f <=[ m ]=< g" :=
  (@kleisli_compose _ m _ _ g _ f) (at level 42, right associativity,
                                    format "f <=[ m ]=< g") : monad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

(* run x only when the guard holds, else the no-op ret tt / 仅当保护条件成立时运行 x，否则执行无操作返回 tt *)
Definition when `(b : bool) (x : m ()) : m () :=
  if b then x else ret tt.

(* run x only when the guard fails (the dual of [when]) / 仅在守卫失败时运行 x（[when] 的对偶） *)
Definition unless `(b : bool) (x : m ()) : m () :=
  if negb b then x else ret tt.

(*
   Fixpoint mapM {Applicative m} {A B} (f : A → m B) (l : list A) :
   m (list B) :=
   match l with
   | nil => ret nil
   | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
   end.

   Definition forM {Applicative m} {A B} (l : list A) (f : A → m B) :
   m (list B) := mapM f l.

   Fixpoint mapM_ {Applicative m} {A B} (f : A → m B) (l : list A) : m () :=
   match l with
   | nil => ret tt
   | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
   end.

   Definition forM_ {Applicative m} {A B} (l : list A) (f : A → m B) : m () :=
   mapM_ f l.

   --------
   Fixpoint mapM {Applicative m} {A B} (f : A → m B) (l : list A) :
   m (list B) :=
   match l with
   | nil => ret nil
   | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
   end.

   Definition forM {Applicative m} {A B} (l : list A) (f : A → m B) :
   m (list B) := mapM f l.

   Fixpoint mapM_ {Applicative m} {A B} (f : A → m B) (l : list A) : m () :=
   match l with
   | nil => ret tt
   | cons x xs => liftA2 (const id) (f x) (mapM_ f xs)
   end.

   Definition forM_ {Applicative m} {A B} (l : list A) (f : A → m B) : m () :=
   mapM_ f l.
*)

Definition foldM {A : Type} {B : Type}
  (f : A → B → m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => ret z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM {A : Type} {B : Type}
  (s : A) (l : list B) (f : A → B → m A) : m A := foldM f s l.

Definition foldrM {A : Type} {B : Type}
  (f : B → A → m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => ret z
        | cons y ys => go ys z >>= f y
      end in
  go l s.

Definition forFoldrM {A : Type} {B : Type}
  (s : A) (l : list B) (f : B → A → m A) : m A := foldrM f s l.

Fixpoint flatten `(xs : list (list A)) : list A :=
  match xs with
  | nil => nil
  | cons x xs' => app x (flatten xs')
  end.

(*
   Definition concatMapM `{Applicative m} {A B}
   (f : A → m (list B)) (l : list A) : m (list B) :=
   fmap flatten (mapM f l).

   --------
   定义 concatMapM `{Applicative m} {A B} 
   (f : A → m (list B)) (l : list A) : m (list B) := 
   fmap flatten (mapM f l).
*)

Fixpoint replicateM_ (n : nat) (x : m ()) : m () :=
  match n with
  | O => ret tt
  | S n' => x >> replicateM_ n' x
  end.

Fixpoint insertM {a} (P : a → a → m bool)
  (z : a) (l : list a) : m (list a) :=
  match l with
  | nil => ret (cons z nil)
  | cons x xs =>
    b <- P x z ;
    if (b : bool)
    then cons x <$> insertM P z xs
    else ret (cons z (cons x xs))
  end.
Arguments insertM {a} P z l : simpl never.

(*
 The four [Monad] laws restated pointwise. In COQ the homset equivalence ≈
 is ∀ x, _ x = _ x, so applying each class field at an argument turns the
 equation of morphisms into a Leibniz equality usable as a rewrite rule:
 join_fmap_join (associativity), join_fmap_ret (left unit), join_ret (right
 unit) and join_fmap_fmap (naturality of μ). 

 --------
 四条 [Monad] 法则逐点重述。在 COQ 中，同态集等价 ≈ 表示 ∀ x, _ x = _ x，因此将每个类字段应用于一个参数，会将态射的方程转化为可用作重写规则的 Leibniz 等式：join_fmap_join（结合律）、join_fmap_ret（左单位律）、join_ret（右单位律）以及 join_fmap_fmap（μ 的自然性）。
*)

Corollary join_fmap_join_x : ∀ a (x : (m ◯ m ◯ m) a),
  join (fmap join x) = join (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_join; reflexivity.
Qed.

Corollary join_fmap_ret_x : ∀ a x,
  join (fmap (ret (x:=a)) x) = x.
Proof.
  intros.
  replace x with (id x) at 2; auto.
  pose proof (@join_fmap_ret Coq m M a) as HA.
  rewrites; reflexivity.
Qed.

Corollary join_ret_x : ∀ a x,
  join (ret x) = @id _ (m a) x.
Proof.
  intros.
  pose proof (@join_ret Coq m M a) as HA.
  rewrites; reflexivity.
Qed.

Corollary join_fmap_fmap_x : ∀ (a b : Type) (f : a → b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  destruct m, M; simpl in *; intros.
  rewrite <- join_fmap_fmap; reflexivity.
Qed.

End Monad.
