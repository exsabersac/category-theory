Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.

Require Import Coq.Vectors.Vector.

Import VectorNotations.

Generalizable All Variables.
Unset Universe Polymorphism.
Set Universe Minimization ToSet.
Set Transparent Obligations.

(** Shape-indexed tries as exponentials of types / 形状索引的字典树作为类型的指数 *)

(*
 A [Shape] is a binary expression tree over the constructors [Bottom],
 [Top], [Plus] and [Times].  Reading it as an arithmetic expression with
 [Bottom = 0], [Top = 1], [Plus = +] and [Times = *] gives its [size], the
 number of leaves it carries.

 [Trie a s] is the type of [a]-labelled tries of shape [s].  It realises the
 exponential [a^s], indexed not by a number but by the shape itself, so that
 the standard exponent laws hold definitionally on the constructors:

 a^0     = 1          (Unit  : Trie a Bottom)
 a^1     = a          (Id    : a -> Trie a Top)
 a^(b+c) = a^b * a^c  (Join  : Trie a b -> Trie a c -> Trie a (Plus b c))
 a^(b*c) = (a^b)^c    (Joins, the nested/representable case)

 This is the “logarithm of a type” / Naperian-functor view: a trie of shape
 [s] is isomorphic to a function from the [size s] positions, equivalently to
 a length-[size s] vector ([vec]/[trie] are mutually inverse, [vec_trie] and
 [trie_vec]).  See Gibbons, “APLicative Programming with Naperian Functors”.

 The file catalogues, for each carrier type [a]:
 - [Tries a]    : the category of tries over [a], shapes as objects;
 - [Vectors a]  : the category of vectors over [a], lengths as objects;
 each shown [Terminal] and [Cartesian] (Plus / plus are the products), and
 - [Cardinality a : Tries a -> Vectors a]   (s |-> size s, t |-> vec t)
 - [Canonicity a  : Vectors a -> Tries a]   (n |-> unsize n)
 forming the adjunction [Cardinality a ⊣ Canonicity a].  Since [vec]/[trie]
 are inverse this adjunction is in fact an equivalence presented in adjoint
 form.

 nLab (representable functor, of which these tries are an instance):
 https://ncatlab.org/nlab/show/representable+functor
 nLab (polynomial functor / container, the shapes-and-positions view):
 https://ncatlab.org/nlab/show/polynomial+functor
 Wikipedia (representable functor):
 https://en.wikipedia.org/wiki/Representable_functor
 Wikipedia (the exponent laws annotated on the [Trie] constructors):
 https://en.wikipedia.org/wiki/Exponentiation

 Note: because [Trie] is indexed by [Shape] and the homsets are quotiented
 through stdlib [Vector.t], the dependent [inversion]/[dependent induction]
 used by [Trie_left], [Trie_right] and [Tries_Cartesian]/[Tries_Terminal]
 relies on [Eqdep.Eq_rect_eq] (Streicher K / UIP on [Shape]).  This is the
 only axiom this file depends on; [Vectors], [Cardinality], [Canonicity] and
 [Card_Canon_Adjunction] are axiom-free. 

 --------
 [Shape] 是一个二元表达式树，其构造器包括 [Bottom]、[Top]、[Plus] 和 [Times]。按算术表达式读取它，使用 [Bottom = 0]、[Top = 1]、[Plus = +] 和 [Times = *]，可以得到它的 [size]，即它所携带的叶子节点的数量。

 [Trie a s] 是形状为 [s] 的 [a] 标记的字典树的类型。它实现了指数 [a^s]，其索引不是数字，而是形状本身，因此在构造器上定义上保持标准的指数法则：

 a^0     = 1          (Unit  : Trie a Bottom)
 a^1     = a          (Id    : a -> Trie a Top)
 a^(b+c) = a^b * a^c  (Join  : Trie a b -> Trie a c -> Trie a (Plus b c))
 a^(b*c) = (a^b)^c    (Joins, 嵌套/可表示情况)这是“类型的对数”/ Naperian-函子视图：形状为 [s] 的 trie 同构于来自 [size s] 位置的函数，等价于一个长度为 [size s] 的向量（[vec] / [trie] 互为逆，[vec_trie] 和 [trie_vec]）。参见 Gibbons，《使用 Naperian 函子进行应用式编程》。该文件对每种载体类型 [a] 进行目录编制：
 -  [Tries a]     ：在 [a] 上的 tries 类别，形状作为对象；
 -  [Vectors a]   ：在 [a] 上的向量类别，长度作为对象；
 每个显示 [Terminal] 和 [Cartesian]（Plus / plus 是乘积），以及
 -  [Cardinality a : Tries a -> Vectors a]   （s |-> size s, t |-> vec t）
 -  [Canonicity a  : Vectors a -> Tries a]   （n |-> unsize n）
 形成了伴随 [Cardinality a ⊣ Canonicity a]。由于 [vec] / [trie] 是逆的，这个伴随实际上是以伴随形式呈现的等价。nLab（可表示函子，这些 tries 是其一个实例）：
 https://ncatlab.org/nlab/show/representable+functor 
 nLab（多项式函子 / 容器，形状与位置的视角）：
 https://ncatlab.org/nlab/show/polynomial+functor 
 维基百科（可表示函子）：
 https://en.wikipedia.org/wiki/Representable_functor 
 维基百科（指数律注释在 [Trie] 构造子上）：
 https://en.wikipedia.org/wiki/Exponentiation 

 注意：因为 [Trie] 是由 [Shape] 索引的，并且 hom 集通过 stdlib [Vector.t] 被商化，
 [Trie_left]、[Trie_right] 和 [Tries_Cartesian] / [Tries_Terminal] 使用的依赖 [inversion] / [dependent induction] 
 依赖于 [Eqdep.Eq_rect_eq]（Streicher K / 在 [Shape] 上的 UIP）。这是
 该文件唯一依赖的公理；[Vectors]、[Cardinality]、[Canonicity] 和
 [Card_Canon_Adjunction] 是无公理的。
*)

(* These two lemmas are missing in Coq 8.11 and earlier. / 这两个引理在 Coq 8.11 及更早版本中缺失。 *)
Lemma map_id A: ∀ n (v : t A n),
  map (fun x => x) v = v.
Proof.
  induction v; simpl; auto.
  now rewrite IHv.
Qed.

Lemma map_map A B C: ∀ (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
  induction v; simpl; auto.
  now rewrite IHv.
Qed.

Fixpoint concat `(xs : t (t a n) m) : t a (m * n) :=
  match xs with
  | nil _ => nil a
  | cons _ hd n tl => append hd (concat tl)
  end.

Program Fixpoint group_dep {a : Type} (m n : nat) (xs : t a (m * n)) :
  ∃ xss : t (t a n) m, xs = concat xss :=
  match m with
  | O => (Vector.nil (t a n); _)
  | S m' =>
      match splitat n xs with
      | (ys, zs) => let (zss, H) := group_dep m' n zs
                    in (cons _ ys _ zss; _)
      end
  end.
Next Obligation.
  now destruct xs using case0.
Qed.
Next Obligation.
  symmetry in Heq_anonymous.
  now apply append_splitat.
Qed.

Definition group {a : Type} (m n : nat) (xs : t a (m * n)) : t (t a n) m :=
  `1 (group_dep m n xs).

Lemma map_append `(f : a → b) `(xs : t a n) `(ys : t a m) :
  map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  induction xs; simpl; auto.
  now rewrite IHxs.
Qed.

Lemma map_concat `(f : a → b) `(xs : t (t a n) m) :
  map f (concat xs) = concat (map (map f) xs).
Proof.
  induction xs; simpl; auto.
  rewrite <- IHxs.
  now apply map_append.
Qed.

(**************************************************************************)

(*
 Shapes: the free algebra on 0, 1, sum and product, with [size] reading a
 shape as a natural number and [unsize] picking the canonical shape
 [Top + ... + Top] of a given size.  Two shapes are equivalent when they
 have the same size. 

 --------
 形状：在 0、1、加法和乘法上的自由代数，其中 [size] 将形状读取为自然数，[unsize] 选择给定大小的规范形状 [Top + ... + Top]。当两个形状具有相同的大小时，它们是等价的。
*)

Inductive Shape : Set :=
  | Bottom
  | Top
  | Plus (x y : Shape)
  | Times (x y : Shape).

Fixpoint size (s : Shape) : nat :=
  match s with
  | Bottom => 0
  | Top => 1
  | Plus x y => size x + size y
  | Times x y => size x * size y
  end.

Fixpoint unsize (n : nat) : Shape :=
  match n with
  | O => Bottom
  | S n => Plus Top (unsize n)
  end.

Theorem size_unsize n : size (unsize n) = n.
Proof. now induction n; simpl; auto. Qed.

#[export]
Program Instance Shape_Setoid : Setoid Shape := {|
  equiv := λ x y, size x = size y
|}.

(**************************************************************************)

(*
 Tries: the exponential [a^s], with [vec]/[trie] the isomorphism to
 length-[size s] vectors and [Trie_map] making [Trie _ s] a functor in [a]. 

 --------
 尝试：指数[a^s]，其中[vec] / [trie]是到长度[size s]向量的同构，并且[Trie_map]使[Trie _ s]在[a]中成为一个函子。
*)

Unset Uniform Inductive Parameters.

Inductive Trie (a : Type) : Shape → Type :=
  | Unit : Trie a Bottom                      (* a^0 = 1 *)
  | Id : a → Trie a Top                      (* a^1 = a *)
  | Join {x y} :
    Trie a x → Trie a y → Trie a (Plus x y) (* a^(b+c) = a^b * a^c *)
  | Joins {x y} :
    (* This allows us to positively express Trie (Trie a y) x / 这让我们能够正面表达 Trie（Trie a y）x *)
    ∀ z, (z → Trie a y) ->
         Trie z x → Trie a (Times x y).      (* a^(b*c) = (a^b)^c *)

Arguments Unit {a}.
Arguments Id {a} _.
Arguments Join {a x y} _ _.
Arguments Joins {a x y} _ _ _.

Fixpoint vec `(x : Trie a s) : Vector.t a (size s) :=
  match x with
  | Unit         => nil a
  | Id x         => cons a x 0 (nil a)
  | Join xs ys   => vec xs ++ vec ys
  | Joins _ k xs => concat (map (vec ∘ k) (vec xs))
  end.

Program Fixpoint trie {a : Type} `(x : Vector.t a (size s)) : Trie a s :=
  match s with
  | Bottom    => Unit
  | Top       => Id (@hd a 0 x)
  | Plus s t  => let (ys, zs) := splitat (size s) x
                 in Join (trie ys) (trie zs)
  | Times s t => Joins (Vector.t a (size t)) trie
                       (trie (group (size s) (size t) x))
  end.

Fixpoint vec_trie {a : Type} `(x : Vector.t a (size s)) : vec (trie x) = x.
Proof.
  induction s; simpl in *.
  - now induction x using case0.
  - induction x using caseS'; simpl.
    now induction x using case0.
  - destruct (splitat (size s1) x) eqn:Heqe; simpl in *.
    apply append_splitat in Heqe; subst.
    now rewrite IHs1, IHs2.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    subst.
    rewrite vec_trie.
    clear -vec_trie.
    induction x0; simpl; auto.
    rewrite IHx0.
    now rewrite vec_trie.
Qed.

Definition Trie_equiv {s : Shape} {a : Type} (x y : Trie a s) : Type :=
  vec x = vec y.

Arguments Trie_equiv {s a} x y /.

#[export]
Program Instance Trie_Setoid {s : Shape} {a : Type} : Setoid (Trie a s) := {|
  equiv := Trie_equiv
|}.
Next Obligation.
  unfold Trie_equiv.
  constructor; repeat intro; intuition.
  now rewrite H, H0.
Qed.

#[export]
Program Instance vec_Proper {a : Type} {s : Shape} :
  Proper (equiv ==> eq) (@vec a s).

Theorem trie_vec `(x : Trie a s) : trie (vec x) ≈ x.
Proof. now simpl; rewrite vec_trie. Qed.

Fixpoint Trie_map {s : Shape} `(f : a → b) (x : Trie a s) : Trie b s :=
  match x with
  | Unit => Unit
  | Id x => Id (f x)
  | Join xs ys => Join (Trie_map f xs) (Trie_map f ys)
  | Joins z k xs => Joins z (Trie_map f ∘ k) xs
  end.

Fixpoint Trie_map_flatten `(f : a → b) `(t : Trie a s) :
  vec (Trie_map f t) = map f (vec t).
Proof.
  induction t; try (simpl; reflexivity); simpl.
  - rewrite map_append.
    now rewrite IHt1, IHt2.
  - rewrite map_concat.
    rewrite map_map.
    clear -Trie_map_flatten.
    induction (vec t0); simpl; auto.
    rewrite IHt1.
    now rewrite Trie_map_flatten.
Qed.

#[export]
Program Instance Trie_map_Proper {s : Shape} `{f : a → b} :
  Proper (equiv ==> equiv) (@Trie_map s a b f).
Next Obligation.
  proper.
  rewrite !Trie_map_flatten.
  now rewrite X.
Qed.

(**************************************************************************)

(*
 The categories [Tries a] and [Vectors a], their terminal/cartesian
 structure, and the adjunction [Cardinality a ⊣ Canonicity a] between them. 

 --------
 类别 [Tries a] 和 [Vectors a]，它们的终端/笛卡尔结构，以及它们之间的伴随 [Cardinality a ⊣ Canonicity a]。
*)

#[export]
Program Instance Trie_Functor (s : Shape) : Coq ⟶ Sets := {|
  fobj := λ a,     {| carrier   := Trie a s
                    ; is_setoid := Trie_Setoid |};
  fmap := λ _ _ f, {| morphism := Trie_map f
                    ; proper_morphism := Trie_map_Proper |}
|}.
Next Obligation.
  proper.
  rewrite !Trie_map_flatten.
  induction (vec x1); simpl; auto.
  now rewrite H, IHt.
Qed.
Next Obligation.
  rewrite Trie_map_flatten.
  now rewrite map_id.
Qed.
Next Obligation.
  rewrite !Trie_map_flatten.
  now rewrite map_map.
Qed.

Program Definition Tries (a : Type) : Category := {|
  obj     := Shape;
  hom     := λ x y,
    (* This is a setoid morphism within a smaller category than Coq. / 这是一个在比 Coq 更小的范畴中的集合同态。 *)
    ∃ f : Trie a x → Trie a y, Proper (equiv ==> equiv) f;
  homset  := λ _ _, {| equiv := fun f g => ∀ x, `1 f x ≈ `1 g x |};
  id      := λ _, (λ x, x; _);
  compose := _
|}.
Next Obligation.
  equivalence.
  simpl in *.
  now repeat match goal with [ H : context [_ = _] |- _ ] => rewrite H; clear H end.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H.
  now apply e1, H0.
Qed.

Definition Trie_case0
           {A : Type} (P : Trie A Bottom → Type)
           (Punit : P Unit) : ∀ v : Trie A Bottom, P v.
Proof. now dependent induction v. Qed.

Definition Trie_left {a : Type} {X Y : Shape} (v : Trie a (Plus X Y)) : Trie a X.
Proof. now inversion v; subst. Defined.

Definition Trie_right {a : Type} {X Y : Shape} (v : Trie a (Plus X Y)) : Trie a Y.
Proof. now inversion v; subst. Defined.

Lemma vec_Trie_left {a : Type} {X Y : Shape} (v : Trie a (Plus X Y)) :
  vec (Trie_left v) = fst (splitat (size X) (vec v)).
Proof.
  dependent induction v; simpl in *.
  simpl_eq.
  now rewrite splitat_append.
Qed.

Lemma vec_Trie_right {a : Type} {X Y : Shape} (v : Trie a (Plus X Y)) :
  vec (Trie_right v) = snd (splitat (size X) (vec v)).
Proof.
  dependent induction v; simpl in *.
  simpl_eq.
  now rewrite splitat_append.
Qed.

Program Definition Tries_Terminal (a : Type) : @Terminal (Tries a) := {|
  terminal_obj := Bottom;
  one          := λ _, (λ _, Unit; _)
|}.
Next Obligation.
  f_equal.
  remember (f x0) as i.
  remember (g x0) as j.
  clear.
  induction i using Trie_case0.
  induction j using Trie_case0.
  reflexivity.
Qed.

Program Definition Tries_Cartesian (a : Type) : @Cartesian (Tries a) := {|
  product_obj := Plus;
  fork        := λ _ _ _ f g, (λ x, Join (`1 f x) (`1 g x); _);
  exl         := λ _ _, (Trie_left; _);
  exr         := λ _ _, (Trie_right; _)
|}.
Next Obligation.
  proper.
  f_equal.
  - now apply X0.
  - now apply X.
Qed.
Next Obligation.
  proper.
  rewrite !vec_Trie_left.
  now do 2 f_equal.
Qed.
Next Obligation.
  proper.
  rewrite !vec_Trie_right.
  now do 2 f_equal.
Qed.
Next Obligation.
  proper.
  simpl in *.
  now rewrite H, H0.
Qed.
Next Obligation.
  split; intros.
  - split; intros.
    + now rewrite vec_Trie_left, H, splitat_append.
    + now rewrite vec_Trie_right, H, splitat_append.
  - destruct H.
    specialize (e x0).
    specialize (e0 x0).
    rewrite vec_Trie_left in e.
    rewrite vec_Trie_right in e0.
    rewrite <- e, <- e0.
    apply append_splitat.
    now apply surjective_pairing.
Qed.

Program Definition Vectors (a : Type) : Category := {|
  obj     := nat;
  hom     := λ x y, Vector.t a x → Vector.t a y;
  homset  := λ x y, @funext_Setoid _ (Vector.t a) x y (eq_Setoid (t a y));
  id      := λ _ x, x;
  compose := λ _ _ _ f g x, f (g x)
|}.
Next Obligation.
  proper.
  now rewrite H0, H.
Qed.

Program Definition Vectors_Terminal (a : Type) : @Terminal (Vectors a) := {|
  terminal_obj := 0%nat;
  one          := λ _ _, nil a
|}.
Next Obligation.
  remember (f x0) as i.
  remember (g x0) as j.
  clear.
  induction i using case0.
  induction j using case0.
  reflexivity.
Qed.

Program Definition Vectors_Cartesian (a : Type) : @Cartesian (Vectors a) := {|
  product_obj := plus;
  fork        := λ _ _ _ f g, λ x, f x ++ g x;
  exl         := λ x _, fst ∘ splitat x;
  exr         := λ x _, snd ∘ splitat x
|}.
Next Obligation.
  proper.
  now rewrite H, H0.
Qed.
Next Obligation.
  split; intros.
  - split; intros;
    now rewrite H, splitat_append.
  - destruct H.
    rewrite <- e, <- e0.
    apply append_splitat.
    now apply surjective_pairing.
Qed.

Program Definition Cardinality (a : Type) : Tries a ⟶ Vectors a := {|
  fobj := size;
  fmap := λ _ _ f, vec ∘ `1 f ∘ trie
|}.
Next Obligation.
  now rewrite vec_trie.
Qed.
Next Obligation.
  apply X0; simpl.
  now rewrite vec_trie.
Qed.

Definition sized `(x : t a (size (unsize n))) : t a n.
Proof. now rewrite size_unsize in x. Defined.

Definition resized `(x : t a n) : t a (size (unsize n)).
Proof. now rewrite <- size_unsize in x. Defined.

Lemma resized_sized `(x : t a (size (unsize n))) : resized (sized x) = x.
Proof.
  unfold sized, resized.
  now destruct (size_unsize n); simpl.
Qed.

Lemma sized_resized `(x : t a n) : sized (resized x) = x.
Proof.
  unfold sized, resized.
  Import EqNotations.
  assert (∀ x, rew [t a] size_unsize n in
               rew <- [t a] size_unsize n in x = x). {
    now destruct (size_unsize n); simpl.
  }
  now rewrite H.
Qed.

Program Definition Canonicity (a : Type) : Vectors a ⟶ Tries a := {|
  fobj := unsize;
  fmap := λ _ _ f, (trie ∘ resized ∘ f ∘ sized ∘ vec; _)
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  now rewrite H.
Qed.
Next Obligation.
  rewrite resized_sized.
  now apply vec_trie.
Qed.
Next Obligation.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.

Program Definition Card_Canon_Adjunction a :
  Cardinality a ⊣ Canonicity a := {|
  adj := λ x y,
    {| to   := {| morphism := λ f, (trie ∘ resized ∘ f ∘ vec; _) |}
     ; from := {| morphism := λ f, sized ∘ vec ∘ _ ∘ trie |} |}
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  now rewrite H.
Qed.
Next Obligation.
  proper.
  simpl in *.
  now rewrite H.
Qed.
Next Obligation.
  rewrite !vec_trie.
  rewrite resized_sized.
  apply X.
  now apply trie_vec.
Qed.
Next Obligation.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.
Next Obligation.
  rewrite !vec_trie.
  do 2 f_equal.
  apply X.
  now apply trie_vec.
Qed.
Next Obligation.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.
Next Obligation.
  f_equal.
  apply X0; simpl.
  now rewrite trie_vec.
Qed.
Next Obligation.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.
