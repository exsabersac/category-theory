Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Par.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(** * Partial maps and pointed sets / * 部分映射和有标记的集合 *)

(*
 nLab:      https://ncatlab.org/nlab/show/partial+function
 nLab:      https://ncatlab.org/nlab/show/pointed+set
 Wikipedia: https://en.wikipedia.org/wiki/Partial_function

 The header of Instance/Coq/Par.v states, in prose, that the category of
 partial maps is “equivalent (not isomorphic) to the category of pointed
 sets”: the object A realizes the pointed set A ⊔ {*}, with the adjoined
 point standing for divergence.  This file proves that sentence for the
 setoid variant, comparing Instance/Sets/Par.v's [Part] with
 Instance/Sets/Pointed.v's [PointedSets].

 The comparison functor [Part_to_Pointed] sends A to (option A, None) and a
 partial map — which in [Part] IS a total map A → option B — to the pointed
 map fixing [None].  It is FULL and FAITHFUL with no hypotheses: the
 restriction g ↦ (a ↦ g (Some a)) inverts its action on homs, and
 pointedness, i.e. g None ≈ None, is exactly the statement that nothing is
 lost by restricting.

 Essential surjectivity is another matter.  To exhibit an arbitrary pointed
 set (B, b0) as B' ⊔ {*} one must produce B' — the points of B other than
 the basepoint — and that requires deciding `b ≈ b0`.  The equivalence is
 therefore stated over an explicit hypothesis [PointedDecidablePt], with the
 quasi-inverse sending (B, b0) to the apartness sub-setoid { b : B | b ≉ b0 }
 ([Apart]).  Classically that hypothesis always holds, so what is proved
 here IS the textbook statement; constructively, the decidable objects are
 precisely where the classical picture survives.  Objects satisfying it are
 exhibited in the companion file Finite.v of this directory.

 Why the equivalence is not an isomorphism is visible in the round trip:
 [Apart] of (option A, None) is A only up to isomorphism, since its elements
 are points of [option A] paired with a proof of apartness from [None].  The
 conclusion is packaged as [EquivalenceOfCategories] through the full +
 faithful + essentially surjective assembly of
 Theory/Equivalence/FullFaithful.v, which consumes no choice principle
 because all three classes are choice-carrying in this library (the chosen
 section [prefmap], the chosen preimage object [eso_obj]). 

 --------
 nLab：https://ncatlab.org/nlab/show/partial+function
 nLab：https://ncatlab.org/nlab/show/pointed+set
 Wikipedia：https://en.wikipedia.org/wiki/Partial_function

 Instance/Coq/Par.v 的头部以散文方式说明，偏映射类别“等价（不是同构）于有基集合的类别”：对象 A 实现有基集合 A ⊔ {*}，其中附加的点表示发散。该文件为集合等价变体证明了这一句子，将 Instance/Sets/Par.v 的 [Part] 与 Instance/Sets/Pointed.v 的 [PointedSets] 进行比较。比较函子 [Part_to_Pointed] 将 A 映射为 (option A, None)，并将部分映射——在 [Part] 中是从 A → option B 的全映射——映射为固定 [None] 的指向映射。它是完全且忠实的，没有任何假设：限制 g ↦ (a ↦ g (Some a)) 可以反转它在 Hom 上的作用，而指向性，即 g None ≈ None，正是通过限制没有损失任何信息的陈述。本质满射是另一回事。要将一个任意标点集 (B, b0) 表示为 B' ⊔ {*}，必须生成 B'——即 B 中除基点之外的点——而这需要判定 `b ≈ b0`。因此该等价是在明确假设 [PointedDecidablePt] 下陈述的，准逆映射将 (B, b0) 发送到离散子集合 { b : B | b ≉ b0 } ([Apart])。从经典观点看，该假设总是成立，所以这里证明的就是教材中的陈述；从构造观点看，可判定的对象正是经典情形得以保留的地方。满足该条件的对象在本目录的辅文件 Finite.v 中有展示。为什么这个等价不是同构在往返过程中可以看出：
 [Apart] (选项A, None) 的结果只是同构意义上的 A，因为它的元素
 是 [option A] 的点，并配有与 [None] 不相交的证明。
 结论通过 Theory/Equivalence/FullFaithful.v 中的完全 + 可信 + 本质上满射的组合封装为 [EquivalenceOfCategories]，它不依赖选择公理，
 因为在这个库中所有三个类都是带选择的（选出的截面 [prefmap]，选出的原像对象 [eso_obj]）。
*)

#[local] Obligation Tactic := idtac.

(*
 The comparison functor.  A setoid [A] is sent to [A] with a fresh point
 adjoined, that fresh point being the basepoint; a partial map A ⇀ B, which
 is a total map A → option B, is sent to the pointed map that fixes the
 fresh point.  This is the functor behind the remark in Instance/Coq/Par.v's
 header that PAR is equivalent — not isomorphic — to pointed sets. 

 --------
 比较函子。一个集合等价类 [A] 被映射到 [A]，并附加一个新的点，该新点作为基点；一个部分映射 A ⇀ B（即从 A 到 option B 的全映射）被映射到固定该新点的有基点映射。这就是 Instance/Coq/Par.v 文件头中提到 PAR 与有基点集合等价（而非同构）背后的函子。
*)
Definition Part_Pointed_obj (A : SetoidObject) : PointedSetoid := {|
  pointed_setoid := {| carrier   := option (carrier A)
                     ; is_setoid := @option_setoid _ (is_setoid A) |};
  pt := Datatypes.None
|}.

(*
 The underlying function is given as a plain [Definition] rather than inside
 the [Program] record: [Program] compiles a match into the equality-carrying
 form, whose normal form on a stuck scrutinee differs syntactically from the
 plain match [Part]'s own composition reduces to, and the functor law below
 is then no longer available by conversion. 

 --------
 底层函数被作为一个普通的 [Definition] 给出，而不是在 [Program] 记录中：[Program] 将匹配编译为携带等式的形式，其在卡住的检视对象上的标准形式在语法上与普通匹配 [Part] 自身的组合减少结果不同，因此下面的函子律就无法通过转换获得。
*)
Definition part_pointed_fun {A B : SetoidObject} (f : A ~{Part}~> B)
  (o : option (carrier A)) : option (carrier B) :=
  match o with
  | Datatypes.Some a => f a
  | Datatypes.None => Datatypes.None
  end.

Program Definition Part_Pointed_map {A B : SetoidObject} (f : A ~{Part}~> B) :
  SetoidMorphism (pointed_setoid (Part_Pointed_obj A))
                 (pointed_setoid (Part_Pointed_obj B)) := {|
  morphism := part_pointed_fun f
|}.
Next Obligation.
  intros A B f; simpl; intros o o' Hoo.
  unfold part_pointed_fun.
  destruct o as [a|], o' as [a'|]; simpl in *; try contradiction.
  - exact (proper_morphism f _ _ Hoo).
  - exact Hoo.
Qed.

Definition Part_Pointed_fmap {A B : SetoidObject} (f : A ~{Part}~> B) :
  Part_Pointed_obj A ~{PointedSets}~> Part_Pointed_obj B.
Proof.
  refine (Build_PointedMorphism _ _ (Part_Pointed_map f) _).
  reflexivity.
Defined.

Program Definition Part_to_Pointed : Part ⟶ PointedSets := {|
  fobj := Part_Pointed_obj;
  fmap := fun A B f => Part_Pointed_fmap f
|}.
Next Obligation.
  intros A B f g Hfg o.
  destruct o as [a|].
  - exact (Hfg a).
  - reflexivity.
Qed.
Next Obligation.
  intros A o.
  destruct o as [a|]; reflexivity.
Qed.
Next Obligation.
  intros A B C f g o.
  destruct o as [a|]; reflexivity.
Qed.

(*
 Faithfulness: two partial maps inducing the same pointed map already agree
 at every [Some a]. 

 --------
 忠实性：两个诱导同一指向映射的部分映射在每个 [Some a] 上已经一致。
*)
Theorem Part_to_Pointed_Faithful : Faithful Part_to_Pointed.
Proof.
  constructor; intros A B f g Hfg a.
  exact (Hfg (Datatypes.Some a)).
Qed.

(* Fullness: a pointed map g : option A ~> option B restricts to the partial map [a ↦ g (Some a)], and pointedness — [g None ≈ None] — is exactly what makes the restriction lose nothing. / 充满性：一个指向映射 g ：option A ~> option B 限制到偏映射 [a ↦ g (Some a)]，而指向性 — [g None ≈ None] — 恰恰是使得这种限制不会丢失任何东西的原因。 *)
Program Definition Part_prefmap {A B : SetoidObject}
  (g : Part_Pointed_obj A ~{PointedSets}~> Part_Pointed_obj B) :
  A ~{Part}~> B := {|
  morphism := fun a => g (Datatypes.Some a)
|}.
Next Obligation.
  intros A B g; simpl; intros a a' Haa.
  exact (proper_morphism (pointed_map g)
           (Datatypes.Some a) (Datatypes.Some a') Haa).
Qed.

Program Definition Part_to_Pointed_Full : Full Part_to_Pointed := {|
  prefmap := fun A B g => Part_prefmap g
|}.
Next Obligation.
  intros A B g o.
  destruct o as [a|].
  - reflexivity.
  - symmetry.
    exact (preserves_pt g).
Qed.

(* * ** Essential surjectivity, and the equivalence / * ** 本质上的满射性，以及等价性 *)

(*
 Essential surjectivity is where decidability enters, and it is unavoidable:
 to exhibit a pointed set (B, b0) as [option] of something one must know
 which points of B are the basepoint, i.e. decide `b ≈ b0`.  Classically
 this always holds, so what follows IS the textbook statement; the
 constructive reading is that the classical picture survives exactly on the
 decidable objects. 

 --------
 本质上的满射性是可判定性出现的地方，这是不可避免的：要将一个有基点集合 (B, b0) 展示为某物的 [option]，必须知道 B 中哪些点是基点，即判定 `b ≈ b0`。在经典情况下，这总是成立，所以以下内容是教材中的陈述；构造性解读是，经典图景恰恰在可判定对象上得以保留。
*)
Definition PointedDecidablePt : Type := ∀ Z : PointedSetoid, DecidablePt Z.

(*
 The apartness sub-setoid: the points provably distinct from the basepoint,
 compared by their underlying points.  This is the candidate preimage of
 (Z, pt Z) under the comparison functor — “Z with the basepoint removed”. 

 --------
 不可接近子等价集合：可以证明与基点不同的点，通过它们的基础点进行比较。这是比较函子下 (Z, pt Z) 的候选原像——“去掉基点的 Z”.
*)
Program Definition Apart (Z : PointedSetoid) : SetoidObject := {|
  carrier   := ∃ z : carrier Z, ¬ (z ≈ pt Z);
  is_setoid := {| equiv := fun u v => `1 u ≈ `1 v |}
|}.
Next Obligation.
  intros Z.
  constructor.
  - intros u.
    reflexivity.
  - intros u v Huv.
    now symmetry.
  - intros u v w Huv Hvw.
    now transitivity (`1 v).
Qed.

Definition apart_to_fun (Z : PointedSetoid)
  (o : option (carrier (Apart Z))) : carrier Z :=
  match o with
  | Datatypes.Some u => `1 u
  | Datatypes.None => pt Z
  end.

Definition apart_from_fun (dec : PointedDecidablePt) (Z : PointedSetoid)
  (z : carrier Z) : option (carrier (Apart Z)) :=
  match dec Z z with
  | Datatypes.inl _ => Datatypes.None
  | Datatypes.inr n => Datatypes.Some (z; n)
  end.

Program Definition apart_to_map (Z : PointedSetoid) :
  SetoidMorphism (pointed_setoid (Part_Pointed_obj (Apart Z)))
                 (pointed_setoid Z) := {|
  morphism := apart_to_fun Z
|}.
Next Obligation.
  intros Z; simpl; intros o o' Hoo.
  unfold apart_to_fun.
  destruct o as [u|], o' as [u'|]; simpl in *; try contradiction.
  - exact Hoo.
  - reflexivity.
Qed.

Program Definition apart_from_map (dec : PointedDecidablePt) (Z : PointedSetoid) :
  SetoidMorphism (pointed_setoid Z)
                 (pointed_setoid (Part_Pointed_obj (Apart Z))) := {|
  morphism := apart_from_fun dec Z
|}.
Next Obligation.
  intros dec Z; simpl; intros z z' Hzz.
  unfold apart_from_fun.
  destruct (dec Z z) as [p|n], (dec Z z') as [p'|n'].
  - reflexivity.
  - destruct (n' (transitivity (symmetry Hzz) p)).
  - destruct (n (transitivity Hzz p')).
  - exact Hzz.
Qed.

Lemma apart_to_pt (Z : PointedSetoid) :
  apart_to_fun Z Datatypes.None ≈ pt Z.
Proof. reflexivity. Qed.

Lemma apart_from_pt (dec : PointedDecidablePt) (Z : PointedSetoid) :
  @equiv _ (@option_setoid _ (is_setoid (Apart Z)))
    (apart_from_fun dec Z (pt Z)) Datatypes.None.
Proof.
  unfold apart_from_fun.
  destruct (dec Z (pt Z)) as [p|n].
  - reflexivity.
  - refine (False_rect _ (n _)).
    reflexivity.
Qed.

Definition apart_to (Z : PointedSetoid) :
  Part_to_Pointed (Apart Z) ~{PointedSets}~> Z :=
  Build_PointedMorphism _ _ (apart_to_map Z) (apart_to_pt Z).

Definition apart_from (dec : PointedDecidablePt) (Z : PointedSetoid) :
  Z ~{PointedSets}~> Part_to_Pointed (Apart Z) :=
  Build_PointedMorphism _ _ (apart_from_map dec Z) (apart_from_pt dec Z).

Lemma apart_to_from (dec : PointedDecidablePt) (Z : PointedSetoid) :
  apart_to Z ∘ apart_from dec Z ≈ id.
Proof.
  intro z; simpl.
  unfold apart_from_fun.
  destruct (dec Z z) as [p|n]; simpl.
  - now symmetry.
  - reflexivity.
Qed.

Lemma apart_from_to (dec : PointedDecidablePt) (Z : PointedSetoid) :
  apart_from dec Z ∘ apart_to Z ≈ id.
Proof.
  intro o.
  destruct o as [u|]; simpl; unfold apart_from_fun.
  - destruct u as [z n]; simpl.
    destruct (dec Z z) as [p|n'].
    + refine (False_rect _ (n p)).
    + simpl.
      reflexivity.
  - destruct (dec Z (pt Z)) as [p|n].
    + reflexivity.
    + refine (False_rect _ (n _)).
      reflexivity.
Qed.

Definition apart_iso (dec : PointedDecidablePt) (Z : PointedSetoid) :
  Part_to_Pointed (Apart Z) ≅[PointedSets] Z :=
  @Build_Isomorphism PointedSets _ _ (apart_to Z) (apart_from dec Z)
    (apart_to_from dec Z) (apart_from_to dec Z).

Definition Part_to_Pointed_ESO (dec : PointedDecidablePt) :
  EssentiallySurjective Part_to_Pointed :=
  @Build_EssentiallySurjective Part PointedSets Part_to_Pointed
    Apart (apart_iso dec).

(*
 PAR is equivalent to Set_*, on the decidable objects.  This upgrades the
 remark in the header of Instance/Coq/Par.v — “equivalent (not isomorphic)
 to the category of pointed sets” — from prose to a theorem, in the setoid
 setting.  The comparison functor is fully faithful with no hypotheses at
 all; only the essential surjectivity consumes [dec]. 

 --------
 PAR 在可判定对象上等价于 Set_*。这将 Instance/Coq/Par.v 头部注释中的说明——“等价（非同构）于带基集合的范畴”——从散文升级为在集合范畴环境下的定理。比较函子在没有任何假设的情况下是全忠的；只有本质上的满射性需要消耗 [dec]。
*)
Definition pointed_part_equivalence (dec : PointedDecidablePt) :
  EquivalenceOfCategories Part_to_Pointed :=
  @FF_ESO_Equivalence Part PointedSets Part_to_Pointed
    Part_to_Pointed_Full Part_to_Pointed_Faithful (Part_to_Pointed_ESO dec).
