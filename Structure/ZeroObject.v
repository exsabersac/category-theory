Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* * * Zero objects and zero morphisms / * * 零对象和零态射 *)

(*
 nLab:      https://ncatlab.org/nlab/show/zero+object
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 A zero object in a category C is an object that is at once initial and
 terminal (nLab; Wikipedia calls it a "null object").  In this setoid-based
 library we do not demand that one chosen object literally play both roles:
 [ZeroObject] packages a terminal structure, an initial structure, and an
 isomorphism [zero_coincide] between the chosen initial object 0 and the
 chosen terminal object 1.  Since initial (resp. terminal) objects are
 unique up to unique isomorphism -- [initial_unique] and [terminal_unique],
 with [initial_arrow_unique] / [terminal_arrow_unique] supplying the
 "unique" half -- this is no loss of generality, and it avoids any appeal to
 equality of objects.  [zero_object_unique] below is the corresponding
 statement for zero objects themselves.

 [zero_coincide] is a FIELD, i.e. data, so a caller must supply it; the
 header used to justify that by rhetoric alone.  It need not be assumed:
 [terminal_initial_arrow_iso] below (Riehl, CTiC, Exercise 1.6.i) shows
 that ANY morphism 1 ~> 0 is already an isomorphism, and
 [ZeroObject_from_arrow] turns one such morphism into the whole
 [ZeroObject] record.  That is the constructive source of the coincidence,
 and until it was added nothing in tree derived one -- the sole inhabitant,
 [CMon_Zero] (Instance/CMon/Biproduct.v), supplies [iso_id] only because
 its two chosen objects are literally the same term.

 Every pair of objects x, y then acquires a canonical zero morphism
 x ~> y, obtained by tunnelling through the zero object:

 x ~> 1 ~> 0 ~> y

 first the unique map into 1, then the coincidence isomorphism read
 backwards, then the unique map out of 0.  Zero morphisms absorb
 composition on both sides ([zero_mor_left], [zero_mor_right]), and any
 morphism factoring through the zero object in this way is the zero
 morphism ([zero_mor_unique]). 

 --------
 nLab:       https://ncatlab.org/nlab/show/zero+object 
 维基百科:  https://en.wikipedia.org/wiki/Initial_and_terminal_objects 

 类别 C 中的零对象是同时作为初始对象和终对象的对象（nLab；维基百科称之为“零对象”）。在这个基于集合等价类的库中，我们不要求一个选择的对象字面上同时扮演这两个角色：[ZeroObject] 包含一个终结构、一个初结构，以及一个 [zero_coincide] 的同构，它连接所选择的初始对象 0 和所选择的终对象 1。由于初始对象（或终对象）在唯一同构下是唯一的——[initial_unique] 和 [terminal_unique]，并且 [initial_arrow_unique] / [terminal_arrow_unique] 提供了“唯一”的部分——这并不会损失一般性，同时也避免了对对象相等性的任何诉求。下面的 [zero_object_unique] 是零对象本身的相应表述。[zero_coincide] 是一个域，即数据，因此调用者必须提供它；标题仅凭修辞来证明这一点。这不需要被假设：下面的 [terminal_initial_arrow_iso]（Riehl, CTiC, 练习 1.6.i）显示，任何态射 1 ~> 0 已经是一个同构，而 [ZeroObject_from_arrow] 将这样的一个态射转化为整个 [ZeroObject] 记录。这就是巧合的构造来源，在它被添加之前，树中没有任何东西能够导出它 —— 唯一的存在者 [CMon_Zero]（Instance/CMon/Biproduct.v）仅在其两个选定对象字面上相同的情况下提供 [iso_id]。  

 每一对对象 x, y 然后会获得一个标准的零态射 x ~> y，通过零对象进行穿越获得：  

 x ~> 1 ~> 0 ~> y首先是到 1 的唯一映射，然后是逆读的同构重合映射，然后是从 0 的唯一映射。零态射在两边吸收组合（[zero_mor_left]，[zero_mor_right]），任何以这种方式通过零对象分解的态射都是零态射（[zero_mor_unique]）。
*)

Class ZeroObject (C : Category) := {
  zero_terminal : @Terminal C;
  zero_initial  : @Initial C;

  (*
 The chosen initial and terminal objects coincide up to isomorphism.
 Stating the coincidence as an iso, rather than as an equality of
 objects, keeps the notion setoid-honest and transportable. 

 --------
 所选的初始对象和终端对象在同构意义下是重合的。将这种重合表述为同构（iso），而不是对象的相等，可以保持这一概念在集合论中的严格性并且便于传递。
*)
  zero_coincide : @initial_obj C zero_initial ≅ @terminal_obj C zero_terminal
}.

(*
 A convenience name for the zero object itself.  We take the terminal
 side as the representative; [zero_coincide] carries us to the initial
 side whenever needed.  Note: the name [zero] belongs to Initial's
 accessor 0 ~> x, so the object gets the distinct name [zero_obj]. 

 --------
 零对象本身的一个便利名称。我们以终端端为代表；[zero_coincide] 在需要时将我们带到初始端。注意：名称 [zero] 属于初始对象的访问器 0 ~> x，因此该对象获得了独特的名称 [zero_obj]。
*)
Definition zero_obj {C : Category} `{Z : @ZeroObject C} : C :=
  @terminal_obj C zero_terminal.

(* The zero morphism x ~> y: into 1, across the coincidence iso, out of 0. / 零态射 x ~> y：进入 1，通过同构重合，输出 0。 *)
Definition zero_mor {C : Category} `{Z : @ZeroObject C} {x y : C} : x ~> y :=
  @zero C (@zero_initial C Z) y
    ∘ from (@zero_coincide C Z)
    ∘ @one C (@zero_terminal C Z) x.

(*
 Postcomposition absorbs: f ∘ 0 ≈ 0.  After reassociation the composite
 f ∘ zero is a morphism out of the initial object, so [zero_comp]
 collapses it to zero, and the zero morphism reassembles. 

 --------
 后组合吸收：f ∘ 0 ≈ 0。在重新关联后，复合 f ∘ zero 是一个从初始对象出发的态射，因此 [zero_comp] 将其压缩为零，零态射重新组合。
*)
Lemma zero_mor_left {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : y ~> z) :
  f ∘ @zero_mor C Z x y ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite !comp_assoc.
  now rewrite (@zero_comp C (@zero_initial C Z) y z f).
Qed.

(*
 Precomposition absorbs: 0 ∘ f ≈ 0.  Dually, after reassociation the
 composite one ∘ f is a morphism into the terminal object, so [one_comp]
 collapses it to one. 

 --------
 前合成吸收：0 ∘ f ≈ 0。 相反地，在重新结合之后，复合 one ∘ f 是一个到终对象的态射，因此 [one_comp] 将其简化为 one。
*)
Lemma zero_mor_right {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : x ~> y) :
  @zero_mor C Z y z ∘ f ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite <- !comp_assoc.
  now rewrite (@one_comp C (@zero_terminal C Z) x y f).
Qed.

(*
 Any morphism factoring through the zero object is the zero morphism:
 the leg into 1 is unique by [one_unique], and the leg out of 0 is
 unique by [zero_unique]. 

 --------
 任何通过零对象分解的态射都是零态射：进入 1 的腿由 [one_unique] 唯一确定，而从 0 出来的腿由 [zero_unique] 唯一确定。
*)
Lemma zero_mor_unique {C : Category} `{Z : @ZeroObject C} {x y : C}
  (g : x ~> @terminal_obj C (@zero_terminal C Z))
  (h : @initial_obj C (@zero_initial C Z) ~> y) :
  (h ∘ from (@zero_coincide C Z)) ∘ g ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite (@one_unique C (@zero_terminal C Z) x g
             (@one C (@zero_terminal C Z) x)).
  rewrite (@zero_unique C (@zero_initial C Z) y h
             (@zero C (@zero_initial C Z) y)).
  reflexivity.
Qed.

(*
 Uniqueness of the zero object (Mac Lane, CWM 2nd ed., §I.5, p. 20).

 Two [ZeroObject] structures on C are related by an isomorphism of their
 underlying objects. Because a zero object is simultaneously terminal and
 initial, either half supplies the isomorphism. We take the terminal side as
 the representative, matching the convention used by [zero_mor] above, and
 record the initial-side reading separately; [zero_object_unique_compat]
 below proves the two readings agree. 

 --------
 零对象的唯一性（Mac Lane，《范畴论基础》第二版，第I.5节，第20页）。

 C 上的两个 [ZeroObject] 结构通过它们的底层对象的同构相关。由于零对象同时是终对象和初对象，任意一半都能提供同构。我们取终对象这一边作为代表，与上述 [zero_mor] 使用的惯例相匹配，并单独记录初对象一边的读法；下面的 [zero_object_unique_compat] 证明这两种读法是一致的。
*)
Program Definition zero_object_unique {C : Category} (Z1 Z2 : ZeroObject C) :
  @terminal_obj C (@zero_terminal C Z1) ≅ @terminal_obj C (@zero_terminal C Z2) :=
  terminal_unique (@zero_terminal C Z1) (@zero_terminal C Z2).

(* The same statement read through the chosen initial objects. / 相同的陈述通过所选的初始对象进行阅读。 *)
Program Definition zero_object_unique_initial {C : Category}
      (Z1 Z2 : ZeroObject C) :
  @initial_obj C (@zero_initial C Z1) ≅ @initial_obj C (@zero_initial C Z2) :=
  initial_unique (@zero_initial C Z1) (@zero_initial C Z2).

(*
 The two readings agree: transporting along [zero_coincide] turns one into
 the other, so the choice of representative above is immaterial.  The square

 0₁ ---- zero_object_unique_initial ----> 0₂
 |                                        |
 zero_coincide Z1                      zero_coincide Z2
 v                                        v
 1₁ ------- zero_object_unique --------> 1₂

 commutes for the cheapest possible reason: both composites are morphisms
 OUT OF the initial object 0₁, and [zero_unique] identifies any two of
 those.  Stating it is still worth the two lines, because it is the one
 claim about zero objects that neither uniqueness lemma above makes -- each
 of them is, on its own, a pure alias for the terminal or initial case. 

 --------
 两个读数是一致的：沿着 [zero_coincide] 传输会将一个变成另一个，因此上述代表的选择无关紧要。该平方

 0₁ ---- zero_object_unique_initial ----> 0₂
 |                                        |
 zero_coincide Z1                      zero_coincide Z2
 v                                        v
 1₁ ------- zero_object_unique --------> 1₂

 因为最简单的原因而交换：两个复合都是来自初始对象 0₁ 的态射，而 [zero_unique] 识别了它们中的任意两个。写出来仍然值得两行，因为这是关于零对象的唯一主张，上述唯一性引理都没有提及——它们各自单独而言，是终端对象或初始对象情形的纯别名。
*)
Lemma zero_object_unique_compat {C : Category} (Z1 Z2 : ZeroObject C) :
  to (@zero_coincide C Z2) ∘ to (zero_object_unique_initial Z1 Z2)
    ≈ to (zero_object_unique Z1 Z2) ∘ to (@zero_coincide C Z1).
Proof. apply (@zero_unique C (@zero_initial C Z1)). Qed.

(*
 An arrow between the underlying objects of two zero objects is unique, so
 the isomorphism above is canonical -- the "up to a UNIQUE isomorphism" half
 of the statement, inherited from the terminal side. 

 --------
 两个零对象的底层对象之间的箭头是唯一的，所以上述同构是典型的——陈述中“至多唯一同构”的部分是继承自终对象一方的。
*)
Corollary zero_object_arrow_unique {C : Category} (Z1 Z2 : ZeroObject C)
      (f g : @terminal_obj C (@zero_terminal C Z1)
               ~> @terminal_obj C (@zero_terminal C Z2)) : f ≈ g.
Proof. apply (@one_unique C (@zero_terminal C Z2)). Qed.

(*
 Riehl, CTiC, Exercise 1.6.i.  If there is ANY morphism from a terminal
 object to an initial one, it is an isomorphism, and the two objects are
 then both zero objects.

 The proof is the degenerate case of the usual uniqueness argument.  The
 candidate inverse is the unique arrow `! : 0 ~> 1` supplied by
 terminality of 1 (equivalently `¡`, supplied by initiality of 0 -- they
 agree, being parallel arrows into a terminal object).  One round trip
 `f ∘ ! : 0 ~> 0` is an arrow OUT OF an initial object, so [zero_unique]
 identifies it with the identity; the other, `! ∘ f : 1 ~> 1`, is an
 arrow INTO a terminal object, so [one_unique] does.  Neither direction
 needs the arrow f to be anything in particular -- the hypothesis is
 used only for its existence. 

 --------
 Riehl, CTiC, 练习 1.6.i。如果存在从终对象到初对象的任何态射，那么它是一个同构，于是这两个对象都是零对象。

 证明是通常唯一性论证的退化情况。候选逆态射是由 1 的终性提供的唯一箭头 `! : 0 ~> 1`（或者等价地由 0 的初性提供的 `¡`——它们在箭头指向终对象时是相同的）。一次完整的往返 `f ∘ ! : 0 ~> 0` 是从初对象出的箭头，因此 [zero_unique] 将其识别为恒等箭头；另一次 `! ∘ f : 1 ~> 1` 是指向终对象的箭头，因此 [one_unique] 起作用。无论哪个方向，都不需要箭头 f 有任何特定性质——假设仅用于其存在性。
*)
Program Definition terminal_initial_arrow_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) :
  @terminal_obj C T ≅ @initial_obj C I := {|
  to   := f;
  from := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(* The same fact as a predicate on the given morphism. / 作为给定态射的谓词的相同事实。 *)
Program Definition terminal_initial_arrow_is_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : IsIsomorphism f := {|
  two_sided_inverse := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(*
 Consequently a zero object can be DERIVED rather than posited.  The
 [zero_coincide] field of [ZeroObject] is data, and until now the only
 in-tree inhabitant (Instance/CMon/Biproduct.v) supplied [iso_id]
 because its two chosen objects were literally the same term.  This
 constructor produces the field from a single morphism 1 ~> 0, which is
 the practical form of the exercise: to know that a category with both
 an initial and a terminal object is pointed, it suffices to connect
 them in the harder direction. 

 --------
 因此，零对象可以被推导出来，而不是假定的。[ZeroObject] 的 [zero_coincide] 字段是数据，直到现在，唯一的树内居民（Instance/CMon/Biproduct.v）提供了 [iso_id]，因为它选择的两个对象在字面上是相同的术语。这个构造函数从单个态射 1 ~> 0 生成字段，这就是练习的实际形式：要知道一个同时具有初始对象和终端对象的范畴是有指向的，只需在较难的方向上将它们连接起来。
*)
Definition ZeroObject_from_arrow {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : ZeroObject C := {|
  zero_terminal := T;
  zero_initial  := I;
  zero_coincide := iso_sym (terminal_initial_arrow_iso T I f)
|}.
