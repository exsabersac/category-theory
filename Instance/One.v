Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The terminal category 1 (the point). / 终端范畴1（点）。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/terminal+category
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories
 Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 1 is the category with a single object and a single (identity) morphism on
 it.  Here the lone object and the lone arrow are both [ttt], the unique
 inhabitant of the universe-polymorphic unit type [poly_unit]; the hom-setoid
 is strict equality, under which that hom is trivially contractible.

 1 is the terminal object of Cat: for every category C there is a unique
 functor `! : C ⟶ 1` ([Erase]), sending every object and morphism to [ttt].
 Dually, functors *out* of 1 pick out objects of the target, so [1, C] ≃ C.
 Theory/Shapes.v proves both readings: [Point] and [point_of] with their
 round trips for the objects, and [One_Fun_iso : [_1, C] ≅[Cat] C] for the
 functor category — an equivalence of categories in the sense of
 Instance/Cat.v, not an isomorphism of categories.
 The dual notion — the initial/empty category 0 — lives in Instance/Zero.v. 

 --------
 nLab：https://ncatlab.org/nlab/show/terminal+category
 Wikipedia：https://en.wikipedia.org/wiki/Category_of_small_categories
 Wikipedia：https://en.wikipedia.org/wiki/Initial_and_terminal_objects

 1 是只有一个对象和一个（恒等）态射的范畴。在这里，唯一的对象和唯一的箭头都是 [ttt]，这是宇宙多态单位类型 [poly_unit] 的唯一元素；同态集族是严格相等的，在这种情况下该同态是显然可收缩的。1 是 Cat 的终对象：对于每个范畴 C，都存在一个唯一的函子 `! : C ⟶ 1` ([Erase])，将每个对象和态射映射到 [ttt]。与之对偶，从 1 出发的函子会选择目标范畴中的对象，所以 [1, C] ≃ C。Theory/Shapes.v 证明了这两种理解：[Point] 和 [point_of] 及其对象的往返映射，以及 [One_Fun_iso : [_1, C] ≅ [Cat] C] 对于函子范畴——这在 Instance/Cat.v 的意义上是范畴的等价，而不是范畴的同构。对偶的概念——初始/空范畴 0——存在于 Instance/Zero.v。
*)

(*
   【1 / _1 终范畴实例展开】/ Terminal category walkthrough
   （口吻对齐 Theory/Functor.v；受众：Coq 小白 + Haskell）

   1) 这是什么 / What this is
      1 = 终范畴：一个对象、一条恒等箭（皆为 poly_unit 的 ttt）。Cat 中的终对象。
      Terminal category: one object, one arrow. Terminal object of Cat.
      Haskell 对照：像 unit 类型升到范畴层；C⟶1 唯一（Erase）；1⟶C 挑对象。
      Analogy: unit at category level; ! : C⟶1 unique; functors 1⟶C pick objects.

   2) 关键字段 / Key fields
      - obj := poly_unit；hom := fun _ _ => poly_unit
      - homset := Morphism_equality；id/compose := ttt

   阅读：_1 → Erase → Cat_Terminal；对偶见 Zero.v。
   Read: _1 → Erase → Cat_Terminal; dual in Zero.v.
*)
Program Definition _1@{o h p} : Category@{o h p} := {|
  obj     := poly_unit@{o};            (* the single object / 单个物体 *)
  hom     := fun _ _ => poly_unit@{h}; (* the single (identity) arrow / 单（恒等）箭头 *)
  homset  := Morphism_equality@{o h p}; (* hom-setoid is strict equality / hom-setoid 是严格相等 *)
  id      := fun _ => ttt;             (* identity = the lone arrow / 身份 = 孤独的箭 *)
  compose := fun _ _ _ _ _ => ttt      (* composition = the lone arrow / 构图 = 孤箭 *)
|}.
Next Obligation.
  now destruct f.
Qed.
Next Obligation.
  now destruct f.
Qed.

Notation "1" := _1 : category_scope.

(* `one[C]` names the unique functor `! : C ⟶ 1` at Cat's Terminal instance. / `one [C]ZZ ` 在 Cat 的 Terminal 实例中命名了唯一的函子 `! : C ⟶ 1`。 *)
Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.

(* The unique functor `! : C ⟶ 1`, collapsing all of C onto the point. / 唯一的函子 `! : C ⟶ 1`，将所有的 C 折叠到一个点上。 *)
#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 := {
  fobj := fun _ => ttt;      (* every object goes to the lone object / 每个物体都去孤独的物体 *)
  fmap := fun _ _ _ => id    (* every morphism goes to the identity / 每个态射都映射到恒等映射 *)
}.

(* 1 is the terminal object of Cat, witnessed by the unique functor [Erase]. / 1 是 Cat 的终对象，由唯一函子 [Erase] 证明。 *)
#[export]
Program Instance Cat_Terminal : @Terminal Cat := {
  terminal_obj := _1;        (* the terminal category 1 / 终端类别 1 *)
  one := Erase               (* the unique functor ! : C ⟶ 1 / 唯一函子 ! : C ⟶ 1 *)
}.
Next Obligation.
  constructive; auto; try exact ttt.
  destruct (fmap[f] f0); auto.
Qed.
