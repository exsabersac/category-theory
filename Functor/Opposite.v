Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** The opposite (dual) functor F^op : C^op ⟶ D^op. *)

(* nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   给定 F : C ⟶ D，对偶函子 F^op : C^op ⟶ D^op 在对象与态射上与 F 作用相同；仅
   （形式反向的）源与目标范畴改变。对象上 (F^op) x := F x；态射 f : x ~{C^op}~> y
   （即 C 中 f : y ~> x）被送到 fmap[F] f，读作态射 F x ~{D^op}~> F y。函子性字段是
   F 的对应字段，对象指标交换，fmap_comp 重指标以匹配 C^op 的反向复合（彼处 g ∘ f
   是 C 中的 f ∘ g）。

   因底层对偶使 (C^op)^op = C 由 reflexivity 成立，且 F^op 复用与 F 相同的对象/态射映射，
   构造对合：(F^op)^op = F，可由 [reflexivity] 证明（见下文 Opposite_Functor_invol）。
   反变函子 C ⟶ D 按定义是出自 C^op 的普通函子；见文末 [contramap]。

   在 1-胞（函子）上对偶化共变，但注意在 2-胞（自然变换）上方向反转：自然变换
   F^op ⟹ G^op 对应 G ⟹ F，故 op 是 2-函子 Cat^co ⟶ Cat。 *)

Definition Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op :=
  @Build_Functor (C^op) (D^op) F
    (λ (x y : C ^op) (f : x ~{ C ^op }~> y), @fmap C D F y x f)
    (λ (x y : C ^op) (f g : x ~{ C ^op }~> y), @fmap_respects _ _ F y x f g)
    (λ x : C ^op, fmap_id)
    (λ (x y z : C ^op) (f : y ~{ C ^op }~> z)
      (g : x ~{ C ^op }~> y), @fmap_comp _ _ F _ _ _ g f).

(* Mirrors the C^op notation on categories, at the same level/scope. *)

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op", left associativity) : functor_scope.

Open Scope functor_scope.

(* The op functor is an involution on functors: applying it twice recovers F
   on the nose. Both sources state (C^op)^op = C, and F^op reuses F's maps. *)

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

(* A functor F : C^op ⟶ D is a contravariant functor on C: it reverses the
   direction of morphisms. [contramap] applies it to a C-arrow f : x ~> y by
   reading f as the C^op-arrow (op f), yielding F y ~> F x in D. *)

Definition contramap `{F : C^op ⟶ D} `(f : x ~{C}~> y) :
  F y ~{D}~> F x := fmap (op f).

(* The fullness and faithfulness rows of Mac Lane §IV.3 Exercise 1's
   dualization table, for an ARBITRARY functor — previously reachable
   only through the equivalence detour of Theory/Equivalence/Limit.v.
   The op-functor's hom-action at (x, y) is the original's at (y, x), so
   each property transports by reindexing, in both directions; every
   obligation is an [exact] at the swapped indices. *)

#[local] Obligation Tactic := idtac.

Program Definition Full_op `{F : C ⟶ D} (H : Full F) : Full (F^op) := {|
  prefmap := fun x y g => @prefmap _ _ F H y x g
|}.
Next Obligation.
  intros; exact (@fmap_sur _ _ F H y x g).
Qed.

Program Definition Full_of_op `{F : C ⟶ D} (H : Full (F^op)) : Full F := {|
  prefmap := fun x y g => @prefmap _ _ (F^op) H y x g
|}.
Next Obligation.
  intros; exact (@fmap_sur _ _ (F^op) H y x g).
Qed.

Program Definition Faithful_op `{F : C ⟶ D} (H : Faithful F) :
  Faithful (F^op) := {|
  fmap_inj := fun x y f g => @fmap_inj _ _ F H y x f g
|}.

Program Definition Faithful_of_op `{F : C ⟶ D} (H : Faithful (F^op)) :
  Faithful F := {|
  fmap_inj := fun x y f g => @fmap_inj _ _ (F^op) H y x f g
|}.
