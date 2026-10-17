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

(* Mirrors C^op notation 范畴, at same level/scope. （已译） *)

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op", left associativity) : functor_scope.

Open Scope functor_scope.

(* The op 函子 involution 函子: applying it twice recovers F
 nose. Both sources state (C^op)^op = C, F^op reuses F's maps. （已译） *)

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

(* A 函子 F : C^op ⟶ D is contravariant 函子 C: it reverses the
 direction 态射. [contramap] applies it C-arrow f : x ~> y by
 reading f as C^op-arrow (op f), yielding F y ~> F x D.（已译） *)

Definition contramap `{F : C^op ⟶ D} `(f : x ~{C}~> y) :
  F y ~{D}~> F x := fmap (op f).

(*
   本节说明函子、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
