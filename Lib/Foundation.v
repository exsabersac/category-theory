From Coq Require Export Program.
From Coq Require Export CMorphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Close Scope nat_scope.

(*
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

 Foundational plumbing shared by the whole library. There is no single
 mathematical object defined here; instead this file fixes the global
 conventions under which everything downstream is built:

 - The library is setoid-based (see Lib/Setoid.v): a type is equipped with a
 chosen equivalence relation `≈` standing in for equality, in the sense of
 Bishop sets / setoids. To make those equivalences and the `Proper`
 machinery `Type`-valued rather than `Prop`-valued, we work in `Type`
 throughout and use Coq's `CMorphisms`/`CRelationClasses` (the `Type`-valued
 analogues of `Morphisms`/`RelationClasses`).

 - Accordingly the logical connectives are rebound to their constructive,
 `Type`-valued forms in `category_theory_scope`: `exists`/`∃` denote `sigT`,
 `∧` denotes `prod`, `∨` denotes `sum`, and `↔` denotes `iffT`. These carry
 computational content, unlike the `Prop`-valued `ex`/`and`/`or`/`iff`.

 - Notation also supplies the sigma-type projections `` ``x `` / `` `1 x `` /
 `` `2 x `` / `` `3 x `` (the latter projecting a two-predicate `sigT2`) and
 the pairing `( x ; y )`, plus unicode forms for `∀`, `→`, `¬`, `≠`, and
 `λ`. 

 --------
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

 本文件是整库共用的基础设施，并不定义单一数学对象；它固定下游一切构建所依赖的全局约定：

 - 本库以 setoid 为基础（见 Lib/Setoid.v）：类型配备选定的等价关系 `≈` 以充当相等，即 Bishop 集合 / setoid 意义下的相等。为使这些等价与 `Proper` 机制取值为 `Type` 而非 `Prop`，我们全程在 `Type` 中工作，并使用 Coq 的 `CMorphisms`/`CRelationClasses`（即 `Morphisms`/`RelationClasses` 的 `Type` 值对应物）。

 - 相应地，逻辑联结词在 `category_theory_scope` 中被重绑定为构造性的 `Type` 值形式：`exists`/`∃` 表示 `sigT`，`∧` 表示 `prod`，`∨` 表示 `sum`，`↔` 表示 `iffT`。它们携带计算内容，不同于 `Prop` 值的 `ex`/`and`/`or`/`iff`。

 - 记号还提供 sigma 类型投影 ``x`` / `` `1 x `` / `` `2 x `` / `` `3 x ``（后者投影二元谓词 `sigT2`）以及配对 `( x ; y )`，并提供 `∀`、`→`、`¬`、`≠`、`λ` 的 Unicode 形式。
*)

Declare Scope category_theory_scope.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.

Notation "`` x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "( x ; y )" := (existT _ x y) (at level 0) : category_theory_scope.

Notation "`1 x" := (@projT1 _ _ x) (at level 0) : category_theory_scope.
Notation "`2 x" := (@projT2 _ _ x) (at level 0) : category_theory_scope.
Notation "`3 x" := (@projT3 _ _ x) (at level 0) : category_theory_scope.

Tactic Notation "given" "(" ident(H) ":" lconstr(type) ")" :=
  unshelve (refine (let H := (_ : type) in _)).

#[export] Hint Unfold Basics.compose : core.
#[export] Hint Unfold Basics.arrow : core.
#[export] Hint Unfold Datatypes.id : core.

Arguments Basics.compose {_ _ _} _ _ /.
Arguments Basics.arrow _ _ /.
Arguments Datatypes.id {_} _ /.

Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'") :
  category_theory_scope.

Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 10, x binder, y binder, P at level 200, right associativity) :
  category_theory_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): category_theory_scope.
Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity) : category_theory_scope.
Notation "¬ x" := (x → False)
  (at level 75, right associativity) : category_theory_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : category_theory_scope.

Infix "∧" := prod (at level 80, right associativity) : category_theory_scope.
Infix "∨" := sum (at level 85, right associativity) : category_theory_scope.

Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 10, x binder, y binder, t at level 200, right associativity) :
  category_theory_scope.
