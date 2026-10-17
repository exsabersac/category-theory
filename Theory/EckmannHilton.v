Require Import Category.Lib.

Generalizable All Variables.

(** * The Eckmann–Hilton argument *)

(* nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument
   Paper:     Eckmann, Hilton, "Group-like structures in general categories
              I. Multiplications and comultiplications", Mathematische
              Annalen 145, 1962
   Paper:     Eckmann, Hilton, "Structure maps in group theory", Fundamenta
              Mathematicae 50, 1961 (Theorem 1.12)
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.5 Exercise 5 (printed p. 45)

   设一载体带有两个二元运算，各有双侧单位，且两运算*交换* (interchange)：对 2×2 数组
   先按行求值与先按列求值一致，

       f (g a b) (g c d)  ≈  g (f a c) (f b d).

   则两单位重合、两运算重合，剩下的单一运算交换且结合。此外一无所设——无结合律、
   无交换律，甚至不要求任一运算自身是幺半群。两定律都是*输出*。

   本文件在裸 setoid 上恰陈述并证明这一点。它刻意是*前范畴的*：仅导入 [Category.Lib]，
   尤其不导入 [Category.Theory.Category]。论证从不提及对象、态射或复合；它是关于带两个
   交换单位运算的集合的事实，下文范畴实例是实例而非内容。 *)

(*
   本节说明相关定义、性质与动机。 Where argument comes from, what it is used for. Eckmann Hilton isolated principle while studying H-spaces dual "H-cospaces": space 乘法 comultiplication that are compatible above sense has 阿贝尔 fundamental structure.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明相关定义、性质与动机。 Lib.v sets [Default Proof Using "Type"], which keeps only Section. variables occurring lemma's STATEMENT. Every statement here mentions only [f], [g], [uf] [ug];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Set Default Proof Using "All".

Section EckmannHilton.

Context {A : Type}.
Context `{sA : Setoid A}.

(* The two operations and their units. *)
Context (f g : A → A → A).
Context (uf ug : A).

(*
   Both operations respect the carrier's 等价.  These are stated as

   本节说明相关定义、性质与动机。 [Proper] hypotheses so that setoid rewriting can work underneath them.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (f_respects : Proper (equiv ==> equiv ==> equiv) f).
Context (g_respects : Proper (equiv ==> equiv ==> equiv) g).

(* [uf] is a two-sided unit for [f], and [ug] one for [g].  Note that
   nothing yet relates the two. *)
Context (f_unit_left  : ∀ a, f uf a ≈ a).
Context (f_unit_right : ∀ a, f a uf ≈ a).
Context (g_unit_left  : ∀ a, g ug a ≈ a).
Context (g_unit_right : ∀ a, g a ug ≈ a).

(*
   本节说明相关定义、性质与动机。 The interchange law. The orientation is one Structure/Semiadditive.v.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (interchange : ∀ a b c d, f (g a b) (g c d) ≈ g (f a c) (f b d)).

(*
   本节说明相关定义、性质与动机。 Eckmann–Hilton, step one: two units coincide.. Read interchange law at array whose entries are two units arranged antidiagonally, ( uf ug ) ( ug uf ).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eh_units : uf ≈ ug.
Proof.
  transitivity (f (g uf ug) (g ug uf)).
  - rewrite g_unit_right, g_unit_left.
    now rewrite f_unit_left.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite g_unit_left.
Qed.

(* With the units identified, [uf] is a two-sided unit for [g] as well, so
   the padding arguments below can be written with a single unit. *)
Lemma eh_common_unit_left (a : A) : g uf a ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_left.
Qed.

Lemma eh_common_unit_right (a : A) : g a uf ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_right.
Qed.

(*
   本节说明相关定义、性质与动机。 Eckmann–Hilton, step two: two operations coincide.. In three chains that follow, [1] abbreviates common unit — [uf], which [eh_common_unit_left]/[eh_common_unit_right] is now two-sided unit [g] well.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eh_ops (a b : A) : f a b ≈ g a b.
Proof.
  transitivity (f (g a uf) (g uf b)).
  - now rewrite eh_common_unit_right, eh_common_unit_left.
  - rewrite interchange.
    now rewrite f_unit_right, f_unit_left.
Qed.

(*
   本节说明相关定义、性质与动机。 Eckmann–Hilton, step three: operation is commutative.. The same padding, units placed other side, so that interchange transposes two arguments;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eh_comm (a b : A) : f a b ≈ f b a.
Proof.
  transitivity (f (g uf a) (g b uf)).
  - now rewrite eh_common_unit_left, eh_common_unit_right.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite <- eh_ops.
Qed.

(*
   本节说明相关定义、性质与动机。 Eckmann–Hilton, step four: operation is associative.. Pad only first argument, read interchange both directions around intermediate term [f (g 1) (g b c)]: f (f b) c ≈ g (f b) (f 1 c) ≈ f (g 1) (g b c) ≈ f (g b c) ≈ f (f b c).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eh_assoc (a b c : A) : f (f a b) c ≈ f a (f b c).
Proof.
  transitivity (f (g a uf) (g b c)).
  - rewrite interchange.
    rewrite f_unit_left.
    now rewrite <- eh_ops.
  - rewrite eh_common_unit_right.
    now rewrite <- eh_ops.
Qed.

(* The [g]-side readings.  Since the operations coincide these are one
   rewrite away, but they are what a consumer holding only [g] wants. *)
Lemma eh_g_comm (a b : A) : g a b ≈ g b a.
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_comm.
Qed.

Lemma eh_g_assoc (a b c : A) : g (g a b) c ≈ g a (g b c).
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_assoc.
Qed.

(*
   本节说明相关定义、性质与动机。 The theorem, packaged.. PACKAGING CHOICE: library's `≈` is [crelation], i.e. Type-valued, so four conclusions cannot be conjoined [and]. They are conjoined library's [∧], which is [prod] (Lib/Foundation.v), right-associated. A record was alternative;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition eckmann_hilton :
  (uf ≈ ug)
    ∧ (∀ a b : A, f a b ≈ g a b)
    ∧ (∀ a b : A, f a b ≈ f b a)
    ∧ (∀ a b c : A, f (f a b) c ≈ f a (f b c)) :=
  (eh_units, (eh_ops, (eh_comm, eh_assoc))).

End EckmannHilton.
