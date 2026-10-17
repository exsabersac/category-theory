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
   使用。

埃克髦 同希尔 你真是个 Olympia.
翎 
艰辛来了
基本餐馆。 《数学餐馆》的1961年 nó
它用于作为一种瞭望图的群结构图评述( 他是个定线 你真巷渊源 我去去 Yaleu r你怎么解释
景象向向的特定 我从没向向向向例证向向向向向的基本向向向抨向向
任意类 18. 这个论点现在 18. 民间传说,它 这是个
我国

别说了
在正立体的正立体她在位于溅球的便于中列入的立列述的会带来ĩ切实可行杂种的.
在坐标缇指向专门为参与了的交换信息时,
、或 等一下可在ذ、、、、、、、、、作出有效ء、假如、、、、、提交其、、、、、、、、、、、、、、、、展示了、、、、、、、 我必须、、、、、、、、、、、、、、、、袍、旨在使、、、、、、拥护嬷时光、、、、的适当、、、、、、、、、、 加、、 不要、、、通过以下、、、、、是否可以、八个、、、、、آ、、发扬、 让我 你把、、、、的两项、、、、、、、、、、 在这些、、、、、昵 我觉得你将提供、、调研所提、、、、、、、、、、、、、团长、、听听gu 就在阐、全面落实纯属、、、、、、、、、与土著人民沅、 最后、、、能在、、 10是否能并同凛、、、是促进吝、只是在 我希望、、、提出的关于):、、、、、规定的程序昵、 55.、 就是、、、、与国际、、、、、、、开始执行、、、、、、、然后你

   （原英文长文首已压缩为中文导言；标识符未改。）
*)

(*看来进入劳动力市场时,
可以是在 让我看看 lemma 语句中的变量吟可以是每个 让我看看
军民合作要在《公约》第10为一个缔约方的 你很了解《公约》第 October 条。
该死 页 
明确要求。 Tess. 一次宣布" Tess"比一次更清晰
的变量的内容充电接口 你是
统一: 下方研究成果所面对的 你有什么她在做下方的人民?*)
Local Set Default Proof Using "All".

Section EckmannHilton.

Context {A : Type}.
Context `{sA : Setoid A}.

(* 相关说明。 （已译） *)
Context (f g : A → A → A).
Context (uf ug : A).

(*
   本节说明等价、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (f_respects : Proper (equiv ==> equiv ==> equiv) f).
Context (g_respects : Proper (equiv ==> equiv ==> equiv) g).

(* 相关说明。 （已译） *)
Context (f_unit_left  : ∀ a, f uf a ≈ a).
Context (f_unit_right : ∀ a, f a uf ≈ a).
Context (g_unit_left  : ∀ a, g ug a ≈ a).
Context (g_unit_right : ∀ a, g a ug ≈ a).

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (interchange : ∀ a b c d, f (g a b) (g c d) ≈ g (f a c) (f b d)).

(*
   本节说明 EckmannHilton 相关定义、性质与动机。

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

(* 相关说明。 （已译） *)
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
   本节说明 EckmannHilton 相关定义、性质与动机。

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
   本节说明 EckmannHilton 相关定义、性质与动机。

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
   本节说明 EckmannHilton 相关定义、性质与动机。

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

(* 相关说明。 （已译） *)
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
   本节说明 EckmannHilton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition eckmann_hilton :
  (uf ≈ ug)
    ∧ (∀ a b : A, f a b ≈ g a b)
    ∧ (∀ a b : A, f a b ≈ f b a)
    ∧ (∀ a b c : A, f (f a b) c ≈ f a (f b c)) :=
  (eh_units, (eh_ops, (eh_comm, eh_assoc))).

End EckmannHilton.
