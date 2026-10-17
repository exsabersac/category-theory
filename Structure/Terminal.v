Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * 带终对象的范畴 *)

(* nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   范畴 C 中的终对象 `1` 是这样的对象：对每个对象 `x` 恰有一个态射 `! : x ~> 1`。
   「恰有一个」拆成存在性（态射 [one]）与唯一性（进入 `1` 的任意两态射在 `≈` 下
   一致，定律 [one_unique]）。等价地，每个 hom-setoid `x ~> 1` 可收缩（至多 `≈`
   下的单点）。终对象是初始对象的对偶——它是 `C^op` 中的初始对象——并且是空图的极限；
   见 Structure/Initial.v，由对偶从本文件导出初始对象。终对象若存在则在（唯一）同构
   下唯一：下文 [terminal_unique] 构造同构，[terminal_arrow_unique] 表明它是两对象间
   仅有的箭头，[terminal_unique_up_to_unique_iso] 把两者打包为单个 [Unique]。 *)

(*
   关于terminal objects的来源与用途

   nLab:  https://ncatlab.org/nlab/show/global+element
   nLab:  https://ncatlab.org/nlab/show/unit+type
   Paper: Samuel, "On universal mappings and free topological groups",
   Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950
   Paper: Lawvere, "An elementary theory of the category of sets",

   本节说明（余）极限、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;                     (* the terminal object 1 *)
  one {x} : x ~> terminal_obj;          (* the morphism ! : x ~> 1 *)

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g  (* ! is unique up to ≈ *)
}.

End Terminal.

Notation "1" := terminal_obj : object_scope.

(* Precomposing the unique map collapses: ! ∘ f ≈ !, since both land in `1`. *)
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

(* `one[x]` names the morphism `! : x ~> 1` at an explicit Terminal instance. *)
Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.

(* A "constant" map `x ~> y` factoring through `1`: pick `f : 1 ~> y`, then
   precompose with `! : x ~> 1`, so the result ignores its argument's data. *)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary terminal_arrow_unique {C : Category} (T1 T2 : @Terminal C)
      (f g : @terminal_obj C T1 ~> @terminal_obj C T2) : f ≈ g.
Proof. apply (@one_unique C T2). Qed.

(*
   本节说明hom、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsTerminalObj {C : Category} (c : C) : Type :=
  ∀ x : C, Unique (fun _ : x ~> c => True).

(* The unique arrow x ~> c supplied by the predicate. *)
Definition is_terminal_one {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} : x ~> c := unique_obj (H x).

(* ... and its uniqueness, in the two-arrow form used by [one_unique]:
   both arrows agree with the chosen witness, hence with each other. *)
Lemma is_terminal_unique {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} (f g : x ~> c) : f ≈ g.
Proof.
  pose proof (uniqueness (H x) f I) as Hf.
  pose proof (uniqueness (H x) g I) as Hg.
  now rewrite <- Hf, <- Hg.
Qed.

(* Bundling: the predicate at c yields a [Terminal] structure choosing c. *)
Program Definition Terminal_from_IsTerminalObj {C : Category} {c : C}
  (H : IsTerminalObj c) : @Terminal C := {|
  terminal_obj := c;
  one := fun x => @is_terminal_one C c H x
|}.
Next Obligation. now apply (is_terminal_unique H). Qed.

(* ... and conversely, unbundling at the chosen object. *)
Program Definition IsTerminalObj_from_Terminal {C : Category}
  (T : @Terminal C) : IsTerminalObj (@terminal_obj C T) := fun x =>
  {| unique_obj := @one C T x
   ; unique_property := I |}.
Next Obligation. now apply (@one_unique C T). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Terminal_iso {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @Terminal C := {|
  terminal_obj := y;
  one := fun x => to i ∘ @one C T x
|}.
Next Obligation.
  assert (Hf : to i ∘ (from i ∘ f) ≈ f)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  assert (Hg : to i ∘ (from i ∘ g) ≈ g)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  transitivity (to i ∘ (from i ∘ f)).
  - now symmetry.
  - now rewrite (@one_unique C T _ (from i ∘ f) (from i ∘ g)).
Qed.

(*
   本节说明等价、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_unique_up_to_unique_iso {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) := {|
  unique_obj := terminal_unique T1 T2;
  unique_property := I
|}.
Next Obligation.
  split.
  - apply (@one_unique C T2).
  - apply (@one_unique C T1).
Qed.

(*
   本节说明hom、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_hom_unique {C : Category} (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ~> @terminal_obj C T2 => True) := {|
  unique_obj := @one C T2 (@terminal_obj C T1);
  unique_property := I
|}.
Next Obligation. apply (@one_unique C T2). Qed.
