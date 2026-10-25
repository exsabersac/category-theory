Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * 带终对象的范畴 / Categories with a terminal object *)

(* nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   范畴 C 中的终对象 `1` 是这样的对象：对每个对象 `x` 恰有一个态射 `! : x ~> 1`。
   「恰有一个」拆成存在性（态射 [one]）与唯一性（进入 `1` 的任意两态射在 `≈` 下
   一致，定律 [one_unique]）。等价地，每个 hom-setoid `x ~> 1` 可收缩（至多 `≈`
   下的单点）。终对象是初始对象的对偶——它是 `C^op` 中的初始对象——并且是空图的极限；
   见 Structure/Initial.v，由对偶从本文件导出初始对象。终对象若存在则在（唯一）同构
   下唯一：下文 [terminal_unique] 构造同构，[terminal_arrow_unique] 表明它是两对象间
   仅有的箭头，[terminal_unique_up_to_unique_iso] 把两者打包为单个 [Unique]。

   A terminal object `1` in C is an object such that for every `x` there is
   exactly one morphism `! : x ~> 1`. Existence is [one]; uniqueness up to ≈
   is [one_unique]. Dual of initial; limit of the empty diagram.
*)

(*
   关于终对象的来源与用途 / On terminal objects

   nLab:  https://ncatlab.org/nlab/show/global+element
   nLab:  https://ncatlab.org/nlab/show/unit+type
   Paper: Samuel, "On universal mappings and free topological groups",
   Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950
   Paper: Lawvere, "An elementary theory of the category of sets",

   Haskell 对照：Unit / () ——「只有一个值」；从任意类型到 () 恰有一个函数
   `const ()`。终对象 = 范畴版的 Unit。
   Haskell analogy: Unit / () — exactly one value; unique map `x -> ()`.
*)

(*
   【Class Terminal 语法与字段展开】/ Syntax & field walkthrough

   1) Class Terminal：给「已有范畴 C」加结构（类型类字段），不是新范畴。
      Instance 填具体的 1 与 !。≈ Haskell 的 class constraint，定律也是字段。
      [Class Terminal] equips an existing C; Instance fills 1 and !.
      Like a Haskell class; laws are proof-carrying fields.

   2) 数据字段 / Data fields
      - terminal_obj : C  —— 对象 1 本身 / the object 1
      - one {x} : x ~> terminal_obj  —— 唯一箭头 ! : x ~> 1（{x} 隐式）
        / the unique arrow ! ({x} implicit)

   3) 公理 / Law
      - one_unique : 任意 f,g : x ~> 1 都有 f ≈ g（唯一性）
        / any two arrows into 1 are ≈

   4) 记号：Notation "1" := terminal_obj。读代码时 1 就是终对象。
      Notation "1" names the terminal object.

   阅读顺序：terminal_obj → one → one_unique → terminal_unique（同构唯一性）。
   Read: terminal_obj → one → one_unique → uniqueness up to iso.
*)

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;  (* 终对象 1 / the terminal object 1 *)
  one {x} : x ~> terminal_obj;  (* 唯一箭头 ! : x ~> 1 / unique ! *)

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
    (* ! 在 ≈ 下唯一 / ! unique up to ≈ *)
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

(* 常值映射：经 1 分解，f : 1 ~> y 再预复合 ! / Constant map via 1 *)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].

(* 两终对象之间的（唯一）同构 / Unique iso between two terminals *)
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.

(* 两终对象间任意两箭头相等 / Any two arrows between terminals agree *)
Corollary terminal_arrow_unique {C : Category} (T1 T2 : @Terminal C)
      (f g : @terminal_obj C T1 ~> @terminal_obj C T2) : f ≈ g.
Proof. apply (@one_unique C T2). Qed.

(* 谓词形式：「c 是终对象」/ Predicate form: c is terminal *)
Definition IsTerminalObj {C : Category} (c : C) : Type :=
  ∀ x : C, Unique (fun _ : x ~> c => True).

(* 谓词给出的唯一箭头 x ~> c / Unique arrow from the predicate *)
Definition is_terminal_one {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} : x ~> c := unique_obj (H x).

(* 谓词形式的唯一性 / Uniqueness from the predicate *)
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

(* 反之：从 Terminal 解包为谓词 / Conversely: unbundle Terminal *)
Program Definition IsTerminalObj_from_Terminal {C : Category}
  (T : @Terminal C) : IsTerminalObj (@terminal_obj C T) := fun x =>
  {| unique_obj := @one C T x
   ; unique_property := I |}.
Next Obligation. now apply (@one_unique C T). Qed.

(* 沿同构搬运 Terminal 结构 / Transport Terminal along an iso *)
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

(* 打包：唯一同构下唯一 / Pack uniqueness-up-to-unique-iso *)
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

(* 两终对象间唯一箭头 / Unique arrow between two terminals *)
Program Definition terminal_hom_unique {C : Category} (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ~> @terminal_obj C T2 => True) := {|
  unique_obj := @one C T2 (@terminal_obj C T1);
  unique_property := I
|}.
Next Obligation. apply (@one_unique C T2). Qed.
