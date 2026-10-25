Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Section TerminalSubcategory.

Context {C : Category}.

(*
 Riehl, CTiC, Lemma 1.6.16: the full subcategory spanned by the terminal
 objects of C.  [sobj] selects exactly the terminal objects (Block A's
 predicate is what makes this expressible -- the bundled class cannot
 span a subcategory, since it carries a choice of object), and [shom]
 retains every C-morphism between them, which is fullness.  Closure
 under composition and identity is then vacuous.

 Written with [Build_Subcategory] rather than [Program]: a Program
 record whose obligations are discharged by [Qed] is opaque to the
 unifier, and the [Replete] witness below needs [shom] to reduce. 

 --------
 Riehl, CTiC, 引理 1.6.16：由 C 的终对象生成的满子范畴。[sobj] 精确地选择了终对象（Block A 的谓词使其可表达——捆绑的类不能生成子范畴，因为它带有对象的选择），而 [shom] 保留它们之间的每一个 C-态射，这就是满性。然后，在复合和恒等下的闭合性是平凡的。 

 用 [Build_Subcategory] 而不是 [Program] 来书写：一个其义务由 [Qed] 完成的程序记录对统一器是不可见的，而下面的 [Replete] 见证需要 [shom] 来化简。
*)
Definition TerminalObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsTerminalObj c)          (* the terminal objects / 终端对象 *)
    (fun _ _ _ _ _ => True)             (* full: every C-morphism is kept / 完整：保留每个 C-态射 *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition / 在复合运算下封闭 *)
    (fun _ _ => I).                     (* closed under identities / 在恒等式下封闭 *)

Notation "'TSub'" := (Sub C TerminalObjects).

Definition TerminalObjects_Full :
  Construction.Subcategory.Full C TerminalObjects := fun _ _ _ _ _ => I.

(*
 Riehl, CTiC, Exercise 1.6.ii(i) in its subcategory form: the span of
 the terminal objects is replete.  The object half is Block A's
 [Terminal_iso], routed through the bundling pair; the morphism halves
 are trivial because the subcategory is full. 

 --------
 Riehl, CTiC，第1.6.ii(i)练习的子范畴形式：终端对象的张成是充实的。对象的一半是 Block A 的 [Terminal_iso]，通过捆绑对路由；态射的一半是平凡的，因为子范畴是满的。
*)
Definition TerminalObjects_Replete : Replete C TerminalObjects :=
  fun x ox y f =>
    (IsTerminalObj_from_Terminal
       (Terminal_iso (Terminal_from_IsTerminalObj ox) y f); (I, I)).

(*
 Each hom-set is INHABITED: the target is terminal, so it receives an
 arrow from the source, and fullness lets it into the subcategory. 

 --------
 每个Hom集都是非空的：目标是终端的，因此它会从源接收一个箭头，并且满性使它进入子范畴。
*)
Definition terminal_sub_hom (a b : TSub) : a ~{TSub}~> b :=
  (@is_terminal_one C (`1 b) (`2 b) (`1 a); I).

(*
 ... and it is a SINGLETON up to ≈, since the subcategory's hom-setoid
 compares underlying C-morphisms and the target is terminal. 

 --------
 ... 并且它是一个单例，直到 ≈，因为子范畴的同态集合比较了底层的 C-态射，而目标是终对象。
*)
Lemma terminal_sub_hom_unique (a b : TSub) (f g : a ~{TSub}~> b) : f ≈ g.
Proof. exact (is_terminal_unique (`2 b) (`1 f) (`1 g)). Qed.

(*
 The two facts packaged as Lemma 1.6.16's "exactly one morphism in each
 hom-set", in the library's own [Unique] idiom. 

 --------
 这两个事实被打包为引理 1.6.16 的“在每个 Hom-集合中恰好存在一个态射”，使用了库自身的 [Unique] 习惯用法。
*)
Definition terminal_sub_hom_contractible (a b : TSub) :
  Unique (fun _ : a ~{TSub}~> b => True) :=
  {| unique_obj       := terminal_sub_hom a b
   ; unique_property  := I
   ; uniqueness       := fun v _ =>
       terminal_sub_hom_unique a b (terminal_sub_hom a b) v |}.

(*
 It is a GROUPOID: the reverse arrow exists for the same reason, and
 both round trips are arrows into terminal objects, hence identities. 

 --------
 它是一个群oids：反向箭头存在的原因相同，并且两个往返路径都是指向终端对象的箭头，因此是恒等式。
*)
Definition terminal_sub_IsIso {a b : TSub} (f : a ~{TSub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

Definition terminal_sub_iso (a b : TSub) : @Isomorphism TSub a b.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom a b).
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

(*
 A bundled [Terminal] structure is an object of the subcategory; this is
 what makes it non-empty, and it is the hypothesis of the contractibility
 statement in Block E. 

 --------
 一个捆绑的 [Terminal] 结构是子范畴的一个对象；这就是使其非空的原因，并且它是区块 E 中可收缩性陈述的假设。
*)
Definition terminal_sub_obj (T : @Terminal C) : TSub :=
  (@terminal_obj C T; IsTerminalObj_from_Terminal T).

End TerminalSubcategory.

Section InitialSubcategory.

Context {C : Category}.

(*
 The initial dual.  Unlike Block B this is stated directly rather than
 as [TerminalObjects] at C^op, because [Sub (C^op) (op_subcategory S)]
 and [(Sub C S)^op] are different terms, so duality would buy a
 definition and then cost a translation at every use. 

 --------
 初始对偶。与 Block B 不同，这里是直接陈述的，而不是在 C^op 上表示为 [TerminalObjects]，因为 [Sub (C^op) (op_subcategory S)] 和 [(Sub C S)^op] 是不同的项，因此对偶性会带来一次定义，然后在每次使用时都需要一次转换。
*)
Definition InitialObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsInitialObj c)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Notation "'ISub'" := (Sub C InitialObjects).

Definition InitialObjects_Full :
  Construction.Subcategory.Full C InitialObjects := fun _ _ _ _ _ => I.

Definition InitialObjects_Replete : Replete C InitialObjects :=
  fun x ox y f =>
    (IsInitialObj_from_Initial
       (Initial_iso (Initial_from_IsInitialObj ox) y f); (I, I)).

Definition initial_sub_hom (a b : ISub) : a ~{ISub}~> b :=
  (@is_initial_zero C (`1 a) (`2 a) (`1 b); I).

Lemma initial_sub_hom_unique (a b : ISub) (f g : a ~{ISub}~> b) : f ≈ g.
Proof. exact (is_initial_unique (`2 a) (`1 f) (`1 g)). Qed.

Definition initial_sub_hom_contractible (a b : ISub) :
  Unique (fun _ : a ~{ISub}~> b => True) :=
  {| unique_obj      := initial_sub_hom a b
   ; unique_property := I
   ; uniqueness      := fun v _ =>
       initial_sub_hom_unique a b (initial_sub_hom a b) v |}.

Definition initial_sub_IsIso {a b : ISub} (f : a ~{ISub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_iso (a b : ISub) : @Isomorphism ISub a b.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom a b).
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_obj (I0 : @Initial C) : ISub :=
  (@initial_obj C I0; IsInitialObj_from_Initial I0).

End InitialSubcategory.
