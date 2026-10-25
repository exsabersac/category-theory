Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The category PROP of propositions / * * 命题的类别 PROP *)

(*
 nLab: https://ncatlab.org/nlab/show/Heyting+algebra
 nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Heyting_algebra

 Objects are propositions (`Prop`) and a morphism P ~> Q is an implication,
 i.e. a proof of `P → Q` (`Basics.impl`). Since every hom-setoid is made
 trivial (`equiv f g := True`), this is a thin / posetal category: at most
 one arrow between any two objects, so P ~> Q is inhabited exactly when
 P entails Q. That makes Props the preorder of propositions ordered by
 implication.

 Equipped with the logical connectives below it is a bicartesian closed
 thin category — a Heyting prealgebra — modelling intuitionistic
 propositional logic:

 1 = True          (terminal,   Props_Terminal)
 0 = False         (initial,    Props_Initial)
 P × Q = P ∧ Q     (product,    Props_Cartesian)
 P + Q = P ∨ Q     (coproduct,  Props_Cocartesian)
 Q ^ P = P → Q     (exponent,   Props_Closed)

 The exponential is implication because cartesian closure is exactly the
 adjunction (R ∧ P) ⊢ Q  ↔  R ⊢ (P → Q), the deduction theorem. 

 --------
 nLab：https://ncatlab.org/nlab/show/Heyting+algebra
 nLab：https://ncatlab.org/nlab/show/bicartesian+closed+category
 Wikipedia：https://en.wikipedia.org/wiki/Heyting_algebra

 对象是命题（`Prop`），而态射 P ~> Q 是一个蕴含，即一个 `P → Q`（`Basics.impl`）的证明。由于每个 Hom-集合都是平凡的（`equiv f g := True`），因此这是一个薄/序范畴：任意两个对象之间最多有一个箭头，因此当且仅当 P 蕴含 Q 时，P ~> Q 才存在。这使得 Props 成为按蕴含排序的命题的前序。

 配备下面的逻辑连接词，它是一个双积闭薄范畴——一个 Heyting 预代数——用于模拟直觉主义命题逻辑：1 = 真          （终端,   Props_Terminal）
 0 = 假          （初始,   Props_Initial）
 P × Q = P ∧ Q （乘积,   Props_Cartesian）
 P + Q = P ∨ Q （余积,   Props_Cocartesian）
 Q ^ P = P → Q （指数,   Props_Closed）

 指数是蕴涵，因为笛卡尔闭包恰好是
 伴随关系 (R ∧ P) ⊢ Q  ↔  R ⊢ (P → Q)，即演绎定理。
*)

(*
   【Props 范畴实例展开】/ Props instance walkthrough
   （薄注；受众同 Functor.v）

   1) 这是什么 / What this is
      Props = 命题按蕴涵排序的薄范畴：对象=Prop；P~>Q = 证明 P→Q。
      Thin category of propositions ordered by implication.
      ≈ := True（证明无关）。逻辑：1=True，0=False，×=∧，+=∨，指数=→（Heyting）。
      Proof-irrelevant ≈. Logic: True/False/∧/∨/→ as (co)limits/exp.

   2) 关键字段 / Key fields
      - obj := Prop；hom := Basics.impl
      - homset.equiv := True；id/compose = 蕴涵的自反/传递

   Haskell 对照：像 Constraint/证明无关的 ⇒；Curry–Howard 的命题侧。
   Analogy: proof-irrelevant constraints; CH propositions side.

   阅读：Props → Terminal/Initial/Cartesian/Closed 逻辑实例。
   Read: Props → logical (co)limits/CCC structure below.
*)
Program Definition Props : Category := {|
  obj     := Prop;                         (* objects are propositions / 对象是命题 *)
  hom     := Basics.impl;                  (* P ~> Q is the implication P → Q / P ~> Q 是蕴含 P → Q *)
  (*
 The hom-setoid is trivial, so any two proofs P → Q are identified: Props
 is thin. (This needs no proof-irrelevance axiom; `equiv := True` does it
 definitionally, the same idiom as Proset.v and Roof.v.) 

 --------
 同态等价类是平凡的，所以任何两个证明 P → Q 都是相同的：Props 是稀疏的。（这不需要证明不可区分公理；`equiv := True` 在定义上就实现了，与 Proset.v 和 Roof.v 的习惯用法相同。）
*)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;                 (* identity implication P → P / 恒等蕴涵 P → P *)
  compose := fun _ _ _ g f x => g (f x)    (* transitivity of implication / 蕴涵的传递性 *)
|}.

(*
 Terminal object: True is the top proposition, with `I : True` giving the
 unique map P ~> True (every P implies True). 

 --------
 终端对象：True 是最高命题，`I : True` 给出了唯一映射 P ~> True（每个 P 都蕴含 True）。
*)
#[export]
Program Instance Props_Terminal : @Terminal Props := {
  terminal_obj := True;                    (* 1 = True *)
  one := fun _ _ => I                       (* ! : P → True *)
}.

(*
 Initial object: False is the bottom proposition; ex falso quodlibet gives
 the unique map False ~> P (False implies every P). 

 --------
 初始对象：False 是最底层命题；ex falso quodlibet 给出唯一映射 False ~> P（False 蕴含每个 P）。
*)
#[export]
Program Instance Props_Initial : @Initial Props := {
  terminal_obj := False;                   (* 0 = False (terminal in Props^op) / 0 = 假（Props^op 中的终端） *)
  one := fun _ _ => False_rect _ _          (* ¡ : False → P, by ex falso / ¡ : 假 → P, 根据假言推理 *)
}.

(*
 Product: conjunction. P ∧ Q is the meet, with proj1/proj2 the projections
 and conj the pairing of two implications. 

 --------
 产品：连接词。P ∧ Q 是交，proj1/proj2 是投影，conj 是两个蕴含的配对。
*)
#[export]
Program Instance Props_Cartesian : @Cartesian Props := {
  product_obj := and;                      (* P × Q = P ∧ Q *)
  fork := fun _ _ _ f g x => conj (f x) (g x);  (* ⟨f, g⟩ : R → P ∧ Q *)
  exl  := fun _ _ p => proj1 p;            (* first projection P ∧ Q → P / 第一投射 P ∧ Q → P *)
  exr  := fun _ _ p => proj2 p             (* second projection P ∧ Q → Q / 第二投影 P ∧ Q → Q *)
}.

(*
 Coproduct: disjunction. P ∨ Q is the join, with the injections or_introl/
 or_intror and case analysis providing the copairing. (product_obj names the
 coproduct here, since Cocartesian is Cartesian read in Props^op.) 

 --------
 余积：析取。P ∨ Q 是并集，其对应的注入为 or_introl/or_intror，使用 case 分析提供余配对。（product_obj 在这里命名余积，因为 Cocartesian 在 Props^op 中被理解为 Cartesian。）
*)
#[export]
Program Instance Props_Cocartesian : @Cocartesian Props := {
  product_obj := or;                       (* P + Q = P ∨ Q *)
  fork := fun _ _ _ f g x =>               (* copairing [f, g] : P ∨ Q → R / 共配对 [f, g] ：P ∨ Q → R *)
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;        (* left injection P → P ∨ Q / 左侧引入 P → P ∨ Q *)
  exr  := fun _ _ p => or_intror p         (* right injection Q → P ∨ Q / 右注入 Q → P ∨ Q *)
}.

(* Exponential: implication. Q ^ P = P → Q, and exp_iso is the currying bijection Hom(R ∧ P, Q) ≅ Hom(R, P → Q) witnessing (- ∧ P) ⊣ (P → -). / 指数：蕴含。Q ^ P = P → Q，并且 exp_iso 是函子双射 Hom(R ∧ P, Q) ≅ Hom(R, P → Q)，见证了 (- ∧ P) ⊣ (P → -)。 *)
#[export]
Program Instance Props_Closed : @Closed Props _ := {
  exponent_obj := Basics.impl;             (* Q ^ P = P → Q *)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
