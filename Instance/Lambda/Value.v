Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** The values (canonical forms) of the call-by-value de Bruijn STLC. / 调用值 de Bruijn STLC 的值（规范形式）。 *)

(*
 [ValueP e] holds exactly when [e] is a value: a term that cannot reduce any
 further under the call-by-value strategy of [Step] (see [Value_irreducible]
 there).  The value grammar carved out by the constructors below is

 v ::= ()              (EUnit)
 | (v, v)          (Pair of values)
 | λ. e            (LAM, never reduced under)

 matching the standard CBV grammar for unit, products, and functions.  The
 eliminators -- [Fst], [Snd], [APP] -- are deliberately absent: a projection
 or application is a redex (or contains one), never a value.  [VAR] is absent
 too: progress ([strong_progress]) is stated for closed terms ([Exp []]),
 where no free variable can occur, so variables need not be values.  (nLab
 has no page for "value" in this PL sense: ncatlab.org/nlab/show/value is the
 mathematical "value of a function".)

 The predicate lands in [Set] rather than [Prop] so that downstream
 evaluators ([Eval]) may compute with the witness; [ValueP_irrelevance]
 recovers proof irrelevance constructively, so the [Set] placement costs no
 uniqueness. 

 --------
 [ValueP e] 当且仅当 [e] 是一个值时成立：一个在 [Step] 的按值求值策略下无法再进一步规约的项（参见 [Value_irreducible]）。下面由构造子划定的值语法是

 v ::= ()              (EUnit)
 | (v, v)          (值对)
 | λ. e            (LAM，在下文中从不规约)匹配单位、产品和函数的标准 CBV 语法。消去器 -- [Fst]、[Snd]、[APP] -- 故意缺失：投影或应用是一个还原式（或包含一个），从不属于值。[VAR] 也缺失：针对封闭项（[Exp []]）声明了进展性（[strong_progress]），其中不存在自由变量，因此变量不必是值。（nLab 在这个编程语言意义上的“值”没有相关页面：ncatlab.org/nlab/show/value 是函数的数学“值”。）

 谓词落在 [Set] 而不是 [Prop] 上，以便下游求值器（[Eval]）可以使用见证进行计算；[ValueP_irrelevance] 建设性地恢复了证明不相关性，因此 [Set] 的放置不会影响唯一性。
*)
Section Value.

Import ListNotations.

Open Scope Ty_scope.

(* [ValueP] is an inductive predicate that indicates whether an expression represents a value, i.e., that it does not reduce any further. / [ValueP] 是一个归纳谓词，用于指示一个表达式是否表示一个值，即它不能再进一步化简。 *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Set :=
  | UnitP : ValueP EUnit                          (* () is a value / () 是一个值 *)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP x → ValueP y → ValueP (Pair x y)       (* a pair of values is a value / 一对值是一个值 *)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) :
    ValueP (LAM e).                               (* an abstraction is a value / 抽象是一个值 *)

Derive Signature for ValueP.

#[local] Hint Constructors ValueP : core.

Fixpoint ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent elimination H1;
  dependent elimination H2.
  - reflexivity.
  - f_equal;
    now apply ValueP_irrelevance.
  - f_equal;
    now apply ValueP_irrelevance.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP Γ e ∨ ¬ ValueP Γ e.
Proof.
  induction e; try solve [now left|now right].
  destruct IHe1, IHe2.
  - left.
    now constructor.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
  - right.
    intro.
    dependent elimination H.
    contradiction.
Qed.

End Value.

Arguments ValueP {Γ τ} _.
Arguments UnitP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments LambdaP {Γ dom cod} _.
