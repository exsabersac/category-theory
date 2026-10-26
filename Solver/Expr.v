Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.

(**
* Abstract syntax for the categorical solver

    This is the bottom of the [Solver/] reflective decision procedure: a
    first-order syntax of categorical expressions that goals are reified into
    (see Solver/Reify.v), interpreted back to real morphisms (Solver/Denote.v),
    normalized (Solver/Normal.v), and decided (Solver/Decide.v).  The technique
    is the standard “proof by reflection”: represent the term as data, compute
    on that data, and relate the computation back to the original goal — see
    Adam Chlipala's “Certified Programming with Dependent Types” (CPDT), from
    which much of this solver is adapted.

    Objects and morphism variables are referred to by de Bruijn-style indices
    into ambient lists ([objs], [arrs]); the [Objects]/[Arrows] classes below
    package those lists together with the interpretation functions that resolve
    the indices to concrete objects and morphisms of a fixed category [cat].

--------
* 范畴求解器的抽象语法

这是[Solver/]反射决策过程的底层：一个一阶的范畴表达式语法，目标被实体化为这些表达式（见 Solver/Reify.v），然后再解释回真实的态射（Solver/Denote.v），进行归一化（Solver/Normal.v），并作出决定（Solver/Decide.v）。该技术是标准的“反射证明”: 将术语表示为数据，在这些数据上计算，并将计算结果与原始目标关联——参见Adam Chlipala的《依赖类型的认证编程》(CPDT)，本求解器的大部分内容是从中改编而来的。

对象和态射变量通过 de Bruijn 风格的索引引用到环境列表中（[objs], [arrs]）；下面的 [Objects]/[Arrows] 类将这些列表与解释函数打包在一起，这些解释函数将索引解析为固定范畴 [cat] 的具体对象和态射。
*)

(* An object of the syntax is just an index into the ambient [objs] list. / 语法对象只是对环境 [objs] 列表的一个索引。 *)
Definition Obj := nat.

(*
Resolve an object index to a concrete object of [C], falling back to the
   default [d] when the index is out of range (so the lookup is total).

--------
将对象索引解析为 [C] 的具体对象，当索引超出范围时回退到默认的 [d]（因此查找是完全的）。
*)
Definition objD' {C : Category} (d : C) (objs : list C) (n : Obj) :=
  List.nth n objs d.

(*
The hom-set type a morphism variable of typing [(dom, cod)] must inhabit;
   used below as the index family [B] of the heterogeneous [arrs].

--------
同态集合类型 一个类型为 [(dom, cod)] 的态射变量必须属于；下面用作异构 [arrs] 的索引族 [B]。
*)
Definition arrD' {C : Category} (d : C) (objs : list C) '(dom, cod) :=
  objD' d objs dom ~> objD' d objs cod.

(*
The objects an [Expr] may mention: a default object [def_obj] (used by the
   total lookup [objD]) together with the list [objs] they index into.  [objD]
   is a let-bound class field, i.e. a derived projection rather than a field
   the user must supply.

--------
[Expr] 可能提到的对象：一个默认对象 [def_obj]（由总查找 [objD] 使用）以及它们索引的列表 [objs]。[objD] 是一个 let 绑定的类字段，即派生投影，而不是用户必须提供的字段。
*)
Class Objects (cat : Category) := {
  def_obj : cat;
  objs : list cat;
  objD := objD' def_obj objs;
}.

(*
The morphism variables an [Expr] may mention.  [tys] gives the (dom, cod)
   index pair typing each variable, and [arrs] is the heterogeneous list (see
   Lib/IList.v) holding the concrete morphism for each variable, where entry
   [i] inhabits [arrD (nth i tys)].  A [Morph i] term thus denotes [arrs]'s
   [i]-th morphism.

--------
形态变量 [Expr] 可能会提到。[tys] 给出了对每个变量的（dom, cod）索引对类型，而 [arrs] 是一个异质列表（见 Lib/IList.v），保存每个变量的具体态射，其中条目 [i] 属于 [arrD (nth i tys)]。因此，一个 [Morph i] 项表示 [arrs] 的第 [i] 个态射。
*)
Class Arrows (cat : Category) := {
  has_objects : Objects cat;

  arrD := arrD' def_obj objs;
  tys  : list (Obj * Obj);
  arrs : ilist (B:=arrD) tys;
}.
#[export] Existing Instance has_objects.

(*
Syntax of a single morphism, built from identities, morphism variables, and
   composition.  This is exactly a term of the free category on the quiver
   whose edges are the variables [arrs]: morphisms there are paths of edges and
   identities are empty paths, and the category laws relating these terms are
   quotiented out by normalization in Solver/Normal.v.  [Morph a] indexes the
   ambient [arrs]/[tys].
   nLab: https://ncatlab.org/nlab/show/free+category

--------
单一态射的语法，由恒等态射、态射变量和组合构建。这正是以这些变量为边的箭图自由范畴的一个项：那里态射是边的路径，恒等态射是空路径，涉及这些项的范畴律在 Solver/Normal.v 中通过归一化被取商。[Morph a] 索引了环境 [arrs]/[tys]。
nLab: https://ncatlab.org/nlab/show/free+category
*)
Inductive Term : Set :=
  | Ident
  | Morph (a : nat)
  | Comp  (f g : Term).

(*
Syntax of a decidable goal: the propositional connectives over morphism
   equivalences.  [Equiv x y f g] asserts that terms [f] and [g], both typed
   [x ~> y] (with [x y : Obj] object indices), denote equivalent morphisms.

--------
可判定目标的语法：关于同态等价的命题连接词。[Equiv x y f g] 断言项 [f] 和 [g]，均为类型 [x ~> y]（带有 [x y : Obj] 对象索引），表示等价的同态。
*)
Inductive Expr : Set :=
  | Top
  | Bottom
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr)
  | Equiv (x y : Obj) (f g : Term).
