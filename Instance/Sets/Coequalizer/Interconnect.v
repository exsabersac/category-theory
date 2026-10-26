Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Coequalizer.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * * An evaluated coequalizer: interconnecting a set of ports / * * 一个已评估的协同终结器：连接一组端口 *)

(*
 Fong and Spivak, “Seven Sketches in Compositionality”, §6.2.4
 example 6.42 (printed p. 194).  Take X the set of “connect these two”
 markers and Y the set of ports of a circuit; the two families of
 arrows give functions f, g : X → Y, and the coequalizer of f and g is
 the set of TERMINALS resulting from the interconnection -- the
 connected groups of ports.

 This file works one such circuit end to end over
 Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers]: six ports, three
 wires, and three resulting terminals, one of which is a lone
 unconnected port.  Nothing here is a new construction; it is the
 delivered one, exercised.

 WHY [Sets] AND NOT [FinSet], AND WHAT “EVALUATED” MEANS HERE

 [FinSet] is where this library's finite combinatorics computes:
 Instance/FinSet/Pushout.v labels connected components with
 [components], counts them at [po_apex], maps into them at
 [po_cls] and selects representatives at [po_cls_rep].
 A witness built there would compute the terminal COUNT by [eq_refl] on
 a numeral.  It would also compute it in a category for which no
 [HasCoequalizers] instance exists -- building one is a separate piece
 of work and is NOT part of this file or of the issue it serves --
 so it would exercise a parallel construction rather than the delivered
 one.  The witness is therefore over [Sets].

 Over [Sets] the delivered coequalizer is the codomain under a coarser
 `≈`, and the coarser `≈` is an INDUCTIVE relation, so it does not
 reduce: exhibiting two ports as connected is a derivation, and no
 amount of computation will produce one.  What does reduce is
 everything on the other side of the universal property, and that is
 where this file puts its [eq_refl]s:

 - the coequalizer's CARRIER is the ic_port type on the nose
 ([interconnect_carrier]);
 - the terminal-labelling map computes on every closed port
 ([label_P0] and its five siblings);
 - the mediator produced by [coeq_desc] out of the delivered
 [IsCoequalizer] IS that labelling, evaluated
 ([interconnect_med_at_P2] and siblings) -- so it is the universal
 property being run, not a hand-built map;
 - one leg of the isomorphism with the three-element terminal set
 closes by [eq_refl] ([ic_label_of_rep]), the other being the
 six derivations that [ic_rep_of_label] collects.

 And the count is PROVED, not read off: [interconnect_iso] exhibits
 the coequalizer as isomorphic in [Sets] to a three-element discrete
 setoid whose three elements are pairwise distinct
 ([ic_terminal_distinct]) and which has no others
 ([ic_terminal_cases]).  Without those two the isomorphism would pin
 nothing.

 NEGATIVE RESULTS GO OUT THROUGH THE MEDIATOR.  That two ports are NOT
 connected cannot be shown by induction on the generated relation --
 an induction over a congruence yields no negation -- so
 [port_P0_P3_apart] and its siblings map out into the terminal setoid,
 where the question is an equation between constructors and
 [discriminate] settles it.  This is the discipline
 Instance/Mod/Tensor.v uses for the same reason. 

 --------
 Fong 和 Spivak，《组合性七个草图》，§6.2.4 示例 6.42（印刷第 194 页）。取 X 为“连接这两个”的标记集合，Y 为电路端口的集合；这两族箭头给出函数 f, g : X → Y，f 和 g 的共等化子是由互连产生的端子集合——端口的连接组。

 这个文件对 Instance/Sets/Coequalizer.v 中的一个电路从头到尾进行了处理：[Sets_HasCoequalizers]：六个端口，三根导线，以及三个产生的端子，其中一个是孤立未连接的端口。这里没有任何新的构造；它就是提供的那个，已经演练过。

 为什么是 [Sets] 而不是 [FinSet]，以及这里“评估”是什么意思[FinSet] 是这个库的有限组合计算执行的地方：
 Instance/FinSet/Pushout.v 使用 [components] 对连通分支进行标记，
 在 [po_apex] 上计数，映射到 [po_cls] 上，并在 [po_cls_rep] 上选择代表。
 在那里构建的一个证据将在一个数值上通过 [eq_refl] 计算终端 COUNT。
 它还会在一个没有 [HasCoequalizers] 实例的类别中计算它——构建一个是一个单独的工作部分，并不是这个文件或其所服务的问题的一部分——
 因此它将执行一个平行构造而不是提供的构造。
 因此这个证据是超出 [Sets] 的。在 [Sets] 上，所传递的余等化器是在更粗糙的 `≈` 下的余域，并且更粗糙的 `≈` 是一个归纳关系，因此它不会简化：将两个端口显示为已连接是一种推导，任何计算都无法生成它。可以简化的是泛性质另一侧的一切，这正是该文件放置其 [eq_refl] 的地方：- 共轭器的 CARRIER 是鼻子上的 ic_port 类型（[interconnect_carrier]）；
 - 端子标注映射在每个闭端口上计算（[label_P0] 及其五个同类）；
 - 由 [coeq_desc] 从交付的 [IsCoequalizer] 生成的中介者就是该标注，经过评估（[interconnect_med_at_P2] 及其同类）——所以运行的是通用属性，而不是手工构建的映射；
 - 与三元素端子集合的同构的一条腿由 [eq_refl]（[ic_label_of_rep]）闭合，另一条腿是 [ic_rep_of_label] 收集的六个推导。并且计数是被证明的，而不是直接读出的：[interconnect_iso] 展示了在 [Sets] 中上同余器是同构的，对应于一个三元素的离散等价类集合，其三元素彼此不同（[ic_terminal_distinct]），并且没有其他元素（[ic_terminal_cases]）。如果没有这两个元素，该同构将无法确定任何东西。

 负结果通过中介者传出。两个端口不连接不能通过生成关系的归纳来证明——在一个同余上进行归纳不会产生否定——所以 [port_P0_P3_apart] 及其兄弟映射到终端等价类集合，在那里这个问题是构造子之间的等式，而 [discriminate] 解决了它。这就是 Instance/Mod/Tensor.v 出于相同原因所使用的规范。
*)

(*
 WHAT IS DELIVERED

 * The circuit: [ic_port] (six), [ic_wire] (three), [ic_terminal] (three), each
 as a discrete setoid, with [ic_wire_src] and [ic_wire_dst] the two ends.

 * [Interconnect], the coequalizer of that pair, taken from
 [Sets_HasCoequalizers] rather than rebuilt
 ([interconnect_is_chosen], by [eq_refl]).

 * The three groups, each proved to be a group
 ([port_P0_P1_merged], [port_P0_P2_merged], [port_P4_P5_merged]) and
 proved to be separate from the others ([port_P0_P3_apart],
 [port_P0_P4_apart], [port_P3_P4_apart]).

 * [interconnect_iso], the coequalizer identified with the
 three-element terminal setoid, with [ic_terminal_distinct] and
 [ic_terminal_cases] pinning that set at exactly three elements.

 * Evaluated readings throughout, all [eq_refl] -- including the
 defining triangle [interconnect_triangle], which holds pointwise by
 [reflexivity] because the coequalizing map is the identity
 function.

 WHAT IS NOT DELIVERED

 * NO [HasCoequalizers FinSet], and no claim about FinSet at all.

 * NO GENERAL CIRCUIT VOCABULARY.  There is no type of circuits, no
 composition of interconnections, and no connection to
 Construction/Cospan/ or to the hypergraph-category development,
 which is where Seven Sketches takes the example next.

 * NO DECISION PROCEDURE for connectedness of the generated relation.
 Each negative below is a separate mapping-out argument; nothing
 produces them uniformly.

 A NOTE ON NAMES.  The circuit vocabulary carries an [Ic]/[ic_] prefix
 ([ic_port], [IcP0], [ic_wire], [IcW0], [ic_terminal], [IcT0], [ic_label],
 [ic_rep]) because the Makefile's [print-assumptions] target requires
 every audited module into ONE scope, where the later [Require] wins a
 duplicated short name and the audit then silently reports on the wrong
 constant.  Unprefixed, [wire] would have collided with
 Construction/ColouredPROP.v and Construction/PROP/Term.v, and
 [P1] with Structure/Monoidal/Drinfeld.v.

 STATUS: axiom-free.  61 named constants (the three inductives and
 their twelve constructors included), no [Program] obligations, all reporting
 “Closed under the global context”; the Makefile's
 [print-assumptions] target audits eight of them. 

 --------
 交付内容

 * 电路：[ic_port]（六个）、[ic_wire]（三个）、[ic_terminal]（三个），每个作为一个独立的集合效应，[ic_wire_src] 和 [ic_wire_dst] 为两端。

 * [Interconnect]，该对的余二等化器，取自 [Sets_HasCoequalizers] 而非重新构建（[interconnect_is_chosen]，通过 [eq_refl]）。

 * 三个群，每个都被证明是一个群（[port_P0_P1_merged]、[port_P0_P2_merged]、[port_P4_P5_merged]），并且证明彼此独立（[port_P0_P3_apart]、[port_P0_P4_apart]、[port_P3_P4_apart]）。

 * [interconnect_iso]，被确定为三元素终端集合效应的余二等化器，[ic_terminal_distinct] 和 [ic_terminal_cases] 将该集合精确固定为三个元素。

 * 遍及的评估读数，全部为 [eq_refl]——包括定义三角形 [interconnect_triangle]，因 [reflexivity] 而逐点成立，因为余二等化映射是恒等函数。未交付的内容

 * 没有 [HasCoequalizers FinSet]，也完全没有关于 FinSet 的声明。

 * 没有通用电路词汇。没有电路类型，没有互连的组合，也没有与 Construction/Cospan 或超图范畴发展的联系，而 Seven Sketches 接下来就在该示例中使用这些内容。

 * 没有已生成关系连通性的决策过程。下面每个否定都是一个单独的映射论证；没有任何方法能够统一地产生这些结论。关于名称的说明。电路词汇带有 [Ic] / [ic_] 前缀（[ic_port]、[IcP0]、[ic_wire]、[IcW0]、[ic_terminal]、[IcT0]、[ic_label]、[ic_rep]），因为 Makefile 的 [print-assumptions] 目标要求将每个被审核的模块放入一个作用域，其中后来的 [Require] 将覆盖重复的短名称，审核然后会默默地报告错误的常量。如果没有前缀，[wire] 会与 Construction/ColouredPROP.v 和 Construction/PROP/Term.v 冲突，而 [P1] 会与 Structure/Monoidal/Drinfeld.v 冲突。

 状态：无公理。61 个命名常量（包括三个归纳类型及其十二个构造函数），无 [Program] 义务，全部报告“在全局上下文下闭合”；Makefile 的 [print-assumptions] 目标审核其中八个。
*)

(** ** The circuit / ** 电路 *)

Inductive ic_port : Set := IcP0 | IcP1 | IcP2 | IcP3 | IcP4 | IcP5.
Inductive ic_wire : Set := IcW0 | IcW1 | IcW2.
Inductive ic_terminal : Set := IcT0 | IcT1 | IcT2.

Definition IcPortSet : SetoidObject :=
  {| carrier := ic_port ; is_setoid := eq_Setoid ic_port |}.
Definition IcWireSet : SetoidObject :=
  {| carrier := ic_wire ; is_setoid := eq_Setoid ic_wire |}.
Definition IcTerminalSet : SetoidObject :=
  {| carrier := ic_terminal ; is_setoid := eq_Setoid ic_terminal |}.

(*
 Three wires: IcP0-IcP1, IcP1-IcP2, IcP4-IcP5.  IcP3 is left unconnected, which is
 what makes the third terminal a singleton and keeps the example from
 degenerating into “everything is joined”. 

 --------
 三根线：IcP0-IcP1，IcP1-IcP2，IcP4-IcP5。IcP3未连接，这正是使第三个端子成为单独端子并防止示例退化为“所有端子都连接在一起”的原因。
*)
Definition ic_wire_src_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP0 | IcW1 => IcP1 | IcW2 => IcP4 end.

Definition ic_wire_dst_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP1 | IcW1 => IcP2 | IcW2 => IcP5 end.

Definition ic_wire_src : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_src_fun |}. Defined.

Definition ic_wire_dst : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_dst_fun |}. Defined.

(* * ** The coequalizer, taken from the delivered instance / * ** 平等化器，取自所提供的实例 *)

Definition Interconnect : SetoidObject := SetsCoeq ic_wire_src ic_wire_dst.

Definition interconnect_proj : IcPortSet ~{Sets}~> Interconnect :=
  sets_coeq_proj ic_wire_src ic_wire_dst.

(* It IS the object [Sets_HasCoequalizers] chooses, by conversion. / 它是对象 [Sets_HasCoequalizers] 通过转换选择的。 *)
Example interconnect_is_chosen :
  `1 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst)
    = Interconnect.
Proof. reflexivity. Qed.

(* ... and so is the coequalizing map. / ... 同样，等同化映射也是如此。 *)
Example interconnect_proj_is_chosen :
  `1 (`2 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst))
    = interconnect_proj.
Proof. reflexivity. Qed.

(*
 The carrier is the ic_port type on the nose, and the coequalizing map is
 the identity function on it: only `≈` moved. 

 --------
 载体是鼻部的 ic_port 类型，共轭映射是其上的恒等函数：只有 `≈` 移动了。
*)
Example interconnect_carrier : carrier Interconnect = ic_port.
Proof. reflexivity. Qed.

Example interconnect_proj_at (p : ic_port) : interconnect_proj p = p.
Proof. reflexivity. Qed.

(* * ** The three terminals, and that they are three / * ** 三个端子，并且它们是三个 *)

Definition ic_label_fun (p : ic_port) : ic_terminal :=
  match p with
  | IcP0 => IcT0 | IcP1 => IcT0 | IcP2 => IcT0
  | IcP3 => IcT1
  | IcP4 => IcT2 | IcP5 => IcT2
  end.

Definition ic_label : IcPortSet ~{Sets}~> IcTerminalSet.
Proof. unshelve refine {| morphism := ic_label_fun |}. Defined.

Example label_P0 : ic_label IcP0 = IcT0. Proof. reflexivity. Qed.
Example label_P1 : ic_label IcP1 = IcT0. Proof. reflexivity. Qed.
Example label_P2 : ic_label IcP2 = IcT0. Proof. reflexivity. Qed.
Example label_P3 : ic_label IcP3 = IcT1. Proof. reflexivity. Qed.
Example label_P4 : ic_label IcP4 = IcT2. Proof. reflexivity. Qed.
Example label_P5 : ic_label IcP5 = IcT2. Proof. reflexivity. Qed.

(* The labelling coforks the wire pair: one computation per wire. / 标记共叉接电线对：每根电线一次计算。 *)
Lemma ic_label_coforks : ic_label ∘ ic_wire_src ≈ ic_label ∘ ic_wire_dst.
Proof. intros [ | | ]; reflexivity. Qed.

(*
 The terminal set has exactly three elements: three cases and no
 others, and the three are pairwise distinct.  Without both halves the
 isomorphism below would pin no count. 

 --------
 终结集恰好有三个元素：三个情况，没有其他，并且这三个是两两不同的。如果没有两部分，下面的同构将无法确定任何计数。
*)
Lemma ic_terminal_cases (t : ic_terminal) : ((t = IcT0) ∨ (t = IcT1)) ∨ (t = IcT2).
Proof. destruct t; [ left; left | left; right | right ]; reflexivity. Qed.

Lemma ic_terminal_distinct :
  ((IcT0 = IcT1 → False) ∧ (IcT0 = IcT2 → False)) ∧ (IcT1 = IcT2 → False).
Proof. repeat split; intro E; discriminate E. Qed.

(** ** The universal property, run / ** 通用属性，运行 *)

(*
 The mediator [coeq_desc] produces out of the DELIVERED
 [IsCoequalizer], evaluated at closed ports.  This is the point of the
 file: the arrow whose existence the universal property asserts is a
 function that computes. 

 --------
 调解器 [coeq_desc] 从 DELIVERED [IsCoequalizer] 中产生，在闭合端口处评估。这是该文件的重点：普遍性属性所断言存在的箭头是一个计算函数。
*)
Definition interconnect_med : Interconnect ~{Sets}~> IcTerminalSet :=
  unique_obj
    (coeq_desc (sets_coeq_IsCoequalizer ic_wire_src ic_wire_dst) ic_label ic_label_coforks).

Example interconnect_med_at_P0 : interconnect_med IcP0 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P2 : interconnect_med IcP2 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P3 : interconnect_med IcP3 = IcT1.
Proof. reflexivity. Qed.
Example interconnect_med_at_P5 : interconnect_med IcP5 = IcT2.
Proof. reflexivity. Qed.

(*
 ... and it IS the labelling, by conversion -- the universal property
 rebuilt nothing.  The defining triangle then holds pointwise by
 [reflexivity], the coequalizing map being the identity function. 

 --------
 ... 并且它确实是通过转换标记 -- 通用性质重建了什么都没有。然后，定义三角形按点成立，由 [reflexivity]，共等化映射是恒等函数。
*)
Example interconnect_med_is_label (p : ic_port) : interconnect_med p = ic_label p.
Proof. reflexivity. Qed.

Example interconnect_triangle : interconnect_med ∘ interconnect_proj ≈ ic_label.
Proof. intro p; reflexivity. Qed.

(* * ** What the interconnection joins / * ** 互连所连接的内容 *)

(* Directly joined by a wire. / 直接用一根电线连接。 *)
Lemma port_P0_P1_merged : @equiv _ Interconnect IcP0 IcP1.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW0). Qed.

Lemma port_P4_P5_merged : @equiv _ Interconnect IcP4 IcP5.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW2). Qed.

(*
 Joined only through a third port: this is where transitivity of the
 generated relation does the work, and it is a DERIVATION, not a
 computation. 

 --------
 仅通过第三个端口连接：这里是生成关系的传递性发挥作用的地方，这是一种推导，而不是计算。
*)
Lemma port_P0_P2_merged : @equiv _ Interconnect IcP0 IcP2.
Proof.
  exact (cq_trans ic_wire_src ic_wire_dst IcP0 IcP1 IcP2
           (cq_glue ic_wire_src ic_wire_dst IcW0) (cq_glue ic_wire_src ic_wire_dst IcW1)).
Qed.

(** ** What it does not join / ** 它不连接的东西 *)

(*
 Every negative goes out through [interconnect_med]: from a supposed
 identification in the coequalizer, respectfulness of the mediator
 gives an equation of terminals, and terminals are constructors. 

 --------
 每个负面通过 [interconnect_med] 发出：从共同化器中的假定识别开始，调解者的尊重性给出了终端的方程，而终端是构造器。
*)
Lemma interconnect_apart (p q : ic_port) (H : ic_label_fun p = ic_label_fun q → False) :
  @equiv _ Interconnect p q → False.
Proof.
  intro Hpq.
  exact (H (@proper_morphism _ _ _ _ interconnect_med p q Hpq)).
Qed.

Lemma port_P0_P3_apart : @equiv _ Interconnect IcP0 IcP3 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P0_P4_apart : @equiv _ Interconnect IcP0 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P3_P4_apart : @equiv _ Interconnect IcP3 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

(** ** The count, as an isomorphism / ** 计数，作为同构 *)

(* A chosen port in each group. / 每组中选择的端口。 *)
Definition ic_rep_fun (t : ic_terminal) : ic_port :=
  match t with IcT0 => IcP0 | IcT1 => IcP3 | IcT2 => IcP4 end.

(*
 The source is discrete, so respectfulness is [Proper (eq ==> _)] and
 instance resolution discharges it against reflexivity of the
 coequalizer's relation; both carriers are concrete, so nothing
 polymorphic is at stake in leaving it to resolution. 

 --------
 源是离散的，因此礼貌性是[Proper (eq ==> _)]，并且实例解析将其对等化器关系的自反性进行释放；两个承载者都是具体的，因此将其留给解析没有涉及任何多态性。
*)
Definition ic_rep : IcTerminalSet ~{Sets}~> Interconnect.
Proof.
  unshelve refine
    (@Build_SetoidMorphism ic_terminal (is_setoid IcTerminalSet)
       ic_port (is_setoid Interconnect) ic_rep_fun _).
Defined.

(*
 One leg computes: labelling a chosen representative returns its own
 terminal, for all three, by [eq_refl]. 

 --------
 一条腿计算：标记一个选定的代表会返回它自己的终端，对三者都是如此，由 [eq_refl]。
*)
Lemma ic_label_of_rep (t : ic_terminal) : ic_label_fun (ic_rep_fun t) = t.
Proof. destruct t; reflexivity. Qed.

(* The other leg is the six derivations -- one per port -- that each port is joined to its group's representative. / 另一条腿是六个派生——每个端口一个——每个端口都连接到其组的代表。 *)
Lemma ic_rep_of_label (p : ic_port) : @equiv _ Interconnect (ic_rep_fun (ic_label_fun p)) p.
Proof.
  destruct p.
  - apply coeq_rel_refl.
  - exact port_P0_P1_merged.
  - exact port_P0_P2_merged.
  - apply coeq_rel_refl.
  - apply coeq_rel_refl.
  - exact port_P4_P5_merged.
Qed.

(*
 Seven Sketches' conclusion, at this circuit: the coequalizer IS the
 set of terminals.  With [ic_terminal_cases] and [ic_terminal_distinct] this
 says the interconnection has exactly three terminals. 

 --------
 《七个素描》的结论，在这个电路中：余等化子就是端子集合。使用 [ic_terminal_cases] 和 [ic_terminal_distinct]，这意味着互连恰好有三个端子。
*)
Definition interconnect_iso : @Isomorphism Sets Interconnect IcTerminalSet.
Proof.
  unshelve refine {| to := interconnect_med ; from := ic_rep |}.
  - intro t; exact (ic_label_of_rep t).
  - intro p; exact (ic_rep_of_label p).
Defined.

(* Both legs read off, by conversion. / 两条腿通过换算读出。 *)
Example interconnect_iso_to (p : ic_port) : to interconnect_iso p = ic_label_fun p.
Proof. reflexivity. Qed.

Example interconnect_iso_from (t : ic_terminal) : from interconnect_iso t = ic_rep_fun t.
Proof. reflexivity. Qed.

(*
 The isomorphism is not vacuous in either direction: it identifies
 three ports with the same terminal and separates ports in different
 groups. 

 --------
 同构在任何方向上都不是空的：它将具有相同端子的三个端口识别出来，并将不同组中的端口分开。
*)
Example interconnect_iso_groups :
  ((to interconnect_iso IcP0 = IcT0) ∧ (to interconnect_iso IcP2 = IcT0))
    ∧ (to interconnect_iso IcP3 = IcT1).
Proof. repeat split; reflexivity. Qed.
