Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section TracedMonoidal.

Context {C : Category}.

(** Traced monoidal category. / 带迹的单体范畴。 *)

(*
 nLab: https://ncatlab.org/nlab/show/traced+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Traced_monoidal_category

 A traced monoidal category is a (balanced or, as here, symmetric) monoidal
 category equipped with a trace, or “partial trace”/“feedback”, operator

 Tr^u_{x,y} : Hom(x ⨂ u, y ⨂ u) → Hom(x, y)              ([trace]),

 that contracts the shared object u against itself, leaving x ~> y. Here u is
 left implicit and inferred from the morphism, so a single polymorphic
 [trace] stands for the whole family Tr^u_{x,y}. Writing the laws in this
 library's notation (composition reads right to left, ⨂ is the tensor on
 morphisms), the axioms are, following Joyal-Street-Verity:

 trace (f ∘ g ⨂ id)  ≈  trace f ∘ g       (naturality in x / left
 tightening,
 [trace_natural_in_x]),
 trace (g ⨂ id ∘ f)  ≈  g ∘ trace f       (naturality in y / right
 tightening,
 [trace_natural_in_y]),
 trace (id ⨂ g ∘ f)  ≈  trace (f ∘ id ⨂ g)
 (dinaturality in u / sliding,
 [trace_natural_in_u]),
 trace (unit_right⁻¹ ∘ f ∘ unit_right)  ≈  f
 (vanishing I, [vanishing_unit]),
 trace f  ≈  trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc))
 (vanishing ⨂, [vanishing_tensor]),
 trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)  ≈  id[c] ⨂ trace f
 (superposing, [superposing]),
 trace braid  ≈  id[x]                     (yanking, [yanking]).

 The unitor [unit_right] and associator [tensor_assoc] conjugations make the
 non-strict (coherent) statements of vanishing and superposing typecheck;
 under strictness they reduce to nLab's Tr^I(f) = f, Tr^{u⨂v}(f) =
 Tr^u(Tr^v(f)), and Tr^u(id_c ⨂ f) = id_c ⨂ Tr^u(f). Yanking uses the
 symmetry [braid] at {x, x}, recovering the identity by tracing the swap. 

 --------
 nLab:  https://ncatlab.org/nlab/show/traced+monoidal+category 
 维基百科:  https://en.wikipedia.org/wiki/Traced_monoidal_category 

 跟踪单体范畴（traced monoidal category）是一个（平衡的，或者像这里的，对称的）单体范畴，配备有一个迹（trace），或者“部分迹/反馈”操作符

 Tr^u_{x,y} : Hom(x ⨂ u, y ⨂ u) → Hom(x, y)              ([trace]),

 它将共享对象 u 自我收缩，保留 x ~> y。在这里 u 默认省略，并从态射中推断，因此单个多态的
 [trace]  代表整个 family Tr^u_{x,y}。用该库的符号书写定律（组合从右到左读取，⨂ 是态射上的张量），公理如下，遵循 Joyal-Street-Verity:trace (f ∘ g ⨂ id)  ≈  trace f ∘ g       （在 x 上的自然性 / 左侧紧缩，[trace_natural_in_x]），
 trace (g ⨂ id ∘ f)  ≈  g ∘ trace f       （在 y 上的自然性 / 右侧紧缩，[trace_natural_in_y]），
 trace (id ⨂ g ∘ f)  ≈  trace (f ∘ id ⨂ g)   （在 u 上的双自然性 / 滑动，[trace_natural_in_u]），
 trace (unit_right⁻¹ ∘ f ∘ unit_right)  ≈  f   （消失 I, [vanishing_unit]），
 trace f  ≈  trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc))   （消失 ⨂, [vanishing_tensor]）（
 trace (tensor_assoc⁻¹ ∘ id [c] ⨂ f ∘ tensor_assoc) ≈ id [c] ⨂ trace f
 （叠加，[superposing]），
 trace braid ≈ id [x]                      （甩动，[yanking]）。单位元 [unit_right] 和结合子 [tensor_assoc] 的共轭作用使非严格（相干）类型检查的消失和叠加陈述成立；在严格条件下，它们简化为 nLab 的 Tr^I(f) = f，Tr^{u⨂v}(f) = Tr^u(Tr^v(f))，以及 Tr^u(id_c ⨂ f) = id_c ⨂ Tr^u(f)。拉回操作使用在 {x, x} 上的对称 [braid]，通过追踪交换操作恢复恒等映射。
*)

(*
 Feedback, fixed points, and the geometry of interaction

 nLab: https://ncatlab.org/nlab/show/traced+monoidal+category

 The trace operator axiomatizes feedback: a loop that plugs an output of
 type u back into an input of the same type, hiding an internal channel.
 Where a category has dual objects the loop comes for free — the u-wire
 bends around through the unit and counit of the duality, the [cc_unit]
 and [cc_counit] of Structure/Monoidal/CompactClosed.v, whose snake laws
 that file likewise annotates as “yanking” — and every compact closed
 category is canonically traced.  The definition of Joyal, Street and
 Verity (“Traced monoidal categories”, Mathematical Proceedings of the
 Cambridge Philosophical Society 119(3) 1996) isolates the equational
 theory of that loop without demanding duals, so that categories with no
 dual objects — cartesian categories, pointed cpos, partial functions
 under coproduct — can still support feedback.  Their aim was to abstract
 the notion of trace shared by algebraic topology, knot theory, and
 theoretical computer science; their structure theorem shows the axiom
 set complete.  The Int construction — in their words “a glorification
 of the construction of the integers from the natural numbers” — embeds
 every traced monoidal category fully and faithfully in a tortile
 monoidal category Int(C) whose objects are pairs of a positive and a
 negative part and whose composition closes off the middle object with
 [trace]; Int is left biadjoint to the forgetful 2-functor from tortile
 to traced monoidal categories, with details refined in later
 literature.  A trace is therefore exactly the restriction of a genuine
 duality loop, and the seven axioms are the legal moves on a string
 diagram with a feedback loop (Selinger, “A survey of graphical
 languages for monoidal categories”, Springer Lecture Notes in Physics
 813 2011).

 One operator carries three computational readings, keyed to the choice
 of tensor.  On finite-dimensional vector spaces [trace] is the partial
 matrix trace, summing over the loop index and recovering the classical
 trace when x and y are the unit.  On a cartesian category a trace is
 the same thing as a Conway fixed-point operator — a bijective
 correspondence found independently by Hasegawa and by Hyland (Hasegawa,
 “Recursion from Cyclic Sharing: Traced Monoidal Categories and Models
 of Cyclic Lambda Calculi”, TLCA 1997), with equivalent observations
 predating the traced formulation in the iteration theories of Bloom and
 Ésik — so that [trace] computes parameterized least fixed points on
 pointed cpos and models letrec and cyclic sharing (Hasegawa, “Models of
 Sharing Graphs: A Categorical Semantics of let and letrec”, Springer
 1999).  On partial functions with coproduct as tensor, [trace]
 iterates: run f, and feed the result back for as long as it lands in
 the loop summand u — the semantics of a while loop.

 A fourth reading is Girard's Geometry of Interaction (“Geometry of
 Interaction I: Interpretation of System F”, Logic Colloquium '88,
 North-Holland 1989), which models cut-elimination in linear logic as
 tokens circulating through a proof net.  Abramsky (“Retracing some
 paths in Process Algebra”, CONCUR 1996) identified traced monoidal
 categories as the common axiomatic core of its particle-style and
 wave-style formulations; in that tradition Int(C) is the GoI
 construction G(C), a morphism of which serves positive and negative
 channels while composition traces out the internal dialogue, and GoI
 situations over traced categories yield the linear combinatory
 algebras that capture the exponentials of linear logic (Abramsky,
 Haghverdi, Scott, “Geometry of Interaction and linear combinatory
 algebras”, MSCS 12(5) 2002).

 In this library the balanced setting of the original definition —
 braided monoidal with a twist, of which the symmetric case bundled by
 [traced_is_symmetric] is the specialization with trivial twist — lives
 in Structure/Monoidal/Balanced.v.  Neither direction of the
 compact-closed connection is formalized in-tree: the canonical trace
 on a compact closed category and the Int construction are the natural
 follow-up developments, as is the Hasegawa–Hyland correspondence at
 the interface with Structure/Monoidal/Cartesian.v.  Theory/Recursion.v
 develops recursion in its universal-property form, through initial
 algebras and catamorphisms; a traced cartesian category is the
 operator form of the same idea.  Instance/Coq/Comonad/Traced.v is
 unrelated despite the name: it houses the traced (cowriter) comonad
 over a monoid. 

 --------
 反馈、固定点与交互几何

 nLab：https://ncatlab.org/nlab/show/traced+monoidal+category迹算子公理化了反馈：一个将类型为 u 的输出重新接入同类型输入的回路，隐藏了内部通道。当一个范畴具有对偶对象时，这个回路自然存在——u 线通过对偶的单位和余单位弯曲，通过 Structure/Monoidal/CompactClosed.v 中的 [cc_unit] 和 [cc_counit]，它们的蛇形律在该文件中同样标注为“拉伸”——每个紧闭范畴都是规范的可追踪范畴。Joyal、Street 和 Verity 在《Traced monoidal categories》（剑桥哲学学会数学会刊 119(3) 1996）中给出的定义，分离了该回路的方程理论而不要求对偶，因此即使是没有对偶对象的范畴——笛卡儿范畴、有基点的 cpo、余积下的偏函数——仍然可以支持反馈。他们的目标是抽象出代数拓扑、结理论和理论计算机科学共有的迹的概念；他们的结构定理显示了公理集合是完整的。Int 构造——用他们的话说，是“从自然数构造整数的一个美化”——将每一个带迹的单oidal范畴完全且忠实地嵌入到一个扭结单oidal范畴 Int(C) 中，该范畴的对象是由正部和负部组成的对，其复合在中间对象上封闭 [trace]；Int 是从扭结单oidal范畴到带迹单oidal范畴的遗忘二维函子（2-functor）的左双伴随，其细节在后来的文献中有所完善。因此，迹正是一个真正对偶环的限制，而七个公理是带有反馈环的弦图上的合法操作（Selinger，“单体范畴图形语言综述”，Springer物理讲义813 2011）。一个算子携带三个计算读数，取决于张量的选择。在有限维向量空间中，[trace] 是部分矩阵迹，对循环指标求和，并在 x 和 y 为单位时恢复经典迹。在笛卡尔范畴上，追踪（trace）与康威不动点算子（Conway fixed-point operator）是同一件事——这是由 Hasegawa 和 Hyland 独立发现的双射对应关系（Hasegawa，《从循环共享到递归：追踪单体范畴与循环 λ 演算模型》，TLCA 1997），且在 Bloom 和 Ésik 的迭代理论中已有等效的观察，早于追踪公式的提出——因此 [trace] 计算带参数的最小不动点于有指点上完备偏序集，并且模拟 letrec 与循环共享（Hasegawa，《共享图的模型：let 与 letrec 的范畴语义》，Springer 1999）。在以余积为张量的偏函数上，[trace] 进行迭代：运行 f，并将结果反馈回去，只要它落在循环分量 u 中——即 while 循环的语义。第四种解读是吉拉尔的《交互几何》（“交互几何 I：系统 F 的解释”，逻辑专题讨论会 '88，北荷兰 1989），它将线性逻辑中的剪切消去建模为在证明网中循环的标记。Abramsky（《Retracing some paths in Process Algebra》，CONCUR 1996）将追踪单意类别识别为其粒子式和波动式表述的共同公理核心；在这一传统中，Int(C) 是 GoI 构造 G(C)，其态射为正负通道服务，而组合追踪内部对话，而在追踪类别上的 GoI 情况产生捕捉线性逻辑指数的线性组合代数（Abramsky、Haghverdi、Scott，《几何交互与线性组合代数》，MSCS 12(5) 2002）。在这个库中，原始定义的平衡设定——带有扭转的编织单体（braided monoidal），其中由 [traced_is_symmetric] 打包的对称情况是带有平凡扭转的特例——位于 Structure/Monoidal/Balanced.v 中。紧凑封闭连接的两个方向都没有在树中形式化：紧凑封闭范畴上的规范迹（canonical trace）和 Int 构造是自然的后续发展，同样还有与 Structure/Monoidal/Cartesian.v 接口处的 Hasegawa–Hyland 对应。Theory/Recursion.v 通过初始代数和 cata 形态（catamorphisms）以其泛性质（universal-property）形式发展递归；一个被追踪的笛卡尔范畴是同一思想的算子形式。Instance/Coq/Comonad/Traced.v 尽管名字相似，却无关：它包含了作用于幺半群上的被追踪的（cowriter）余单子（comonad）。
*)

Class TracedMonoidal := {
  (* The underlying symmetric monoidal structure (braiding + symmetry). / 基础的对称单体范畴结构（编织 + 对称）。 *)
  traced_is_symmetric : @SymmetricMonoidal C;

  (* Trace / partial trace: contracts the loop object u, Tr^u_{x,y}. / 迹 / 部分迹：收缩循环对象 u，Tr^u_{x,y}。 *)
  trace {x y u} : x ⨂ u ~> y ⨂ u → x ~> y;

  (* Naturality in x (left tightening): precompose by g ⨂ id outside trace. / x 的自然性（左紧缩）：在迹之外通过 g ⨂ id 进行前组合。 *)
  trace_natural_in_x {x x' y u} {f : x ⨂ u ~> y ⨂ u} {g : x' ~> x} :
    trace (f ∘ g ⨂ id) ≈ trace f ∘ g;
  (* Naturality in y (right tightening): postcompose by g ⨂ id outside trace. / 在 y 中的自然性（右收紧）：在迹外通过 g ⨂ id 后组合。 *)
  trace_natural_in_y {x y y' u} {f : x ⨂ u ~> y ⨂ u} {g : y ~> y'} :
    trace (g ⨂ id ∘ f) ≈ g ∘ trace f;
  (* Dinaturality / sliding in u: a loop morphism g may slide around the loop. / 自然性 / 在 u 中滑动：一个环形态射 g 可能沿着环滑动。 *)
  trace_natural_in_u {x y u u'} {f : x ⨂ u ~> y ⨂ u'} {g : u' ~> u} :
    trace (id ⨂ g ∘ f) ≈ trace (f ∘ id ⨂ g);

  (* Vanishing I: tracing over the unit object leaves f unchanged. / 消失 I：在单位对象上进行描绘不会改变 f。 *)
  vanishing_unit {x y} {f : x ~> y} :
    trace (unit_right⁻¹ ∘ f ∘ unit_right) ≈ f;
  (* Vanishing ⨂: a trace over u ⨂ v is two nested traces over u then v. / 消失 ⨂：在 u ⨂ v 上的迹是先对 u 再对 v 的两层嵌套迹。 *)
  vanishing_tensor {x y u v} {f : x ⨂ (u ⨂ v) ~> y ⨂ (u ⨂ v)} :
    trace f ≈ trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc));

  (* Superposing: an untraced factor c passes through the trace untouched. / 叠加：一个未被追踪的因子 c 通过追踪而不受影响。 *)
  superposing {a b c u} {f : a ⨂ u ~> b ⨂ u} :
    trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)
      ≈ id[c] ⨂ trace f;

  (* Yanking: tracing the braiding of x past itself yields the identity. / 扯动：沿着 x 的编结回溯自己会得到恒等映射。 *)
  yanking {x} : trace braid ≈ id[x];
}.
#[export] Existing Instance traced_is_symmetric.

Coercion traced_is_symmetric : TracedMonoidal >-> SymmetricMonoidal.

End TracedMonoidal.
