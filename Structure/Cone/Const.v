Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)
 nLab: https://ncatlab.org/nlab/show/diagonal+functor

 A cone over a diagram F : J ⟶ C with apex N is the same data as a natural
 transformation Δ(N) ⟹ F out of the constant (diagonal) functor at N, and
 the same data as an object of the comma category (Δ ↓ F). The two lemmas
 below realise the first two of these equivalences in library notation:
 [Cone_Natural_Transform] proves Δ[J](N) ⟹ F ↔ Cone[N] F (a leg family with
 apex N), and [Cone_Comma] proves (Δ ↓ Δ(F)) ↔ Cone F (the diagram F is
 encoded as the constant functor Δ(F) : 1 ⟶ [J, C] so that both sides of the
 comma share a codomain). Limits arise as the universal/terminal such cone,
 equivalently as the right adjoint Δ ⊣ lim of the diagonal functor.

 Wikipedia: “At first glance cones seem to be slightly abnormal
 constructions in category theory. They are maps from an object to a functor
 (or vice versa). In keeping with the spirit of category theory we would
 like to define them as morphisms or objects in some suitable category. In
 fact, we can do both.

 ”Let J be a small category and let Cᴶ be the category of diagrams of type J
 in C (this is nothing more than a functor category). Define the diagonal
 functor Δ : C → Cᴶ as follows: Δ(N) : J → C is the constant functor to N
 for all N in C.

 “If F is a diagram of type J in C, the following statements are equivalent:

 - ψ is a cone from N to F
 - ψ is a natural transformation from Δ(N) to F
 - (N, ψ) is an object in the comma category (Δ ↓ F)

 ”The dual statements are also equivalent:

 - ψ is a co-cone from F to N
 - ψ is a natural transformation from F to Δ(N)
 - (N, ψ) is an object in the comma category (F ↓ Δ)

 “These statements can all be verified by a straightforward application of
 the definitions. Thinking of cones as natural transformations we see that
 they are just morphisms in Cᴶ with source (or target) a constant functor.” 

 --------
 nLab: https://ncatlab.org/nlab/show/cone
 Wikipedia: https://en.wikipedia.org/wiki/Cone_(category_theory)
 nLab: https://ncatlab.org/nlab/show/diagonal+functor

 一个以顶点 N 为 apex 的图 F : J ⟶ C 的锥与从 N 的常量（对角）函子出发的自然变换 Δ(N) ⟹ F 是相同的数据，并且与对逗号范畴 (Δ ↓ F) 的一个对象的数据相同。下面的两个引理以库符号实现了这两种等价的前两种：
 [Cone_Natural_Transform] 证明 Δ [J] (N) ⟹ F ↔ Cone [N]  F（一个以 N 为顶点的腿族），并且 [Cone_Comma] 证明 (Δ ↓ Δ(F)) ↔ Cone F（图 F 被编码为常量函子 Δ(F) : 1 ⟶  [J, C]，以便逗号两边共享目标域）。极限出现为这样的普遍/终端锥等价地作为对角函子的右伴 Δ ⊣ lim。维基百科：“乍一看，圆锥（cones）似乎是在范畴论中稍微不正常的构造。它们是从一个对象到一个函子（或反之）的映射。秉承范畴论的精神，我们希望将它们定义为某个合适范畴中的态射或对象。实际上，我们两者都可以做到。

 “设 J 为一个小范畴，并设 Cᴶ 为 C 中类型为 J 的图的范畴（这不过是一个函子范畴）。将对角函子 Δ : C → Cᴶ 定义如下：Δ(N) : J → C 是到 N 的恒等函子，对于 C 中的所有 N。

 “如果 F 是 C 中类型为 J 的图，则以下陈述等价：

 - ψ 是从 N 到 F 的圆锥
 - ψ 是从 Δ(N) 到 F 的自然变换
 - (N, ψ) 是逗号范畴 (Δ ↓ F) 中的一个对象

 “对偶陈述也同样等价：”- ψ 是从 F 到 N 的余锥  
 - ψ 是从 F 到 Δ(N) 的自然变换  
 - (N, ψ) 是逗号范畴 (F ↓ Δ) 中的一个对象  

 这些陈述都可以通过直接应用定义来验证。将锥视为自然变换时，我们可以看到它们只是 Cᴶ 中的态射，其源（或目标）是一个常值函子。
*)

Lemma Cone_Natural_Transform `(F : [J, C]) :
  ∀ N : C, Δ[J](N) ⟹ F ↔ Cone[N] F.
Proof.
  split; intros.
  - construct; [ exact (X x) |].
    abstract(pose proof (naturality[X] _ _ f) as nat;
        simpl in nat;
        rewrite id_right in nat;
             now apply nat).
  - construct.
    + now apply X.
    + abstract(simpl; rewrite id_right; apply cone_coherence).
    + abstract(simpl; rewrite id_right; symmetry; apply cone_coherence).
Defined.

(*
 See Instance/Cones/Comma.v for the analogous statement upgraded to a
 functorial equivalence Cones F ≅[Cat] (Δ ↓ =(F)) between the whole category
 of cones and the comma category. 

 --------
 参见 Instance/Cones/Comma.v，了解将类似陈述提升为范畴函子等价 Cones F ≅ [Cat] (Δ ↓ =(F)) 的情况，该等价存在于整个圆锥类别与逗号类别之间。
*)

Lemma Cone_Comma `(F : [J, C]) : (Δ ↓ Δ(F)) ↔ Cone F.
Proof.
  split; simpl.
  - intros [[? ?] f].
    simplify; simpl in *.
    unshelve econstructor; [ exact o | unshelve econstructor ].
    + now apply f.
    + abstract(destruct f; simpl in *; intros x y f;
      rewrite <- (id_right (transform y));
      now apply naturality).
  - intros X.
    destruct X.
    exists (vertex_obj, vertex_obj).
    construct.
    + now apply vertex_map.
    + abstract(simpl;
               rewrite id_right;
               now apply cone_coherence).
    + abstract(simpl;
               rewrite id_right;
               symmetry;
               now apply cone_coherence).
Defined.
