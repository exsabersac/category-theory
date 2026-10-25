Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** Strong natural transformations (compatible with tensorial strength)  / 强大的自然变换（与张量强度兼容）*)

(*
nLab: https://ncatlab.org/nlab/show/strong+natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   Given two strong endofunctors F, G : C ⟶ C on a monoidal category, each
   carrying a left strength strength[F], strength[G] (see Functor.Strong), a
   natural transformation N : F ⟹ G is *strong* when it is compatible with the
   two strengths, i.e. the square

     x ⨂ F y --- id ⨂ N_y ---> x ⨂ G y
        |                          |
     strength[F]               strength[G]
        |                          |
        v                          v
     F (x ⨂ y) --- N_{x⨂y} ---> G (x ⨂ y)

   commutes:  N_{x⨂y} ∘ strength[F] ≈ strength[G] ∘ (id_x ⨂ N_y).  This is the
   notion of morphism between strong functors that respects strength (Kock 1972;
   Moggi 1991; Ratkovic 2012, Def. 3.1.4); in the closed setting it corresponds
   to an enriched natural transformation between the induced C-enrichments.  No
   extra coherence beyond this single square is required: ordinary naturality of
   N already supplies the rest. 

--------
nLab：https://ncatlab.org/nlab/show/strong+natural+transformation
维基百科：https://en.wikipedia.org/wiki/Strong_monad

在一个单体范畴上，给定两个强自函子 F, G : C ⟶ C，每个都携带一个左强度 strength[F], strength[G]（见 Functor.Strong），当自然变换 N : F ⟹ G 与这两个强度兼容时，它是*强的*，即该方形

x ⨂ F y --- id ⨂ N_y ---> x ⨂ G y
        |                          |
     strength[F]               strength[G]
        |                          |
        v                          v
     F (x ⨂ y) --- N_{x⨂y} ---> G (x ⨂ y)

交换图：N_{x⨂y} ∘ strength[F] ≈ strength[G] ∘ (id_x ⨂ N_y)。这是尊重强度的强函子之间的态射的概念（Kock 1972；Moggi 1991；Ratkovic 2012，第 3.1.4 定义）；在闭合环境下，它对应于所引入的 C-增强之间的增强自然变换。除此单个方形之外，不需要额外的一致性：N 的普通自然性已经提供了其余部分。 
*)

Class Strong_Transform {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@StrongFunctor _ _ F}
      {G : C ⟶ C} `{@StrongFunctor _ _ G} (N : F ⟹ G) := {
  strength_transform {x y} :                         (* strength-compatibility square *)
    strength[G] ∘ id[x] ⨂ transform[N] y ≈ transform[N] _ ∘ strength[F]
}.
