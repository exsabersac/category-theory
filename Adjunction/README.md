# 伴随 (Adjunctions)

至少有四种方式给出伴随 F ⊣ G：

1. hom 集 `F a ~> b` 与 `a ~> U b` 之间的双射，且对 `a`、`b` 自然。这是 `Category.Theory.Adjunction` 中的定义。

2. 一对 `unit` 与 `counit` 自然变换，并以特定方式复合为恒等函子。见 `Category.Adjunction.Natural.Transformation`。

3. 一对 `unit` 与 `counit` 态射及其相关等式。这是把 (2) 用态射、C 与 D 中的等价、以及自然性条件写开，而不是用函子范畴 [C, D] 与 [D, C] 中的自然变换与等价。本库未给出此形式，因未使用。

4. hom 集函子 `Hom(F -, -)` 与 `Hom(-, U -)` 之间的同构。这是最简短的陈述，其余形式均可由此导出。见 `Category.Adjunction.Hom`。

这四种表述如何互相关联，见 Wikipedia 页面
[Adjunctions](https://en.wikipedia.org/wiki/Adjoint_functors)。
