# 计划索引 (Plan index) — 经典补全战役 phases 7–17

> **给执行者：从这里开始。** 本目录把冻结的总计划 `doc/classical-completion-plan.md` 的剩余工作，拆成**每阶段一份可独立执行的工单**，外加一份共享公约。每会话先读一次 `00-CONVENTIONS.md`，再一次处理一个完整的 `phase-NN-*.md`。本索引给出地图、依赖图、工具链，以及 phases 5–6（已完成）换来的执行教训。此处皆为工作态，不是已承诺交付。

原英文文件名与路径保持不变，便于对照总计划与 PR。

## 状态快照 (Status snapshot)（2026-07-08）

- **Phases 1–4** — 已合并入 `master`（PRs #191–#194）：funny tensor、Markov/copy-discard 栈、自由与着色 PROP、预幺半/效应。
- **Phase 5**（范畴等价、RAPL/LAPC、运送）— 完成，PR #195（`johnw/ct-phase5` → `master`）。fess 通过，门禁全绿。
- **Phase 6**（余单子、单子分解）— 完成，PR #196（`johnw/ct-phase6` → `johnw/ct-phase5`）。门禁全绿；fess 为环内自审计（见「阻塞原因」）。
- **Phases 7–17** — **未开始**。本目录即其计划。约 113 个 Coq 文件。

分支 `johnw/ct-phase7` 已作为标签存在于 phase-6 尖端，可接着用。

## 阻塞原因 (The blocker)（为何 7–17 曾暂停）

（英文原文细节保留于 git 历史 / 总计划；要点：外环额度与探针失败曾迫使文档先行。现 zh-CN 分支上的文档翻译不替代执行那些 phase 工单。）

## 如何使用本计划集 (How to use)

1. 读 `00-CONVENTIONS.md`（宇宙、公理、门禁、提交约定）。
2. 按依赖顺序选一个 `phase-NN-*.md`。
3. 把该文件当完整工单执行；完成后更新本索引状态。

## 阶段地图 (Phase map)

| 文件 | 主题 |
|------|------|
| `phase-07-falgebras-lambek-adamek.md` | F-代数、Lambek、Adámek |
| `phase-08-factorization-regular-karoubi.md` | 分解系统、正则、Karoubi |
| `phase-09-monadicity.md` | 单子性 |
| `phase-10-displayed-fibrations-grothendieck.md` | 展示、纤维化、Grothendieck |
| `phase-11-additive-structure.md` | 加性结构 |
| `phase-12-coends-profunctors-day-drinfeld.md` | （余）端、双函子、Day、Drinfeld |
| `phase-13-bicategory-mates.md` | 双范畴与 mates |
| `phase-14-aft-reflective-localization.md` | 伴随函子定理、反射、局部化 |
| `phase-15-enriched-double-categories.md` | 充实与双重范畴 |
| `phase-16-lawvere-operads.md` | Lawvere 理论与 operad |
| `phase-17-topos.md` | Topos |
| `phase-18-concept-docs.md` | 概念文档 |

书籍目录战役见 `books-catalog-campaign.md` 与 `books/`。

详细英文工单正文仍在各 `phase-*.md` 文件中（标识符与检查清单未改）；需要逐步执行时打开对应文件。
