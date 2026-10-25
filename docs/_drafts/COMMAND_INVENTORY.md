# category-theory 指令扫描（内部草稿）

仓库：`/workspace/category-theory`，分支：`docs/coq-commands-guide`（从 `zh-CN` 分出，避免与 COQ 导读/双语 worktree 冲突）。

优先示例文件（可读、偏入门）：
- `Theory/Category.v`、`Theory/Functor.v`、`Theory/Natural/*.v`、`Theory/Isomorphism.v`（若有）
- `Lib/Tactics.v`、`Lib/Foundation.v`、`Lib/Setoid.v`
- `Functor/*.v`、`Structure/*.v` 中较短片段
- 已有字段展开注释块可引用，但不要改动 `.v` 文件

写作要求：中文；**【每个指令必须详细】**；模板固定：
1. 做什么
2. 常见语法
3. 何时用 / 何时别用
4. 仓库示例（相对路径 + 短片段；勿大段改证明）
5. 易混点

本任务**只写 markdown 文档**，不要修改任何 `.v`，不要 merge 进 zh-CN。
