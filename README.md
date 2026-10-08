# lean-proj

Lean 4 数学定理证明工作区

## 环境

- Lean 4.34.0 / Lake 5.0（通过 elan 管理）
- mathlib（v4.34.0）预编译缓存
- 发行版：WSL2 Ubuntu 24.04

## 文件

- `NewtonComplete.lean` — 牛顿法二阶收敛性证明：单根 r 处 f(r)=0、f'(r)≠0 时，牛顿映射 g(x)=x−f(x)/f'(x) 满足 g'(r)=0，从而误差比 e_{n+1}/e_n² → f''(r)/(2f'(r))，若 f''(r) ≠ 0，则收敛阶恰好为 2。
- `lakefile.toml` — 项目与依赖配置。
- `lean-toolchain` — 锁定 Lean 版本。
- `.lake/` — 编译缓存（不入库）。

## 使用

在 VS Code 中通过 Remote-WSL 连接 LeanBox，打开本文件夹；打开 `.lean` 文件即可在 InfoView 中实时看到证明状态。

以后每证一个新问题，在本目录新建一个 `.lean` 文件即可。
