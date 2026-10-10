# QEPCAD 本地证书生产线（C5）

## 分工（用户 2026-10-10 裁定）

- **QEPCAD 只在你本地跑**，负责出证书（会话日志＋等价无量词答案）。
- **证书作为数据入仓**：本目录 `qepcad_certs/<cert-id>/`。
- **Lean 侧验证器**（W3-3 的 `Seams/UnifiedQECert.lean`）吃证书做纯算术验证。
- **CI 永不安装任何外部求解器**；证书缺失即该输入 CI_NOT_RUN（fail-closed）。

## 本地环境（已搭好，2026-10-10）

- Docker 容器 `qepcad-build`（Ubuntu 22.04 + gcc/cmake，源码
  github.com/PetterS/qepcad，CMake 构建）；已 `docker commit` 为本地镜像
  **`qepcad-local:20261010`**（重建一条命令：`docker run -d --name qepcad-run
  qepcad-local:20261010 sleep infinity`）。
- QEPCAD 输入协议（批式）：`[描述]\n(变量表)\n自由变量数\n前束公式.\ngo\nfinish\n`。

## 产证书流程

1. 在容器里跑：
   `printf "[<id>]\n(x)\n0\n<公式>.\ngo\nfinish\n" | docker exec -i <容器> bash -c "cd /app/qepcad/build/bin && ./qepcad"`
2. 全量会话日志存 `qepcad_certs/<id>/qepcad-session.log`（含答案行
   "An equivalent quantifier-free formula: TRUE/FALSE/式"）。
3. 每份证书配 `statement.md`：命题原文、预期答案、Lean 验证定理名（验证器闭合后回填）。

## 已有证书

| id | 命题 | QEPCAD 答案 | Lean 可验证性 |
|---|---|---|---|
| cert-001 | ∃x∈ℝ, (x+1)²=0 ∧ x>0 | **FALSE** | Lean 侧待证：∀x, (x+1)²=0 → x=-1 → ¬x>0（无解方向，正是需外部帮助的半边） |
| smoke | ∃x∈ℝ, x²=4 | TRUE | 有理见证 x=2 直接代入即证（smoke 测试用） |

## 复现

```bash
docker start qepcad-build  # 或 docker run -d --name qepcad-run qepcad-local:20261010 sleep infinity
printf "[smoke]\n(x)\n0\n(Ex)[x^2 = 4].\ngo\nfinish\n" | \
  docker exec -i qepcad-build bash -c "cd /app/qepcad/build/bin && ./qepcad" | \
  grep -A 1 "equivalent quantifier-free"
```

## 诚实边界

- 证书是"QEPCAD 对该输入算出的等价无量词答案＋完整会话记录"；Lean 验证器
  只验证**有理见证类**答案（TRUE 且给样本点）与**可由代数恒等式复推**的
  FALSE 答案（逐证书写对应 Lean 定理）。不冒称"验证了 QEPCAD 本身正确"。
- 若某输入 QEPCAD 超时/超内存，该输入如实记开放，不缩减输入充数。
