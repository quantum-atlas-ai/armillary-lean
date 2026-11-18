# Armillary Lean

本仓形式化 Armillary 码的具体实例，首阶段是三个代表实例的距离证书。 [qatlib-dev #553](https://github.com/quantum-atlas-ai/qatlib-dev/issues/553)

## 实例 8749

[`Data8749.lean`](ArmillaryLean/Instances/Data8749.lean) 保存 Supplement §1 Table S2 的保留组、通道排列和位移。参数来自 Dev 冻结转录，对应原稿 SHA-256 `8f6f858707d886619011c71c171239e2c410892bf0e819546dbf6efa1d8dc72c`。 [冻结转录](https://github.com/quantum-atlas-ai/qatlib-dev/blob/b78096c6c45bb15622d186cd211e98b979a8323c/TASK/task-ecc-armillary/parameters.json)

数据模块记录 #553 给出的候选逻辑算符支撑，并证明它包含 12 个互异坐标。[`Code8749.lean`](ArmillaryLean/Instances/Code8749.lean) 将源参数接到 `Qatlib` 路由，定义 X/Z 校验矩阵，并证明码长为 3636、列重为 3、矩阵关联与路由访问等价，以及访问关系在循环平移下的相容性。

[`Css8749.lean`](ArmillaryLean/Instances/Css8749.lean) 核验块配对并构造具体 CSS 码。[`Upper8749.lean`](ArmillaryLean/Instances/Upper8749.lean) 对三个保留 Z 校验组逐一核验支撑的成对抵消，再用块 `0` 和 `3` 上的分离向量排除 X 稳定子行空间，得出 `distance_le_twelve`。精确距离还需要 X/Z 两侧的低重量排除。

## 本地检查

Lean 工具链固定为 `v4.35.0`，`Qatlib` 固定为 `5c88a0b7275769d44542d0a371a5af8f8841cbae`。本仓用 Lake 检查 `ArmillaryLean`，并消费上游的预编译制品。首次检出时先准备锁定版本的依赖缓存。 [Qatlib 缓存指南](https://github.com/quantum-atlas-ai/qatlib/blob/5c88a0b7275769d44542d0a371a5af8f8841cbae/docs/getting-started.md)

在仓库根目录先用 `--no-build` 确认两个上游入口的缓存可用。通过后构建本仓顶层导入。

```bash
lake --no-build build +Qatlib.Papers.Armillary26.Instances.Routed \
  +Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance
lake build +ArmillaryLean
```
