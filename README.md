# Armillary Lean

本仓形式化 Armillary 码的具体实例，首阶段是三个代表实例的距离证书。 [qatlib-dev #553](https://github.com/quantum-atlas-ai/qatlib-dev/issues/553)

## 实例 8749

[`Data8749.lean`](ArmillaryLean/Instances/Data8749.lean) 保存 Supplement §1 Table S2 的保留组、通道排列和位移。参数来自 Dev 冻结转录，对应原稿 SHA-256 `8f6f858707d886619011c71c171239e2c410892bf0e819546dbf6efa1d8dc72c`。 [冻结转录](https://github.com/quantum-atlas-ai/qatlib-dev/blob/b78096c6c45bb15622d186cd211e98b979a8323c/TASK/task-ecc-armillary/parameters.json)

数据模块记录 #553 给出的候选逻辑算符支撑，并证明它包含 12 个互异坐标。[`Code8749.lean`](ArmillaryLean/Instances/Code8749.lean) 将源参数接到 `Qatlib` 路由，定义 X/Z 校验矩阵，并证明码长为 3636、列重为 3、矩阵关联与路由访问等价，以及访问关系在循环平移下的相容性。距离上界还需要候选的零 syndrome 和非平凡性，精确距离还需要低重量排除。

## 本地检查

Lean 工具链固定为 `v4.35.0`，`Qatlib` 固定为 `5c88a0b7275769d44542d0a371a5af8f8841cbae`。本仓用 Lake 检查 `ArmillaryLean`，并消费上游的预编译制品。首次检出时先准备锁定版本的依赖缓存。 [Qatlib 缓存指南](https://github.com/quantum-atlas-ai/qatlib/blob/5c88a0b7275769d44542d0a371a5af8f8841cbae/docs/getting-started.md)

在仓库根目录先构建只依赖 Lean 核心的数据模块，再用 `--no-build` 检查路由模块。依赖缓存缺失时第二条命令会失败。通过后可构建顶层导入。

```bash
lake build +ArmillaryLean.Instances.Data8749
lake --no-build lean ArmillaryLean/Instances/Code8749.lean
lake build +ArmillaryLean
```
