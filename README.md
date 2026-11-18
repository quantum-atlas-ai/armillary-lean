# Armillary Lean

本仓形式化 Armillary 码的具体实例，首阶段是三个代表实例的距离证书。 [qatlib-dev #553](https://github.com/quantum-atlas-ai/qatlib-dev/issues/553)

## 实例 8749

[`Data8749.lean`](ArmillaryLean/Instances/Data8749.lean) 保存 Supplement §1 Table S2 的保留组、通道排列和位移。参数来自 Dev 冻结转录，对应原稿 SHA-256 `8f6f858707d886619011c71c171239e2c410892bf0e819546dbf6efa1d8dc72c`。 [冻结转录](https://github.com/quantum-atlas-ai/qatlib-dev/blob/b78096c6c45bb15622d186cd211e98b979a8323c/TASK/task-ecc-armillary/parameters.json)

数据模块记录 #553 给出的候选逻辑算符支撑，并证明它包含 12 个互异坐标。[`Code8749.lean`](ArmillaryLean/Instances/Code8749.lean) 将源参数接到 `Qatlib` 路由，定义 X/Z 校验矩阵，并证明码长为 3636、列重为 3、矩阵关联与路由访问等价，以及访问关系在循环平移下的相容性。

[`Css8749.lean`](ArmillaryLean/Instances/Css8749.lean) 核验块配对并构造具体 CSS 码。[`Upper8749.lean`](ArmillaryLean/Instances/Upper8749.lean) 对三个保留 Z 校验组逐一核验支撑的成对抵消，再用块 `0` 和 `3` 上的分离向量排除 X 稳定子行空间，得出 `distance_le_twelve`。精确距离还需要 X/Z 两侧的低重量排除。

## 下界证书

[`Lower8749.lean`](ArmillaryLean/Instances/Lower8749.lean) 证明源校验矩阵的零 syndrome 等价于稀疏邻域偶交叠，并推出偶重量与 station-zero 锚点归约。[`Exact8749.lean`](ArmillaryLean/Instances/Exact8749.lean) 证明两套锚点排除结论足以与已验证的上界合成精确距离。

[`Masked.lean`](ArmillaryLean/Certificates/Masked.lean) 证明 512 位分块检查器的接受结果能传递到集合版，后者证明封闭叶与 packing 叶的排除有效。[`Rows8749.lean`](ArmillaryLean/Instances/Rows8749.lean) 的查表数据逐项核对了源路由，[`Anchor8749.lean`](ArmillaryLean/Instances/Anchor8749.lean) 将位掩码中的关联传递回具体源矩阵。

`ArmillaryLean.Code8749.sample_excludes` 验收了 X 校验矩阵在 `(0, (0, 0))` 上重量至多 4 的排除。X/Z 校验矩阵各 36 棵重量上限 10 的候选树已生成并通过独立离线回放。完整的 Lean 内核验收待完成。 [样例证书](ArmillaryLean/Instances/Sample8749.lean)

在同一 X 校验锚点上，重量上限 4 的集合版与分块版分别约用 26 秒和 16 秒。重量上限 6 的集合版超过 180 秒，分块版约用 91 秒并通过内核验收。重量上限 8 和 10 的分块版分别超过本次设定的 170 秒和 155 秒。耗时包含 Lake 启动。

下列命令重生成候选树。X/Z 是校验矩阵的名称，锚点序号为 `3 * block + channel`。

```bash
lake --no-build lean tools/ExportRows8749.lean
c++ -O3 -std=c++20 tools/search8749.cpp -o .lake/dist8749/search8749
for checks in X Z; do
  .lake/dist8749/search8749 ".lake/dist8749/$checks.rows" 10 0 36 > ".lake/dist8749/$checks-10.words"
  python3 tools/replay8749.py ".lake/dist8749/$checks.rows" ".lake/dist8749/$checks-10.words" --budget 10
done
```

重量上限 4 的内核样例可独立复现。使用 `--checker finset` 可以在同一份数据上比较集合版。

```bash
.lake/dist8749/search8749 .lake/dist8749/X.rows 4 0 1 > .lake/dist8749/X0-4.words
python3 tools/render8749.py .lake/dist8749/X0-4.words .lake/dist8749/Probe8749.lean \
  --checks X --anchor 0 --budget 4
lake --no-build lean .lake/dist8749/Probe8749.lean
```

渲染时加 `--fragment-words 20` 会在实际分支处切开同一份样例。Lean 独立核验各片段，并用已证明的分支组合定理得出根状态的排除结果。重量上限 6 的样例使用 `--fragment-words 100` 复现，约用 53 秒通过内核验收。重量上限 10 的实际证书切分后，首个独立片段约用 12 秒通过内核验收，整个锚点仍超过本次设定的 155 秒。

### 最小锚点与数值验收

[`Symmetry8749.lean`](ArmillaryLean/Instances/Symmetry8749.lean) 在源路由上证明了 X、Z 校验图同构。X 校验侧的最小锚点排除因此足以证明精确距离。每个支撑只需考虑块与通道编号最小的锚点，最后一块的三个锚点由单块论证直接排除。

[`Numeric.lean`](ArmillaryLean/Certificates/Numeric.lean) 用自然数位图检查其余锚点。生成的行字表通过 Lean 核验，与源路由逐字相等。重生成重量上限 10 的候选后，可让本仓分模块核对证明片段并合成最终目标。生成的 `HeadX*.lean` 和 `Exact.lean` 保存在本地，由下面的流程复现。

```bash
.lake/dist8749/search8749 .lake/dist8749/X.rows 10 0 36 --minimum > .lake/dist8749/MinX.words
python3 tools/replay8749.py .lake/dist8749/X.rows .lake/dist8749/MinX.words --budget 10 --minimum
python3 tools/build_min8749.py .lake/dist8749/MinX.words --jobs 4
```

## 本地检查

Lean 工具链固定为 `v4.35.0`，`Qatlib` 固定为 `5c88a0b7275769d44542d0a371a5af8f8841cbae`。本仓用 Lake 检查 `ArmillaryLean`，并消费上游的预编译制品。首次检出时先准备锁定版本的依赖缓存。 [Qatlib 缓存指南](https://github.com/quantum-atlas-ai/qatlib/blob/5c88a0b7275769d44542d0a371a5af8f8841cbae/docs/getting-started.md)

在仓库根目录先用 `--no-build` 确认两个上游入口的缓存可用。通过后构建本仓顶层导入。

```bash
lake --no-build build +Qatlib.Papers.Armillary26.Instances.Routed \
  +Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance
lake build +ArmillaryLean
```
