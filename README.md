# Armillary Lean

本仓形式化 Armillary 码的具体实例，首阶段是三个代表实例的距离证书。 [qatlib-dev #553](https://github.com/quantum-atlas-ai/qatlib-dev/issues/553)

| 实例 | 码长 | 已在 Lean 证明 | 精确距离剩余义务 |
| --- | ---: | --- | --- |
| `8749` | 3636 | `d = 12` | 已闭合 |
| `9053` | 4932 | `d ≤ 14` | X 校验侧重量至多 12 的约简锚点内核验收 |
| `p181` | 8688 | `d ≤ 16` | X/Z 两侧重量至多 14 的约简锚点内核验收 |

## 实例 9053 和 p181

两份实例使用同一冻结转录中的 Table S3 和 S4。Lean 验证源路由给出的 CSS 正交性，再通过 Z 校验行内的配对抵消以及块 `0, 1` 的分离向量，证明两个纯 X 逻辑见证给出上界。 [9053 上界](ArmillaryLean/Instances/Code9053.lean) · [p181 上界](ArmillaryLean/Instances/CodeP181.lean)

下界归约证明了翻转交叠超过 6 的重量 12 稳定子行可以严格减重，并保持 syndrome 与稳定子陪集。循环平移将减重后的支撑移到 station-zero 最小锚点，同时保持对每条稳定子行的交叠数。`distance_eq_fourteen_of_anchors` 和 `distance_eq_sixteen_of_anchors` 分别把两侧完整的锚点排除证书合成为目标等式。 [稳定子约简](ArmillaryLean/Certificates/Stabilizer.lean) · [锚点归约](ArmillaryLean/Instances/RoutedAnchors.lean) · [等式接口](ArmillaryLean/Instances/ReducedDistances.lean)

`9053` 还有一个经过 Lean 验证的扇区互换。它用同一个数据坐标双射互换两套校验行，同时保持 syndrome 和稳定子交叠。`distance_eq_fourteen_of_x` 因此只需要 X 校验侧的 36 个锚点。 [扇区互换](ArmillaryLean/Instances/Swap9053.lean)

### 约简证书生成与核验

两个实例全部 168 个 X/Z 锚点已有候选树，并通过独立离线回放。Lean 的约简检查器支持校验行封闭、packing、分裂及稳定子交叠四种指令。校验行表与 Lean 源路由一致，且已有实际锚点与交叠叶通过内核验证。完整的精确等式仍需其余内核检查通过。 [检查器](ArmillaryLean/Certificates/Reduced.lean) · [源路由表示](ArmillaryLean/Instances/ReducedNumeric.lean)

完成本仓默认构建后，可生成两个实例的证书并独立回放。最后两个命令调度正式内核检查，并在全部目标通过后构建相应精确距离模块。大部分运行时间在编号较小的锚点，日志写入 `.lake/reduced/build-logs`。

```bash
lake --no-build lean tools/ExportReducedRows.lean
c++ -O3 -std=c++20 tools/search_reduced.cpp -o .lake/reduced/search
c++ -O3 -std=c++20 tools/replay_reduced.cpp -o .lake/reduced/replay
for spec in '137 3 12' '181 4 14'; do
  read -r p q budget <<< "$spec"
  for pair in 'X Z' 'Z X'; do
    read -r opposite stabilizers <<< "$pair"
    O=".lake/reduced/$p-$opposite.rows"
    S=".lake/reduced/$p-$stabilizers.rows"
    B=".lake/reduced/$p-$opposite.bin"
    .lake/reduced/search "$O" "$S" "$p" "$q" "$budget" 0 "$((12*q))" --binary > "$B"
    .lake/reduced/replay "$O" "$S" "$p" "$q" "$budget" 0 "$((12*q))" "$B"
  done
done
python3 tools/build_reduced.py 9053 --jobs 4
python3 tools/build_reduced.py P181 --jobs 4
```

## 实例 8749

Lean 定理 `ArmillaryLean.Code8749.distance_eq_twelve` 证明了 `cssDistance code = 12`。完整证明入口为 `import ArmillaryLean.Instances.MinProof8749.Exact`。公理审计结果为 `propext`、`Classical.choice` 和 `Quot.sound`。 [定理源码](ArmillaryLean/Instances/MinProof8749/Exact.lean)

[`Data8749.lean`](ArmillaryLean/Instances/Data8749.lean) 保存 Supplement §1 Table S2 的保留组、通道排列和位移。参数来自 Dev 冻结转录，对应原稿 SHA-256 `8f6f858707d886619011c71c171239e2c410892bf0e819546dbf6efa1d8dc72c`。 [冻结转录](https://github.com/quantum-atlas-ai/qatlib-dev/blob/b78096c6c45bb15622d186cd211e98b979a8323c/TASK/task-ecc-armillary/parameters.json)

数据模块记录 #553 给出的候选逻辑算符支撑，并证明它包含 12 个互异坐标。[`Code8749.lean`](ArmillaryLean/Instances/Code8749.lean) 将源参数接到 `Qatlib` 路由，定义 X/Z 校验矩阵，并证明码长为 3636、列重为 3、矩阵关联与路由访问等价，以及访问关系在循环平移下的相容性。

[`Css8749.lean`](ArmillaryLean/Instances/Css8749.lean) 核验块配对并构造具体 CSS 码。[`Upper8749.lean`](ArmillaryLean/Instances/Upper8749.lean) 对三个保留 Z 校验组逐一核验支撑的成对抵消，再用块 `0` 和 `3` 上的分离向量排除 X 稳定子行空间，得出 `distance_le_twelve`。

## 下界证书

[`Lower8749.lean`](ArmillaryLean/Instances/Lower8749.lean) 证明源校验矩阵的零 syndrome 等价于稀疏邻域偶交叠，并推出偶重量与 station-zero 锚点归约。[`Exact8749.lean`](ArmillaryLean/Instances/Exact8749.lean) 证明两套锚点排除结论足以与已验证的上界合成精确距离。

[`Masked.lean`](ArmillaryLean/Certificates/Masked.lean) 证明 512 位分块检查器的接受结果能传递到集合版，后者证明封闭叶与 packing 叶的排除有效。[`Rows8749.lean`](ArmillaryLean/Instances/Rows8749.lean) 的查表数据逐项核对了源路由，[`Anchor8749.lean`](ArmillaryLean/Instances/Anchor8749.lean) 将位掩码中的关联传递回具体源矩阵。

`ArmillaryLean.Code8749.sample_excludes` 验收了 X 校验矩阵在 `(0, (0, 0))` 上重量至多 4 的排除，可用于复现分块检查器的行为。 [样例证书](ArmillaryLean/Instances/Sample8749.lean)

在同一 X 校验锚点上，重量上限 4 的集合版与分块版分别约用 26 秒和 16 秒。重量上限 6 的集合版超过 180 秒，分块版约用 91 秒并通过内核验收。重量上限 8 和 10 的分块版分别超过本次设定的 170 秒和 155 秒。耗时包含 Lake 启动。

下列命令复现最初的双侧候选树和离线回放。X/Z 是校验矩阵的名称，锚点序号为 `3 * block + channel`。

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

[`Numeric.lean`](ArmillaryLean/Certificates/Numeric.lean) 用自然数位图检查其余 33 个 X 侧锚点。Lean 内核核验了全部证书以及行字表与源路由的一致性。零 syndrome 的支撑重量必为偶数，因此排除重量至多 10 的非空支撑也排除了重量 11。

完成下文的本地检查后，先导出校验行，再生成最小锚点证书、离线回放，并分模块完成 Lean 构建。`HeadX*.lean` 由脚本在本地生成，`Exact.lean` 是仓库中的证明入口。最后一次构建会输出定理的公理审计。

```bash
lake --no-build lean tools/ExportRows8749.lean
c++ -O3 -std=c++20 tools/search8749.cpp -o .lake/dist8749/search8749
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
