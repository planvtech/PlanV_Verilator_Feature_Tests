# PlanV Feature Tests 重构计划

## 目标

1. 建立清晰的测试分类标准
2. 重命名不规范的测试文件
3. 归档状态子目录和历史测试
4. 保持测试内容完整性
5. 提供可追溯性

## 测试分类方案

### 方案对比分析

#### 方案 A: 按功能大类划分(当前方式的改进版)
```
planv_tests/feature_tests/
├── randomization/          # 随机化相关
├── assertions/             # 断言
├── timing/                 # 时序控制
├── interfaces/             # 接口相关
└── ...
```

**优点:** 直观,易于查找
**缺点:** 分类边界模糊,同一个特性可能跨多个类别

#### 方案 B: 按 IEEE 1800 章节划分
```
planv_tests/feature_tests/
├── ch18_randomization/           # Chapter 18: Constrained random value generation
│   ├── 18.4_random_variables/
│   ├── 18.5_constraint_blocks/
│   ├── 18.6_randomization_methods/
│   ├── 18.7_disabling_constraints/
│   ├── 18.8_controlling_constraints/
│   └── 18.17_random_stability/
├── ch16_assertions/              # Chapter 16: Assertions
│   ├── 16.3_immediate_assertions/
│   └── 16.5_concurrent_assertions/
├── ch10_scheduling/              # Chapter 10: Scheduling semantics
└── ...
```

**优点:** 有明确标准可依据,与规范对应
**缺点:** 对新人不够直观,需要熟悉 IEEE 1800 标准

#### 方案 C: 混合方案(推荐)★★★
```
planv_tests/feature_tests/
├── randomization/                        # 顶层按功能大类
│   ├── rand_variables/                  # 对应 IEEE 1800-2017 §18.4
│   ├── constraint_blocks/               # §18.5
│   ├── randomize_methods/               # §18.6
│   ├── constraint_control/              # §18.7-18.8
│   ├── unique_constraints/              # §18.5.5
│   ├── dist_constraints/                # §18.5.4
│   ├── std_randomize/                   # §18.16
│   └── special_cases/                   # 特殊场景(bug复现、边界条件等)
│       ├── issue_reproductions/         # GitHub issue 复现
│       └── edge_cases/                  # 边界条件
├── assertions/                           # IEEE 1800-2017 Ch16
│   ├── immediate/                       # §16.3
│   └── concurrent/                      # §16.5-16.14
├── timing/                               # IEEE 1800-2017 Ch4, Ch9, Ch10
│   ├── delays/                          # §4.7, §9.4
│   ├── scheduling/                      # Ch10
│   └── event_control/                   # §9.4.2
├── interfaces/                           # IEEE 1800-2017 Ch25
│   ├── basic/
│   ├── virtual_interfaces/              # §25.9
│   └── modports/                        # §25.5
├── data_types/                           # IEEE 1800-2017 Ch6
│   ├── arrays/                          # §6.20-6.23
│   ├── structures/                      # §6.24
│   └── unions/                          # §6.24
├── classes/                              # IEEE 1800-2017 Ch8
│   ├── inheritance/
│   ├── polymorphism/
│   └── static_members/
└── coverage/                             # IEEE 1800-2017 Ch19
    ├── functional/
    └── assertion_based/
```

**优点:**
- 顶层直观(功能大类)
- 子层有标准可依据(IEEE 章节)
- 灵活处理特殊场景
- 可在 README.md 中注明对应的 IEEE 章节

**实施建议:**
- 每个目录包含 `README.md`,注明对应的 IEEE 1800-2017 章节
- 特殊场景(issue 复现、边界条件)单独分类
- 保持测试名称描述性强

## 测试命名规范

### 命名模板

```
t_<category>_<feature>_<variant>.sv

<category>: 功能类别简称
<feature>:  具体特性
<variant>:  变体(可选,如 basic, edge_case, issue1234 等)
```

### 示例对照表

| 现有文件名 | 新文件名 | 说明 |
|-----------|---------|------|
| `t_1.sv` | `t_rand_class_basic.sv` | 从内容推断,基础随机化类测试 |
| `t_2.sv` | `t_rand_class_inheritance.sv` | 类继承场景 |
| `t_bad.sv` | `t_constraint_error_detection.sv` | 错误检测测试 |
| `t_fuxian.sv` | `t_issue_fuxian_randomize.sv` | Issue 复现(保留 fuxian 作为 issue ID) |
| `t_arr_sel.sv` | `t_constraint_array_selection.sv` | 数组选择约束 |
| `t_call_within_class.sv` | ✅ 已合规 | 保持不变 |
| `t_constraint_global_randMode.sv` | `t_constraint_control_rand_mode_global.sv` | 更明确分类 |

### 命名原则

1. **描述性强** - 从文件名能大致理解测试内容
2. **一致性** - 同类测试使用相同前缀
3. **可排序** - 相关测试自然聚集在一起
4. **避免数字** - 除非是 issue 编号,不要用 `t_1`, `t_2`
5. **保留历史信息** - Issue 复现测试保留原始标识符

## 当前测试盘点

### Randomization 类别(126 个测试)

#### 需要重命名的文件(优先级高)

**无意义命名:**
- `t_1.sv` → 需要读取内容确定用途
- `t_2.sv` → 需要读取内容确定用途
- `t_bad.sv` → 需要确定是错误检测测试还是失败的测试

**简写过度:**
- `t_arr_sel.sv` → `t_constraint_array_selection.sv`

**Issue 复现测试(建议移到 special_cases/issue_reproductions/):**
- `t_fuxian*.sv` (7个) → 保留名称,移动到专门目录
- `t_issue_*.sv` (2个) → 已有 issue 前缀,移动即可

#### 已经规范的文件(保持不变)

- `t_constraint_*.sv` 系列(约80个) - 已有明确前缀和描述
- `t_rand_*.sv` 系列(约20个) - 清晰标识随机变量测试

### 其他类别

#### Assertions (5个)
- 命名规范,保持不变
- 建议细分为 `immediate/` 和 `concurrent/` 子目录

#### Timing (少量)
- `t_timing_basic_delay.sv` - 规范,保持不变

#### Interfaces (若干)
- 当前混在 `t_virtual_interface/` 目录
- 建议重组为 `interfaces/virtual_interfaces/`

## 重构实施计划

### Phase 1: 清理测试结果目录(1-2天)

**目标:** 移除源码树中的测试结果

```bash
# 清理分支特定测试结果
find planv_tests/feature_tests -type d -name "*_verilator_*" -delete
find planv_tests/feature_tests -type d -name "9_19" -delete
find planv_tests/feature_tests -type d -name "master" -delete
find planv_tests/feature_tests -type d -name "vsim_failed" -delete
```

**输出:** 清理脚本 `scripts/cleanup_test_results.sh`

### Phase 2: 创建新目录结构(1天)

**目标:** 建立目标目录结构和文档

```bash
# Randomization 细分
mkdir -p planv_tests/feature_tests/randomization/{rand_variables,constraint_blocks,randomize_methods,constraint_control,unique_constraints,dist_constraints,std_randomize,special_cases/{issue_reproductions,edge_cases}}

# 其他类别细分
mkdir -p planv_tests/feature_tests/assertions/{immediate,concurrent}
mkdir -p planv_tests/feature_tests/interfaces/{basic,virtual_interfaces,modports}
mkdir -p planv_tests/feature_tests/timing/{delays,scheduling,event_control}
mkdir -p planv_tests/feature_tests/data_types/{arrays,structures,unions}
mkdir -p planv_tests/feature_tests/classes/{inheritance,polymorphism,static_members}

# 归档目录
mkdir -p planv_tests/feature_tests/_archived/$(date +%Y%m%d)_pre_refactor
```

**输出:**
- 新目录树
- 每个目录的 `README.md` 模板

### Phase 3: 盘点和分类现有测试(2-3天)

**目标:** 为每个测试确定新位置和新名称

**方法:**
1. 生成测试清单(CSV 格式)
2. 读取测试内容,理解用途
3. 确定新分类和新名称
4. 记录迁移映射

**输出:** `MIGRATION_MAP.csv`

```csv
原路径,新路径,新文件名,分类,IEEE章节,备注
planv_tests/feature_tests/constrained_random/constraint_blocks/t_1.sv,planv_tests/feature_tests/randomization/rand_variables/,t_rand_class_basic.sv,rand_variables,§18.4,基础类随机化
planv_tests/feature_tests/constrained_random/case_from_issues/t_fuxian.sv,planv_tests/feature_tests/randomization/special_cases/issue_reproductions/,t_issue_fuxian_randomize.sv,issue_reproduction,N/A,Fuxian 发现的 randomize bug
...
```

### Phase 4: 执行迁移和重命名(1-2天)

**目标:** 根据映射表执行文件移动和重命名

**自动化脚本:** `scripts/migrate_tests.sh`

```bash
#!/bin/bash
# 读取 MIGRATION_MAP.csv
# 对每个测试:
#   1. 创建目标目录
#   2. 复制文件到新位置并重命名
#   3. 更新文件内模块名(module t_old -> module t_new)
#   4. 验证语法正确性
#   5. 运行测试确认功能不变
#   6. 移动原文件到 _archived/
```

**安全措施:**
- 先复制,后归档(不直接删除)
- Git commit 每个大的迁移步骤
- 保留完整的迁移日志

### Phase 5: 整合状态子目录(2-3天)

**目标:** 处理 `passed/`, `failed/`, `modify_passed/` 等子目录

**策略:**

1. **`passed/` 子目录:**
   - 检查是否与父目录测试重复
   - 如果重复 → 归档
   - 如果不同 → 重命名后迁移到新结构

2. **`failed/` 或 `*_failed/` 子目录:**
   - 确定失败原因(Verilator bug? 测试错误?)
   - 如果是已知 Verilator bug → 移到 `special_cases/known_failures/`
   - 如果测试本身有问题 → 归档并记录

3. **`modify_passed/` 子目录:**
   - 通常是修复后的版本
   - 检查与当前测试关系
   - 保留最新版本,旧版本归档

4. **`to_test/` 子目录:**
   - 待验证的测试
   - 本地运行验证
   - 通过 → 迁移到正式目录
   - 失败 → 移到 `special_cases/known_failures/` 或归档

**输出:**
- `STATUS_SUBDIRS_ANALYSIS.md` - 每个状态子目录的处理决策
- 更新的测试树

### Phase 6: 更新自动化脚本和文档(1天)

**目标:** 确保工具链兼容新结构

**需要更新的文件:**
- `scripts/setup_framework` - 验证是否需要调整
- `scripts/set_build_run_functions` - 更新路径引用(如果有)
- `.github/workflows/*.yml` - 检查 CI 兼容性
- `README.md` - 更新项目说明
- `.claude/CLAUDE.md` - 更新测试结构说明

**新增文档:**
- 每个类别的 `README.md` (包含 IEEE 章节引用)
- `CONTRIBUTING.md` - 如何添加新测试
- `MIGRATION_HISTORY.md` - 记录重构过程

### Phase 7: 验证和测试(2-3天)

**目标:** 确保重构后所有测试正常运行

**验证步骤:**

1. **本地全量测试**
   ```bash
   ./scripts/run -b master -t planv_tests/feature_tests
   ```

2. **对比测试结果**
   - 重构前后测试数量一致
   - 通过/失败的测试集合一致
   - 没有测试遗漏

3. **CI/CD 验证**
   - 提交到测试分支
   - 观察 GitHub Actions 运行结果
   - 确认所有版本正常

4. **文档检查**
   - 所有 README.md 完整
   - 迁移映射文档准确
   - 归档记录清晰

## 归档策略

### 归档目录结构

```
planv_tests/feature_tests/_archived/
├── 20250112_pre_refactor/              # 重构前完整快照
│   ├── constrained_random/             # 原始目录结构
│   └── SNAPSHOT_README.md              # 快照说明
├── status_subdirs/                     # 状态子目录归档
│   ├── passed/
│   ├── failed/
│   └── STATUS_ANALYSIS.md              # 为什么归档
├── renamed_tests/                      # 被重命名的测试原始版本
│   ├── t_1.sv -> t_rand_class_basic.sv
│   ├── t_2.sv -> t_rand_class_inheritance.sv
│   └── RENAME_MAP.md                   # 重命名映射
└── obsolete/                           # 过时/重复的测试
    └── OBSOLETE_REASON.md              # 废弃原因
```

### 归档原则

1. **完整快照** - 重构前创建完整备份
2. **保留历史** - 不直接删除,移到归档
3. **文档化** - 每个归档决策有文字说明
4. **可追溯** - Git history + 归档文档双重保险
5. **定期清理** - 归档 6 个月后可考虑真正删除

## 重命名工具设计

### 自动化脚本功能

**`scripts/rename_test.sh`**

```bash
#!/bin/bash
# 用法: ./scripts/rename_test.sh <old_name> <new_name> <category>
#
# 功能:
# 1. 重命名文件
# 2. 更新文件内模块名
# 3. 更新文件头注释
# 4. 移动到正确的类别目录
# 5. 运行测试验证
# 6. 生成迁移记录
```

**关键步骤:**

```bash
# 1. 读取原文件
old_file="planv_tests/feature_tests/constrained_random/t_1.sv"
new_name="t_rand_class_basic"
new_category="randomization/rand_variables"

# 2. 提取模块名
old_module=$(grep "^module" $old_file | awk '{print $2}' | sed 's/;//')

# 3. 替换模块名
sed -i "s/module $old_module/module $new_name/" $old_file

# 4. 更新文件头(可选)
sed -i "1i// Migrated from: t_1.sv on $(date +%Y-%m-%d)" $old_file

# 5. 移动文件
new_file="planv_tests/feature_tests/$new_category/$new_name.sv"
mkdir -p $(dirname $new_file)
mv $old_file $new_file

# 6. 测试验证
./scripts/run -b master -t $new_file

# 7. 记录迁移
echo "$(date),$old_file,$new_file,SUCCESS" >> MIGRATION_LOG.csv
```

### 批量重命名工作流

```bash
# 1. 生成待重命名清单
find planv_tests/feature_tests -name "t_[12].sv" -o -name "t_bad.sv" > rename_candidates.txt

# 2. 人工审阅并编辑 MIGRATION_MAP.csv
# (包含新名称和新分类)

# 3. 批量执行
while IFS=, read -r old_path new_path new_name category ieee notes; do
    ./scripts/rename_test.sh "$old_path" "$new_name" "$category"
done < MIGRATION_MAP.csv

# 4. 验证所有重命名的测试
./scripts/run -b master -t planv_tests/feature_tests/randomization
```

## 风险控制

### 风险识别

| 风险 | 影响 | 概率 | 缓解措施 |
|------|------|------|---------|
| 测试重命名后无法运行 | 高 | 中 | 每次重命名后立即测试;保留原文件备份 |
| 遗漏测试文件 | 高 | 低 | 使用脚本生成完整清单;重构前后对比测试数量 |
| CI/CD 失败 | 中 | 低 | 提前在测试分支验证;分阶段合并 |
| 丢失测试历史 | 中 | 低 | Git history + 归档目录双重保护 |
| 重复测试未发现 | 低 | 中 | 人工审阅 + 内容哈希比对 |

### 回滚策略

**如果重构失败,如何回滚:**

1. **Git 层面:**
   ```bash
   git checkout refactor/test-reorganization
   git reset --hard backup-before-refactor
   ```

2. **归档恢复:**
   ```bash
   cp -r planv_tests/feature_tests/_archived/20250112_pre_refactor/* \
         planv_tests/feature_tests/
   ```

3. **分阶段提交:**
   - 每个 Phase 独立提交
   - 可以回滚到任意 Phase

## 时间估算

| Phase | 任务 | 预计时间 | 风险缓冲 |
|-------|------|---------|---------|
| 1 | 清理测试结果目录 | 0.5天 | +0.5天 |
| 2 | 创建新目录结构 | 0.5天 | +0.5天 |
| 3 | 盘点和分类测试 | 2天 | +1天 |
| 4 | 执行迁移和重命名 | 1.5天 | +0.5天 |
| 5 | 整合状态子目录 | 2天 | +1天 |
| 6 | 更新脚本和文档 | 1天 | +0.5天 |
| 7 | 验证和测试 | 2天 | +1天 |
| **总计** | | **9.5天** | **+5天** |

**建议时间线:** 2-3 周(包含缓冲和 code review 时间)

## 下一步行动

### 立即执行(本周)

1. **审阅本重构计划**
   - 确认分类方案(方案 C)
   - 确认命名规范
   - 调整不合理的地方

2. **创建重构分支**
   ```bash
   git checkout -b refactor/test-reorganization
   git tag backup-before-refactor
   ```

3. **执行 Phase 1: 清理测试结果目录**
   - 生成并运行清理脚本
   - 提交 Phase 1 结果

### 本周末前

4. **执行 Phase 2: 创建新目录结构**
   - 建立目录树
   - 创建所有 README.md 模板

5. **开始 Phase 3: 盘点测试**
   - 生成测试清单
   - 开始分析前 20 个测试的分类

### 下周

6. **完成 Phase 3 和 Phase 4**
   - 完成所有测试分类
   - 执行迁移脚本
   - 逐步提交

## 成功标准

重构完成后应该达到:

✅ **清晰的分类体系**
- 任何人都能快速找到相关测试
- 新测试有明确的归属

✅ **规范的命名**
- 所有测试名称描述性强
- 无 `t_1`, `t_2` 等无意义命名

✅ **完整的文档**
- 每个类别都有 README.md
- 关键测试有详细注释
- IEEE 1800 章节引用清晰

✅ **干净的目录结构**
- 无测试结果混在源码中
- 无状态子目录
- 归档井然有序

✅ **功能完整性**
- 测试数量不减少
- 所有测试正常运行
- CI/CD 通过

✅ **可追溯性**
- 迁移映射文档完整
- Git history 清晰
- 归档记录详细

---

**准备好开始了吗?我可以帮你:**
1. 生成 Phase 1 清理脚本
2. 创建 README.md 模板
3. 开始盘点测试并生成 MIGRATION_MAP.csv
4. 其他你需要的帮助
