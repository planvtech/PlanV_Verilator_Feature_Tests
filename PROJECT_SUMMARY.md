# PlanV Verilator Feature Tests - Project Summary

## 项目概述

这是一个专门用于验证 PlanV 定制 Verilator 功能的测试框架项目,包含 165+ 个 SystemVerilog 特性测试和多个 UVM 测试平台。

**核心价值:**
- 跨多个 Verilator 版本的自动化测试
- 系统化的 SystemVerilog 特性覆盖
- CI/CD 集成的回归测试
- UVM 验证方法学支持

## 当前项目状态分析

### 优势

1. **良好的自动化框架**
   - `scripts/run` 提供完整的本地测试流程
   - `scripts/setup_framework` 自动生成测试 Makefile
   - GitHub Actions 实现多版本并行测试
   - 生成详细日志和 HTML 报告

2. **广泛的功能覆盖**
   - 约束随机化测试(最大类别)
   - 断言(立即/并发)
   - 虚拟接口
   - 时序控制
   - UVM 集成

3. **多版本支持**
   - 通过 git submodule 管理多个 Verilator 版本
   - 支持版本间行为对比
   - 灵活的版本切换机制

### 需要改进的问题

#### 🔴 严重问题:测试组织混乱

**现象:**
```
constrained_random/constraint_global/
├── 9_19/                        # 分支测试结果(应该在 logs/)
│   ├── 9_19_verilator_failed/
│   └── 9_19_verilator_passed/
├── master/                      # 分支测试结果(应该在 logs/)
│   ├── master_verilator_failed/
│   └── master_verilator_passed/
├── passed/                      # 状态子目录
├── modify_passed/               # 状态子目录
├── to_test/                     # 状态子目录
├── vsim_failed/                 # 状态子目录
└── t_constraint_global_*.sv     # 实际的活跃测试文件
```

**问题:**
1. **测试源文件与测试结果混杂**
   - `9_19/`, `master/` 子目录包含的是某次测试运行的结果快照
   - 这些应该在 `logs/` 或 CI artifacts 中,而非源代码树

2. **状态子目录导致混乱**
   - `passed/`, `failed/`, `modify_passed/` 等目录含义不明确
   - 无法确定哪些是"官方"测试集
   - CI/CD 运行时会扫描所有 `.sv` 文件,包括这些子目录

3. **维护困难**
   - 新增测试时不知道放在哪里
   - 修改测试后不知道如何更新状态分类
   - 历史测试难以追溯

#### 🟡 中等问题:文档缺失

1. **缺少测试类别说明**
   - 没有 README.md 解释每个类别的目的
   - 新人难以理解测试组织逻辑

2. **测试用例缺少内联文档**
   - 很多测试没有注释说明测试目的
   - 边界条件和预期行为不明确

3. **UVM 测试结构复杂但缺少指导**
   - 多个 UVM 测试但没有统一的说明文档
   - 构建依赖和运行要求分散

#### 🟢 轻微问题:一致性

1. **命名约定不统一**
   - 有些用 `t_` 前缀,有些没有
   - 目录名有 `t_` 前缀(如 `t_racing`),有些没有

2. **成功标记不一致**
   - 脚本检查 "*-* All Finished *-*"
   - 文档说应该是 "*-* All Tests Passed *-*"

## 建议的重构方案

### 方案 A: 渐进式清理(推荐)

**优势:** 低风险,可以逐步进行,不影响现有工作流

**步骤:**

1. **第一阶段:清理测试结果目录**
   ```bash
   # 移除混在源代码中的测试结果
   rm -rf planv_tests/feature_tests/*/9_19/
   rm -rf planv_tests/feature_tests/*/master/
   rm -rf planv_tests/feature_tests/*/vsim_failed/
   ```

2. **第二阶段:整合状态子目录**
   ```bash
   # 将 passed/, failed/, modify_passed/ 中的测试移到父目录
   # 如果测试已过时,移到 archived/ 目录
   ```

3. **第三阶段:添加文档**
   - 为每个测试类别添加 README.md
   - 在测试文件中添加详细注释

**预期结构:**
```
planv_tests/feature_tests/constrained_random/
├── README.md                          # 类别说明
├── constraint_blocks/
│   ├── README.md
│   ├── t_constraint_block_basic.sv
│   └── t_constraint_block_nested.sv
├── constraint_global/
│   ├── README.md
│   ├── t_constraint_global_basic.sv
│   ├── t_constraint_global_randMode.sv
│   └── archived/                      # 可选:历史测试
│       └── 2024-10-08_old_version/
└── constraint_unique/
    ├── README.md
    └── t_constraint_unique_*.sv
```

### 方案 B: 彻底重构(激进)

**优势:** 一步到位,清晰明确

**风险:** 可能影响现有工作流,需要完整测试

**步骤:**

1. **备份当前状态**
   ```bash
   git tag backup-before-refactor
   git checkout -b refactor/test-organization
   ```

2. **重新组织测试树**
   - 将所有活跃测试移到扁平结构
   - 创建 `test_archive/` 存放历史测试
   - 统一命名规范

3. **更新自动化脚本**
   - 修改 `setup_framework` 以适应新结构
   - 更新 CI/CD 配置

4. **编写完整文档**
   - 测试添加指南
   - 维护手册
   - 故障排查文档

### 推荐行动计划

**立即执行(本周):**
1. ✅ 创建 `.claude/CLAUDE.md` (已完成)
2. 📝 为每个主要测试类别创建 README.md
3. 🗑️ 清理明显的测试结果目录(9_19/, master/)

**短期(1-2周):**
4. 📋 盘点所有测试,标记活跃/归档状态
5. 🔀 整合状态子目录中的测试
6. 📖 为关键测试添加详细注释

**中期(1个月):**
7. 🏗️ 统一测试命名规范
8. 🧪 验证所有测试在 CI 上正常运行
9. 📚 编写新测试添加指南

**长期(持续):**
10. 🔄 定期审查和清理归档测试
11. 📈 扩展测试覆盖
12. 🤝 同步上游 Verilator 变化

## 具体改进建议

### 1. 创建测试类别 README.md 模板

```markdown
# <Category Name> Tests

## Purpose
Brief description of what features this category tests.

## Test List

### Active Tests
- `t_<name>.sv` - Description and expected behavior

### Known Issues
- List any failing tests with issue tracker links

### Notes
- Platform-specific requirements
- Special build flags needed
```

### 2. 清理脚本示例

```bash
#!/bin/bash
# cleanup_test_results.sh - Remove test result directories from source tree

FEATURE_TESTS="planv_tests/feature_tests"

# Remove branch-specific test results
find $FEATURE_TESTS -type d -name "*_verilator_*" -exec rm -rf {} +
find $FEATURE_TESTS -type d -name "9_19" -exec rm -rf {} +
find $FEATURE_TESTS -type d -name "master" -exec rm -rf {} +
find $FEATURE_TESTS -type d -name "vsim_failed" -exec rm -rf {} +

echo "Cleanup complete. Review with 'git status' before committing."
```

### 3. 测试迁移检查清单

迁移 `passed/`, `failed/` 等子目录中的测试时:

- [ ] 确认测试仍然相关(功能未废弃)
- [ ] 本地运行测试验证功能
- [ ] 检查是否与父目录测试重复
- [ ] 添加/更新测试注释
- [ ] 移动到父目录或归档
- [ ] 更新类别 README.md

### 4. Git 忽略配置

添加到 `.gitignore`:
```
# Build artifacts
sim/
logs/
*.log
*.vcd

# Test results (should be in CI artifacts)
**/test_results/
**/*_verilator_passed/
**/*_verilator_failed/

# Temporary files
transcript
work/
```

## 成功指标

重构后应该能够:

1. **新人快速上手**
   - 5 分钟内理解项目结构
   - 10 分钟内添加新测试

2. **明确的测试集**
   - CI 运行的测试明确可见
   - 不会误运行归档测试

3. **清晰的维护路径**
   - 知道在哪里添加新测试
   - 知道如何归档过时测试

4. **自文档化**
   - 每个类别都有 README.md
   - 关键测试有详细注释

## 总结

**当前状态:** 功能完整的测试框架,但组织结构混乱

**核心问题:** 测试源文件与测试结果混杂,状态子目录导致维护困难

**解决方向:** 渐进式清理,添加文档,统一规范

**优先级:**
1. 🔴 清理测试结果目录(风险低,收益高)
2. 🟡 添加类别文档(改善可维护性)
3. 🟢 统一命名规范(长期持续改进)

**预期效果:** 清晰、可维护、易扩展的测试框架

---

**下一步行动:** 与团队讨论重构方案,确定优先级和时间表
