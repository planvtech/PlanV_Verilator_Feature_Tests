# PlanV Verilator Feature Tests - Quick Reference

## 快速开始

### 运行单个测试
```bash
cd /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests
./scripts/run -b master -t planv_tests/feature_tests/assertions/t_assertion_immediate.sv
```

### 运行整个类别
```bash
./scripts/run -b master -t planv_tests/feature_tests/constrained_random
```

### 测试不同 Verilator 版本
```bash
./scripts/run -b version-5.044 -t planv_tests/feature_tests/assertions
```

### 查看测试结果
```bash
# 查看汇总报告
cat logs/feature_tests/tests_report.log

# 查看单个测试日志
cat logs/feature_tests/assertions/t_assertion_immediate.log

# 打开 HTML 报告
firefox logs/feature_tests/fancy_test_report_master.html
```

## 添加新测试

### Feature Test (单文件测试)

1. **选择或创建类别目录**
   ```bash
   # 使用现有类别
   cd planv_tests/feature_tests/assertions

   # 或创建新类别
   mkdir -p planv_tests/feature_tests/my_new_category
   ```

2. **创建测试文件** (文件名 = 模块名)
   ```systemverilog
   // planv_tests/feature_tests/assertions/t_my_new_test.sv

   // DESCRIPTION: PlanV Verilator <Feature> Test
   //
   // Property of PlanV GmbH, 2024. All rights reserved.
   // Contact: yilou.wang@planv.tech

   module t_my_new_test;  // 必须与文件名匹配!
       initial begin
           // Your test logic here

           // 成功标记
           $display("*-* All Tests Passed *-*");
           $finish;
       end
   endmodule
   ```

3. **本地测试**
   ```bash
   ./scripts/run -b master -t planv_tests/feature_tests/assertions/t_my_new_test.sv
   ```

4. **提交**
   ```bash
   git add planv_tests/feature_tests/assertions/t_my_new_test.sv
   git commit -m "Add test for <feature>"
   ```

### UVM Test (多文件测试)

1. **创建测试目录**
   ```bash
   mkdir -p planv_tests/uvm_tests/my_uvm_test
   cd planv_tests/uvm_tests/my_uvm_test
   ```

2. **添加测试文件和 Makefile**
   - 不会自动生成,需要手动创建 Makefile
   - 参考 `uvm_test_1/` 作为模板

3. **本地测试**
   ```bash
   cd planv_tests/uvm_tests/my_uvm_test
   export VERILATOR_ROOT=/path/to/PlanV_Verilator_Feature_Tests/verilator/master
   make
   ```

## 调试测试失败

### 查看详细错误
```bash
# 1. 找到测试日志
cat logs/feature_tests/<category>/<test>.log

# 2. 手动进入 sim 目录重新运行
cd sim/feature_tests/<category>/<test>
export VERILATOR_ROOT=$(pwd)/../../../../verilator/master

# 3. 清理重编译
make clean
make

# 4. 启用 debug 模式
make debug=1

# 5. 导出 AST JSON (检查 Verilator 内部)
make json_dump=1
```

### 常见错误及解决

#### 错误: Width truncation warning
```
%Warning-WIDTHTRUNC: ...
```

**解决:**
```systemverilog
/* verilator lint_off WIDTHTRUNC */
int result = obj.randomize();
/* verilator lint_on WIDTHTRUNC */
```

#### 错误: No solver installed
```
No constraint solver installed
```

**解决:**
```bash
pip3 install z3-solver
python3 -c "import z3; print(z3.get_version_string())"
```

#### 错误: Module not found
```
%Error: Cannot find file/module: 't_my_test'
```

**原因:** 模块名与文件名不匹配

**解决:** 确保 `module <name>` 与文件名 `<name>.sv` 完全一致

#### 错误: Variable used before initialization
```
%Error: Variable 'x' used before initialization
```

**解决:**
```systemverilog
// 错误:
initial begin
    int x;
    x = 5;
end

// 正确:
initial begin
    automatic int x = 0;  // 添加 automatic 和初始值
    x = 5;
end
```

## 项目维护

### 更新 Verilator 子模块
```bash
cd verilator/master
git pull origin master
cd ../..
git add verilator/master
git commit -m "Update Verilator master to latest"
```

### 清理生成文件
```bash
# 清理 sim 和 logs
rm -rf sim/ logs/

# 重新运行测试会自动重建
./scripts/run -b master -t planv_tests/feature_tests/assertions
```

### 添加新 Verilator 版本
```bash
cd verilator
git clone https://github.com/planvtech/verilator.git version-X.XXX
cd version-X.XXX
git checkout stable  # 或特定 tag
autoconf
./configure
make -j$(nproc)
```

## 测试覆盖概览

### Feature Tests (165+ 测试)

| 类别 | 测试数量 | 描述 |
|------|---------|------|
| `assertions` | ~5 | 立即/并发断言 |
| `assignment_statements` | 若干 | 赋值语句模式 |
| `constrained_random` | ~100+ | **最大类别**,约束随机化 |
| `foreach` | 若干 | foreach 循环 |
| `functional_coverage` | 若干 | 功能覆盖率 |
| `t_racing` | 4 | 竞争条件 |
| `t_recursive` | 若干 | 递归实例化 |
| `t_timing_debug` | 若干 | 时序/延迟 |
| `t_virtual_interface` | 若干 | 虚拟接口 |

### UVM Tests

| 测试 | 状态 | 描述 |
|------|------|------|
| `DUT` | ✅ | 简单 C++ testbench |
| `pyuvm_test` | ✅ | Python-based UVM (cocotb) |
| `uvm_test_1` | ⚠️ | 仅 master 分支可运行 |
| `uvm_test_2` | ❌ | 递归实例化不支持 |
| `uvm_test_cvv` | ⚠️ | Core-V-Verif 风格 |

## 文件位置速查

### 测试源文件
```
planv_tests/
├── feature_tests/     # SystemVerilog 特性测试
└── uvm_tests/         # UVM 验证测试
```

### 自动化脚本
```
scripts/
├── run                        # 主运行脚本
├── set_build_run_functions    # 核心函数库
├── setup_framework            # 生成 Makefile
└── ciSystemRunner             # CI 专用脚本
```

### 生成的文件(不提交)
```
sim/           # 每个测试的 Makefile 和编译产物
logs/          # 测试日志和 HTML 报告
```

### 依赖库(submodules)
```
verilator/     # 多个 Verilator 版本
uvm_lib/       # UVM 库
```

### 配置文件
```
.github/workflows/PlanV_verilator_feature_tests.yml  # CI/CD 配置
.gitmodules                                           # Git 子模块配置
```

## 关键脚本解析

### scripts/run

**功能:** 本地测试主入口

**参数:**
- `-b <branch>` : Verilator 分支 (默认: master)
- `-t <test>` : 测试文件或目录 (默认: planv_tests/feature_tests)

**流程:**
1. 调用 `setup` → 生成 sim/ 目录和 Makefile
2. 调用 `build` → 编译 Verilator
3. 调用 `run_tests` → 运行测试,生成日志和报告

### scripts/setup_framework

**功能:** 扫描 `.sv` 文件,为每个测试生成 Makefile

**输入:** 测试目录路径

**输出:** `sim/` 目录,镜像 `planv_tests/` 结构,每个测试一个 Makefile

**关键逻辑:**
```bash
find "${TESTS_DIR}" -type f -name "*.sv" | while read -r sv_file; do
    test_path=$(dirname "$sv_file")
    test_name=$(basename "$sv_file" .sv)
    create_test_framework "$test_path" "$test_name"
done
```

### scripts/set_build_run_functions

**功能:** 定义核心函数(setup, build, run_tests)

**关键函数:**
- `create_logdir`: 创建/清空 logs/
- `setup`: 更新子模块 + 运行 setup_framework
- `build`: 编译指定 Verilator 分支
- `run_tests`: 执行所有测试,生成报告

**成功判定:**
```bash
if grep -q "*-* All Finished *-*" "$LOGFILE"; then
    echo "PASSED"
fi
```

## CI/CD 行为

### 触发条件
- Push to `main` 分支
- Pull Request
- 每周一 07:00 (cron)
- 手动触发

### 执行流程
1. **动态发现 Verilator 分支**
   ```bash
   ls verilator | jq -R -s -c 'split("\n")[:-1]'
   ```

2. **并行执行每个分支**
   - 独立的 GitHub runner
   - 独立的 ccache

3. **上传产物**
   - 日志文件: `test-output-<branch>`
   - HTML 报告

### 依赖安装(Ubuntu)
```bash
sudo apt-get install git help2man perl python3 make autoconf flex bison ccache
sudo apt-get install gcc-12 g++-12 libunwind-dev libgoogle-perftools-dev
sudo pip3 install pyyaml jinja2 robotframework z3-solver
```

## 常用检查命令

### 统计测试数量
```bash
# 统计所有 .sv 文件
find planv_tests/feature_tests -name "*.sv" | wc -l

# 按类别统计
for dir in planv_tests/feature_tests/*/; do
    echo -n "$(basename $dir): "
    find $dir -name "*.sv" | wc -l
done
```

### 检查测试状态
```bash
# 查看最近一次运行的汇总
cat logs/feature_tests/tests_report.log

# 统计 PASSED/FAILED
grep PASSED logs/feature_tests/tests_report.log | wc -l
grep FAILED logs/feature_tests/tests_report.log | wc -l
```

### 查找特定模式的测试
```bash
# 查找所有 constraint 相关测试
find planv_tests/feature_tests -name "*constraint*.sv"

# 查找所有 randomize 相关测试
find planv_tests/feature_tests -name "*random*.sv"
```

### 检查子模块状态
```bash
git submodule status
git submodule update --init --recursive
```

## 故障排查检查清单

测试失败时,按顺序检查:

- [ ] **日志文件存在吗?**
  - `cat logs/feature_tests/<category>/<test>.log`

- [ ] **Verilator 编译通过了吗?**
  - 搜索日志中的 `%Error:`

- [ ] **仿真运行了吗?**
  - 日志中应该有 `simulate` 阶段输出

- [ ] **测试超时了吗?**
  - 检查是否有无限循环

- [ ] **依赖安装了吗?**
  - `python3 -c "import z3"` (constraint tests)
  - `which verilator`

- [ ] **环境变量设置了吗?**
  - `echo $VERILATOR_ROOT`

- [ ] **文件名和模块名匹配吗?**
  - `t_test.sv` → `module t_test;`

- [ ] **成功标记正确吗?**
  - 必须有 `$display("*-* All Tests Passed *-*");` 和 `$finish;`

## 性能优化

### 加速本地测试
```bash
# 使用 ccache
export CCACHE_DIR=$HOME/.ccache
export PATH="/usr/lib/ccache:$PATH"

# 并行编译
export NPROC=$(nproc)
make -j$NPROC

# 只测试修改的类别
./scripts/run -b master -t planv_tests/feature_tests/assertions
```

### 减少 CI 运行时间
- 限制测试的 Verilator 版本数量
- 使用 GitHub Actions matrix 策略的 `fail-fast: false`
- 缓存 Verilator 编译产物(已配置 ccache)

## 备忘录

### 测试必须包含
```systemverilog
// 文件头
// DESCRIPTION: PlanV Verilator <Feature> Test
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

// 模块名 = 文件名
module t_<test_name>;

initial begin
    // Test logic

    // 成功标记
    $display("*-* All Tests Passed *-*");
    $finish;  // 必须有!
end
endmodule
```

### 不要做的事
- ❌ 提交 `sim/` 或 `logs/` 到 git
- ❌ 在 `planv_tests/` 中创建测试结果目录
- ❌ 修改 `verilator/` 子模块(应在专门的 Verilator 开发 repo)
- ❌ 在没有本地测试的情况下直接提交
- ❌ 创建新的状态子目录(`passed/`, `failed/` 等)

### 应该做的事
- ✅ 本地测试通过后再提交
- ✅ 为新类别添加 README.md
- ✅ 在测试中添加详细注释
- ✅ 使用有意义的测试名称
- ✅ 一个测试只测一个特性
- ✅ 定期更新文档

---

**快速联系:** yilou.wang@planv.tech
