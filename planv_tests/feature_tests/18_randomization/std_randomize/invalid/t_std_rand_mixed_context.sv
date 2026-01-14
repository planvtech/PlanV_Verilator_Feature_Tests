// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with multiple error conditions

`include "test_utils.svh"

class Cls;
  rand int m_1;
  int m_2;
  function void test_this_randomize;
    int a;

    a = randomize(m_2) with {m_2 > 2 && m_2 < 5;};
    `DBG(("%d: a=%0d %0d", `__LINE__, a, m_2))
    if (a != 1) $stop;
    // Problem 2: m_2 should be 3 or 4, but get out-of-range return
    //FIXME-uncomment:  if (!(m_2 > 2 && m_2 < 5)) $stop;

    // Problem 1:
    //   Got %Warning: /svaha/wsnyder/SandBox/homecvs/v4/verilator/include/verilated_random.cpp:417: Internal: Solver error: (error "line 9 column 27: invalid empty $
    a = this.randomize() with {m_1 > 5 && m_1 < 10;};
    `DBG(("%d: a=%0d %0d", `__LINE__, a, m_1))
    if (a != 1) $stop;
    if (!(m_1 > 5 && m_1 < 10)) $stop;
  endfunction
endclass

module t_std_rand_mixed_context;
  initial begin
    Cls c = new;
    c.test_this_randomize();

    `TEST_PASS
  end
endmodule