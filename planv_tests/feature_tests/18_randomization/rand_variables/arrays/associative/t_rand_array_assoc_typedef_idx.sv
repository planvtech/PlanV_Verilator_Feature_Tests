// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: associative arrays with user-defined type indices

`include "test_utils.svh"

typedef struct packed {
  bit [15:0] high;
  bit [15:0] low;
} UserDefinedIndexType;

typedef enum { RED,GREEN, YELLOW } color_t;

class EnumAssocArr;

  rand bit[7:0] asso_colors [color_t] ;
  int i;

  constraint c1 { foreach (asso_colors[i]) asso_colors[i] > 4; }

  function new();
    asso_colors[RED] = 8'd0;
    asso_colors[GREEN] = 8'd0;
    asso_colors[YELLOW] = 8'd0;
  endfunction

  function void self_check();
    foreach (asso_colors[i]) begin
      if (asso_colors[i] <= 4) begin
        `DBG(("Self-check failed: asso_colors[%0d] = %0d", i, asso_colors[i]))
        $stop;
      end
    end
  endfunction

  function void print();
    `DBG(("asso_colors size = %d", asso_colors.size()))
    foreach (asso_colors[i]) begin
      `DBG(("asso_colors[%0d] = %0d", i, asso_colors[i]))
    end
  endfunction

endclass

class NormalAssocArrayUserDefined;

  bit [31:0] assoc_array[UserDefinedIndexType];

  function void insert(UserDefinedIndexType index, bit [31:0] value);
    assoc_array[index] = value;
  endfunction

  function void self_check(UserDefinedIndexType index);
    if (!assoc_array.exists(index)) begin
      $stop;
    end
  endfunction

  function void print();
    UserDefinedIndexType index;
    if (assoc_array.first(index)) begin
      do begin
        `DBG(("Index: high=%0d, low=%0d, Value: %0d", index.high, index.low, assoc_array[index]))
      end while (assoc_array.next(index));
    end
  endfunction
endclass

class ConstrainedAssocArrayUserDefined;

  rand bit [31:0] assoc_array[UserDefinedIndexType];
  UserDefinedIndexType t1, t2, t3, t4, t5;

  constraint valid_entries {
    foreach (assoc_array[i]) {
      assoc_array[i] < 100; // Values must be less than 100
    }
  }

  function new();
    t1.high = 111;
    t1.low = 111;
    assoc_array[t1] = 0;
    t2.high = 222;
    t2.low = 222;
    assoc_array[t2] = 0;
    t3.high = 333;
    t3.low = 333;
    assoc_array[t3] = 0;
    t4.high = 444;
    t4.low = 444;
    assoc_array[t4] = 0;
    t5.high = 555;
    t5.low = 555;
    assoc_array[t5] = 0;
  endfunction

  function void self_check();
    foreach (assoc_array[i]) begin
      if (assoc_array[i] >= 100) begin
        $stop;
      end
    end
  endfunction

  function void print();
    UserDefinedIndexType index;
    if (assoc_array.first(index)) begin
      do begin
        `DBG(("Index: high=%0d, low=%0d, Value: %0d", index.high, index.low, assoc_array[index]))
      end while (assoc_array.next(index));
    end
  endfunction
endclass

module t_rand_array_assoc_typedef_idx;

  EnumAssocArr obj = new();
  NormalAssocArrayUserDefined normal_user_defined;
  UserDefinedIndexType index_normal;
  ConstrainedAssocArrayUserDefined constrained_user_defined;
  int success;

  initial begin

    success = obj.randomize();
    if (success != 1) $stop;
    obj.self_check();
    obj.print();

    normal_user_defined = new();
    index_normal = '{high: 123, low: 456};
    normal_user_defined.insert(index_normal, 42);
    normal_user_defined.self_check(index_normal);
    normal_user_defined.print();

    constrained_user_defined = new();
    success = constrained_user_defined.randomize();
    if (success != 1) $stop;
    constrained_user_defined.self_check();
    constrained_user_defined.print();

    `TEST_PASS
  end
endmodule
