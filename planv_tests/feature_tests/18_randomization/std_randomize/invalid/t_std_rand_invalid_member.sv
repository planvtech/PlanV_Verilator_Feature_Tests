// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() invalid usage patterns
//
// TEST_NEGATIVE: Expected compilation failure
// EXPECTED_ERROR: (vlog-2934) Argument for randomize() function must be a field of 'foo'
// VERIFIED: 2026-01-13 - QuestaSim correctly rejects non-member arguments to obj.randomize()

`include "test_utils.svh"

class Foo;
   int x;

   static function Foo get;
      Foo foo = new;
      return foo;
   endfunction
endclass

module t_std_rand_invalid_member;
   initial begin
      Foo foo = Foo::get();
      Foo foos[] = new[1];
      void'(foo.randomize(Foo::get().x));
      void'(foo.randomize(foos[0].x));
      void'(foo.randomize(null));
   end
endmodule
