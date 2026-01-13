class inner;
    rand int val;
    function new();
        val = 0;
    endfunction
    constraint c_1 { val == 1; }
endclass

class Foo;
   rand inner in;
   rand int x;
   function new();
      in = new();
      x = 2;
   endfunction
endclass

class Cls;
   rand Foo foo;
   rand int y;

   constraint c_1 {
      foo.x < y;
      foo.x > foo.in.val;
      y < 5;
      foo.in.val > 0;
   }

   function new();
       foo = new();
       y = 0;
   endfunction
endclass

module t_global_rand_t1;

   Cls obj;
   int res;
   bit success;

   initial begin
      obj = new();
      res = obj.randomize();
      $display("Randomization result: %0d, foo.x: %0d, y: %0d, foo.in.val: %0d", res, obj.foo.x, obj.y, obj.foo.in.val);
      success = (res == 1) && (obj.foo.x < obj.y) && (obj.foo.x > obj.foo.in.val) && (obj.y < 5) && (obj.foo.in.val > 0) && (obj.foo.in.val == 1);
      if (!success) begin
         $display("ERROR: Constraints not satisfied");
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
