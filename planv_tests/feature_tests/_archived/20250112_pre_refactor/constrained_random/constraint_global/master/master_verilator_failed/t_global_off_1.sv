class Foo;
   rand int x;
endclass

class Cls;
    rand Foo foo;
    rand int y;
    
    constraint c { foo.x < y; }

endclass

module t_global_off_1;

   Cls obj;
   int res;

   initial begin
      obj = new;
      obj.foo = new;
      res = obj.randomize();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
