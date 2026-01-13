class A;
  rand int x;
endclass

class B extends A;
  constraint c {x == 1;};
endclass

class C;
  rand A a;
  constraint c {a.x < 100;};
endclass

module t_poly;
  initial begin
    C c = new;
    B b = new;
    // c.a = b;
    void'(c.randomize());
    $display("Randomized value: c.a.x = %0d", c.a.x);
    if (c.a.x != 1) $stop;
    $display("Test passed: c.a.x = %0d\n", c.a.x);
  end
endmodule
