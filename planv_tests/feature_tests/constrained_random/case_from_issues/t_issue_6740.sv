// Test case for Verilator issue #6740
// Regression in constraints with inheritance and rand_mode

class RandomValue;
  rand int value;
  constraint small_int_c { value < 10; }

  task disable_val();
    value.rand_mode(0);
  endtask
endclass

class Base;
  rand RandomValue v = new;
endclass

class Foo extends Base;
endclass

module t_issue_6740;
  initial begin
    Foo d = new;
    Base b = d;

    // Disable randomization of v.value
    b.v.disable_val();

    // Set value to 11 (violates constraint, but should be OK since rand_mode is off)
    b.v.value = 11;

    // Randomize should fail because value is set to 11 and can't be changed
    if (bit'(b.randomize())) begin
      $display("ERROR: randomize() should have failed");
      $stop;
    end

    // Value should remain 11
    if (b.v.value != 11) begin
      $display("ERROR: value changed from 11 to %0d", b.v.value);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
