`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class array;

    rand int assoc_arr[string][string];

    function new();
      assoc_arr["John"]["Math"] = 85;
      assoc_arr["John"]["Science"] = 90;
      assoc_arr["Alice"]["Math"] = 75;
      assoc_arr["Alice"]["Science"] = 80;
    endfunction

    function check();
      check_rand(assoc_arr["John"]["Math"]);
      check_rand(assoc_arr["John"]["Science"]);
      check_rand(assoc_arr["Alice"]["Math"]);
      check_rand(assoc_arr["Alice"]["Science"]);
    endfunction

    task display_assoc_array();
      $display(assoc_arr);
      $display(assoc_arr["John"]["Science"]);
      $display(assoc_arr["Alice"]["Science"]);
      $display(assoc_arr["Alice"]);
    endtask
endclass

module assoc_arr_basic_rand;

    array cl;

  initial begin
    cl = new();

    $display("Associative Array Content before rand:");
    cl.display_assoc_array();
    $display("Associative Array Check Rand:");
    cl.check();
    $display("Associative Array Content after rand:");
    cl.display_assoc_array();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
