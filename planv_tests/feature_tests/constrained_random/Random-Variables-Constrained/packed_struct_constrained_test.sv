typedef struct packed {
    rand bit [7:0] byte_value;
    rand int int_value;
} PackedStruct;

class PackedStructTest;
    rand PackedStruct my_struct;

    function new();
        my_struct.byte_value = 8'hA0;
    endfunction

    // Constraint block
    constraint struct_constraint {
        my_struct.byte_value == 8'hA0;    // Keep byte_value fixed at 8'hA0
        my_struct.int_value inside {[0:100]};  // Constrain int_value to be between 0 and 100
    }
    
endclass

module packed_struct_constrained_test;
    PackedStructTest struct_test;
    initial begin
        struct_test = new();
        repeat(10) begin
            if (!struct_test.randomize()) $error("Randomization failed");
            $display("byte_value: %h, int_value: %0d", struct_test.my_struct.byte_value, struct_test.my_struct.int_value);
        end
        $finish;
    end
endmodule