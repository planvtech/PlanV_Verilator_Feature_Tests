typedef struct packed {
    rand bit [7:0] byte_value;
    rand int int_value;
} PackedStruct;

class PackedStructTest;
    rand PackedStruct my_struct;

    function new();
        my_struct.byte_value = 8'hA0;
    endfunction
endclass

module packed_struct_test;
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