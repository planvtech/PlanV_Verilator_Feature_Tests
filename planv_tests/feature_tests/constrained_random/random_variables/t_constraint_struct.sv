// DESCRIPTION: PlanV Verilator Struct Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

typedef struct packed {
    bit [7:0] byte_value;
    int int_value;
} PackedStruct;

typedef struct {
    rand bit [7:0] byte_value;
    rand int int_value;
} UnpackedStruct;

class PackedStructTest;
    rand PackedStruct my_struct;

    function new();
        my_struct.byte_value = 8'hA0;
    endfunction

    // Constraint block for packed struct
    constraint struct_constraint {
        my_struct.byte_value == 8'hA0;               // Keep byte_value fixed at 8'hA0
        my_struct.int_value inside {[0:100]};       // Constrain int_value to be between 0 and 100
    }

    // Self-check function for packed struct
    function void check();
        if (my_struct.byte_value != 8'hA0) begin
            $display("Error: my_struct.byte_value = %h is not equal to 8'hA0", my_struct.byte_value);
            $stop;
        end
        if (!(my_struct.int_value inside {[0:100]})) begin
            $display("Error: my_struct.int_value = %d is out of bounds", my_struct.int_value);
            $stop;
        end
        $display("PackedStruct constraints validated successfully.");
    endfunction
endclass

class UnpackedStructTest;
    rand UnpackedStruct my_unpacked_struct;

    // Constraint block for unpacked struct
    constraint unpacked_struct_constraint {
        my_unpacked_struct.byte_value inside {8'hA0, 8'hB0, 8'hC0};  // Constrain byte_value to specific values
        my_unpacked_struct.int_value inside {[50:150]};               // Constrain int_value to be between 50 and 150
    }

    // Self-check function for unpacked struct
    function void check();
        if (!(my_unpacked_struct.byte_value inside {8'hA0, 8'hB0, 8'hC0})) begin
            $display("Error: my_unpacked_struct.byte_value = %h is out of bounds", my_unpacked_struct.byte_value);
            $stop;
        end
        if (!(my_unpacked_struct.int_value inside {[50:150]})) begin
            $display("Error: my_unpacked_struct.int_value = %d is out of bounds", my_unpacked_struct.int_value);
            $stop;
        end
        $display("UnpackedStruct constraints validated successfully.");
    endfunction
endclass

module t_constraint_struct;
    PackedStructTest packed_struct_test;
    UnpackedStructTest unpacked_struct_test;

    initial begin
        // Test packed struct
        packed_struct_test = new();
        repeat(10) begin
            if (!packed_struct_test.randomize()) $error("Packed struct randomization failed");
            packed_struct_test.check();  // Self-check for packed struct
            $display("PackedStruct: byte_value: %h, int_value: %0d", packed_struct_test.my_struct.byte_value, packed_struct_test.my_struct.int_value);
        end

        // Test unpacked struct
        unpacked_struct_test = new();
        repeat(10) begin
            if (!unpacked_struct_test.randomize()) $error("Unpacked struct randomization failed");
            unpacked_struct_test.check();  // Self-check for unpacked struct
            $display("UnpackedStruct: byte_value: %h, int_value: %0d", unpacked_struct_test.my_unpacked_struct.byte_value, unpacked_struct_test.my_unpacked_struct.int_value);
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
