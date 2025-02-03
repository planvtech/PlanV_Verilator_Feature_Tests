// DESCRIPTION: PlanV Verilator Complex Struct Constrained Randomization Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

typedef struct {
    rand bit [7:0] byte_array[5];
    rand int int_array[5];
    bit [7:0] non_rand_byte_array[5];
} ArrayStruct;

typedef struct {
    rand bit [7:0] byte_value;
    rand int int_value;
} UnpackedStruct;

typedef struct {
    rand UnpackedStruct unpacked_array[5];
} UnpackedArrayStruct;

class ArrayStructTest;
    rand ArrayStruct my_array_struct;

    // Constraint block for array struct
    constraint array_struct_constraint {
        foreach (my_array_struct.byte_array[i]) {
            my_array_struct.byte_array[i] inside {8'hA0, 8'hB0, 8'hC0};  // Constrain byte_array to specific values
        }
        foreach (my_array_struct.int_array[i]) {
            my_array_struct.int_array[i] inside {[50:150]};  // Constrain int_array to be between 50 and 150
        }
    }

    // Self-check function for array struct
    function void check();
        foreach (my_array_struct.byte_array[i]) begin
            if (!(my_array_struct.byte_array[i] inside {8'hA0, 8'hB0, 8'hC0})) begin
                $display("Error: my_array_struct.byte_array[%0d] = %h is out of bounds", i, my_array_struct.byte_array[i]);
                $stop;
            end
        end
        foreach (my_array_struct.int_array[i]) begin
            if (!(my_array_struct.int_array[i] inside {[50:150]})) begin
                $display("Error: my_array_struct.int_array[%0d] = %d is out of bounds", i, my_array_struct.int_array[i]);
                $stop;
            end
        end
        $display("ArrayStruct constraints validated successfully.");
    endfunction
endclass

class StructArrayTest;
    rand UnpackedStruct struct_array[5];
    // Constraint block for struct array
    constraint struct_array_constraint {
        foreach (struct_array[i]) {
            struct_array[i].byte_value inside {8'hA0, 8'hB0, 8'hC0};  // Constrain byte_value to specific values
            struct_array[i].int_value inside {[50:150]};  // Constrain int_value to be between 50 and 150
        }
    }

    // Self-check function for struct array
    function void check();
        foreach (struct_array[i]) begin
            if (!(struct_array[i].byte_value inside {8'hA0, 8'hB0, 8'hC0})) begin
                $display("Error: struct_array[%0d].byte_value = %h is out of bounds", i, struct_array[i].byte_value);
                $stop;
            end
            if (!(struct_array[i].int_value inside {[50:150]})) begin
                $display("Error: struct_array[%0d].int_value = %d is out of bounds", i, struct_array[i].int_value);
                $stop;
            end
        end
        $display("StructArray constraints validated successfully.");
    endfunction

endclass

class UnpackedArrayStructTest;
    rand UnpackedArrayStruct my_unpacked_array_struct;

    // Constraint block for unpacked array struct
    constraint unpacked_array_struct_constraint {
        foreach (my_unpacked_array_struct.unpacked_array[i]) {
            my_unpacked_array_struct.unpacked_array[i].byte_value inside {8'hA0, 8'hB0, 8'hC0};  // Constrain byte_value to specific values
            my_unpacked_array_struct.unpacked_array[i].int_value inside {[50:150]};  // Constrain int_value to be between 50 and 150
        }
    }

    // Self-check function for unpacked array struct
    function void check();
        foreach (my_unpacked_array_struct.unpacked_array[i]) begin
            if (!(my_unpacked_array_struct.unpacked_array[i].byte_value inside {8'hA0, 8'hB0, 8'hC0})) begin
                $display("Error: my_unpacked_array_struct.unpacked_array[%0d].byte_value = %h is out of bounds", i, my_unpacked_array_struct.unpacked_array[i].byte_value);
                $stop;
            end
            if (!(my_unpacked_array_struct.unpacked_array[i].int_value inside {[50:150]})) begin
                $display("Error: my_unpacked_array_struct.unpacked_array[%0d].int_value = %d is out of bounds", i, my_unpacked_array_struct.unpacked_array[i].int_value);
                $stop;
            end
        end
        $display("UnpackedArrayStruct constraints validated successfully.");
    endfunction
endclass

module t_constraint_struct_complex;
    ArrayStructTest array_struct_test;
    UnpackedArrayStructTest unpacked_array_struct_test;
    StructArrayTest struct_array_test;

    initial begin
        // Test array struct
        array_struct_test = new();
        repeat(10) begin
            if (!array_struct_test.randomize()) $error("Array struct randomization failed");
            array_struct_test.check();  // Self-check for array struct
            foreach (array_struct_test.my_array_struct.byte_array[i]) begin
                $display("ArrayStruct: byte_array[%0d]: %h", i, array_struct_test.my_array_struct.byte_array[i]);
            end
            foreach (array_struct_test.my_array_struct.int_array[i]) begin
                $display("ArrayStruct: int_array[%0d]: %0d", i, array_struct_test.my_array_struct.int_array[i]);
            end
        end

        // Test unpacked array struct
        unpacked_array_struct_test = new();
        repeat(10) begin
            if (!unpacked_array_struct_test.randomize()) $error("Unpacked array struct randomization failed");
            unpacked_array_struct_test.check();  // Self-check for unpacked array struct
            foreach (unpacked_array_struct_test.my_unpacked_array_struct.unpacked_array[i]) begin
                $display("UnpackedArrayStruct: unpacked_array[%0d]: byte_value: %h, int_value: %0d", i, unpacked_array_struct_test.my_unpacked_array_struct.unpacked_array[i].byte_value, unpacked_array_struct_test.my_unpacked_array_struct.unpacked_array[i].int_value);
            end
        end

        // Test struct array
        struct_array_test = new();
        repeat(10) begin
            if (!struct_array_test.randomize()) $error("Struct array randomization failed");
            struct_array_test.check();  // Self-check for struct array
            foreach (struct_array_test.struct_array[i]) begin
                $display("StructArray: struct_array[%0d]: byte_value: %h, int_value: %0d", i, struct_array_test.struct_array[i].byte_value, struct_array_test.struct_array[i].int_value);
            end
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
