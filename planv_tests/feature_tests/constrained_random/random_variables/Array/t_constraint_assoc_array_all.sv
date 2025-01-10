// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

typedef struct packed {
    bit [15:0] high;
    bit [15:0] low;
} PackedIndexType;

typedef struct {
    int a;
    int b;
} UnpackedIndexType;

typedef enum { RED, GREEN, YELLOW } color_t;

// Enum-based associative array
class AssocArrayEnum;
    rand bit [7:0] colors [color_t];
    constraint c1 { foreach (colors[i]) colors[i] > 4; }

    function new();
        colors[RED] = 8'd5;
        colors[GREEN] = 8'd10;
        colors[YELLOW] = 8'd15;
    endfunction
endclass

// Struct (packed) index associative array
class AssocArrayPackedStruct;
    rand bit [31:0] data [PackedIndexType];
    constraint valid_entries { foreach (data[i]) data[i] < 100; }

    function new();
        PackedIndexType idx;
        idx.high = 16'd1;
        idx.low = 16'd1;
        data[idx] = 32'd50;
    endfunction
endclass

// Struct (unpacked) index associative array
class AssocArrayUnpackedStruct;
    rand bit [31:0] data [UnpackedIndexType];
    // constraint valid_entries { foreach (data[i]) data[i] < 100; } Illegal non-integral expression in random constraint.

    function new();
        UnpackedIndexType idx;
        idx.a = 1;
        idx.b = 2;
        data[idx] = 32'd25;
    endfunction
endclass
typedef logic [2:0][7:0] IndexArrayType;
// Array as index associative array
class AssocArrayArrayIndex;
    rand bit [31:0] data [IndexArrayType];
    constraint valid_entries { foreach (data[i]) data[i] > 0; }

    function new();
        IndexArrayType idx;
        idx = 0;
        data[idx] = 32'd75;
    endfunction
endclass
class keyClass;
    bit [3:0] id;
endclass
class AssocArrayClass;
    rand bit [31:0] data [keyClass];
    constraint c3 { foreach (data[i]) data[i] > 0;}
    function new();
        keyClass cl;
        cl.id = 0;
        data[cl] = 32'd77;
    endfunction
endclass
class AssocArrayIntegral;
    rand int int_index [int];
    rand int str_index [string];

    constraint valid_int_index { foreach (int_index[i]) int_index[i] > 0; }
    constraint valid_str_index { foreach (str_index[i]) str_index[i] > 10; }

    function new();
        int_index[1] = 10;
        str_index["key"] = 20;
    endfunction
endclass

module t_constraint_assoc_array_all;
    AssocArrayEnum enum_arr;
    AssocArrayPackedStruct packed_arr;
    AssocArrayUnpackedStruct unpacked_arr;
    AssocArrayArrayIndex array_index_arr;
    AssocArrayIntegral integral_arr;
    int success;
    initial begin
        // Create instances of the classes
        enum_arr = new();
        packed_arr = new();
        unpacked_arr = new();
        array_index_arr = new();
        integral_arr = new();

        // Randomization tests
        success = enum_arr.randomize();
        $display("AssocArrayEnum randomization successful[ %0d ].", success);
        foreach (enum_arr.colors[i])
            $display("colors[%0s] = %0d", i.name(), enum_arr.colors[i]);

        success = packed_arr.randomize();
        $display("packed_arr randomization successful[ %0d ].", success);
        foreach (packed_arr.data[i])
            $display("data[%0d:%0d] = %0d", i.high, i.low, packed_arr.data[i]);

        success = unpacked_arr.randomize();
        $display("unpacked_arr randomization successful[ %0d ].", success);
        foreach (unpacked_arr.data[i])
            $display("data[%0d, %0d] = %0d", i.a, i.b, unpacked_arr.data[i]);

        success = array_index_arr.randomize();
        $display("array_index_arr randomization successful[ %0d ].", success);
        foreach (array_index_arr.data[i])
            $display("data[[%0d, %0d]] = %0d", i[0], i[1], array_index_arr.data[i]);

        success = integral_arr.randomize();
        $display("integral_arr randomization successful[ %0d ].", success);
        foreach (integral_arr.int_index[i])
            $display("int_index[%0d] = %0d", i, integral_arr.int_index[i]);
        foreach (integral_arr.str_index[i])
            $display("str_index[%0s] = %0d", i, integral_arr.str_index[i]);

        // Successful execution marker
        $write("*-* All Finished *-*");
        $finish;
    end

endmodule
