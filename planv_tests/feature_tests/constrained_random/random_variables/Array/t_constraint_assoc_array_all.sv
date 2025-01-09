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
    constraint valid_entries { foreach (data[i]) data[i] < 100; }

    function new();
        UnpackedIndexType idx;
        idx.a = 1;
        idx.b = 2;
        data[idx] = 32'd25;
    endfunction
endclass
typedef int IndexArrayType[2];
// Array as index associative array
class AssocArrayArrayIndex;
    rand bit [31:0] data [IndexArrayType];
    constraint valid_entries { foreach (data[i]) data[i] > 0; }

    function new();
        IndexArrayType idx;
        idx[0] = 1;
        idx[1] = 2;
        data[idx] = 32'd75;
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

    initial begin
        // Create instances of the classes
        AssocArrayEnum enum_arr = new();
        AssocArrayPackedStruct packed_arr = new();
        AssocArrayUnpackedStruct unpacked_arr = new();
        AssocArrayArrayIndex array_index_arr = new();
        AssocArrayIntegral integral_arr = new();

        // Randomization tests
        enum_arr.randomize();
        $display("AssocArrayEnum randomization successful.");
        foreach (enum_arr.colors[i])
            $display("colors[%0s] = %0d", i.name(), enum_arr.colors[i]);

        packed_arr.randomize();
        $display("AssocArrayPackedStruct randomization successful.");
        foreach (packed_arr.data[i])
            $display("data[%0d:%0d] = %0d", i.high, i.low, packed_arr.data[i]);

        unpacked_arr.randomize();
        $display("AssocArrayUnpackedStruct randomization successful.");
        foreach (unpacked_arr.data[i])
            $display("data[%0d, %0d] = %0d", i.a, i.b, unpacked_arr.data[i]);

        array_index_arr.randomize();
        $display("AssocArrayArrayIndex randomization successful.");
        foreach (array_index_arr.data[i])
            $display("data[[%0d, %0d]] = %0d", i[0], i[1], array_index_arr.data[i]);

        integral_arr.randomize();
        $display("AssocArrayIntegral randomization successful.");
        foreach (integral_arr.int_index[i])
            $display("int_index[%0d] = %0d", i, integral_arr.int_index[i]);
        foreach (integral_arr.str_index[i])
            $display("str_index[%0s] = %0d", i, integral_arr.str_index[i]);

        // Successful execution marker
        $write("*-* All Finished *-*");
        $finish;
    end

endmodule
