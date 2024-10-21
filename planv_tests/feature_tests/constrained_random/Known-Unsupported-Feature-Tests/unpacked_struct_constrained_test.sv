typedef union packed{
    int x;
    bit [3:0][7:0] byte_value;
} UNION;

typedef struct packed{
    int x;
    bit [13:0] byte_value;
} packed_struct;

typedef struct {
    rand int x;
    rand bit [13:0] byte_value;
} unpacked_struct;

class cls;
    rand UNION union;
    rand packed_struct packed_struct;
    rand unpacked_struct unpacked_struct;

    constraint union_con {
        union.x inside {3, 7};
    }

    constraint p_struct_con {
        packed_struct.x inside {3, 7};
        packed_struct.byte_value inside {[181:186]};
    }

    constraint unp_struct_con {
        unpacked_struct.x inside {2, 8};
        unpacked_struct.byte_value inside {[170:180]};
    }
endclass

module unpacked_struct_constrained_test;
    cls cl;
    int v;
    initial begin
        repeat(10) begin

            v = cl.randomize();
            if (v !=1 ) $stop;
            $display("cls: union: %d, %d", cl.union.x, cl.union.byte_value);
            $display("cls: packed_struct: %d, %d", cl.packed_struct.x, cl.packed_struct.byte_value);
            $display("cls: unpacked_struct: %d, %d", cl.unpacked_struct.x, cl.unpacked_struct.byte_value);

        end
        $finish;
    end
endmodule