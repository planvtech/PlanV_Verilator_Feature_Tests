typedef enum bit[15:0] { 
    ONE = 3,
    TWO = 5,
    THREE = 8,
    FOUR = 13
} ENUM;

typedef union packed{
    int x;
    bit [3:0][7:0] byte_value;
} UNION;

typedef struct packed {
    int x;
    bit [3:0][7:0] byte_value;
} STRUCT;

class cls;
    rand ENUM enum_4;
    rand UNION union_2;
    rand STRUCT struct_2;
    //rand int dyn_arr[];
    rand bit[31:0] y;
    rand bit x;

    function new();
        enum_4 = ONE;
    endfunction
endclass
//DEBUG USE

class w_sequence_item;

    rand bit [2:0] typ;
    cls cls_1;
    int r;

    rand logic[7:0] data1;
    rand logic[7:0] data2;
    rand logic[7:0] data3;
    rand int delay;
    int flag;
    
    constraint data1_con {
        if(flag) {
            data1 inside {1, 2, 3} || data1 % 2 == 0;
        } else {
            // mask
            (data1 & 8'hF0) == 8'hA0;
        }
    }

    constraint data2_con {
        data2 inside {[32:256]};
    }

    constraint data3_con {
        (data3 & 8'hF0) == 8'hA0;
    }

    //constraint typ_con {
        //typ dist { 0:/20, [1:5]:/50, 6:/40, 7:/10};
    //}

    function new(string name = "w_sequence_item");
        cls_1 = new();
        r = cls_1.randomize();
        flag = cls_1.x;
    endfunction

endclass

module simple_tb;
    w_sequence_item w;
    int v;
    initial begin
        repeat(10) begin
            w = new();

            v = w.randomize(); // with { delay > 90 && delay < 700; };
            if (v !=1 ) $stop;
            
            $display("w_sequence_item: delay: %0d, flag: %b", w.delay, w.flag);
            $display("data1(h) = %h", w.data1);
            //$display("data1(d) = %d", w.data1);
            $display("data2(h) = %h", w.data2);
            //$display("data2(d) = %d", w.data2);
            $display("data3(h) = %h", w.data3);
            //$display("data3(d) = %d", w.data3);
            $display("typ(d) = %d", w.typ);

            $display("cls: enum_4: %0d, y: %h, x: %b", w.cls_1.enum_4, w.cls_1.y, w.cls_1.x);
            $display("cls: union: %d, %h", w.cls_1.union_2.x, w.cls_1.union_2.byte_value);
            $display("cls: struct: %d, %h", w.cls_1.struct_2.x, w.cls_1.struct_2.byte_value);

            $display("***************************");
        end
        $finish;
    end
endmodule