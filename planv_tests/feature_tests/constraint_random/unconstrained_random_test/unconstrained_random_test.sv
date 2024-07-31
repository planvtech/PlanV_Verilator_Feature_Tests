typedef enum bit[15:0] { 
    ONE = 3,
    TWO = 5,
    THREE = 8,
    FOUR = 13
} ENUM;

class cls;
    rand ENUM enum_4_;
    rand bit[31:0] lgc_32_bit;
    rand bit x;

    function new();
        enum_4_ = ONE;
    endfunction
endclass

class w_sequence_item;
    cls cls_1_;
    int r;
    int flag = 0;

    rand logic[7:0] data1;
    rand logic[7:0] data2;
    rand logic[7:0] data3;
    rand int delay;
    
    // constraint w_delay_con { delay > 90 && delay < 700;}
    constraint data1_con {
        // conditional doesn't work
        if(flag) {
            data1 inside {1, 2, 3}; //|| data % 2 == 0;
        } else {
            // mask
            (data1 & 8'hF0) == 8'hA0;
        }
    }

    constraint data2_con {
        data2 inside {1, 2, 3};
    }

    constraint data3_con {
        (data3 & 8'hF0) == 8'hA0;
    }

    function new(string name = "w_sequence_item");
        cls_1_ = new();
        r = cls_1_.randomize(); // randomize() with {} is not supported in Verilator currently.
        flag = cls_1_.x;
    endfunction

endclass

module unconstrained_random_test;
    w_sequence_item w;
    int v;
    initial begin
        repeat(50) begin

            w = new();
            v = w.randomize(); // with { delay > 90 && delay < 700; };
            if (v !=1 ) $stop;
            
            if (w.flag) begin
                if (!(w.data1 == 1 || w.data1 == 2 || w.data1 == 3)) $display("Constraint violated: flag = %0d, data1 = %0d", w.flag, w.data1);
            end else begin
                if (!((w.data1 & 8'hF0) == 8'hA0)) $display("Constraint violated: flag = %0d, data1 = %0d", w.flag, w.data1);
            end
            
            if (!(w.data2 == 1 || w.data2 == 2 || w.data2 == 3)) $display("Constraint violated: data2 = %0d", w.data2);
            if (!((w.data3 & 8'hF0) == 8'hA0)) $display("Constraint violated: data3 = %0d", w.data3);

            if (!(w.cls_1_.enum_4_ == 5 || w.cls_1_.enum_4_ == 8)) $display("Constraint violated: cls_1_.enum_4_ = %0d", w.cls_1_.enum_4_);

            //$display(w);
            $display("w_sequence_item: delay: %0d, flag: %b", w.delay, w.flag);
            $display("data1(h) = %h", w.data1);
            $display("data2(h) = %h", w.data2);
            $display("data3(h) = %h", w.data3);

            $display("cls: enum_4_: %0d, lgc_32_bit: %h, x: %b", w.cls_1_.enum_4_, w.cls_1_.lgc_32_bit, w.cls_1_.x);
            $display("***************************");
            
        end
        $finish;
    end
endmodule