// Examples from LRM 1800-2023

class Bus;
    rand bit[15:0] addr;
    rand bit[31:0] data;
    constraint word_align {addr[1:0] == 2'b0;}
endclass

typedef enum {low, mid, high} AddrType;

class MyBus extends Bus;
    rand AddrType atype;
    constraint addr_range
    {
    (atype == low ) -> addr inside { [0 : 15] };
    (atype == mid ) -> addr inside { [16 : 127]};
    (atype == high) -> addr inside {[128 : 255]};
    }
endclass

task exercise_bus (MyBus bus);
    int res;
    // EXAMPLE 1: restrict to low addresses 
    res = bus.randomize() with {atype == low;}; 
    // EXAMPLE 2: restrict to address between 10 and 20
    res = bus.randomize() with {10 <= addr && addr <= 20;};
    // EXAMPLE 3: restrict data values to powers-of-two
    res = bus.randomize() with {(data & (data - 1)) == 0;};
endtask

task exercise_illegal(MyBus bus, int cycles);
    int res;
    // Disable word alignment constraint.
    bus.word_align.constraint_mode(0);
    repeat (cycles) begin
        // CASE 1: restrict to small addresses.
        res = bus.randomize() with {addr[0] || addr[1];};
    end
    // Reenable word alignment constraint
    bus.word_align.constraint_mode(1);
endtask

class XYPair;
    rand integer x, y;
endclass
class MyXYPair extends XYPair; 

    int res;
    // Disable random.
    x.rand_mode(0);
    repeat (cycles) begin
        x.randomize()
    end
    // Reenable random
    x.rand_mode(1);

    function void pre_randomize();
        super.pre_randomize(); 
        $display("Before randomize x=%0d, y=%0d", x, y);
    endfunction
    function void post_randomize();
        super.post_randomize();
        $display("After randomize x=%0d, y=%0d", x, y);
    endfunction
endclass

 x dist {100:=1, 200:=2, 300:=5};
 x dist {100:/1, 200:/2, 300:/5};

 x != 200;
x dist {100:=1, 200:=2, 300:=5} ;

 x dist {[100:102]:=1, 103:=1};
 x dist {[100:102]:/3, 103:=1};

rand byte a[5];
rand byte b;
rand byte excluded;
constraint u { unique {b, a[2:3], excluded}; }
constraint exclusion { excluded == 5; }


module LRM_random_and_disable_test;

    Bus bus = new;

        initial begin
        
        repeat (50) begin
            if (bus.randomize() == 1)
                $display ("addr = %4h data = %h\n", bus.addr, bus.data);
            else
                $display ("BUS Randomization test failed.\n");
        end

        repeat(50) begin

            $display("***************************");

            v = w.randomize(); // with { delay > 90 && delay < 700; };
            if (v !=1 ) $stop;
            
            // Test results
            
            if (w.ic_data1 > 2) begin
                if (!(w.ic_data2 == 1 || w.ic_data2 == 2 || w.ic_data2 == 3)) $display("Constraint violated: ic_data1 = %0d, ic_data2 = %0d", w.ic_data1, w.ic_data2);
            end

            if (w.flag > 2) begin
                if (!(w.iec_data1 == 1 || w.iec_data1 == 2 || w.iec_data1 == 3 || w.iec_data1 % 2 == 0)) $display("Constraint violated: flag = %0d, iec_data1 = %0d", w.flag, w.iec_data1);
            end else begin
                if (!((w.iec_data1 & 8'hF0) == 8'hA0)) $display("Constraint violated: flag = %0d, iec_data1 = %0d", w.flag, w.iec_data1);
            end

            if (w.flag > 2) begin
                if (!(w.iec_data2 == 1 || w.iec_data2 == 2 || w.iec_data2 == 3)) $display("Constraint violated: flag = %0d, iec_data2 = %0d", w.flag, w.iec_data2);
            end else if (w.flag > 0) begin
                if (!(w.iec_data2 == 4 || w.iec_data2 == 5)) $display("Constraint violated: flag = %0d, iec_data2 = %0d", w.flag, w.iec_data2);
            end else if (w.flag > -2) begin
                if (!(w.iec_data2 == 6 || w.iec_data2 == 7)) $display("Constraint violated: flag = %0d, iec_data2 = %0d", w.flag, w.iec_data2);
            end else begin
                if (!(w.iec_data2 == 8 || w.iec_data2 == 9)) $display("Constraint violated: flag = %0d, iec_data2 = %0d", w.flag, w.iec_data2);
            end
                // assert doesn't work!
            if (w.flag > 0) begin
                if (w.sub_flag > 10) begin
                    assert(w.iec_data3 == 1 || w.iec_data3 == 2 || w.iec_data3 == 3 || w.iec_data3 % 2 == 0) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end else if (w.sub_flag == 10) begin
                    assert(w.iec_data3 == 6 || w.iec_data3 == 7) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end else begin
                    assert(w.iec_data3 == 4 || w.iec_data3 == 5) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end
            end else if (w.flag == 0 || w.flag == -1) begin
                if (w.sub_flag < -10) begin
                    assert(w.iec_data3 == 10 || w.iec_data3 == 11) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end else begin
                    assert(w.iec_data3 == 12 || w.iec_data3 == 13) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end
            end else begin
                if (w.sub_flag > 20) begin
                    assert(w.iec_data3 == 14 || w.iec_data3 == 15) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end else if (w.sub_flag == 20) begin
                    assert(w.iec_data3 == 16 || w.iec_data3 == 17) else $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end else begin
                    // Error
                    if(!(w.iec_data3 == 8 || w.iec_data3 == 9)) $error("Constraint violated: flag = %0d, sub_flag = %0d, iec_data3 = %0d", w.flag, w.sub_flag, w.iec_data3);
                end
            end

            $display("ic_data1(h) = %h", w.ic_data1);
            $display("ic_data2(h) = %h", w.ic_data2);

            $display("flag(d) = %d", w.flag);
            $display("sub_flag(d) = %d", w.sub_flag);
            $display("iec_data1(h) = %h", w.iec_data1);
            $display("iec_data2(d) = %d", w.iec_data2);
            $display("iec_data3(d) = %d", w.iec_data3);

        end
        $finish;
    end
endmodule