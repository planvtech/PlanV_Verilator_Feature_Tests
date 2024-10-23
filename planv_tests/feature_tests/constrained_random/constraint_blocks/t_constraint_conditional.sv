// DESCRIPTION: PlanV Verilator Conditional Constraints Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ConditionalConstraintClass;

    rand int flag = 0;
    rand int sub_flag = 0;
    rand bit [2:0] ic_data1;
    rand logic [3:0] ic_data2;
    rand logic [7:0] iec_data1;
    rand logic [7:0] iec_data2;
    rand logic [9:0] iec_data3;

    constraint imp_con {
        ic_data1 > 2 -> ic_data2 inside {1, 2, 3};
    }

    constraint flag_con {
        flag > -4 && flag < 4;
        sub_flag inside {-15, -10, -5, 0, 10, 20, 25};
    }

    constraint if_else_con_1 {
        if(flag > 2) {
            iec_data1 inside {1, 2, 3} || iec_data1 % 2 == 0;
        } else {
            (iec_data1 & 8'hF0) == 8'hA0;
        }
    }
    
    constraint if_else_con_2 {
        if(flag > 2) {
            iec_data2 inside {1, 2, 3};
        } else if (flag > 0) {
            iec_data2 inside {4, 5};
        } else if (flag > -2) {
            iec_data2 inside {6, 7};
        } else {
            iec_data2 inside {8, 9};
        }
    }
    
    constraint if_else_con_3 {
        if (flag > 0) {
            if (sub_flag > 10) {
                iec_data3 inside {1, 2, 3} || iec_data3 % 2 == 0;
            } else if (sub_flag == 10) {
                iec_data3 inside {6, 7};
            } else {
                iec_data3 inside {4, 5};
            }
        } else if (flag == 0 || flag == -1) {
            if (sub_flag < -10) {
                iec_data3 inside {10, 11};
            } else {
                iec_data3 inside {12, 13};
            }
        } else {
            if (sub_flag > 20) {
                iec_data3 inside {14, 15};
            } else if (sub_flag == 20) {
                iec_data3 inside {16, 17};
            } else {
                iec_data3 inside {8, 9};
            }
        }
    }

    // Self-check function
    function void check_constraints();
        if (ic_data1 > 2 && !(ic_data2 inside {1, 2, 3})) begin
            $display("Error: ic_data1 = %0d, ic_data2 = %0d", ic_data1, ic_data2);
            $stop;
        end

        if (flag > 2) begin
            if (!(iec_data1 inside {1, 2, 3} || iec_data1 % 2 == 0)) begin
                $display("Error: flag = %0d, iec_data1 = %0d", flag, iec_data1);
                $stop;
            end
        end else if (!((iec_data1 & 8'hF0) == 8'hA0)) begin
            $display("Error: flag = %0d, iec_data1 = %0d", flag, iec_data1);
            $stop;
        end

        if (flag > 2) begin
            if (!(iec_data2 inside {1, 2, 3})) begin
                $display("Error: flag = %0d, iec_data2 = %0d", flag, iec_data2);
                $stop;
            end
        end else if (flag > 0) begin
            if (!(iec_data2 inside {4, 5})) begin
                $display("Error: flag = %0d, iec_data2 = %0d", flag, iec_data2);
                $stop;
            end
        end else if (flag > -2) begin
            if (!(iec_data2 inside {6, 7})) begin
                $display("Error: flag = %0d, iec_data2 = %0d", flag, iec_data2);
                $stop;
            end
        end else if (!(iec_data2 inside {8, 9})) begin
            $display("Error: flag = %0d, iec_data2 = %0d", flag, iec_data2);
            $stop;
        end

        if (flag > 0) begin
            if (sub_flag > 10) {
                if (!(iec_data3 inside {1, 2, 3} || iec_data3 % 2 == 0)) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end else if (sub_flag == 10) {
                if (!(iec_data3 inside {6, 7})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end else {
                if (!(iec_data3 inside {4, 5})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end
        end else if (flag == 0 || flag == -1) {
            if (sub_flag < -10) {
                if (!(iec_data3 inside {10, 11})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end else {
                if (!(iec_data3 inside {12, 13})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end
        end else {
            if (sub_flag > 20) {
                if (!(iec_data3 inside {14, 15})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end else if (sub_flag == 20) {
                if (!(iec_data3 inside {16, 17})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end else {
                if (!(iec_data3 inside {8, 9})) begin
                    $display("Error: flag = %0d, sub_flag = %0d, iec_data3 = %0d", flag, sub_flag, iec_data3);
                    $stop;
                end
            end
        end
        $display("All constraints validated successfully.");
    endfunction
endclass

module t_constraint_conditional;

    ConditionalConstraintClass w = new;
    int v;

    initial begin
        repeat(50) begin
            v = w.randomize(); 
            if (v != 1) $stop;

            // Test results
            w.check_constraints();

            $display("ic_data1(h) = %h", w.ic_data1);
            $display("ic_data2(h) = %h", w.ic_data2);
            $display("flag(d) = %d", w.flag);
            $display("sub_flag(d) = %d", w.sub_flag);
            $display("iec_data1(h) = %h", w.iec_data1);
            $display("iec_data2(d) = %d", w.iec_data2);
            $display("iec_data3(d) = %d", w.iec_data3);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
