// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

interface INTF();
    logic field1;
    logic field2;
endinterface

class IntfDriverClass;
    virtual INTF intf;

    function new(virtual INTF intf);
        this.intf = intf;
    endfunction

    task update_field1(input logic val);
        intf.field1 = val;
        intf.field2 = ~val;
    endtask
endclass

module idma_backend_top (
    output logic result,
    input logic update_val
);
    typedef struct packed {
        logic field1;
        logic x;
    } s1_t;

    typedef struct packed {
        logic field2;
        logic y;
    } s2_t;

    s1_t struct1;
    s2_t struct2;

    INTF intf();

    // Interface fields get value from struct1
    always_comb intf.field1 = struct1.field1;

    // struct2.field2 driven from interface
    always_comb struct2.field2 = intf.field2;

    // Simulate logic transfer inside DUT
    always_comb begin
        struct1.x = struct2.y;
        struct2.y = ~struct2.field2;  // For propagation logic
        struct1.field1 = update_val;  // Feed from top-level input
    end

    // Final result: expect field1 = 1, field2 = 0 → y = 1 → x = 1 → result = 1
    assign result = (struct1.field1 == 1 && struct1.x == 1);
endmodule

module t_interface_t2;
    logic result;
    logic update_val = 0;

    idma_backend_top u_top(.result(result), .update_val(update_val));

    IntfDriverClass drv;

    initial begin
        drv = new(u_top.intf);

        #1ns;
        drv.update_field1(1); // Interface-level update
        update_val = 1;

        #1ns;
        if (result !== 1'b1) begin
            $display("FAIL: result = %0b (expected 1)", result);
            $stop;
        end

        $display("PASS: result = %0b, struct updated and propagated.", result);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
