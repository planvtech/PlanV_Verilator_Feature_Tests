interface INTF();
    logic field1;
    logic field2;
endinterface

class IntfDriverClass;
    virtual INTF intf;

    function new(virtual INTF intf);
        this.intf = intf;
    endfunction

    // Simulate update of field1 and observe effect through field2
    task update_field1(input logic val);
        intf.field1 = val;
        intf.field2 = ~val;  // Some dummy dependency
    endtask
endclass

module idma_backend_top (
    output logic result
);
    typedef struct packed {
        logic field1;
        logic x;
    } s1_t;

    typedef struct packed {
        logic field2;
        logic y;
    } s2_t;

    s1_t struct1 = '{1'b0, 1'b0};
    s2_t struct2 = '{1'b0, 1'b0};

    INTF intf();

    assign intf.field1    = struct1.field1;
    assign struct2.field2 = intf.field2;
    assign struct1.x      = struct2.y;

    // For demonstration: if field1=1, field2=0, then result = 1 if x=0
    assign result = (struct1.field1 == 1 && struct1.x == 0);
endmodule

module t_interface_t2;
    logic result;

    idma_backend_top u_top(.result(result));

    IntfDriverClass drv;

    initial begin
        drv = new(u_top.intf);

        #1ns;
        // Change field1 to 1 via interface
        drv.update_field1(1);

        #1ns;
        if (result !== 1'b1) begin
            $display("FAIL: Expected result=1, got result=%0b", result);
            $stop;
        end

        $display("PASS: result = %0b, struct values propagated correctly.", result);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
