interface INTF();
    logic x;
    logic y;
endinterface

module t_interface_t3_simple();
    logic s1, src_val;
    logic s2;

    INTF vintf();

    assign vintf.x = s1;

    assign vintf.y = src_val;
    assign s2 = vintf.y;

    assign s1 = !s2;

    initial begin
        #1ns;
        src_val = 1; // Set src_val to 1 to trigger the interface
        #1ns;
        if(s1 !== 0 || s2 !== 1 || vintf.x !== 0 || vintf.y !== 1) begin
            $display("FAIL: s1 = %0b, s2 = %0b, x = %0b, y = %0b", s1, s2, vintf.x, vintf.y);
            $stop;
        end
        $display("PASS: s1 = %0b, s2 = %0b, x = %0b, y = %0b", s1, s2, vintf.x, vintf.y);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
