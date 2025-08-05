module t_no_args;
    bit [7:0] addr;
    bit [15:0] data;
    bit [7:0] old_addr;
    bit [15:0] old_data;

    initial begin
        old_addr = addr;
        old_data = data;

        if (!std::randomize()) $stop;

        // check if values changed
        if (!(addr == old_addr && data == old_data)) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
