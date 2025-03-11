interface my_if;
    import my_pkg::*;
    int c;
    cl_a a_inst;
    
    function automatic int use_add(int x, int y);
        return a_inst.add(x, y);
    endfunction

    initial begin
        c = 5;
    end
endinterface
