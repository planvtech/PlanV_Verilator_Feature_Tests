class cl_a;
    virtual my_if my_if_inst;
    int c;
    function new();
        c = my_if_inst.c;
    endfunction
    
    function automatic int add(int a, int b);
        return (a + b + c);
    endfunction
endclass
