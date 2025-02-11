class AssocArray;
    rand int str_index [string];
    rand int str_index_1 [string];

    constraint c1{ 
        foreach (str_index[i]) str_index[i] > 10;  // nodep->bitp() would be VARREF, instead of CVTPACKSTRING
    }
    constraint c2 {
        str_index_1["key1"] == 100;
        str_index_1["key2"] == 200;
    }
    
    function new();
        str_index = '{"one":0, "two":0, "three":0};
        str_index_1 = '{"key1":0, "key2":0};
    endfunction
endclass

module t_constraint_assoc_array_string_format;
    AssocArray assoc_arr;
    int success;
    initial begin
        assoc_arr = new();
        success = assoc_arr.randomize();
        if (success != 1) $stop;
        $display("[AssocArray] Randomization successful.");
        foreach (assoc_arr.str_index[i]) begin
            $display("  str_index[%s] = %0d", i, assoc_arr.str_index[i]);
        end
        foreach (assoc_arr.str_index_1[i]) begin
            $display("  str_index_1[%s] = %0d", i, assoc_arr.str_index_1[i]);
        end
    end
endmodule
