class constrained_unpacked_array;

rand int unpacked_array_1 [2][3];

rand int unpacked_array [1][2][3][1][3];

rand int unpacked_array_2 [2][2];

rand int arr_idx;

rand int arr_idx_1;

rand int arr_idx_2;

rand int m_intQueue[$];

rand int m_idx;

function new;

m_intQueue = '{6{0}};

foreach (unpacked_array[i, j, k, m, n]) unpacked_array[i][j][k][m][n] = 0;

foreach (unpacked_array_1[i, j]) unpacked_array_1[i][j] = 0;

foreach (unpacked_array_2[i, j]) unpacked_array_2[i][j] = 0;

endfunction

constraint int_queue_c {

m_idx inside {[0:5]};

m_intQueue[m_idx] == m_idx + 1;

foreach (m_intQueue[i]) {

m_intQueue[i] inside {[0:127]};

}

}

constraint unpacked_array_constraints {

arr_idx inside {[0:1]};

unpacked_array[0][0][arr_idx][0][arr_idx] == arr_idx + arr_idx;

foreach (unpacked_array[i, j, k, m, n]) {

unpacked_array[i][j][k][m][n] inside {[0:127]};

}

}

constraint unpacked_array_1_constraints {

arr_idx_1 inside {[0:6]};
unpacked_array_1[0][0] == arr_idx_1;
unpacked_array_1[0][1] == 7;
unpacked_array_1[1][1] == 8;

}

constraint unpacked_array_2_constraints {
arr_idx_2 inside {[0:6]};
foreach (unpacked_array_2[i, j]) {
  unpacked_array_2[i][j] == arr_idx_2;
}
}

endclass

module unpacked_array_constrained_test_simple;

constrained_unpacked_array my_array;

initial begin

my_array = new();

// Randomization of the unpacked array without constraints

if (!my_array.randomize()) begin

$display("Unpacked array randomization failed.");

$stop;

end

// Displaying the values after randomization

$display("Unpacked array values:");

foreach (my_array.unpacked_array[i, j, k, m, n]) begin

  $display("unpacked_array[%0d][%0d][%0d][%0d][%0d] = %0d", i, j, k, m, n, my_array.unpacked_array[i][j][k][m][n]);

end

$display("Array Index: %0d", my_array.arr_idx);

foreach (my_array.unpacked_array_1[i, j]) begin

$display("unpacked_array_1[%0d][%0d] = %0d", i, j, my_array.unpacked_array_1[i][j]);

end

$display("Array Index_1: %0d", my_array.arr_idx_1);

foreach (my_array.unpacked_array_2[i, j]) begin

$display("unpacked_array_2[%0d][%0d] = %0d", i, j, my_array.unpacked_array_2[i][j]);

end

$display("Array Index_2: %0d", my_array.arr_idx_2);

$display("Queue values (m_intQueue):");
  foreach (my_array.m_intQueue[i]) begin
    $display("m_intQueue[%0d] = %0d", i, my_array.m_intQueue[i]);
  end

$display("Queue Index: %0d", my_array.m_idx);

$finish;

end

endmodule