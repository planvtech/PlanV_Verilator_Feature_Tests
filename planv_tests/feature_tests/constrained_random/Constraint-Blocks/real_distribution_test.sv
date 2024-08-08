class real_constraint_c; 
    const int ZSTATE = -100;
    const real VALUE_LOW = 0.70;
    const real VALUE_MIN = 1.43;
    const real VALUE_NOM = 3.30;
    const real VALUE_MAX = 3.65;
    rand real a;
    rand real b;

    constraint a_constraint {
        a dist {
            ZSTATE := 5,
            [VALUE_LOW:VALUE_MIN] :/ 1,
            [VALUE_NOM +%- 1.0] :/ 13, // equivalent to 3.3 +/- 0.033
            [VALUE_MIN:VALUE_MAX] :/ 1
        };
    }

    constraint b_constraint {
        (a inside [VALUE_LOW:VALUE_MIN]) -> b == ZSTATE;
        b dist {
            ZSTATE := 1,
            [VALUE_MIN:VALUE_MAX] :/ 20
        };
        solve a before b;
    }
endclass

module real_distribution_test;

    real_constraint_c rc = new();
    int a_dist[4] = '{0, 0, 0, 0}; // Counters for ZSTATE, VALUE_LOW-1.43, VALUE_NOM +/- 0.033, 1.43-3.65
    int b_dist[2] = '{0, 0}; // Counters for ZSTATE, 1.43-3.65

    initial begin
        repeat (100) begin
            if (!rc.randomize()) $fatal("Randomization failed.");

            if (rc.a == rc.ZSTATE) a_dist[0]++;
            else if (rc.a >= rc.VALUE_LOW && rc.a <= rc.VALUE_MIN) a_dist[1]++;
            else if (rc.a >= (rc.VALUE_NOM - 0.033) && rc.a <= (rc.VALUE_NOM + 0.033)) a_dist[2]++;
            else if (rc.a >= rc.VALUE_MIN && rc.a <= rc.VALUE_MAX) a_dist[3]++;
            else $fatal("Value out of expected range: %f", rc.a);

            if (rc.a >= rc.VALUE_LOW && rc.a <= rc.VALUE_MIN) begin
                if (rc.b != rc.ZSTATE) $fatal("Constraint violated: b = %f, expected ZSTATE", rc.b);
            end else begin
                if (rc.b == rc.ZSTATE) b_dist[0]++;
                else if (rc.b >= rc.VALUE_MIN && rc.b <= rc.VALUE_MAX) b_dist[1]++;
                else $fatal("Value out of expected range: %f", rc.b);
            end
        end

        $display("a distribution: ZSTATE = %0d, [VALUE_LOW:VALUE_MIN] = %0d, [VALUE_NOM+/-0.033] = %0d, [VALUE_MIN:VALUE_MAX] = %0d", 
                 a_dist[0], a_dist[1], a_dist[2], a_dist[3]);
        $display("b distribution: ZSTATE = %0d, [VALUE_MIN:VALUE_MAX] = %0d", b_dist[0], b_dist[1]);

        $finish;
    end
endmodule
