// DESCRIPTION: PlanV Verilator Pure Constraint Inheritance Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

virtual class BaseClass;
    rand int x;
    pure constraint base_constraint;
endclass

class DerivedClass extends BaseClass;
    rand int y;
    constraint base_constraint {
        x inside {1, 2, 3};
    }
    constraint derived_constraint {
        y inside {4, 5, 6};
    }
endclass

class OverrideClass extends DerivedClass;
    constraint base_constraint {
        x inside {11, 12, 13};
    }
    constraint derived_constraint {
        y inside {14, 15, 16};
    }
endclass

module t_constraint_pure;

    DerivedClass derived_obj;
    OverrideClass override_obj;

    initial begin
        derived_obj = new();
        override_obj = new();

        repeat(10) begin
            if (!derived_obj.randomize()) $fatal("Randomization failed for DerivedClass");
            assert(derived_obj.x inside {1, 2, 3}) else $fatal("Base constraint failed in DerivedClass");
            assert(derived_obj.y inside {4, 5, 6}) else $fatal("Derived constraint failed in DerivedClass");

            if (!override_obj.randomize()) $fatal("Randomization failed for OverrideClass");
            assert(override_obj.x inside {11, 12, 13}) else $fatal("Base constraint override failed in OverrideClass");
            assert(override_obj.y inside {14, 15, 16}) else $fatal("Final derived constraint failed in OverrideClass");
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
