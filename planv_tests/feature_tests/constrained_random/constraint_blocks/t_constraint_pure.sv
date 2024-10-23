// DESCRIPTION: PlanV Verilator Pure Constraint Inheritance Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
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
        x inside {2, 3, 4};
    }
    constraint derived_constraint {
        y inside {5, 6, 7};
    }
endclass

module t_constraint_pure;

    DerivedClass derived_obj;
    OverrideClass override_obj;

    initial begin
        derived_obj = new();
        if (!derived_obj.randomize()) $fatal("Randomization failed for DerivedClass");
        assert(derived_obj.x inside {1, 2, 3}) else $fatal("Base constraint failed in DerivedClass");
        assert(derived_obj.y inside {4, 5, 6}) else $fatal("Derived constraint failed in DerivedClass");

        override_obj = new();
        if (!override_obj.randomize()) $fatal("Randomization failed for OverrideClass");
        assert(override_obj.x inside {2, 3, 4}) else $fatal("Base constraint override failed in OverrideClass");
        assert(override_obj.y inside {5, 6, 7}) else $fatal("Final derived constraint failed in OverrideClass");

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
