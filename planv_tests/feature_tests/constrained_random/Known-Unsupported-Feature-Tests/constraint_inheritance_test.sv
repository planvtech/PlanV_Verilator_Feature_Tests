/*
    Known Unsupported Feature Tests due to the lack of support for "pure constraint"
*/

// Define an abstract base class with a pure constraint
virtual class BaseClass;
    rand int x;
    pure constraint base_constraint;
endclass

// Define a derived class that implements the pure constraint
class DerivedClass extends BaseClass;
    rand int y;
    constraint base_constraint {
        x inside {1, 2, 3};
    }
    constraint derived_constraint {
        y inside {4, 5, 6};
    }
endclass

// Define another class to test overriding constraints with extends
class OverrideClass extends DerivedClass;
    constraint base_constraint extends {
        x inside {2, 3, 4};
    }
    final constraint derived_constraint {
        y inside {5, 6, 7};
    }
endclass

// Testbench to verify constraint inheritance and overriding
module constraint_inheritance_test;

    BaseClass base_obj;
    DerivedClass derived_obj;
    OverrideClass override_obj;

    initial begin
        // Test derived class inheriting from base class
        derived_obj = new();
        if (!derived_obj.randomize()) $fatal("Randomization failed for DerivedClass");
        assert(derived_obj.x inside {1, 2, 3}) else $fatal("Base constraint failed in DerivedClass");
        assert(derived_obj.y inside {4, 5, 6}) else $fatal("Derived constraint failed in DerivedClass");

        // Test overriding constraints in OverrideClass
        override_obj = new();
        if (!override_obj.randomize()) $fatal("Randomization failed for OverrideClass");
        assert(override_obj.x inside {2, 3, 4}) else $fatal("Base constraint override failed in OverrideClass");
        assert(override_obj.y inside {5, 6, 7}) else $fatal("Final derived constraint failed in OverrideClass");

        $display("All constraints passed.");
        $finish;
    end
endmodule
