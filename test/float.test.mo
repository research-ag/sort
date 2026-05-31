import Debug "mo:core/Debug";
import FloatKey "../src/FloatKey";

func assertEqual(name : Text, actual : ?(Nat32, Int), expected : ?(Nat32, Int)) {
  switch (actual, expected) {
    case (null, null) Debug.print("✅ " # name # ": PASS (Both null)");
    case (?(a), ?(b)) {
      if (a.0 == b.0 and a.1 == b.1) {
        Debug.print("✅ " # name # ": PASS (" # debug_show (a) # ")");
      } else {
        Debug.print("❌ " # name # ": FAIL. Got " # debug_show (a) # ", Expected " # debug_show (b));
      };
    };
    case (_, _) Debug.print("❌ " # name # ": FAIL. Mismatch null vs value.");
  };
};

func test_suite(funcToTest : (Float) -> ?(Nat32, Int)) {
  assertEqual("Integer", funcToTest(12345.0), ?(12345, 0));
  assertEqual("Decimal", funcToTest(123.45), ?(12345, -2));
  assertEqual("One", funcToTest(1), ?(10_000, -4));
  assertEqual("Power of 10 max digits", funcToTest(0.1), ?(10_000, -5));
  assertEqual("Power of 10", funcToTest(100.0), ?(10000, -2));
  assertEqual("Max power of 10", funcToTest(10_000), ?(10_000, 0));
  assertEqual("Small < 1", funcToTest(0.012345), ?(12345, -6));
  assertEqual("Precision Overflow", funcToTest(12345.6), null);
  assertEqual("Small Overflow", funcToTest(0.0123456), null);
  assertEqual("Zero", funcToTest(0.0), null);
  assertEqual("Plus inf", funcToTest(1.0 / 0), null);
  assertEqual("Minus inf", funcToTest(-1.0 / 0), null);
  assertEqual("NaN", funcToTest(0.0 / 0), null);
};

let d = FloatKey.Decomposer(5);
test_suite(d.decompose);
