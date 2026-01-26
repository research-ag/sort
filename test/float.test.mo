import Float "mo:base/Float";
import Int "mo:base/Int";
import Nat32 "mo:base/Nat32";
import Debug "mo:base/Debug";

let maxSignificantDigits = 5;

// ---------------------------------------------------------
// 1. ORIGINAL FUNCTION (The "Two-Branch" Approach)
// ---------------------------------------------------------
func decompose_Original(price : Float) : ?(Nat32, Int) {
  if (price >= 1) {
    let e1 = Float.log(price) / 2.302_585_092_994_045;
    let e = Float.trunc(e1);
    let exp = e + 1 - Float.fromInt(maxSignificantDigits);
    let m = 10 ** exp;
    let n = price / m;
    let r = Float.nearest(n);
    if (Float.equalWithin(n, r, 1e-10)) {
      ?(Nat32.fromNat(Int.abs(Float.toInt(r))), Float.toInt(exp));
    } else { null };
  } else {
    let e1 = Float.log(price) / 2.302_585_092_994_047;
    let e = Float.trunc(e1);
    let exp = Float.fromInt(maxSignificantDigits) - e;
    let m = 10 ** exp;
    let n = price * m;
    let r = Float.nearest(n);
    if (Float.equalWithin(n, r, 1e-10)) {
      ?(Nat32.fromNat(Int.abs(Float.toInt(r))), Float.toInt(-exp));
    } else { null };
  };
};

// ---------------------------------------------------------
// 2. IMPROVED FUNCTION (The "One-Branch" Approach)
// ---------------------------------------------------------
func decompose_Improved(price : Float) : ?(Nat32, Int) {
  if (price == 0) return ?(0, 0);

  // Uses abs() to handle potential negative prices safely
  let logPrice = Float.log(Float.abs(price)) / 2.302_585_092_994_045;

  // Uses floor() to handle positive/negative magnitudes consistently
  let magnitude = Float.floor(logPrice);

  // Calculate shift
  let shift = Float.fromInt(maxSignificantDigits - 1) - magnitude;

  let scale = 10 ** shift;
  let n = price * scale;
  let r = Float.nearest(n);

  if (Float.equalWithin(n, r, 1e-10)) {
    // Invert shift for the return exponent
    ?(Nat32.fromNat(Int.abs(Float.toInt(r))), Float.toInt(shift * -1));
  } else {
    null;
  };
};

// ---------------------------------------------------------
// TEST HARNESS
// ---------------------------------------------------------

func assertEqual(name : Text, actual : ?(Nat32, Int), expected : ?(Nat32, Int)) {
  switch (actual, expected) {
    case (null, null) { Debug.print("✅ " # name # ": PASS (Both null)") };
    case (?(a), ?(b)) {
      if (a.0 == b.0 and a.1 == b.1) {
        Debug.print("✅ " # name # ": PASS (" # debug_show (a) # ")");
      } else {
        Debug.print("❌ " # name # ": FAIL. Got " # debug_show (a) # ", Expected " # debug_show (b));
      };
    };
    case (_, _) {
      Debug.print("❌ " # name # ": FAIL. Mismatch null vs value.");
    };
  };
};

func test_suite(funcToTest : (Float) -> ?(Nat32, Int)) {
  // 1. Standard Case: Large number, exact digits
  assertEqual("Integer", funcToTest(12345.0), ?(12345, 0));

  // 2. Standard Case: Decimal
  // 123.45 -> 12345 * 10^-2
  assertEqual("Decimal", funcToTest(123.45), ?(12345, -2));

  // 3. Small Number ( < 1 )
  // 0.012345 -> 12345 * 10^-6
  assertEqual("Small < 1", funcToTest(0.012345), ?(12345, -6));

  // 4. Too much precision (Should be null)
  // 12345.6 requires 6 digits
  assertEqual("Precision Overflow", funcToTest(12345.6), null);

  // 5. Very small overflow
  // 0.0123456 requires 6 digits
  assertEqual("Small Overflow", funcToTest(0.0123456), null);

  // 6. Zero
  assertEqual("Zero", funcToTest(0.0), ?(0, 0));

  // 7. Power of 10
  // 100.0 can be represented as 10000 * 10^-2 OR 1 * 10^2 depending on logic.
  // However, this algorithm attempts to maximize significant digits up to 5.
  // Let's see how it behaves. Usually it normalizes to 10000.
  // 100.0 (log 2) -> exp shift to hit 5 digits is (10000, -2)
  assertEqual("Power of 10", funcToTest(100.0), ?(10000, -2));
};

Debug.print("--- Testing Original Function ---");
test_suite(decompose_Original);

Debug.print("\n--- Testing Improved Function ---");
test_suite(decompose_Improved);
