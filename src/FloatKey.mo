import Float "mo:core/Float";
import Int "mo:core/Int";
import Nat32 "mo:core/Nat32";

module {
  public class Decomposer(maxSignificantDigits : Nat) {
    let log10 = Float.log(10);
    let eps = 1e-10;

    let digits = Float.fromInt(maxSignificantDigits);
    assert maxSignificantDigits <= 15;

    /// Converts a price into a generic scientific notation format (coefficient and exponent)
    /// with a validation rule: the number must not exceed `maxSignificantDigits` significant digits.
    public func decompose(price : Float) : ?(Nat32, Int) {
      if (Float.isNaN(price) or price <= 0) return null;

      let (log, oneOrZero) = if (price >= 1) (log10 - eps, 1.0) else (log10 + eps, 0.0);

      let exp = Float.trunc(Float.log(price) / log) - digits + oneOrZero;
      let withDust = price / (10 ** exp);
      let rounded = Float.nearest(withDust);

      if (not Float.equal(withDust, rounded, eps)) return null;

      ?(Nat32.fromNat(Int.abs(Float.toInt(rounded))), Float.toInt(exp));
    };
  };

  public func sort<T>(self : [var T], key : (implicit : T -> Float)) {
    
  };
};
