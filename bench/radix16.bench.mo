import Bench "mo:bench";
import Radix "radix32.bench";

module {
  public func init() : Bench.Bench = Radix.initParams(23, 5, 16);
};
