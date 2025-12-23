import Bench "mo:bench";
import Radix "../src/private/radix-bench-template";

module {
  public func init() : Bench.Bench = Radix.init(23, 5, 16);
};
