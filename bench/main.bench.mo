import Bench "mo:bench";
import Array "mo:core/Array";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import Text "mo:core/Text";
import Prim "mo:prim";
import Sort "../src";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Shift");
    bench.description("Nat64 bit operations.");

    let rows = [
      "sort",
      "radixSort16",
    ];
    let cols = [
      "1000",
      "10000",
      "100000",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    let sourceArrays : [[Nat32]] = Array.tabulate(
      3,
      func(j) = Array.tabulate<Nat32>(
        [1000, 10000, 100000][j],
        func(i) = Nat32.fromIntWrap(Nat64.toNat(rng.nat64() % 1000000)),
      ),
    );

    let routines : [() -> ()] = Array.tabulate<() -> ()>(
      rows.size() * cols.size(),
      func(i) {
        let row : Nat = i % rows.size();
        let col : Nat = i / rows.size();

        switch (row) {
          case (0) {
            func() = ignore Sort.sort<Nat32>(sourceArrays[col], func i = i);
          };
          case (1) {
            func() = ignore Sort.radixSort16<Nat32>(sourceArrays[col], func i = i);
          };
          case (_) Prim.trap("Row not implemented");
        };
      },
    );

    bench.runner(
      func(row, col) {
        let ?ri = Array.indexOf<Text>(rows, Text.equal, row) else Prim.trap("Unknown row");
        let ?ci = Array.indexOf<Text>(cols, Text.equal, col) else Prim.trap("Unknown column");
        routines[ci * rows.size() + ri]();
      }
    );

    bench;
  };
};
