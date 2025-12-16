import Bench "mo:bench";
import Array "mo:core/Array";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import Text "mo:core/Text";
import VarArray "mo:core/VarArray";
import Prim "mo:prim";
import Sort "../src/Nat32Key";
import Zhus "mo:zhus/sort";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Shift");
    bench.description("Nat64 bit operations.");

    let rows = [
      "bucketSort",
      "bucketSortWorstCase",
      "radixSort",
      "Zhus",
      "mergeSort",
      "VarArray"
    ];
    let cols = [
      "100",
      "1000",
      "10000",
      "12000",
      "100000",
      "1000000",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    let sourceArrays : [[Nat32]] = Array.tabulate(
      6,
      func(j) = Array.tabulate<Nat32>(
        [100, 1_000, 10_000, 12_000, 100_000, 1_000_000][j],
        func(i) = Nat64.toNat32(rng.nat64() % (2 ** 32)),
      ),
    );

    let routines : [() -> ()] = Array.tabulate<() -> ()>(
      rows.size() * cols.size(),
      func(i) {
        let row : Nat = i % rows.size();
        let col : Nat = i / rows.size();

        switch (row) {
          case (0) {
            let varSource = Array.toVarArray<Nat32>(sourceArrays[col]);
            func() = Sort.bucketSort<Nat32>(varSource, func i = i, null);
          };
          case (1) {
            let varSource = VarArray.repeat<Nat32>(0, sourceArrays[col].size());
            func() = Sort.bucketSort<Nat32>(varSource, func i = i, null);
          };
          case (2) {
            let varSource = Array.toVarArray<Nat32>(sourceArrays[col]);
            func() = Sort.radixSort<Nat32>(varSource, func i = i, null);
          };
          case (3) {
            let varSource = Array.toVarArray<Nat32>(sourceArrays[col]);
            func() = Zhus.sortNat32<Nat32>(varSource, func i = i);
          };
          case (4) {
            let varSource = Array.toVarArray<Nat32>(sourceArrays[col]);
            func() = Sort.mergeSort<Nat32>(varSource, func i = i);
          };
          case (5) {
            let varSource = Array.toVarArray<Nat32>(sourceArrays[col]);
            func() = VarArray.sortInPlace<Nat32>(varSource, Nat32.compare);
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
