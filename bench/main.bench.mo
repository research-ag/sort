import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import Option "mo:core/Option";
import Random "mo:core/Random";
import VarArray "mo:core/VarArray";
import Prim "mo:prim";
import Bench "mo:bench-helper";
import Zhus "mo:zhus/sort";

import Sort "../src/Nat32Key";

module {
  public func init() : Bench.V1 {
    let schema : Bench.Schema = {
      name = "Main";
      description = "All the algorithms";
      rows = [
        "bucketSort",
        "bucketSortWorstCase",
        "radixSort",
        "Zhus",
        "mergeSort",
        "VarArray",
      ];
      cols = [
        "100",
        "1000",
        "10000",
        "12000",
        "100000",
        "1000000",
      ];
    };

    // Precompute one random `[Nat32]` per column size, used by every row
    // except `bucketSortWorstCase` which sorts an all-zero array.
    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);
    let sourceArrays : [[Nat32]] = Array.tabulate(
      schema.cols.size(),
      func(ci) = Array.tabulate<Nat32>(
        Option.unwrap(Nat.fromText(schema.cols[ci])),
        func(_) = Nat64.toNat32(rng.nat64() % (2 ** 32)),
      ),
    );

    // routines[ri][ci] : a captured closure that performs exactly one sort.
    // Each closure has its own mutable copy of the input so the surrounding
    // benchmark runner can call it without worrying about cross-cell aliasing.
    let routines : [[() -> ()]] = Array.tabulate<[() -> ()]>(
      schema.rows.size(),
      func(ri) = Array.tabulate<() -> ()>(
        schema.cols.size(),
        func(ci) {
          switch (ri) {
            case (0) {
              let varSource = Array.toVarArray<Nat32>(sourceArrays[ci]);
              func() = Sort.bucketSort<Nat32>(varSource, func i = i, #default);
            };
            case (1) {
              let varSource = VarArray.repeat<Nat32>(0, sourceArrays[ci].size());
              func() = Sort.bucketSort<Nat32>(varSource, func i = i, #default);
            };
            case (2) {
              let varSource = Array.toVarArray<Nat32>(sourceArrays[ci]);
              func() = Sort.radixSort<Nat32>(varSource, func i = i, #default);
            };
            case (3) {
              let varSource = Array.toVarArray<Nat32>(sourceArrays[ci]);
              func() = Zhus.sortNat32<Nat32>(varSource, func i = i);
            };
            case (4) {
              let varSource = Array.toVarArray<Nat32>(sourceArrays[ci]);
              func() = Sort.mergeSort<Nat32>(varSource, func i = i);
            };
            case (5) {
              let varSource = Array.toVarArray<Nat32>(sourceArrays[ci]);
              func() = VarArray.sortInPlace<Nat32>(varSource, Nat32.compare);
            };
            case (_) Prim.trap("Row not implemented");
          };
        },
      ),
    );

    Bench.V1(schema, func(ri : Nat, ci : Nat) = routines[ri][ci]());
  };
};
