import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import Array "mo:core/Array";
import VarArray "mo:core/VarArray";
import Option "mo:core/Option";
import Text "mo:core/Text";
import Prim "mo:prim";
import Sort "../src/Nat32Key";
import { mergeSort; mergeSort16 } "../src/private/merge";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Different sorts");
    bench.description("Compare diffrent sort algorithms");

    let rows = [
      "merge",
      "merge16",
      "bucket",
      "radix",
      "var-array",
    ];
    let cols = [
      "8",
      "12",
      "16",
      "40",
      "80",
      "160",
      "320",
      "640",
      "1280",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);
    let arrays : [[[[var Nat32]]]] = Array.tabulate(
      rows.size(),
      func _ = Array.tabulate(
        cols.size(),
        func i {
          let n = Option.unwrap(Nat.fromText(cols[i]));
          Array.tabulate(
            100,
            func _ = VarArray.tabulate<Nat32>(
              n,
              func _ = Nat64.toNat32(rng.nat64() >> 32),
            ),
          );
        },
      ),
    );

    bench.runner(
      func(row, col) {
        let ?ci = Array.indexOf<Text>(cols, Text.equal, col) else Prim.trap("Unknown column");
        let buffer = VarArray.repeat<Nat32>(0, 16);
        switch (row) {
          case ("merge") for (a in arrays[0][ci].vals()) mergeSort(a, func i = i);
          case ("merge16") {
            let input = arrays[1][ci]; 
            let n = input[0].size();
            if (8 < n and n <= 16) { 
              for (a in input.vals())
              mergeSort16<Nat32>(
                a,
                buffer,
                func i = i,
                0 : Nat32,
                Nat32.fromNat(n),
              );
            };
          };
//          case ("merge16") for (a in arrays[1][ci].vals()) mergeSort16(a, func i = i);
          case ("bucket") for (a in arrays[2][ci].vals()) Sort.bucketSort(a, func i = i, null);
          case ("radix") for (a in arrays[3][ci].vals()) Sort.radixSort(a, func i = i, null);
          case ("var-array") for (a in arrays[4][ci].vals()) VarArray.sortInPlace(a, Nat32.compare);
          case (_) Prim.trap("Unknown row");
        };
      }
    );

    bench;
  };
};
