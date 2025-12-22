import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import Option "mo:core/Option";
import Random "mo:core/Random";
import Text "mo:core/Text";
import VarArray "mo:core/VarArray";
import Prim "mo:prim";
import Bench "mo:bench";

import Radix "../src/private/radix";

module {
  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Shift");
    bench.description("Nat64 bit operations.");

    let rows = [
      "8",
      "9",
      "10",
      "11",
      "12",
      "13",
      "14",
      "15",
      "16",
    ];
    let cols = [
      "2",
      "3",
      "4",
      "5",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    let sourceArrays : [[Nat32]] = Array.tabulate(
      rows.size(),
      func(j) = Array.tabulate<Nat32>(
        2 ** Option.unwrap(Nat.fromText(rows[j])),
        func(i) = Nat64.toNat32(rng.nat64() % (2 ** 32)),
      ),
    );

    let routines : [() -> ()] = Array.tabulate<() -> ()>(
      rows.size() * cols.size(),
      func(i) {
        let row : Nat = i % rows.size();
        let col : Nat = i / rows.size();

        let varSource = Array.toVarArray<Nat32>(sourceArrays[row]);
        let steps = Nat32.fromIntWrap(Option.unwrap(Nat.fromText(cols[col])));
        let radixBits = (32 + steps - 1) / steps;
        func() = Radix.withStepsRadix<Nat32>(varSource, func i = i, 32, steps, radixBits);
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
