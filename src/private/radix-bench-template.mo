import Array "mo:core/Array";
import Nat "mo:core/Nat";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import Option "mo:core/Option";
import Random "mo:core/Random";
import Text "mo:core/Text";
import Prim "mo:prim";
import Bench "mo:bench";

import Radix "radix";

module {
  public func init(rowsCount : Nat, colsCount : Nat, bits : Nat32) : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Radix sort");
    bench.description("bits = " # debug_show bits);

    let rows = Array.tabulate(
      rowsCount,
      func i {
        let j = i / 2;
        let k = i % 2;
        var n = 2 ** (8 + j) + k * (2 ** (7 + j));
        Nat.toText(n);
      },
    );
    let cols = Array.tabulate<Text>(colsCount, func i = Nat.toText(i + 1));

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    let sourceArrays : [[Nat32]] = Array.tabulate(
      rows.size(),
      func(j) = Array.tabulate<Nat32>(
        Option.unwrap(Nat.fromText(rows[j])),
        func(i) = Nat64.toNat32(rng.nat64() % (2 ** Nat32.toNat64(bits))),
      ),
    );

    let routines : [() -> ()] = Array.tabulate<() -> ()>(
      rows.size() * cols.size(),
      func(i) {
        let row : Nat = i % rows.size();
        let col : Nat = i / rows.size();

        let varSource = Array.toVarArray<Nat32>(sourceArrays[row]);
        let steps = Nat32.fromIntWrap(Option.unwrap(Nat.fromText(cols[col])));
        let radixBits = (bits + steps - 1) / steps;
        func() = Radix.withStepsRadix<Nat32>(varSource, func i = i, bits, steps, radixBits);
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
