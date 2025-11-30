import RadixSort "../src";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import Array "mo:core/Array";
import Debug "mo:core/Debug";

func testRadixSort(n : Nat, mod : Nat32) {
  let A : Nat32 = 1664525;
  let C : Nat32 = 1013904223;

  var seed : Nat32 = 12345;

  var a = VarArray.tabulate<(Nat32, Nat)>(
    n,
    func(i) {
      seed := seed *% A +% C;
      (seed, i);
    },
  );

  let b = VarArray.clone(a);

  RadixSort.bucketSort<(Nat32, Nat)>(a, func(x, y) = x);
  VarArray.sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in Nat.range(0, n)) {
    if (a[i] != b[i]) {

      // for (j in Nat.range(0, n)) {
      //   Debug.print(debug_show (Nat32.explode(a[j].0), Nat32.explode(b[j].0)));
      // };

      Runtime.trap("n = " # debug_show n # " mod = " # debug_show mod # " mismatch in index = " # debug_show i);
    };
  };
};

func testRadixSortArray(n : Nat, mod : Nat32) {
  let A : Nat32 = 1664525;
  let C : Nat32 = 1013904223;

  var seed : Nat32 = 12345;

  var a = Array.tabulate<(Nat32, Nat)>(
    n,
    func(i) {
      seed := seed *% A +% C;
      (seed % mod, i);
    },
  );

  assert RadixSort.radixSort16<(Nat32, Nat)>(a, func(x, y) = x) == Array.sort(a, func(x, y) = Nat32.compare(x.0, y.0));

  let b = Array.toVarArray<(Nat32, Nat)>(a);
  RadixSort.radixSort16InPlace<(Nat32, Nat)>(b, func(x, y) = x);
  assert Array.fromVarArray(b) == Array.sort(a, func(x, y) = Nat32.compare(x.0, y.0));
};

let ns = [
  1,
  2,
  3,
  4,
  8,
  10,
  100,
  1000,
  100_000,
];

let mods : [Nat32] = [
  100,
  2 ** 31,
];

for (n in ns.vals()) {
  for (mod in mods.vals()) {
    testRadixSort(n, mod);
  };
};

// assert RadixSort.sort<Nat32>([3, 4, 5, 1, 2], func x = x) == [1, 2, 3, 4, 5];
