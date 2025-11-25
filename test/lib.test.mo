import RadixSort "../src";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";

func testRadixSort(n : Nat, mod : Nat32) {
  let A : Nat32 = 1664525;
  let C : Nat32 = 1013904223;

  var seed : Nat32 = 12345;

  var a = VarArray.tabulate<(Nat32, Nat)>(
    n,
    func(i) {
      seed := seed *% A +% C;
      (seed % mod, i);
    },
  );

  let b = VarArray.clone(a);

  RadixSort.sortInPlace<(Nat32, Nat)>(a, func(x, y) = x);
  VarArray.sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in Nat.range(0, n)) {
    if (a[i] != b[i]) {
      Runtime.trap("Mismatch in index = " # debug_show i);
    };
  };
};

let ns = [1, 2, 3, 4, 10, 100, 100, 100_000];
let mods : [Nat32] = [2 ** 30, 100];

for (n in ns.vals()) {
  for (mod in mods.vals()) {
    testRadixSort(n, mod);
  };
};

assert RadixSort.sort<Nat32>([3, 4, 5, 1, 2], func x = x) == [1, 2, 3, 4, 5];
