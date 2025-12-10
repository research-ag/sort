import Sort "../src/Nat32Key";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import Random "mo:core/Random";
import BucketSortInternal "../src/private/bucketSortInternal";

func testOnArray(array : [var (Nat32, Nat)], f : [var (Nat32, Nat)] -> ()) {
  let a = VarArray.clone(array);
  let b = VarArray.clone(array);

  f(a);
  VarArray.sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in a.keys()) {
    if (a[i] != b[i]) {
      Runtime.trap("Sorting failed " # debug_show a # " " # debug_show b);
    };
  };
};

func testSort(n : Nat, mod : Nat64, sort : ([var (Nat32, Nat)], Nat32) -> ()) {
  let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

  let a = VarArray.tabulate<(Nat32, Nat)>(n, func(i) = (Nat32.fromNat64(rng.nat64Range(0, mod)), i));
  var max : Nat32 = 0;
  for (x in a.vals()) max := Nat32.max(max, x.0);
  let b = VarArray.clone(a);

  sort(a, max);
  VarArray.sortInPlace(b, func(x, y) = Nat32.compare(x.0, y.0));

  for (i in Nat.range(0, n)) {
    if (a[i] != b[i]) {
      Runtime.trap("n = " # debug_show n # " mod = " # debug_show mod # " mismatch in index = " # debug_show i);
    };
  };
};

func tests() {
  let ns = [
    1,
    2,
    3,
    4,
    8,
    10,
    100,
    1000,
    10_000,
  ];

  let fs : [Nat32 -> Nat32] = [
    func n = 1,
    func n = 2,
  ];

  let mods : [Nat64] = [
    16,
    100,
    2 ** 32,
  ];

  for (f in fs.vals()) {
    for (mod in mods.vals()) {
      for (n in ns.vals()) if (n <= 1000) {
        testSort(n, mod, func(a, max) = BucketSortInternal.bucketSort(a, func(x, y) = x, ?max, f));
      };
    };
  };

  for (n in ns.vals()) {
    for (mod in mods.vals()) {
      testSort(n, mod, func(a, max) = Sort.radixSort(a, func(x, y) = x, ?max));
      testSort(n, mod, func(a, max) = Sort.bucketSort(a, func(x, y) = x, ?max));
    };
  };

  let arrays : [[var (Nat32, Nat)]] = [
    // empty
    [var],
    // all equal keys
    [var (5, 0), (5, 1), (5, 2)],
    // already ascending
    [var (1, 0), (2, 1), (3, 2), (4, 3)],
    // descending
    [var (4, 0), (3, 1), (2, 2), (1, 3)],
    // single element
    [var (7, 0)],
    // two elements, equal
    [var (2, 0), (2, 1)],
    // mixed with duplicates
    [var (2, 0), (1, 1), (2, 2), (1, 3)],
    // longer descending
    [var (6, 0), (5, 1), (4, 2), (3, 3), (2, 4), (1, 5)],
    // all identical keys
    [var (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)],
    // 8-element mixed
    [var (3, 0), (1, 1), (4, 2), (1, 3), (5, 4), (2, 5), (3, 6), (0, 7)],
  ];

  for (a in arrays.vals()) {
    testOnArray(a, func a = Sort.radixSort(a, func x = x.0, null));
    testOnArray(a, func a = Sort.bucketSort(a, func x = x.0, null));
  };
};

tests();
