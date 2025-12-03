import RadixSort "../src";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Runtime "mo:core/Runtime";
import VarArray "mo:core/VarArray";
import Array "mo:core/Array";

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

  RadixSort.bucketSort<(Nat32, Nat)>(a, func(x, y) = x, null);
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
  10_000
];

let mods : [Nat32] = [
  16,
  100,
  2 ** 31,
];

for (n in ns.vals()) {
  for (mod in mods.vals()) {
    testRadixSort(n, mod);
  };
};

// func testSmall(n : Nat) {
//   func next_permutation(p : [var Nat32]) : Bool {
//     let n = p.size();

//     func swap(i : Nat, j : Nat) {
//       let x = p[i];
//       p[i] := p[j];
//       p[j] := x;
//     };

//     func reverse(from : Nat, to : Nat) {
//       var a = from;
//       var b = to;
//       while (a < b) {
//         swap(a, b);
//         a += 1;
//         b -= 1;
//       };
//     };

//     var point : ?Nat = null;
//     var i : Int = n - 2;
//     label l while (i >= 0) {
//       if (p[Int.abs(i)] < p[Int.abs(i + 1)]) {
//         point := ?Int.abs(i);
//         break l;
//       };
//       i -= 1;
//     };
//     switch (point) {
//       case (null) {
//         return false;
//       };
//       case (?x) {
//         var i : Int = n - 1;
//         label l while (i > x) {
//           if (p[Int.abs(i)] > p[x]) {
//             break l;
//           };
//           i -= 1;
//         };
//         swap(Int.abs(i), x);
//         reverse(x + 1, n - 1);
//       };
//     };
//     true;
//   };


//   let p = VarArray.tabulate<Nat32>(n, func i = Nat32.fromNat(i));
//   loop {
//     let pp = VarArray.clone(p);
//     RadixSort.sortSmallUnstable(pp, 0 : Nat32, Nat32.fromNat(n), func x = x);
//     if (Array.fromVarArray<Nat32>(pp) != Array.tabulate<Nat32>(n, func i = Nat32.fromNat(i))) {
//       Runtime.trap(debug_show pp);
//     };
//   } while (next_permutation(p));
// };

// for (n in Nat.range(2, 8)) {
//   testSmall(n);
// };
