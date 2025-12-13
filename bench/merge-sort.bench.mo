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
import BucketSortInternal "../src/private/bucketSortInternal";

module {
  func mergeSort<T>(array : [var T], key : T -> Nat32) {
    // Stable merge sort in a bottom-up iterative style. Same algorithm as the sort in Buffer.
    let size = array.size();
    if (size <= 1) return;

    var i = 0;
    while (i < size) {
      BucketSortInternal.insertionSortSmall(array, array, key, Nat32.fromNat(i), Nat32.fromNat(Nat.min(8, size - i)));
      i += 8;
    };
    if (i <= 8) return;

    let scratchSpace = VarArray.repeat<T>(array[0], size);

    var currSize = 8; // current size of the subarrays being merged
    var oddIteration = false;

    // when the current size == size, the array has been merged into a single sorted array
    while (currSize < size) {
      let (fromArray, toArray) = if (oddIteration) (scratchSpace, array) else (array, scratchSpace);
      var leftStart = 0; // selects the current left subarray being merged

      while (leftStart < size) {
        let mid = if (leftStart + currSize < size) leftStart + currSize else size;
        let rightEnd = if (leftStart + 2 * currSize < size) leftStart + 2 * currSize else size;

        // merge [leftStart, mid) with [mid, rightEnd)
        var left = leftStart;
        var right = mid;
        var nextSorted = leftStart;
        while (left < mid and right < rightEnd) {
          let leftElement = fromArray[left];
          let rightElement = fromArray[right];
          toArray[nextSorted] := if (key(leftElement) <= key(rightElement)) {
            left += 1;
            leftElement;
          } else {
            right += 1;
            rightElement;
          };
          nextSorted += 1;
        };
        while (left < mid) {
          toArray[nextSorted] := fromArray[left];
          nextSorted += 1;
          left += 1;
        };
        while (right < rightEnd) {
          toArray[nextSorted] := fromArray[right];
          nextSorted += 1;
          right += 1;
        };

        leftStart += 2 * currSize;
      };

      currSize *= 2;
      oddIteration := not oddIteration;
    };
    if (oddIteration) {
      var i = 0;
      while (i < size) {
        array[i] := scratchSpace[i];
        i += 1;
      };
    };
  };

  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Sort small");
    bench.description("Compare insertion sort and batcher sort");

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
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);
    let arrays : [[[var Nat32]]] = Array.tabulate(
      rows.size(),
      func(_) = Array.tabulate(
        cols.size(),
        func(i) {
          let n = Option.unwrap(Nat.fromText(cols[i]));
          VarArray.tabulate<Nat32>(
            n,
            func(_) = Nat64.toNat32(rng.nat64() >> 32),
          );
        },
      ),
    );

    bench.runner(
      func(row, col) {
        let ?ci = Array.indexOf<Text>(cols, Text.equal, col) else Prim.trap("Unknown column");
        switch (row) {
          case ("merge") mergeSort(arrays[0][ci], func i = i);
          case ("merge16") {
            let n = arrays[1][ci].size();
            if (8 < n and n <= 16) {
              let buffer = VarArray.repeat<Nat32>(0, n);
              BucketSortInternal.mergeSort16<Nat32>(
                arrays[1][ci],
                buffer,
                func i = i,
                0 : Nat32,
                Nat32.fromNat(arrays[1][ci].size()),
              );
            };
          };
          case ("bucket") Sort.bucketSort(arrays[2][ci], func i = i, null);
          case ("radix") Sort.radixSort(arrays[3][ci], func i = i, null);
          case ("var-array") VarArray.sortInPlace(arrays[4][ci], Nat32.compare);
          case (_) Prim.trap("Unknown row");
        };
      }
    );

    bench;
  };
};
