import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import Nat8 "mo:core/Nat8";
import Array "mo:core/Array";
import VarArray "mo:core/VarArray";
import Option "mo:core/Option";
import Text "mo:core/Text";
import Prim "mo:prim";
import Sort "../src/Nat32Key";

module {
  func mergeSort<T>(array : [var T], key : T -> Nat32) {
    // Stable merge sort in a bottom-up iterative style. Same algorithm as the sort in Buffer.
    let size = array.size();
    if (size <= 1) return;

    var i = 0;
    while (i < size) {
      insertionSortSmall(array, array, key, i, Nat.min(8, size - i));
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

  let nat = Nat8.toNat;

  func mergeSort16<T>(buffer : [var T], key : T -> Nat32) {
    let size = Nat8.min(16, Nat8.fromIntWrap(buffer.size()));
    if (size <= 1) return;
    if (size <= 8) {
      insertionSortSmall(buffer, buffer, key, 0, nat(Nat8.min(8, size)));
      return;
    };
    let len1 = size / 2;
    let len2 = size -% len1;
    let dest = VarArray.repeat(buffer[0], nat(len1));
    insertionSortSmall(buffer, dest, key, 0, nat(len1));
    insertionSortSmall(buffer, buffer, key, nat(len1), nat(len2));
    var pos : Nat8 = 0;
    var i : Nat8 = 0; // in dest
    var j : Nat8 = len1; // in buffer
    var dest_i = dest[0]; // i
    var buffer_j = buffer[nat(len1)]; // j
    label L loop {
      if (key(dest_i) <= key(buffer_j)) {
        buffer[nat(pos)] := dest_i;
        i +%= 1;
        pos +%= 1;
        if (i == len1) {
          while (j < size) {
            buffer[nat(pos)] := buffer[nat(j)];
            j +%= 1;
            pos +%= 1;
          };
          break L;
        } else {
          dest_i := dest[nat(i)];
        };
      } else {
        buffer[nat(pos)] := buffer_j;
        j +%= 1;
        pos +%= 1;
        if (j == size) {
          while (i < len1) {
            buffer[nat(pos)] := dest[nat(i)];
            i +%= 1;
            pos +%= 1;
          };
          break L;
        } else {
          buffer_j := buffer[nat(j)];
        };
      };
    };
  };

  func insertionSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat, len : Nat) {
    let newFrom = Nat32.fromIntWrap(from);
    switch (len) {
      case (0) {};
      case (1) {
        let index0 = Nat32.toNat(newFrom);
        dest[index0] := buffer[index0];
      };
      case (2) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let t0 = buffer[index0];
        let t1 = buffer[index1];
        if (key(t1) < key(t0)) {
          dest[index0] := t1;
          dest[index1] := t0;
        } else {
          dest[index0] := t0;
          dest[index1] := t1;
        };
      };
      case (3) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        let t2 = buffer[index2];
        let k2 = key(t2);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };

        if (k2 < k1) {
          if (k2 < k0) {
            dest[index0] := t2;
            dest[index1] := t0;
            dest[index2] := t1;
          } else {
            dest[index0] := t0;
            dest[index1] := t2;
            dest[index2] := t1;
          };
        } else {
          dest[index0] := t0;
          dest[index1] := t1;
          dest[index2] := t2;
        };
      };
      case (4) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };

        var tv = t2;
        var kv = k2;
        if (kv < k1) {
          t2 := t1;
          k2 := k1;
          if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
            t1 := tv;
            k1 := kv;
          };
        };

        if (k3 < k2) {
          tv := t3;
          t3 := t2;
          if (k3 < k1) {
            t2 := t1;
            if (k3 < k0) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
      };
      case (5) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };
        var tv = t2;
        var kv = k2;
        if (kv < k1) {
          t2 := t1;
          k2 := k1;
          if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
            t1 := tv;
            k1 := kv;
          };
        };
        tv := t3;
        kv := k3;
        if (kv < k2) {
          t3 := t2;
          k3 := k2;
          if (kv < k1) {
            t2 := t1;
            k2 := k1;
            if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
              t1 := tv;
              k1 := kv;
            };
          } else { t2 := tv; k2 := kv };
        };
        tv := t4;
        kv := k4;
        if (kv < k3) {
          t4 := t3;
          if (kv < k2) {
            t3 := t2;
            if (kv < k1) {
              t2 := t1;
              if (kv < k0) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
      };
      case (6) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
        var k5 = key(t5);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };
        var tv = t2;
        var kv = k2;
        if (kv < k1) {
          t2 := t1;
          k2 := k1;
          if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
            t1 := tv;
            k1 := kv;
          };
        };
        tv := t3;
        kv := k3;
        if (kv < k2) {
          t3 := t2;
          k3 := k2;
          if (kv < k1) {
            t2 := t1;
            k2 := k1;
            if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
              t1 := tv;
              k1 := kv;
            };
          } else { t2 := tv; k2 := kv };
        };
        tv := t4;
        kv := k4;
        if (kv < k3) {
          t4 := t3;
          k4 := k3;
          if (kv < k2) {
            t3 := t2;
            k3 := k2;
            if (kv < k1) {
              t2 := t1;
              k2 := k1;
              if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                t1 := tv;
                k1 := kv;
              };
            } else { t2 := tv; k2 := kv };
          } else { t3 := tv; k3 := kv };
        };
        tv := t5;
        kv := k5;
        if (kv < k4) {
          t5 := t4;
          if (kv < k3) {
            t4 := t3;
            if (kv < k2) {
              t3 := t2;
              if (kv < k1) {
                t2 := t1;
                if (kv < k0) { t1 := t0; t0 := tv } else {
                  t1 := tv;
                };
              } else { t2 := tv };
            } else { t3 := tv };
          } else { t4 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
      };
      case (7) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        let index6 = Nat32.toNat(newFrom +% 6);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
        var k5 = key(t5);
        var t6 = buffer[index6];
        var k6 = key(t6);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };
        var tv = t2;
        var kv = k2;
        if (kv < k1) {
          t2 := t1;
          k2 := k1;
          if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
            t1 := tv;
            k1 := kv;
          };
        };
        tv := t3;
        kv := k3;
        if (kv < k2) {
          t3 := t2;
          k3 := k2;
          if (kv < k1) {
            t2 := t1;
            k2 := k1;
            if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
              t1 := tv;
              k1 := kv;
            };
          } else { t2 := tv; k2 := kv };
        };
        tv := t4;
        kv := k4;
        if (kv < k3) {
          t4 := t3;
          k4 := k3;
          if (kv < k2) {
            t3 := t2;
            k3 := k2;
            if (kv < k1) {
              t2 := t1;
              k2 := k1;
              if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                t1 := tv;
                k1 := kv;
              };
            } else { t2 := tv; k2 := kv };
          } else { t3 := tv; k3 := kv };
        };
        tv := t5;
        kv := k5;
        if (kv < k4) {
          t5 := t4;
          k5 := k4;
          if (kv < k3) {
            t4 := t3;
            k4 := k3;
            if (kv < k2) {
              t3 := t2;
              k3 := k2;
              if (kv < k1) {
                t2 := t1;
                k2 := k1;
                if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                  t1 := tv;
                  k1 := kv;
                };
              } else { t2 := tv; k2 := kv };
            } else { t3 := tv; k3 := kv };
          } else { t4 := tv; k4 := kv };
        };
        tv := t6;
        kv := k6;
        if (kv < k5) {
          t6 := t5;
          if (kv < k4) {
            t5 := t4;
            if (kv < k3) {
              t4 := t3;
              if (kv < k2) {
                t3 := t2;
                if (kv < k1) {
                  t2 := t1;
                  if (kv < k0) { t1 := t0; t0 := tv } else {
                    t1 := tv;
                  };
                } else { t2 := tv };
              } else { t3 := tv };
            } else { t4 := tv };
          } else { t5 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
        dest[index6] := t6;
      };
      case (8) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        let index6 = Nat32.toNat(newFrom +% 6);
        let index7 = Nat32.toNat(newFrom +% 7);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
        var k5 = key(t5);
        var t6 = buffer[index6];
        var k6 = key(t6);
        var t7 = buffer[index7];
        var k7 = key(t7);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };
        var tv = t2;
        var kv = k2;
        if (kv < k1) {
          t2 := t1;
          k2 := k1;
          if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
            t1 := tv;
            k1 := kv;
          };
        };
        tv := t3;
        kv := k3;
        if (kv < k2) {
          t3 := t2;
          k3 := k2;
          if (kv < k1) {
            t2 := t1;
            k2 := k1;
            if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
              t1 := tv;
              k1 := kv;
            };
          } else { t2 := tv; k2 := kv };
        };
        tv := t4;
        kv := k4;
        if (kv < k3) {
          t4 := t3;
          k4 := k3;
          if (kv < k2) {
            t3 := t2;
            k3 := k2;
            if (kv < k1) {
              t2 := t1;
              k2 := k1;
              if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                t1 := tv;
                k1 := kv;
              };
            } else { t2 := tv; k2 := kv };
          } else { t3 := tv; k3 := kv };
        };
        tv := t5;
        kv := k5;
        if (kv < k4) {
          t5 := t4;
          k5 := k4;
          if (kv < k3) {
            t4 := t3;
            k4 := k3;
            if (kv < k2) {
              t3 := t2;
              k3 := k2;
              if (kv < k1) {
                t2 := t1;
                k2 := k1;
                if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                  t1 := tv;
                  k1 := kv;
                };
              } else { t2 := tv; k2 := kv };
            } else { t3 := tv; k3 := kv };
          } else { t4 := tv; k4 := kv };
        };
        tv := t6;
        kv := k6;
        if (kv < k5) {
          t6 := t5;
          k6 := k5;
          if (kv < k4) {
            t5 := t4;
            k5 := k4;
            if (kv < k3) {
              t4 := t3;
              k4 := k3;
              if (kv < k2) {
                t3 := t2;
                k3 := k2;
                if (kv < k1) {
                  t2 := t1;
                  k2 := k1;
                  if (kv < k0) { t1 := t0; k1 := k0; t0 := tv; k0 := kv } else {
                    t1 := tv;
                    k1 := kv;
                  };
                } else { t2 := tv; k2 := kv };
              } else { t3 := tv; k3 := kv };
            } else { t4 := tv; k4 := kv };
          } else { t5 := tv; k5 := kv };
        };
        tv := t7;
        kv := k7;
        if (kv < k6) {
          t7 := t6;
          if (kv < k5) {
            t6 := t5;
            if (kv < k4) {
              t5 := t4;
              if (kv < k3) {
                t4 := t3;
                if (kv < k2) {
                  t3 := t2;
                  if (kv < k1) {
                    t2 := t1;
                    if (kv < k0) { t1 := t0; t0 := tv } else {
                      t1 := tv;
                    };
                  } else { t2 := tv };
                } else { t3 := tv };
              } else { t4 := tv };
            } else { t5 := tv };
          } else { t6 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
        dest[index6] := t6;
        dest[index7] := t7;
      };
      case (_) Prim.trap("Can never happen");
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
          case ("merge16") mergeSort16(arrays[1][ci], func i = i);
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
