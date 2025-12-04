import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Option "mo:core/Option";
import Sort "../src";

module {
  func mergeSort<T>(array : [var T], key : T -> Nat32) {
    // Stable merge sort in a bottom-up iterative style. Same algorithm as the sort in Buffer.
    let size = array.size();
    if (size <= 1) {
      return;
    };
    let scratchSpace = VarArray.repeat<T>(array[0], size);

    var i = 0;
    while (i < size) {
      insertionSortSmall(array, array, key, i, Nat.min(8, size - i));
      i += 8;
    };

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

  func insertionSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat, len : Nat) {
    switch (len) {
      case (0) {};
      case (1) { dest[from] := buffer[from] };
      case (2) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
        };
        dest[from] := t0;
        dest[from + 1] := t1;
      };
      case (3) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);

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
          if (kv < k0) {
            t1 := t0;
            k1 := k0;
            t0 := tv;
            k0 := kv;
          } else {
            t1 := tv;
            k1 := kv;
          };
        };

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
      };
      case (4) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
      };
      case (5) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
        var k3 = key(t3);
        var t4 = buffer[from + 4];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
      };
      case (6) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
        var k3 = key(t3);
        var t4 = buffer[from + 4];
        var k4 = key(t4);
        var t5 = buffer[from + 5];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
      };
      case (7) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
        var k3 = key(t3);
        var t4 = buffer[from + 4];
        var k4 = key(t4);
        var t5 = buffer[from + 5];
        var k5 = key(t5);
        var t6 = buffer[from + 6];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
        dest[from + 6] := t6;
      };
      case (8) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
        var k3 = key(t3);
        var t4 = buffer[from + 4];
        var k4 = key(t4);
        var t5 = buffer[from + 5];
        var k5 = key(t5);
        var t6 = buffer[from + 6];
        var k6 = key(t6);
        var t7 = buffer[from + 7];
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
          k7 := k6;
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
          } else { t6 := tv; k6 := kv };
        };

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
        dest[from + 6] := t6;
        dest[from + 7] := t7;
      };
      case (_) {
        // treat any len > 8 as 8
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
        var k2 = key(t2);
        var t3 = buffer[from + 3];
        var k3 = key(t3);
        var t4 = buffer[from + 4];
        var k4 = key(t4);
        var t5 = buffer[from + 5];
        var k5 = key(t5);
        var t6 = buffer[from + 6];
        var k6 = key(t6);
        var t7 = buffer[from + 7];
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
          k7 := k6;
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
          } else { t6 := tv; k6 := kv };
        };

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
        dest[from + 6] := t6;
        dest[from + 7] := t7;
      };
    };
  };

  func sort<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, to : Nat32) {
    let n = to -% from;
    if (n <= 8) {
      insertionSortSmall(array, array, key, Nat32.toNat(from), Nat32.toNat(to - from));
      return;
    };

    let mid = from +% (n >> 1);

    sort(array, buffer, key, from, mid);
    sort(array, buffer, key, mid, to);

    var i = from;
    var j = mid;
    var k = from;
    while (i < mid and j < to) {
      let left = array[Nat32.toNat i];
      let right = array[Nat32.toNat j];
      buffer[Nat32.toNat k] := if (key(left) <= key(right)) {
        i +%= 1;
        left;
      } else {
        j +%= 1;
        right;
      };
      k +%= 1;
    };
    while (i < mid) {
      buffer[Nat32.toNat k] := array[Nat32.toNat i];
      i +%= 1;
      k +%= 1;
    };
    while (j < to) {
      buffer[Nat32.toNat k] := array[Nat32.toNat j];
      j +%= 1;
      k +%= 1;
    };

    var l = from;
    while (l < to) {
      let ll = Nat32.toNat l;
      array[ll] := buffer[ll];
      l +%= 1;
    };
  };

  public func init() : Bench.Bench {
    let bench = Bench.Bench();

    bench.name("Sort small");
    bench.description("Compare insertion sort and batcher sort");

    let rows = [
      "merge",
      "bucket",
    ];
    let cols = [
      "10",
      "20",
      "40",
      "80",
      "160",
      "320",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    bench.runner(
      func(row, col) {
        let n = Option.unwrap(Nat.fromText(col));
        let a : [var Nat32] = VarArray.tabulate<Nat32>(n, func(i) = Nat64.toNat32(rng.nat64() % (2 ** 32)));
        if (row == "merge") mergeSort(a, func i = i) else Sort.bucketSort(a, func i = i, null);
      }
    );

    bench;
  };
};
