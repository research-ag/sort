import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import { insertionSortSmall } "./insertion";
import { mergeSort16 } "./merge16";
import { copy } "./utils";

module {
  let nat = Nat32.toNat;

  // should be 1 <= radixBits n <= 31 for all n
  public func bucketSort<T>(array : [var T], key : T -> Nat32, maxInclusive : ?Nat32, radixBits : Nat32 -> Nat32) {
    let n = Nat32.fromNat(array.size());

    // n <= 1 is already sorted
    if (n <= 1) return;

    // sort n <= 8 with insertion sort
    if (n <= 8) {
      insertionSortSmall(array, array, key, 0 : Nat32, n);
      return;
    };

    // sort 8 < n <= 16 with merge sort
    let buffer = VarArray.repeat(array[0], nat(n));
    if (n <= 16) {
      mergeSort16(array, buffer, key, 0 : Nat32, n, false);
      // TODO: with a different mergeSort16 the buffer could be smaller here
      return;
    };

    // sort n > 16 with bucket sort
    let bits : Nat32 = switch (maxInclusive) {
      case (null) 0;
      case (?x) {
        if (x == 0) return;
        Nat32.bitcountLeadingZero(x);
      };
    };
    bucketSortRecursive(radixBits, array, buffer, key, 0 : Nat32, n, bits, false);
  };

  // Will only be called with n > 16
  func bucketSortRecursive<T>(
    radixBits : Nat32 -> Nat32,
    array : [var T],
    buffer : [var T],
    key : T -> Nat32,
    from : Nat32,
    to : Nat32,
    bits : Nat32,
    odd : Bool,
  ) {
    let n = to - from;
    debug assert n > 16;
    debug assert bits < 32;
    let dest = if (not odd) array else buffer;

    let fullLength = n == Nat32.fromNat(array.size());

    let rBits = radixBits(n);
    debug assert 1 <= rBits and rBits <= 31;
    let BITS_ADD = Nat32.min(rBits, 32 - bits);
    let SHIFT = 32 - BITS_ADD;
    let RADIX = nat(1 << BITS_ADD);

    let counts = VarArray.repeat<Nat32>(0, RADIX);
    if (fullLength) {
      if (bits == 0) {
        for (x in array.vals()) counts[nat(key(x) >> SHIFT)] +%= 1;
      } else {
        for (x in array.vals()) counts[nat((key(x) << bits) >> SHIFT)] +%= 1;
      };
    } else {
      var i = from;
      while (i < to) {
        let x = key(array[nat(i)]);
        counts[nat((x << bits) >> SHIFT)] +%= 1;
        i +%= 1;
      };
    };

    var sum : Nat32 = from;
    for (i in counts.keys()) {
      let t = counts[i];
      counts[i] := sum;
      sum +%= t;
    };
    debug assert sum == to;

    if (fullLength) {
      if (bits == 0) {
        for (x in array.vals()) {
          let digit = nat(key(x) >> SHIFT);
          let pos = counts[digit];
          buffer[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else {
        for (x in array.vals()) {
          let digit = nat((key(x) << bits) >> SHIFT);
          let pos = counts[digit];
          buffer[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      };
    } else {
      var i = from;
      while (i < to) {
        let x = array[nat(i)];
        let digit = nat((key(x) << bits) >> SHIFT);
        let pos = counts[digit];
        buffer[nat(pos)] := x;
        counts[digit] := pos +% 1;
        i +%= 1;
      };
    };

    var newFrom : Nat32 = from;
    label L for (newTo in counts.vals()) {
      if (newTo == newFrom) continue L;
      switch (newTo -% newFrom) {
        case (1) {
          let index0 = nat(newFrom);
          dest[index0] := buffer[index0];
        };
        case (2) {
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
          let index3 = nat(newFrom +% 3);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
          let index3 = nat(newFrom +% 3);
          let index4 = nat(newFrom +% 4);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
          let index3 = nat(newFrom +% 3);
          let index4 = nat(newFrom +% 4);
          let index5 = nat(newFrom +% 5);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
          let index3 = nat(newFrom +% 3);
          let index4 = nat(newFrom +% 4);
          let index5 = nat(newFrom +% 5);
          let index6 = nat(newFrom +% 6);
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
          let index0 = nat(newFrom);
          let index1 = nat(newFrom +% 1);
          let index2 = nat(newFrom +% 2);
          let index3 = nat(newFrom +% 3);
          let index4 = nat(newFrom +% 4);
          let index5 = nat(newFrom +% 5);
          let index6 = nat(newFrom +% 6);
          let index7 = nat(newFrom +% 7);
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
        case (len) {
          if (len <= 16) {
            mergeSort16(buffer, array, key, newFrom, newTo, not odd);
          } else {
            let newBits = bits + BITS_ADD;
            if (newBits >= 32) {
              // no sort bits left, all keys in bucket are equal
              if (not odd) copy(buffer, array, from, to);
            } else {
              bucketSortRecursive(radixBits, buffer, array, key, newFrom, newTo, newBits, not odd);
            };
          };
        };
      };
      newFrom := newTo;
    };
  };
};
