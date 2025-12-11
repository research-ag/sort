import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";

module {
  public func bucketSort<T>(array : [var T], key : T -> Nat32, maxInclusive : ?Nat32, radixBits : Nat32 -> Nat32) {
    let n = array.size();
    if (n <= 1) return;

    let buffer = VarArray.repeat(array[0], n);
    let bits : Nat32 = switch (maxInclusive) {
      case (null) 0;
      case (?x) {
        if (x == 0) return;
        Nat32.bitcountLeadingZero(x);
      };
    };

    bucketSortRecursive(radixBits, array, buffer, key, 0 : Nat32, Nat32.fromNat(n), bits, false);
  };

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
    if (bits >= 32) {
      if (odd) {
        var i = from;
        while (i < to) {
          let ii = Nat32.toNat(i);
          buffer[ii] := array[ii];
          i +%= 1;
        };
      };
      return;
    };

    let n = to - from;
    let fullLength = n == Nat32.fromNat(array.size());

    let BITS_ADD = Nat32.min(radixBits(n), 32 - bits);
    let SHIFT = 32 - BITS_ADD;
    let RADIX = Nat32.toNat(1 << BITS_ADD);

    let counts = VarArray.repeat<Nat32>(0, RADIX);
    if (fullLength) {
      if (bits == 0) {
        for (x in array.vals()) counts[Nat32.toNat(key(x) >> SHIFT)] +%= 1;
      } else {
        for (x in array.vals()) counts[Nat32.toNat((key(x) << bits) >> SHIFT)] +%= 1;
      };
    } else {
      var i = from;
      while (i < to) {
        let x = key(array[Nat32.toNat(i)]);
        counts[Nat32.toNat((x << bits) >> SHIFT)] +%= 1;
        i +%= 1;
      };
    };

    var sum : Nat32 = from;
    for (i in counts.keys()) {
      let t = counts[i];
      counts[i] := sum;
      sum +%= t;
    };

    if (fullLength) {
      if (bits == 0) {
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) >> SHIFT);
          let pos = counts[digit];
          buffer[Nat32.toNat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else {
        for (x in array.vals()) {
          let digit = Nat32.toNat((key(x) << bits) >> SHIFT);
          let pos = counts[digit];
          buffer[Nat32.toNat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      };
    } else {
      var i = from;
      while (i < to) {
        let x = array[Nat32.toNat(i)];
        let digit = Nat32.toNat((key(x) << bits) >> SHIFT);
        let pos = counts[digit];
        buffer[Nat32.toNat(pos)] := x;
        counts[digit] := pos +% 1;
        i +%= 1;
      };
    };

    var newFrom : Nat32 = from;
    let dest = if (not odd) array else buffer;
    label L for (newTo in counts.vals()) {
      if (newTo == newFrom) continue L;
      switch (newTo -% newFrom) {
        case (1) {
          let from = Nat32.toNat(newFrom);
          dest[from] := buffer[from];
        };
        case (2) {
          let from = Nat32.toNat(newFrom);
          let fromPlus1 = Nat32.toNat(newFrom +% 1);
          let t0 = buffer[from];
          let t1 = buffer[fromPlus1];
          if (key(t1) < key(t0)) {
            dest[from] := t1;
            dest[fromPlus1] := t0;
          } else {
            dest[from] := t0;
            dest[fromPlus1] := t1;
          };
        };
        case (3) {
          let from = Nat32.toNat(newFrom);
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
          let from = Nat32.toNat(newFrom);
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
          let from = Nat32.toNat(newFrom);
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
          let from = Nat32.toNat(newFrom);
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
          let from = Nat32.toNat(newFrom);
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
          let from = Nat32.toNat(newFrom);
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
        case (_) bucketSortRecursive(radixBits, buffer, array, key, newFrom, newTo, bits + BITS_ADD, not odd);
      };
      newFrom := newTo;
    };
  };
};
