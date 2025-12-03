import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import { min } "mo:core/Nat";
import Array "mo:core/Array";
import Nat "mo:core/Nat";

module {
  func mergeSortInternal(array : [var Nat64]) : [var Nat64] {
    let n = array.size();
    var a = array;
    var b = VarArray.repeat<Nat64>(0, n);

    var currSize = 1;

    while (currSize < n) {
      var leftStart = 0;

      while (leftStart < n) {
        let mid = min(leftStart + currSize, n);
        let rightEnd = min(leftStart + 2 * currSize, n);

        var left = leftStart;
        var right = mid;
        var nextSorted = leftStart;
        while (left < mid and right < rightEnd) {
          let leftElement = a[left];
          let rightElement = a[right];
          b[nextSorted] := if (leftElement <= rightElement) {
            left += 1;
            leftElement;
          } else {
            right += 1;
            rightElement;
          };

          nextSorted += 1;
        };
        while (left < mid) {
          b[nextSorted] := a[left];
          nextSorted += 1;
          left += 1;
        };
        while (right < rightEnd) {
          b[nextSorted] := a[right];
          nextSorted += 1;
          right += 1;
        };

        leftStart += 2 * currSize;
      };

      currSize *= 2;

      let t = b;
      b := a;
      a := t;
    };

    a;
  };

  func sort<T>(array : [var T], scratch : [var T], key : T -> Nat32, from : Nat32, to : Nat32) {
    let n = to -% from;
    if (n <= 1) return;

    let mid = from +% (n >> 1);

    sort(array, scratch, key, from, mid);
    sort(array, scratch, key, mid, to);

    var i = from;
    var j = mid;
    var k = from;
    while (i < mid and j < to) {
      let left = array[Nat32.toNat i];
      let right = array[Nat32.toNat j];
      scratch[Nat32.toNat k] := if (key(left) <= key(right)) {
        i +%= 1;
        left;
      } else {
        j +%= 1;
        right;
      };
      k +%= 1;
    };
    while (i < mid) {
      scratch[Nat32.toNat k] := array[Nat32.toNat i];
      i +%= 1;
      k +%= 1;
    };
    while (j < to) {
      scratch[Nat32.toNat k] := array[Nat32.toNat j];
      j +%= 1;
      k +%= 1;
    };

    var l = from;
    while (l < to) {
      let ll = Nat32.toNat l;
      array[ll] := scratch[ll];
      l +%= 1;
    };
  };

  public func bucketSort<T>(array : [var T], key : T -> Nat32) {
    let n = array.size();
    if (n <= 1) return;

    let scratch = VarArray.repeat(array[0], n);
    if (n < 8) {
      sort(array, scratch, key, 0 : Nat32, Nat32.fromNat n);
      return;
    };

    bucketSortRecursive(array, scratch, key, 0 : Nat32, Nat32.fromNat(n), 0 : Nat32);
  };

  func bucketSortRecursive<T>(array : [var T], scratch : [var T], key : T -> Nat32, from : Nat32, to : Nat32, bits : Nat32) {
    if (bits >= 32) return;
    let n = to - from;

    let SHIFT = Nat32.bitcountLeadingZero(n) + 1;
    let BITS_ADD = 32 - SHIFT;
    let RADIX = Nat32.toNat(1 << BITS_ADD);

    let counts = VarArray.repeat<Nat32>(0, RADIX);
    if (bits == 0) {
      for (x in array.vals()) counts[Nat32.toNat(key(x) >> SHIFT)] +%= 1;
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

    if (bits == 0) {
      for (x in array.vals()) {
        let digit = Nat32.toNat(key(x) >> SHIFT);
        let pos = counts[digit];
        scratch[Nat32.toNat(pos)] := x;
        counts[digit] := pos +% 1;
      };
    } else {
      var i = from;
      while (i < to) {
        let x = array[Nat32.toNat(i)];
        let digit = Nat32.toNat((key(x) << bits) >> SHIFT);
        let pos = counts[digit];
        scratch[Nat32.toNat(pos)] := x;
        counts[digit] := pos +% 1;
        i +%= 1;
      };
    };

    var prev : Nat32 = from;
    for (count in counts.vals()) {
      let len = count -% prev;
      switch (len) {
        case (0) {};
        case (1) {
          let from = Nat32.toNat(prev);
          array[from] := scratch[from];
        };
        case (2) {
          let from = Nat32.toNat(prev);
          var v0 = scratch[from];
          var v1 = scratch[from + 1];

          if (key(v0) > key(v1)) {
            array[from] := v1;
            array[from + 1] := v0;
          } else {
            array[from] := v0;
            array[from + 1] := v1;
          };
        };
        case (3) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0);
          var t1 = scratch[from + 1];
          var k1 = key(t1);
          var t2 = scratch[from + 2];
          var k2 = key(t2);

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
        };
        case (4) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0) << 2;
          var t1 = scratch[from + 1];
          var k1 = (key(t1) << 2) ^ 1;
          var t2 = scratch[from + 2];
          var k2 = (key(t2) << 2) ^ 2;
          var t3 = scratch[from + 3];
          var k3 = (key(t3) << 2) ^ 3;

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k0 > k2) {
            let v = t0;
            t0 := t2;
            t2 := v;
            let k = k0;
            k0 := k2;
            k2 := k;
          };
          if (k1 > k3) {
            let v = t1;
            t1 := t3;
            t3 := v;
            let k = k1;
            k1 := k3;
            k3 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
          array[from + 3] := t3;
        };
        case (5) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0) << 3;
          var t1 = scratch[from + 1];
          var k1 = (key(t1) << 3) ^ 1;
          var t2 = scratch[from + 2];
          var k2 = (key(t2) << 3) ^ 2;
          var t3 = scratch[from + 3];
          var k3 = (key(t3) << 3) ^ 3;
          var t4 = scratch[from + 4];
          var k4 = (key(t4) << 3) ^ 4;

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k3 > k4) {
            let v = t3;
            t3 := t4;
            t4 := v;
            let k = k3;
            k3 := k4;
            k4 := k;
          };
          if (k2 > k4) {
            let v = t2;
            t2 := t4;
            t4 := v;
            let k = k2;
            k2 := k4;
            k4 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k0 > k3) {
            let v = t0;
            t0 := t3;
            t3 := v;
            let k = k0;
            k0 := k3;
            k3 := k;
          };
          if (k0 > k2) {
            let v = t0;
            t0 := t2;
            t2 := v;
            let k = k0;
            k0 := k2;
            k2 := k;
          };
          if (k1 > k4) {
            let v = t1;
            t1 := t4;
            t4 := v;
            let k = k1;
            k1 := k4;
            k4 := k;
          };
          if (k1 > k3) {
            let v = t1;
            t1 := t3;
            t3 := v;
            let k = k1;
            k1 := k3;
            k3 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
          array[from + 3] := t3;
          array[from + 4] := t4;
        };
        case (6) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0) << 3;
          var t1 = scratch[from + 1];
          var k1 = (key(t1) << 3) ^ 1;
          var t2 = scratch[from + 2];
          var k2 = (key(t2) << 3) ^ 2;
          var t3 = scratch[from + 3];
          var k3 = (key(t3) << 3) ^ 3;
          var t4 = scratch[from + 4];
          var k4 = (key(t4) << 3) ^ 4;
          var t5 = scratch[from + 5];
          var k5 = (key(t5) << 3) ^ 5;

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k4 > k5) {
            let v = t4;
            t4 := t5;
            t5 := v;
            let k = k4;
            k4 := k5;
            k5 := k;
          };
          if (k0 > k2) {
            let v = t0;
            t0 := t2;
            t2 := v;
            let k = k0;
            k0 := k2;
            k2 := k;
          };
          if (k3 > k5) {
            let v = t3;
            t3 := t5;
            t5 := v;
            let k = k3;
            k3 := k5;
            k5 := k;
          };
          if (k1 > k4) {
            let v = t1;
            t1 := t4;
            t4 := v;
            let k = k1;
            k1 := k4;
            k4 := k;
          };
          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k4 > k5) {
            let v = t4;
            t4 := t5;
            t5 := v;
            let k = k4;
            k4 := k5;
            k5 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k3 > k4) {
            let v = t3;
            t3 := t4;
            t4 := v;
            let k = k3;
            k3 := k4;
            k4 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
          array[from + 3] := t3;
          array[from + 4] := t4;
          array[from + 5] := t5;
        };
        case (7) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0) << 3;
          var t1 = scratch[from + 1];
          var k1 = (key(t1) << 3) ^ 1;
          var t2 = scratch[from + 2];
          var k2 = (key(t2) << 3) ^ 2;
          var t3 = scratch[from + 3];
          var k3 = (key(t3) << 3) ^ 3;
          var t4 = scratch[from + 4];
          var k4 = (key(t4) << 3) ^ 4;
          var t5 = scratch[from + 5];
          var k5 = (key(t5) << 3) ^ 5;
          var t6 = scratch[from + 6];
          var k6 = (key(t6) << 3) ^ 6;

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k0 > k2) {
            let v = t0;
            t0 := t2;
            t2 := v;
            let k = k0;
            k0 := k2;
            k2 := k;
          };
          if (k1 > k3) {
            let v = t1;
            t1 := t3;
            t3 := v;
            let k = k1;
            k1 := k3;
            k3 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k4 > k5) {
            let v = t4;
            t4 := t5;
            t5 := v;
            let k = k4;
            k4 := k5;
            k5 := k;
          };
          if (k4 > k6) {
            let v = t4;
            t4 := t6;
            t6 := v;
            let k = k4;
            k4 := k6;
            k6 := k;
          };
          if (k5 > k6) {
            let v = t5;
            t5 := t6;
            t6 := v;
            let k = k5;
            k5 := k6;
            k6 := k;
          };
          if (k0 > k4) {
            let v = t0;
            t0 := t4;
            t4 := v;
            let k = k0;
            k0 := k4;
            k4 := k;
          };
          if (k1 > k5) {
            let v = t1;
            t1 := t5;
            t5 := v;
            let k = k1;
            k1 := k5;
            k5 := k;
          };
          if (k2 > k6) {
            let v = t2;
            t2 := t6;
            t6 := v;
            let k = k2;
            k2 := k6;
            k6 := k;
          };
          if (k2 > k4) {
            let v = t2;
            t2 := t4;
            t4 := v;
            let k = k2;
            k2 := k4;
            k4 := k;
          };
          if (k3 > k5) {
            let v = t3;
            t3 := t5;
            t5 := v;
            let k = k3;
            k3 := k5;
            k5 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k3 > k4) {
            let v = t3;
            t3 := t4;
            t4 := v;
            let k = k3;
            k3 := k4;
            k4 := k;
          };
          if (k5 > k6) {
            let v = t5;
            t5 := t6;
            t6 := v;
            let k = k5;
            k5 := k6;
            k6 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
          array[from + 3] := t3;
          array[from + 4] := t4;
          array[from + 5] := t5;
          array[from + 6] := t6;
        };
        case (8) {
          let from = Nat32.toNat(prev);
          var t0 = scratch[from];
          var k0 = key(t0) << 3;
          var t1 = scratch[from + 1];
          var k1 = (key(t1) << 3) ^ 1;
          var t2 = scratch[from + 2];
          var k2 = (key(t2) << 3) ^ 2;
          var t3 = scratch[from + 3];
          var k3 = (key(t3) << 3) ^ 3;
          var t4 = scratch[from + 4];
          var k4 = (key(t4) << 3) ^ 4;
          var t5 = scratch[from + 5];
          var k5 = (key(t5) << 3) ^ 5;
          var t6 = scratch[from + 6];
          var k6 = (key(t6) << 3) ^ 6;
          var t7 = scratch[from + 7];
          var k7 = (key(t7) << 3) ^ 7;

          if (k0 > k1) {
            let v = t0;
            t0 := t1;
            t1 := v;
            let k = k0;
            k0 := k1;
            k1 := k;
          };
          if (k2 > k3) {
            let v = t2;
            t2 := t3;
            t3 := v;
            let k = k2;
            k2 := k3;
            k3 := k;
          };
          if (k4 > k5) {
            let v = t4;
            t4 := t5;
            t5 := v;
            let k = k4;
            k4 := k5;
            k5 := k;
          };
          if (k6 > k7) {
            let v = t6;
            t6 := t7;
            t7 := v;
            let k = k6;
            k6 := k7;
            k7 := k;
          };
          if (k0 > k2) {
            let v = t0;
            t0 := t2;
            t2 := v;
            let k = k0;
            k0 := k2;
            k2 := k;
          };
          if (k1 > k3) {
            let v = t1;
            t1 := t3;
            t3 := v;
            let k = k1;
            k1 := k3;
            k3 := k;
          };
          if (k4 > k6) {
            let v = t4;
            t4 := t6;
            t6 := v;
            let k = k4;
            k4 := k6;
            k6 := k;
          };
          if (k5 > k7) {
            let v = t5;
            t5 := t7;
            t7 := v;
            let k = k5;
            k5 := k7;
            k7 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k5 > k6) {
            let v = t5;
            t5 := t6;
            t6 := v;
            let k = k5;
            k5 := k6;
            k6 := k;
          };
          if (k0 > k4) {
            let v = t0;
            t0 := t4;
            t4 := v;
            let k = k0;
            k0 := k4;
            k4 := k;
          };
          if (k3 > k7) {
            let v = t3;
            t3 := t7;
            t7 := v;
            let k = k3;
            k3 := k7;
            k7 := k;
          };
          if (k1 > k5) {
            let v = t1;
            t1 := t5;
            t5 := v;
            let k = k1;
            k1 := k5;
            k5 := k;
          };
          if (k2 > k6) {
            let v = t2;
            t2 := t6;
            t6 := v;
            let k = k2;
            k2 := k6;
            k6 := k;
          };
          if (k1 > k4) {
            let v = t1;
            t1 := t4;
            t4 := v;
            let k = k1;
            k1 := k4;
            k4 := k;
          };
          if (k3 > k6) {
            let v = t3;
            t3 := t6;
            t6 := v;
            let k = k3;
            k3 := k6;
            k6 := k;
          };
          if (k2 > k4) {
            let v = t2;
            t2 := t4;
            t4 := v;
            let k = k2;
            k2 := k4;
            k4 := k;
          };
          if (k3 > k5) {
            let v = t3;
            t3 := t5;
            t5 := v;
            let k = k3;
            k3 := k5;
            k5 := k;
          };
          if (k1 > k2) {
            let v = t1;
            t1 := t2;
            t2 := v;
            let k = k1;
            k1 := k2;
            k2 := k;
          };
          if (k3 > k4) {
            let v = t3;
            t3 := t4;
            t4 := v;
            let k = k3;
            k3 := k4;
            k4 := k;
          };
          if (k5 > k6) {
            let v = t5;
            t5 := t6;
            t6 := v;
            let k = k5;
            k5 := k6;
            k6 := k;
          };

          array[from] := t0;
          array[from + 1] := t1;
          array[from + 2] := t2;
          array[from + 3] := t3;
          array[from + 4] := t4;
          array[from + 5] := t5;
          array[from + 6] := t6;
          array[from + 7] := t7;
        };
        case (_) {
          bucketSortRecursive(scratch, array, key, prev, count, bits + BITS_ADD);
          var i = prev;
          while (i < count) {
            let ii = Nat32.toNat(i);
            array[ii] := scratch[ii];
            i +%= 1;
          };
        };
      };
      prev := count;
    };
  };

  public func radixSort16<T>(array : [T], key : T -> Nat32) : [T] {
    let RADIX_BITS = 16;
    let RADIX = 2 ** RADIX_BITS;
    let RR = Nat32.fromNat(RADIX);
    let MASK = RR -% 1;

    let n = array.size();

    let indices = VarArray.repeat<Nat>(0, n);
    let output = VarArray.repeat<Nat>(0, n);
    let counts = VarArray.repeat<Nat32>(0, RADIX);

    // perform radix steps
    for (step in [0, 1].vals()) {
      // reset counts
      if (step == 1) {
        for (i in counts.keys()) counts[i] := 0;
      };

      // read in the digits and count
      if (step == 0) {
        // read low
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) & MASK);
          counts[digit] +%= 1;
        };
      } else {
        // read high
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) >> 16);
          counts[digit] +%= 1;
        };
      };

      // convert counts to positions
      var sum : Nat32 = 0;
      for (i in counts.keys()) {
        let t = counts[i];
        counts[i] := sum;
        sum +%= t;
      };

      // move to indices and output
      if (step == 0) {
        for (i in array.keys()) {
          let digit = Nat32.toNat(key(array[i]) & MASK);
          let pos = counts[digit];
          indices[Nat32.toNat(pos)] := i;
          counts[digit] := pos +% 1;
        };
      } else {
        for (i in indices.vals()) {
          let digit = Nat32.toNat(key(array[i]) >> 16);
          let pos = counts[digit];
          output[Nat32.toNat(pos)] := i;
          counts[digit] := pos +% 1;
        };
      };
    };

    Array.tabulate<T>(n, func i = array[output[i]]);
  };

  public func radixSort16InPlace<T>(array : [var T], key : T -> Nat32) {
    if (array.size() == 0) return;

    let RADIX_BITS = 16;
    let RADIX = 2 ** RADIX_BITS;
    let RR = Nat32.fromNat(RADIX);
    let MASK = RR -% 1;

    let n = array.size();

    let scratch = VarArray.repeat<T>(array[0], n);

    //    let indices = VarArray.repeat<Nat>(0, n);
    //    let output = VarArray.repeat<Nat>(0, n);
    let counts = VarArray.repeat<Nat32>(0, RADIX);

    // perform radix steps
    for (step in [0, 1].vals()) {
      // reset counts
      if (step == 1) {
        for (i in counts.keys()) counts[i] := 0;
      };

      // read in the digits and count
      if (step == 0) {
        // read low
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) & MASK);
          counts[digit] +%= 1;
        };
      } else {
        // read high
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) >> 16);
          counts[digit] +%= 1;
        };
      };

      // convert counts to positions
      var sum : Nat32 = 0;
      for (i in counts.keys()) {
        let t = counts[i];
        counts[i] := sum;
        sum +%= t;
      };

      // move to indices and output
      if (step == 0) {
        for (x in array.vals()) {
          let digit = Nat32.toNat(key(x) & MASK);
          let pos = counts[digit];
          scratch[Nat32.toNat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else {
        for (x in scratch.vals()) {
          let digit = Nat32.toNat(key(x) >> 16);
          let pos = counts[digit];
          array[Nat32.toNat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      };
    };

  };

  func radixSortInternal(array : [var Nat64], RADIX_BITS : Nat64) : [var Nat64] {
    let n = array.size();
    var a = array;
    var b = VarArray.repeat<Nat64>(0, n);
    let RADIX = Nat64.toNat(1 << RADIX_BITS);
    let MASK = (1 << RADIX_BITS) - 1;

    let counts = VarArray.repeat<Nat>(0, RADIX);

    var shift : Nat64 = 32;
    while (shift < 64) {
      var i = 0;
      while (i < RADIX) {
        counts[i] := 0;
        i += 1;
      };

      i := 0;
      while (i < n) {
        let digit = Nat64.toNat((a[i] >> shift) & MASK);
        counts[digit] += 1;
        i += 1;
      };

      var sum = 0;
      i := 0;
      while (i < RADIX) {
        let t = counts[i];
        counts[i] := sum;
        sum += t;
        i += 1;
      };

      i := 0;
      while (i < n) {
        let digit = Nat64.toNat((a[i] >> shift) & MASK);
        b[counts[digit]] := a[i];
        counts[digit] += 1;
        i += 1;
      };

      let t = b;
      b := a;
      a := t;

      shift += RADIX_BITS;
    };
    a;
  };

  func gatherInternal<T>(array : [var T], coded : [var Nat64]) {
    let n = array.size();
    let MASK32 : Nat64 = (1 << 32) - 1;
    var i = 0;
    label outer while (i < n) {
      if (coded[i] == MASK32) {
        i += 1;
        continue outer;
      };
      if (Nat64.toNat(coded[i] & MASK32) == i) {
        coded[i] := MASK32;
        i += 1;
        continue outer;
      };

      let start = array[i];
      var current = i;

      label inner loop {
        let next = Nat64.toNat(coded[current] & MASK32);

        if (next == i) {
          array[current] := start;
          coded[current] := MASK32;
          break inner;
        };

        array[current] := array[next];

        coded[current] := MASK32;
        current := next;
      };

      i += 1;
    };
  };

  func sortInternal<T>(n : Nat, key : T -> Nat32, get : Nat -> T) : [var Nat64] {
    let coded = VarArray.tabulate<Nat64>(
      n,
      func(i) {
        let value = Nat64.fromNat32(key(get(i)));
        let index = Nat64.fromNat(i);
        (value << 32) ^ index;
      },
    );

    if (n < 2 ** 8) {
      mergeSortInternal(coded);
    } else if (n < 2 ** 16) {
      radixSortInternal(coded, 8);
    } else {
      radixSortInternal(coded, 16);
    };
  };

  public func sort_old<T>(array : [T], key : T -> Nat32) : [T] {
    let coded = sortInternal(array.size(), key, func i = array[i]);
    let MASK32 : Nat64 = (1 << 32) - 1;
    Array.tabulate<T>(array.size(), func i = array[Nat64.toNat(coded[i] & MASK32)]);
  };

  public func sortInPlace<T>(array : [var T], key : T -> Nat32) {
    let coded = sortInternal(array.size(), key, func i = array[i]);
    gatherInternal(array, coded);
  };
};
