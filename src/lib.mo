import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Array "mo:core/Array";

module {
  func mergeSortInternal(array : [var Nat64]) : [var Nat64] {
    let n = array.size();
    var a = array;
    var b = VarArray.repeat<Nat64>(0, n);

    var currSize = 1;

    while (currSize < n) {
      var leftStart = 0;

      while (leftStart < n) {
        let mid = Nat.min(leftStart + currSize, n);
        let rightEnd = Nat.min(leftStart + 2 * currSize, n);

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

  public func radixSort16<T>(array : [T], key : T -> Nat32) : [T] {
    let RADIX_BITS = 16;
    let RADIX = 2 ** RADIX_BITS;
    let MASK = Nat32.fromNat(RADIX - 1);

    let n = array.size();
    let nn = Nat32.fromNat(n);

    let high = VarArray.repeat<Nat>(0, n);
    let low = VarArray.repeat<Nat>(0, n);
    let allDigits = [low, high];
    var indices = VarArray.repeat<Nat>(0, n);
    var output = VarArray.repeat<Nat>(0, n);
    let counts = VarArray.repeat<Nat32>(0, 2 ** 16);

    // initialize low and high arrays
    do {
      var ii : Nat32 = 0;
      while (ii < nn) {
        let i = Nat32.toNat(ii);
        indices[i] := i;
        let k = key(array[i]);
        low[i] := Nat32.toNat(k & MASK);
        high[i] := Nat32.toNat(k >> 16); // RADIX_BITS
        ii +%= 1;
      };
    };

    // perform radix steps
    for (step in Nat.range(0, 2)) {
      if (step == 1) {
        var i = 0;
        while (i < RADIX) {
          counts[i] := 0;
          i += 1;
        };
      };

      let digits = allDigits[step];
      var i : Nat32 = 0;
      while (i < nn) {
        counts[digits[Nat32.toNat(i)]] +%= 1;
        i +%= 1;
      };

      var sum : Nat32 = 0;
      i := 0;
      let RR = Nat32.fromNat(RADIX);
      while (i < RR) {
        let ii = Nat32.toNat(i);
        let temp = counts[ii];
        counts[ii] := sum;
        sum += temp;
        i +%= 1;
      };

      i := 0;

      if (step == 0) {
        while (i < nn) {
          let ii = Nat32.toNat(i);
          let digit = digits[ii];
          output[Nat32.toNat(counts[digit])] := ii;
          counts[digit] +%= 1;
          i +%= 1;
        };
      } else {
        while (i < nn) {
          let index = indices[Nat32.toNat(i)];
          let digit = digits[index];
          output[Nat32.toNat(counts[digit])] := index;
          counts[digit] +%= 1;
          i +%= 1;
        };
      };

      let t = indices;
      indices := output;
      output := t;
    };

    Array.tabulate<T>(n, func i = array[indices[i]]);
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
        let temp = counts[i];
        counts[i] := sum;
        sum += temp;
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

  public func sort<T>(array : [T], key : T -> Nat32) : [T] {
    let coded = sortInternal(array.size(), key, func i = array[i]);
    let MASK32 : Nat64 = (1 << 32) - 1;
    Array.tabulate<T>(array.size(), func i = array[Nat64.toNat(coded[i] & MASK32)]);
  };

  public func sortInPlace<T>(array : [var T], key : T -> Nat32) {
    let coded = sortInternal(array.size(), key, func i = array[i]);
    gatherInternal(array, coded);
  };
};
