import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import Nat64 "mo:core/Nat64";
import { min } "mo:core/Nat";
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
