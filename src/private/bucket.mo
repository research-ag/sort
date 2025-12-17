import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Prim "mo:⛔";

import { insertionSortSmall } "./insertion";
import { mergeSort16 } "./merge16";

module {
  let nat = Prim.nat32ToNat;

  func copy<T>(source : [var T], dest : [var T], from : Nat32, to : Nat32) {
    var i = from;
    while (i < to) {
      let ii = Prim.nat32ToNat(i);
      dest[ii] := source[ii];
      i +%= 1;
    };
  };

  // should be 1 <= radixBits n <= 31 for all n
  public func bucketSort<T>(array : [var T], key : T -> Nat32, maxInclusive : ?Nat32, radixBits : Nat32 -> Nat32) {
    let n = Nat32.fromNat(array.size());

    // n <= 1 is already sorted
    if (n <= 1) return;

    // sort n == 2
    if (n <= 2) {
      if (key(array[1]) < key(array[0])) {
        let t0 = array[0];
        array[0] := array[1];
        array[1] := t0;
      };
      return;
    };

    // sort n <= 8 with insertion sort
    if (n <= 8) {
      insertionSortSmall(array, array, key, 0 : Nat32, n);
      return;
    };

    // sort 8 < n <= 16 with merge sort
    if (n <= 16) {
      let buffer = VarArray.repeat(array[0], nat(n / 2));
      mergeSort16(array, buffer, key, 0 : Nat32, n, false);
      return;
    };

    // sort n > 16 with bucket sort
    let buffer = VarArray.repeat(array[0], nat(n));
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
      let len = newTo -% newFrom;
      if (len == 1) {
        if (not odd) {
          let index0 = nat(newFrom);
          array[index0] := buffer[index0];
        };
      } else if (len == 2) {
        let index0 = nat(newFrom);
        let index1 = nat(newFrom +% 1);
        let t0 = buffer[index0];
        let t1 = buffer[index1];
        if (key(t1) < key(t0)) {
          // swap
          let dest = if (odd) buffer else array;
          dest[index0] := t1;
          dest[index1] := t0;
        } else {
          // don't swap
          if (not odd) {
            array[index0] := t0;
            array[index1] := t1;
          };
        };
      } else if (len <= 8) {
        let dest = if (odd) buffer else array;
        insertionSortSmall(buffer, dest, key, newFrom, len);
      } else if (len <= 16) {
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
      newFrom := newTo;
    };
  };
};
