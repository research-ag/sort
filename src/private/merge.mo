import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Prim "mo:⛔";

import { insertionSortSmall; insertionSortSmallMove } "./insertion";

module {
  let nat = Prim.nat32ToNat;

  public func mergeSort<T>(array : [var T], key : T -> Nat32) {
    let size = Nat32.fromNat(array.size());
    if (size <= 1) return;
    if (size <= 2) {
      if (key(array[1]) < key(array[0])) {
        let t0 = array[0];
        array[0] := array[1];
        array[1] := t0;
      };
      return;
    };
    if (size <= 8) {
      insertionSortSmall(array, array, key, 0 : Nat32, size);
      return;
    };
    let buffer = VarArray.repeat<T>(array[0], nat(size / 2));
    mergeSortRec(array, buffer, key, 0 : Nat32, size, true, 0 : Nat32);
  };

  // input data is alwways in array
  // even: write output data to array in place
  // odd: write output data to buffer at offset
  // offset is only used when odd
  func mergeSortRec<T>(
    array : [var T],
    buffer : [var T],
    key : T -> Nat32,
    from : Nat32,
    to : Nat32,
    even : Bool,
    offset : Nat32,
  ) {
    debug assert from < to;
    let size = to -% from;
    debug assert size >= 4;

    if (size <= 8) {
      if (even) {
        insertionSortSmall(array, array, key, from, size); // sorts array in place
      } else {
        insertionSortSmallMove(array, buffer, key, from, size, offset); // sorts to buffer at offset
      };
      return;
    };

    let len1 = size / 2;
    let mid = from +% len1;
    if (even) {
      // merge to array in place
      mergeSortRec(array, buffer, key, mid, to, true, 0 : Nat32); // sort upper half to array in place
      mergeSortRec(array, buffer, key, from, mid, false, 0 : Nat32); // sort lower half to beginning of buffer
      merge1(array, buffer, key, from, mid, to); // merge to array in place
    } else {
      // merge to buffer at offset
      mergeSortRec(array, buffer, key, from, mid, true, 0 : Nat32); // lower half to array in place
      mergeSortRec(array, buffer, key, mid, to, false, offset +% len1); // sort upper half to buffer starting shifted offset
      merge2(array, buffer, key, from, mid, size, offset); // merge to buffer at offset
    };
  };

  func merge1<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, mid : Nat32, to : Nat32) {
    debug assert from < mid;
    debug assert mid < to;
    let len = mid -% from;
    var pos = from;
    var i = 0 : Nat32;
    var j = mid;

    var iElem = buffer[nat(i)];
    var jElem = array[nat(j)];
    label L loop {
      if (key(iElem) <= key(jElem)) {
        array[nat(pos)] := iElem;
        i +%= 1;
        pos +%= 1;
        if (i == len) break L;
        iElem := buffer[nat(i)];
      } else {
        array[nat(pos)] := jElem;
        j +%= 1;
        pos +%= 1;
        if (j == to) {
          while (i < len) {
            array[nat(pos)] := buffer[nat(i)];
            i +%= 1;
            pos +%= 1;
          };
          break L;
        };
        jElem := array[nat(j)];
      };
    };
  };

  func merge2<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, mid : Nat32, size : Nat32, offset : Nat32) {
    debug assert from < mid;
    debug assert mid < from +% size;
    let len = mid -% from;
    var pos = offset;
    var i = from;
    var j = offset +% len;
    let j_max = offset +% size;

    var iElem = array[nat(i)];
    var jElem = buffer[nat(j)];
    label L loop {
      if (key(iElem) <= key(jElem)) {
        buffer[nat(pos)] := iElem;
        i +%= 1;
        pos +%= 1;
        if (i == mid) break L;
        iElem := array[nat(i)];
      } else {
        buffer[nat(pos)] := jElem;
        j +%= 1;
        pos +%= 1;
        if (j == j_max) {
          while (i < mid) {
            buffer[nat(pos)] := array[nat(i)];
            i +%= 1;
            pos +%= 1;
          };
          break L;
        };
        jElem := buffer[nat(j)];
      };
    };
  };
};
