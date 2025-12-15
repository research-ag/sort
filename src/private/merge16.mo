import Nat32 "mo:core/Nat32";
import { insertionSortSmall } "./insertion";

module {
  let nat = Nat32.toNat;

  func merge<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, mid : Nat32, to : Nat32) {
    debug assert from < mid;
    debug assert mid < to;
    var pos = from;
    var i = from;
    var j = mid;

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
        if (j == to) {
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

  // should be 8 < size <= 16
  // if move == true: sort from array to buffer
  // if move == false: sort in place in array
  // array and buffer must not be identical
  public func mergeSort16<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, to : Nat32, move : Bool) {
    let size = to - from;
    debug assert size > 8;
    debug assert size <= 16;
    let len1 = size / 2;
    let len2 = size - len1;

    let mid = from + len1;

    if (move) {
      insertionSortSmall(array, array, key, from, len1);
      insertionSortSmall(array, buffer, key, mid, len2);
      merge(array, buffer, key, from, mid, to);
    } else {
      insertionSortSmall(array, buffer, key, from, len1);
      insertionSortSmall(array, array, key, mid, len2);
      merge(buffer, array, key, from, mid, to);
    };
  };
};