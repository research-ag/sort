import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import { insertionSortSmall } "./insertion";
import { merge } "./merge16";

module {
  let nat = Nat32.toNat;

  public func mergeSort<T>(array : [var T], key : T -> Nat32) {
    let size = Nat32.fromNat(array.size());
    if (size <= 1) return;
    if (size <= 8) {
      insertionSortSmall(array, array, key, 0 : Nat32, size);
      return;
    };
    let buffer = VarArray.repeat<T>(array[0], nat(size));
    mergeSortRec(array, buffer, key, 0 : Nat32, size, true);
  };

  // input data is alwways in array
  // even: write output data to array
  // not even: write output data to buffer
  func mergeSortRec<T>(
    array : [var T],
    buffer : [var T],
    key : T -> Nat32,
    from : Nat32,
    to : Nat32,
    even : Bool
  ) {
    debug assert from < to;
    let size = to -% from;
    debug assert size >= 4;

    if (size <= 8) {
      let dest = if (even) array else buffer;
      insertionSortSmall(array, dest, key, from, size);
      return;
    };

    let mid = from +% (size / 2);
    if (even) { // merge to array
      mergeSortRec(array, buffer, key, mid, to, true); // upper half to array
      mergeSortRec(array, buffer, key, from, mid, false); // lower half to buffer
      merge(buffer, array, key, from, mid, to);
    } else { // merge to buffer
      mergeSortRec(array, buffer, key, mid, to, false); // upper half to buffer
      mergeSortRec(array, buffer, key, from, mid, true); // lower half to array
      merge(array, buffer, key, from, mid, to);
    };
  };
};
