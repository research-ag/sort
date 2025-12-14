import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import { insertionSortSmall } "./insertion";
import { copy } "./utils";

module {
  let nat = Nat32.toNat;

  // should be from < mid < to
  func merge<T>(array : [var T], buffer : [var T], key : T -> Nat32, from : Nat32, mid : Nat32, to : Nat32) {
    var pos = from;
    var i = from;
    var j = mid;

    var iElem = array[nat(i)];
    var jElem = array[nat(j)];
    label L loop {
      if (key(iElem) <= key(jElem)) {
        buffer[nat(pos)] := iElem;
        i +%= 1;
        pos +%= 1;
        if (i == mid) {
          while (j < to) {
            buffer[nat(pos)] := array[nat(j)];
            j +%= 1;
            pos +%= 1;
          };
          break L;
        } else {
          iElem := array[nat(i)];
        };
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
        } else {
          jElem := array[nat(j)];
        };
      };
    };
  };

  // should be 8 < size <= 16
  public func mergeSort16<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat32, to : Nat32) {
    let size = to - from;
    let len1 = size / 2;
    let len2 = size - len1;

    let mid = from + len1;

    insertionSortSmall(buffer, buffer, key, from, len1);
    insertionSortSmall(buffer, buffer, key, mid, len2);

    merge(buffer, dest, key, from, mid, to);
  };

  public func mergeSort<T>(array : [var T], key : T -> Nat32) {
    let size = Nat32.fromNat(array.size());

    let bound = size / 8 * 8;
    if (size % 8 > 0) insertionSortSmall(array, array, key, bound, size % 8);

    if (bound == 0) return;
    
    var i : Nat32 = 0;
    while (i < bound) {
      let index0 = nat(i);
      let index1 = nat(i +% 1);
      let index2 = nat(i +% 2);
      let index3 = nat(i +% 3);
      let index4 = nat(i +% 4);
      let index5 = nat(i +% 5);
      let index6 = nat(i +% 6);
      let index7 = nat(i +% 7);
      var t0 = array[index0];
      var k0 = key(t0);
      var t1 = array[index1];
      var k1 = key(t1);
      var t2 = array[index2];
      var k2 = key(t2);
      var t3 = array[index3];
      var k3 = key(t3);
      var t4 = array[index4];
      var k4 = key(t4);
      var t5 = array[index5];
      var k5 = key(t5);
      var t6 = array[index6];
      var k6 = key(t6);
      var t7 = array[index7];
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

      array[index0] := t0;
      array[index1] := t1;
      array[index2] := t2;
      array[index3] := t3;
      array[index4] := t4;
      array[index5] := t5;
      array[index6] := t6;
      array[index7] := t7;

      i += 8;
    };

    let scratchSpace = VarArray.repeat<T>(array[0], nat(size));

    var currSize : Nat32 = 8;
    var oddIteration = false;

    while (currSize < size) {
      let (fromArray, toArray) = if (oddIteration) (scratchSpace, array) else (array, scratchSpace);
      var leftStart : Nat32 = 0;

      while (leftStart < size) {
        let mid = Nat32.min(size, leftStart + currSize);
        let rightEnd = Nat32.min(size, leftStart + 2 * currSize);

        if (mid == rightEnd) {
          copy(fromArray, toArray, leftStart, mid);
        } else {
          merge(fromArray, toArray, key, leftStart, mid, rightEnd);
        };

        leftStart += 2 * currSize;
      };

      currSize *= 2;
      oddIteration := not oddIteration;
    };
    if (oddIteration) for (i in array.keys()) array[i] := scratchSpace[i];
  };
};