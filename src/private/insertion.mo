import Prim "mo:⛔";

module {
  let nat = Prim.nat32ToNat;

  // Must have: 3 <= len <= 8
  // Use dest = buffer when sorting in place

  public func insertionSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat32, len : Nat32) {
    debug assert len > 2;

    // first two elements
    let index0 = nat(from);
    let index1 = nat(from +% 1);
    var t0 = buffer[index0];
    var t1 = buffer[index1];
    var k0 = key(t0);
    var k1 = key(t1);

    if (k1 < k0) {
      do { let t = t0; t0 := t1; t1 := t };
      do { let k = k0; k0 := k1; k1 := k };
    };

    // new element
    let index2 = nat(from +% 2);
    var t2 = buffer[index2];
    var k2 = key(t2);

    if (len == 3) {
      // sort values without keys
      if (k2 < k1) {
        dest[index2] := t1;
        if (k2 < k0) {
          t1 := t0;
          t0 := t2;
        } else t1 := t2;
      } else dest[index2] := t2;

      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };

    // sort values and keys
    if (k2 < k1) {
      let k2_new = k1;
      let t2_new = t1;
      if (k2 < k0) {
        do { t1 := t0; k1 := k0 };
        do { t0 := t2; k0 := k2 };
      } else {
        do { t1 := t2; k1 := k2 };
      };
      do { t2 := t2_new; k2 := k2_new };
    };

    // new element
    let index3 = nat(from +% 3);
    var t3 = buffer[index3];
    var k3 = key(t3);

    if (len == 4) {
      // sort values without keys
      if (k3 < k2) {
        dest[index3] := t2;
        if (k3 < k1) {
          t2 := t1;
          if (k3 < k0) {
            t1 := t0;
            t0 := t3;
          } else t1 := t3;
        } else t2 := t3;
      } else dest[index3] := t3;

      dest[index2] := t2;
      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };

    // sort values and keys
    if (k3 < k2) {
      let t3_new = t2;
      let k3_new = k2;
      if (k3 < k1) {
        do { t2 := t1; k2 := k1 };
        if (k3 < k0) {
          do { t1 := t0; k1 := k0 };
          do { t0 := t3; k0 := k3 };
        } else {
          do { t1 := t3; k1 := k3 };
        };
      } else { t2 := t3; k2 := k3 };
      do { t3 := t3_new; k3 := k3_new };
    };

    // new element
    let index4 = nat(from +% 4);
    var t4 = buffer[index4];
    var k4 = key(t4);

    if (len == 5) {
      // sort values without keys
      if (k4 < k3) {
        dest[index4] := t3;
        if (k4 < k2) {
          t3 := t2;
          if (k4 < k1) {
            t2 := t1;
            if (k4 < k0) {
              t1 := t0;
              t0 := t4;
            } else t1 := t4;
          } else t2 := t4;
        } else t3 := t4;
      } else dest[index4] := t4;

      dest[index3] := t3;
      dest[index2] := t2;
      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };

    // sort values and keys
    if (k4 < k3) {
      let t4_new = t3;
      let k4_new = k3;
      if (k4 < k2) {
        do { t3 := t2; k3 := k2 };
        if (k4 < k1) {
          do { t2 := t1; k2 := k1 };
          if (k4 < k0) {
            do { t1 := t0; k1 := k0 };
            do { t0 := t4; k0 := k4 };
          } else {
            do { t1 := t4; k1 := k4 };
          };
        } else { t2 := t4; k2 := k4 };
      } else { t3 := t4; k3 := k4 };
      do { t4 := t4_new; k4 := k4_new };
    };

    // new element
    let index5 = nat(from +% 5);
    var t5 = buffer[index5];
    var k5 = key(t5);

    if (len == 6) {
      // sort values without keys
      if (k5 < k4) {
        dest[index5] := t4;
        if (k5 < k3) {
          t4 := t3;
          if (k5 < k2) {
            t3 := t2;
            if (k5 < k1) {
              t2 := t1;
              if (k5 < k0) {
                t1 := t0;
                t0 := t5;
              } else t1 := t5;
            } else t2 := t5;
          } else t3 := t5;
        } else t4 := t5;
      } else dest[index5] := t5;

      dest[index4] := t4;
      dest[index3] := t3;
      dest[index2] := t2;
      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };

    // sort values and keys
    if (k5 < k4) {
      let t5_new = t4;
      let k5_new = k4;
      if (k5 < k3) {
        do { t4 := t3; k4 := k3 };
        if (k5 < k2) {
          do { t3 := t2; k3 := k2 };
          if (k5 < k1) {
            do { t2 := t1; k2 := k1 };
            if (k5 < k0) {
              do { t1 := t0; k1 := k0 };
              do { t0 := t5; k0 := k5 };
            } else {
              do { t1 := t5; k1 := k5 };
            };
          } else { t2 := t5; k2 := k5 };
        } else { t3 := t5; k3 := k5 };
      } else { t4 := t5; k4 := k5 };
      do { t5 := t5_new; k5 := k5_new };
    };

    // new element
    let index6 = nat(from +% 6);
    var t6 = buffer[index6];
    var k6 = key(t6);

    if (len == 7) {
      // sort values without keys
      if (k6 < k5) {
        dest[index6] := t5;
        if (k6 < k4) {
          t5 := t4;
          if (k6 < k3) {
            t4 := t3;
            if (k6 < k2) {
              t3 := t2;
              if (k6 < k1) {
                t2 := t1;
                if (k6 < k0) {
                  t1 := t0;
                  t0 := t6;
                } else t1 := t6;
              } else t2 := t6;
            } else t3 := t6;
          } else t4 := t6;
        } else t5 := t6;
      } else dest[index6] := t6;

      dest[index5] := t5;
      dest[index4] := t4;
      dest[index3] := t3;
      dest[index2] := t2;
      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };

    // sort values and keys
    if (k6 < k5) {
      let t6_new = t5;
      let k6_new = k5;
      if (k6 < k4) {
        do { t5 := t4; k5 := k4 };
        if (k6 < k3) {
          do { t4 := t3; k4 := k3 };
          if (k6 < k2) {
            do { t3 := t2; k3 := k2 };
            if (k6 < k1) {
              do { t2 := t1; k2 := k1 };
              if (k6 < k0) {
                do { t1 := t0; k1 := k0 };
                do { t0 := t6; k0 := k6 };
              } else { t1 := t6; k1 := k6 };
            } else { t2 := t6; k2 := k6 };
          } else { t3 := t6; k3 := k6 };
        } else { t4 := t6; k4 := k6 };
      } else { t5 := t6; k5 := k6 };
      do { t6 := t6_new; k6 := k6_new };
    };

    // new element
    let index7 = nat(from +% 7);
    var t7 = buffer[index7];
    var k7 = key(t7);

    if (len == 8) {
      // sort values without keys
      if (k7 < k6) {
        dest[index7] := t6;
        if (k7 < k5) {
          t6 := t5;
          if (k7 < k4) {
            t5 := t4;
            if (k7 < k3) {
              t4 := t3;
              if (k7 < k2) {
                t3 := t2;
                if (k7 < k1) {
                  t2 := t1;
                  if (k7 < k0) {
                    t1 := t0;
                    t0 := t7;
                  } else t1 := t7;
                } else t2 := t7;
              } else t3 := t7;
            } else t4 := t7;
          } else t5 := t7;
        } else t6 := t7;
      } else dest[index7] := t7;

      dest[index6] := t6;
      dest[index5] := t5;
      dest[index4] := t4;
      dest[index3] := t3;
      dest[index2] := t2;
      dest[index1] := t1;
      dest[index0] := t0;
      return;
    };
    Prim.trap("insertionSortSmall for len > 8 is not implemented.");
  };

  // sort from buffer to dest array at the given offset
  public func insertionSortSmallMove<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat32, len : Nat32, offset : Nat32) {
    debug assert len > 0;
    
    if (len == 1) {
      dest[nat(offset)] := buffer[nat(from)];
      return;
    };

    // first two elements  
    let index0 = nat(from);
    let index1 = nat(from +% 1);
    var t0 = buffer[index0];
    var t1 = buffer[index1];
    var k0 = key(t0);
    var k1 = key(t1);

    if (k1 < k0) {
      do { let t = t0; t0 := t1; t1 := t };
      do { let k = k0; k0 := k1; k1 := k };
    };

    if (len == 2) {
      dest[nat(offset)] := t0;
      dest[nat(offset +% 1)] := t1;
      return;
    };

    // new element
    let index2 = nat(from +% 2);
    var t2 = buffer[index2];
    var k2 = key(t2);

    if (len == 3) {
      // sort values without keys
      if (k2 < k1) {
        dest[nat(offset +% 2)] := t1;
        if (k2 < k0) {
          t1 := t0;
          t0 := t2;
        } else t1 := t2;
      } else dest[nat(offset +% 2)] := t2;

      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k2 < k1) {
      let k2_new = k1;
      let t2_new = t1;
      if (k2 < k0) {
        do { t1 := t0; k1 := k0 };
        do { t0 := t2; k0 := k2 };
      } else {
        do { t1 := t2; k1 := k2 };
      };
      t2 := t2_new; k2 := k2_new;
    };

    // new element
    let index3 = nat(from +% 3);
    var t3 = buffer[index3];
    var k3 = key(t3);

    if (len == 4) {
      // sort values without keys
      if (k3 < k2) {
        dest[nat(offset +% 3)] := t2;
        if (k3 < k1) {
          t2 := t1;
          if (k3 < k0) {
            t1 := t0;
            t0 := t3;
          } else t1 := t3;
        } else t2 := t3;
      } else dest[nat(offset +% 3)] := t3;

      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k3 < k2) {
      let t3_new = t2;
      let k3_new = k2;
      if (k3 < k1) {
        do { t2 := t1; k2 := k1 };
        if (k3 < k0) { t1 := t0; k1 := k0; t0 := t3; k0 := k3 } else {
          t1 := t3; k1 := k3;
        };
      } else { t2 := t3; k2 := k3 };
      do { t3 := t3_new; k3 := k3_new };
    };

    // new element
    let index4 = nat(from +% 4);
    var t4 = buffer[index4];
    var k4 = key(t4);

    if (len == 5) {
      // sort values without keys
      if (k4 < k3) {
        dest[nat(offset +% 4)] := t3;
        if (k4 < k2) {
          t3 := t2;
          if (k4 < k1) {
            t2 := t1;
            if (k4 < k0) {
              t1 := t0;
              t0 := t4;
            } else t1 := t4;
          } else t2 := t4;
        } else t3 := t4;
      } else dest[nat(offset +% 4)] := t4;

      dest[nat(offset +% 3)] := t3;
      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k4 < k3) {
      let t4_new = t3;
      let k4_new = k3;
      if (k4 < k2) {
        do { t3 := t2; k3 := k2 };
        if (k4 < k1) {
          do { t2 := t1; k2 := k1 };
          if (k4 < k0) { t1 := t0; k1 := k0; t0 := t4; k0 := k4 } else {
            t1 := t4; k1 := k4;
          };
        } else { t2 := t4; k2 := k4 };
      } else { t3 := t4; k3 := k4 };
      do { t4 := t4_new; k4 := k4_new };
    };

    // new element
    let index5 = nat(from +% 5);
    var t5 = buffer[index5];
    var k5 = key(t5);

    if (len == 6) {
      // sort values without keys
      if (k5 < k4) {
        dest[nat(offset +% 5)] := t4;
        if (k5 < k3) {
          t4 := t3;
          if (k5 < k2) {
            t3 := t2;
            if (k5 < k1) {
              t2 := t1;
              if (k5 < k0) {
                t1 := t0;
                t0 := t5;
              } else t1 := t5;
            } else t2 := t5;
          } else t3 := t5;
        } else t4 := t5;
      } else dest[nat(offset +% 5)] := t5;

      dest[nat(offset +% 4)] := t4;
      dest[nat(offset +% 3)] := t3;
      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k5 < k4) {
      let t5_new = t4;
      let k5_new = k4;
      if (k5 < k3) {
        do { t4 := t3; k4 := k3 };
        if (k5 < k2) {
          do { t3 := t2; k3 := k2 };
          if (k5 < k1) {
            do { t2 := t1; k2 := k1 };
            if (k5 < k0) { t1 := t0; k1 := k0; t0 := t5; k0 := k5 } else {
              t1 := t5; k1 := k5;
            };
          } else { t2 := t5; k2 := k5 };
        } else { t3 := t5; k3 := k5 };
      } else { t4 := t5; k4 := k5 };
      do { t5 := t5_new; k5 := k5_new };
    };

    // new element
    let index6 = nat(from +% 6);
    var t6 = buffer[index6];
    var k6 = key(t6);

    if (len == 7) {
      // sort values without keys
      if (k6 < k5) {
        dest[nat(offset +% 6)] := t5;
        if (k6 < k4) {
          t5 := t4;
          if (k6 < k3) {
            t4 := t3;
            if (k6 < k2) {
              t3 := t2;
              if (k6 < k1) {
                t2 := t1;
                if (k6 < k0) {
                  t1 := t0;
                  t0 := t6;
                } else t1 := t6;
              } else t2 := t6;
            } else t3 := t6;
          } else t4 := t6;
        } else t5 := t6;
      } else dest[nat(offset +% 6)] := t6;

      dest[nat(offset +% 5)] := t5;
      dest[nat(offset +% 4)] := t4;
      dest[nat(offset +% 3)] := t3;
      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k6 < k5) {
      let t6_new = t5;
      let k6_new = k5;
      if (k6 < k4) {
        do { t5 := t4; k5 := k4 };
        if (k6 < k3) {
          do { t4 := t3; k4 := k3 };
          if (k6 < k2) {
            do { t3 := t2; k3 := k2 };
            if (k6 < k1) {
              do { t2 := t1; k2 := k1 };
              if (k6 < k0) {
                do { t1 := t0; k1 := k0 };
                do { t0 := t6; k0 := k6 };
              } else { t1 := t6; k1 := k6 };
            } else { t2 := t6; k2 := k6 };
          } else { t3 := t6; k3 := k6 };
        } else { t4 := t6; k4 := k6 };
      } else { t5 := t6; k5 := k6 };
      do { t6 := t6_new; k6 := k6_new };
    };

    // new element
    let index7 = nat(from +% 7);
    var t7 = buffer[index7];
    var k7 = key(t7);

    if (len == 8) {
      // sort values without keys
      if (k7 < k6) {
        dest[nat(offset +% 7)] := t6;
        if (k7 < k5) {
          t6 := t5;
          if (k7 < k4) {
            t5 := t4;
            if (k7 < k3) {
              t4 := t3;
              if (k7 < k2) {
                t3 := t2;
                if (k7 < k1) {
                  t2 := t1;
                  if (k7 < k0) {
                    t1 := t0;
                    t0 := t7;
                  } else t1 := t7;
                } else t2 := t7;
              } else t3 := t7;
            } else t4 := t7;
          } else t5 := t7;
        } else t6 := t7;
      } else dest[nat(offset +% 7)] := t7;

      dest[nat(offset +% 6)] := t6;
      dest[nat(offset +% 5)] := t5;
      dest[nat(offset +% 4)] := t4;
      dest[nat(offset +% 3)] := t3;
      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    // sort values and keys
    if (k7 < k6) {
      let t7_new = t6;
      let k7_new = k6;
      if (k7 < k5) {
        do { t6 := t5; k6 := k5 };
        if (k7 < k4) {
          do { t5 := t4; k5 := k4 };
          if (k7 < k3) {
            do { t4 := t3; k4 := k3 };
            if (k7 < k2) {
              do { t3 := t2; k3 := k2 };
              if (k7 < k1) {
                do { t2 := t1; k2 := k1 };
                if (k7 < k0) { t1 := t0; k1 := k0; t0 := t7; k0 := k7 } else {
                  t1 := t7; k1 := k7;
                };
              } else { t2 := t7; k2 := k7 };
            } else { t3 := t7; k3 := k7 };
          } else { t4 := t7; k4 := k7 };
        } else { t5 := t7; k5 := k7 };
      } else { t6 := t7; k6 := k7 };
      do { t7 := t7_new; k7 := k7_new };
    };

    // new element
    let index8 = nat(from +% 8);
    var t8 = buffer[index8];
    var k8 = key(t8);

    if (len == 9) {
      // sort values without keys
      if (k8 < k7) {
        dest[nat(offset +% 8)] := t7;
        if (k8 < k6) {
          t7 := t6;
          if (k8 < k5) {
            t6 := t5;
            if (k8 < k4) {
              t5 := t4;
              if (k8 < k3) {
                t4 := t3;
                if (k8 < k2) {
                  t3 := t2;
                  if (k8 < k1) {
                    t2 := t1;
                    if (k8 < k0) {
                      t1 := t0;
                      t0 := t8;
                    } else t1 := t8;
                  } else t2 := t8;
                } else t3 := t8;
              } else t4 := t8;
            } else t5 := t8;
          } else t6 := t8;
        } else t7 := t8;
      } else dest[nat(offset +% 8)] := t8;

      dest[nat(offset +% 7)] := t7;
      dest[nat(offset +% 6)] := t6;
      dest[nat(offset +% 5)] := t5;
      dest[nat(offset +% 4)] := t4;
      dest[nat(offset +% 3)] := t3;
      dest[nat(offset +% 2)] := t2;
      dest[nat(offset +% 1)] := t1;
      dest[nat(offset)] := t0;
      return;
    };

    Prim.trap("insertionSortSmallMove for len > 9 is not implemented.");
  };
};
