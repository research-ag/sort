import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Int "mo:core/Int";
import Array "mo:core/Array";
import Runtime "mo:core/Runtime";

module {
  func batcherSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat, len : Nat) {
    switch (len) {
      case (1) {
        dest[from] := buffer[from];
      };
      case (2) {
        var v0 = buffer[from];
        var v1 = buffer[from + 1];

        if (key(v0) > key(v1)) {
          dest[from] := v1;
          dest[from + 1] := v0;
        } else {
          dest[from] := v0;
          dest[from + 1] := v1;
        };
      };
      case (0) {};
      case (3) {
        var t0 = buffer[from];
        var k0 = key(t0);
        var t1 = buffer[from + 1];
        var k1 = key(t1);
        var t2 = buffer[from + 2];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
      };
      case (4) {

        var t0 = buffer[from];
        var k0 = key(t0) << 2;
        var t1 = buffer[from + 1];
        var k1 = (key(t1) << 2) ^ 1;
        var t2 = buffer[from + 2];
        var k2 = (key(t2) << 2) ^ 2;
        var t3 = buffer[from + 3];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
      };
      case (5) {

        var t0 = buffer[from];
        var k0 = key(t0) << 3;
        var t1 = buffer[from + 1];
        var k1 = (key(t1) << 3) ^ 1;
        var t2 = buffer[from + 2];
        var k2 = (key(t2) << 3) ^ 2;
        var t3 = buffer[from + 3];
        var k3 = (key(t3) << 3) ^ 3;
        var t4 = buffer[from + 4];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
      };
      case (6) {

        var t0 = buffer[from];
        var k0 = key(t0) << 3;
        var t1 = buffer[from + 1];
        var k1 = (key(t1) << 3) ^ 1;
        var t2 = buffer[from + 2];
        var k2 = (key(t2) << 3) ^ 2;
        var t3 = buffer[from + 3];
        var k3 = (key(t3) << 3) ^ 3;
        var t4 = buffer[from + 4];
        var k4 = (key(t4) << 3) ^ 4;
        var t5 = buffer[from + 5];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
      };
      case (7) {

        var t0 = buffer[from];
        var k0 = key(t0) << 3;
        var t1 = buffer[from + 1];
        var k1 = (key(t1) << 3) ^ 1;
        var t2 = buffer[from + 2];
        var k2 = (key(t2) << 3) ^ 2;
        var t3 = buffer[from + 3];
        var k3 = (key(t3) << 3) ^ 3;
        var t4 = buffer[from + 4];
        var k4 = (key(t4) << 3) ^ 4;
        var t5 = buffer[from + 5];
        var k5 = (key(t5) << 3) ^ 5;
        var t6 = buffer[from + 6];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
        dest[from + 6] := t6;
      };
      case (8) {

        var t0 = buffer[from];
        var k0 = key(t0) << 3;
        var t1 = buffer[from + 1];
        var k1 = (key(t1) << 3) ^ 1;
        var t2 = buffer[from + 2];
        var k2 = (key(t2) << 3) ^ 2;
        var t3 = buffer[from + 3];
        var k3 = (key(t3) << 3) ^ 3;
        var t4 = buffer[from + 4];
        var k4 = (key(t4) << 3) ^ 4;
        var t5 = buffer[from + 5];
        var k5 = (key(t5) << 3) ^ 5;
        var t6 = buffer[from + 6];
        var k6 = (key(t6) << 3) ^ 6;
        var t7 = buffer[from + 7];
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

        dest[from] := t0;
        dest[from + 1] := t1;
        dest[from + 2] := t2;
        dest[from + 3] := t3;
        dest[from + 4] := t4;
        dest[from + 5] := t5;
        dest[from + 6] := t6;
        dest[from + 7] := t7;
      };
      case (_) {};
    };
  };

  func insertionSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, newFrom : Nat32, len : Nat) {
    switch (len) {
      case (1) {
        let index0 = Nat32.toNat(newFrom);
        dest[index0] := buffer[index0];
      };
      case (2) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let t0 = buffer[index0];
        let t1 = buffer[index1];
        if (key(t1) < key(t0)) {
          dest[index0] := t1;
          dest[index1] := t0;
        } else {
          dest[index0] := t0;
          dest[index1] := t1;
        };
      };
      case (3) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        let t2 = buffer[index2];
        let k2 = key(t2);

        if (k1 < k0) {
          let v = t1;
          t1 := t0;
          t0 := v;
          let kk = k1;
          k1 := k0;
          k0 := kk;
        };

        if (k2 < k1) {
          if (k2 < k0) {
            dest[index0] := t2;
            dest[index1] := t0;
            dest[index2] := t1;
          } else {
            dest[index0] := t0;
            dest[index1] := t2;
            dest[index2] := t1;
          };
        } else {
          dest[index0] := t0;
          dest[index1] := t1;
          dest[index2] := t2;
        };
      };
      case (4) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
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

        if (k3 < k2) {
          tv := t3;
          t3 := t2;
          if (k3 < k1) {
            t2 := t1;
            if (k3 < k0) { t1 := t0; t0 := tv } else {
              t1 := tv;
            };
          } else { t2 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
      };
      case (5) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
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
          if (kv < k2) {
            t3 := t2;
            if (kv < k1) {
              t2 := t1;
              if (kv < k0) { t1 := t0; t0 := tv } else {
                t1 := tv;
              };
            } else { t2 := tv };
          } else { t3 := tv };
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
      };
      case (6) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
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
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
      };
      case (7) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        let index6 = Nat32.toNat(newFrom +% 6);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
        var k5 = key(t5);
        var t6 = buffer[index6];
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
        };

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
        dest[index6] := t6;
      };
      case (8) {
        let index0 = Nat32.toNat(newFrom);
        let index1 = Nat32.toNat(newFrom +% 1);
        let index2 = Nat32.toNat(newFrom +% 2);
        let index3 = Nat32.toNat(newFrom +% 3);
        let index4 = Nat32.toNat(newFrom +% 4);
        let index5 = Nat32.toNat(newFrom +% 5);
        let index6 = Nat32.toNat(newFrom +% 6);
        let index7 = Nat32.toNat(newFrom +% 7);
        var t0 = buffer[index0];
        var k0 = key(t0);
        var t1 = buffer[index1];
        var k1 = key(t1);
        var t2 = buffer[index2];
        var k2 = key(t2);
        var t3 = buffer[index3];
        var k3 = key(t3);
        var t4 = buffer[index4];
        var k4 = key(t4);
        var t5 = buffer[index5];
        var k5 = key(t5);
        var t6 = buffer[index6];
        var k6 = key(t6);
        var t7 = buffer[index7];
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

        dest[index0] := t0;
        dest[index1] := t1;
        dest[index2] := t2;
        dest[index3] := t3;
        dest[index4] := t4;
        dest[index5] := t5;
        dest[index6] := t6;
        dest[index7] := t7;
      };
      case (_) Runtime.trap("Can never happen");
    };
  };

  func next_permutation(p : [var Nat32]) : Bool {
    let n = p.size();

    func swap(i : Nat, j : Nat) {
      let x = p[i];
      p[i] := p[j];
      p[j] := x;
    };

    func reverse(from : Nat, to : Nat) {
      var a = from;
      var b = to;
      while (a < b) {
        swap(a, b);
        a += 1;
        b -= 1;
      };
    };

    var point : ?Nat = null;
    var i : Int = n - 2;
    label l while (i >= 0) {
      if (p[Int.abs(i)] < p[Int.abs(i + 1)]) {
        point := ?Int.abs(i);
        break l;
      };
      i -= 1;
    };
    switch (point) {
      case (null) {
        return false;
      };
      case (?x) {
        var i : Int = n - 1;
        label l while (i > x) {
          if (p[Int.abs(i)] > p[x]) {
            break l;
          };
          i -= 1;
        };
        swap(Int.abs(i), x);
        reverse(x + 1, n - 1);
      };
    };
    true;
  };

  func testSmall(n : Nat) {
    let p = VarArray.tabulate<Nat32>(n, func i = Nat32.fromNat(i));
    let id = Array.tabulate<Nat32>(n, func i = Nat32.fromNat(i));
    loop {
      // do {
      //   let pp = VarArray.clone(p);
      //   batcherSortSmall(pp, pp, func x = x, 0, n);
      //   if (Array.fromVarArray<Nat32>(pp) != id) Runtime.trap(debug_show pp);
      // };
      do {
        let pp = VarArray.clone(p);
        insertionSortSmall(pp, pp, func x = x, 0 : Nat32, n);
        if (Array.fromVarArray<Nat32>(pp) != id) Runtime.trap(debug_show pp);
      };
    } while (next_permutation(p));
  };

  public func init() : Bench.Bench {
    for (n in Nat.range(2, 8)) {
      testSmall(n);
    };

    let bench = Bench.Bench();

    bench.name("Sort small");
    bench.description("Compare insertion sort and batcher sort");

    let rows = [
      "insertion",
      "batcher",
    ];
    let cols = [
      "8",
      "worst",
      "best",
    ];

    bench.rows(rows);
    bench.cols(cols);

    let rng : Random.Random = Random.seed(0x5f5f5f5f5f5f5f5f);

    let a : [var Nat32] = VarArray.tabulate(8000, func(i) = Nat64.toNat32(rng.nat64() % (2 ** 29)));
    let b = VarArray.clone(a);

    let worst = VarArray.tabulate<Nat32>(8000, func i = Nat32.fromNat(8000 - i));
    let worstClone = VarArray.clone(worst);

    let best = VarArray.tabulate<Nat32>(8000, func i = Nat32.fromNat(i));
    let bestClone = VarArray.clone(best);

    bench.runner(
      func(row, col) {
        if (col == "8") {
          if (row == "insertion") {
            for (i in Nat32.range(0, 1000)) insertionSortSmall(a, a, func i = i, i * 8, 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(b, b, func i = i, i * 8, 8);
          };
        } else if (col == "worst") {
          if (row == "insertion") {
            for (i in Nat32.range(0, 1000)) insertionSortSmall(worst, worst, func i = i, i * 8, 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(worstClone, worstClone, func i = i, i * 8, 8);
          };
        } else {
          if (row == "insertion") {
            for (i in Nat32.range(0, 1000)) insertionSortSmall(best, best, func i = i, i * 8, 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(bestClone, bestClone, func i = i, i * 8, 8);
          };
        };
      }
    );

    bench;
  };
};
