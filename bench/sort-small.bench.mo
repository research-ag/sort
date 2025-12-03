import Bench "mo:bench";
import Random "mo:core/Random";
import Nat "mo:core/Nat";
import Nat64 "mo:core/Nat64";
import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";

module {
  func insertionSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat) {
    var t0 = buffer[from];
    var k0 = key(t0);
    var t1 = buffer[from + 1];
    var k1 = key(t1);
    var t2 = buffer[from + 2];
    var k2 = key(t2);
    var t3 = buffer[from + 3];
    var k3 = key(t3);
    var t4 = buffer[from + 4];
    var k4 = key(t4);
    var t5 = buffer[from + 5];
    var k5 = key(t5);
    var t6 = buffer[from + 6];
    var k6 = key(t6);
    var t7 = buffer[from + 7];
    var k7 = key(t7);

    if (k1 < k0) {
      let v = t1;
      t1 := t0;
      t0 := v;
      let k = k1;
      k1 := k0;
      k0 := k;
    };

    var tv = t2;
    var kv = k2;
    if (kv < k1) {
      t2 := t1;
      k2 := k1;
      if (kv < k0) {
        t1 := t0;
        k1 := k0;
        t0 := tv;
        k0 := kv;
      } else {
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
        if (kv < k0) {
          t1 := t0;
          k1 := k0;
          t0 := tv;
          k0 := kv;
        } else {
          t1 := tv;
          k1 := kv;
        };
      } else {
        t2 := tv;
        k2 := kv;
      };
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
          if (kv < k0) {
            t1 := t0;
            k1 := k0;
            t0 := tv;
            k0 := kv;
          } else {
            t1 := tv;
            k1 := kv;
          };
        } else {
          t2 := tv;
          k2 := kv;
        };
      } else {
        t3 := tv;
        k3 := kv;
      };
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
            if (kv < k0) {
              t1 := t0;
              k1 := k0;
              t0 := tv;
              k0 := kv;
            } else {
              t1 := tv;
              k1 := kv;
            };
          } else {
            t2 := tv;
            k2 := kv;
          };
        } else {
          t3 := tv;
          k3 := kv;
        };
      } else {
        t4 := tv;
        k4 := kv;
      };
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
              if (kv < k0) {
                t1 := t0;
                k1 := k0;
                t0 := tv;
                k0 := kv;
              } else {
                t1 := tv;
                k1 := kv;
              };
            } else {
              t2 := tv;
              k2 := kv;
            };
          } else {
            t3 := tv;
            k3 := kv;
          };
        } else {
          t4 := tv;
          k4 := kv;
        };
      } else {
        t5 := tv;
        k5 := kv;
      };
    };

    tv := t7;
    kv := k7;
    if (kv < k6) {
      t7 := t6;
      k7 := k6;
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
                if (kv < k0) {
                  t1 := t0;
                  k1 := k0;
                  t0 := tv;
                  k0 := kv;
                } else {
                  t1 := tv;
                  k1 := kv;
                };
              } else {
                t2 := tv;
                k2 := kv;
              };
            } else {
              t3 := tv;
              k3 := kv;
            };
          } else {
            t4 := tv;
            k4 := kv;
          };
        } else {
          t5 := tv;
          k5 := kv;
        };
      } else {
        t6 := tv;
        k6 := kv;
      };
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

  func batcherSortSmall<T>(buffer : [var T], dest : [var T], key : T -> Nat32, from : Nat) {
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

  public func init() : Bench.Bench {
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
            for (i in Nat.range(0, 1000)) insertionSortSmall(a, a, func i = i, i * 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(b, b, func i = i, i * 8);
          };
        } else if (col == "worst") {
          if (row == "insertion") {
            for (i in Nat.range(0, 1000)) insertionSortSmall(worst, worst, func i = i, i * 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(worstClone, worstClone, func i = i, i * 8);
          };
        } else {
          if (row == "insertion") {
            for (i in Nat.range(0, 1000)) insertionSortSmall(best, best, func i = i, i * 8);
          } else {
            for (i in Nat.range(0, 1000)) batcherSortSmall(bestClone, bestClone, func i = i, i * 8);
          };
        };
      }
    );

    bench;
  };
};
