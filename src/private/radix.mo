import Nat32 "mo:core/Nat32";
import VarArray "mo:core/VarArray";
import Merge "merge";
import Insertion "insertion";
import Prim "mo:⛔";

module {
  let nat = Prim.nat32ToNat;

  public func withStepsRadix<T>(self : [var T], key : T -> Nat32, totalBits : Nat32, steps : Nat32, radixBits : Nat32) {
    debug assert totalBits > 0;
    debug assert steps * radixBits >= totalBits;
    debug assert (steps - 1) * radixBits < totalBits;

    let RADIX = 1 << radixBits;
    let MASK = RADIX -% 1;

    let buffer = VarArray.repeat<T>(self[0], self.size());
    let counts = VarArray.repeat<Nat32>(0, nat(RADIX));

    for (step in Nat32.range(0, steps)) {
      if (step > 0) for (i in counts.keys()) counts[i] := 0;

      let SHIFT = step * radixBits;

      if (steps == 1) {
        for (x in self.vals()) counts[nat(key(x))] +%= 1;
      } else if (step == 0) {
        for (x in self.vals()) counts[nat(key(x) & MASK)] +%= 1;
      } else if (step < (steps - 1 : Nat32)) {
        for (x in self.vals()) counts[nat((key(x) >> SHIFT) & MASK)] +%= 1;
      } else {
        for (x in self.vals()) counts[nat(key(x) >> SHIFT)] +%= 1;
      };

      var sum : Nat32 = 0;
      for (i in counts.keys()) {
        let t = counts[i];
        counts[i] := sum;
        sum +%= t;
      };

      debug assert nat(sum) == self.size();

      let (from, to) = if (step % 2 == 0) (self, buffer) else (buffer, self);

      if (steps == 1) {
        for (x in from.vals()) {
          let digit = nat(key(x));
          let pos = counts[digit];
          to[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else if (step == 0) {
        for (x in from.vals()) {
          let digit = nat(key(x) & MASK);
          let pos = counts[digit];
          to[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else if (step < (steps - 1 : Nat32)) {
        for (x in from.vals()) {
          let digit = nat((key(x) >> SHIFT) & MASK);
          let pos = counts[digit];
          to[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else {
        for (x in from.vals()) {
          let digit = nat(key(x) >> SHIFT);
          let pos = counts[digit];
          to[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      };
    };

    if (steps % 2 != 0) for (i in self.keys()) self[i] := buffer[i];
  };

  public func radixSort<T>(self : [var T], key : (implicit : T -> Nat32), max : ?Nat32) {
    let n = self.size();
    if (n <= 1) return;
    if (n <= 2) {
      if (key(self[1]) < key(self[0])) {
        let t0 = self[0];
        self[0] := self[1];
        self[1] := t0;
      };
      return;
    };
    if (n <= 8) {
      Insertion.insertionSortSmall(self, self, key, 0 : Nat32, Nat32.fromNat(n));
      return;
    };

    let totalBits : Nat32 = 32 - (
      switch (max) {
        case (null) 0;
        case (?x) {
          if (x == 0) return;
          Nat32.bitcountLeadingZero(x);
        };
      }
    );

    let NBITS = 31 - Nat32.bitcountLeadingZero(Nat32.fromNat(n));
    debug assert NBITS > 0;
    let STEPS = (totalBits + NBITS - 1) / NBITS;

    if (STEPS > 3) {
      Merge.mergeSort(self, key);
      return;
    };

    let RADIX_BITS = (totalBits + STEPS - 1) / STEPS;
    withStepsRadix(self, key, totalBits, STEPS, RADIX_BITS);
  };
}