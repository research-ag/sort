import VarArray "mo:core/VarArray";
import Nat32 "mo:core/Nat32";
import BucketSortInternal "private/bucketSortInternal";

/// This module provides implementations of radix sort and bucket sort for sorting arrays of elements.
/// The sorts are based on a key function that maps elements to `Nat32` values.
module {
  let nat = Nat32.toNat;

  /// Sorts an array in place using bucket sort.
  ///
  /// Max `n` value id `2 ** 32 - 1`.
  ///
  /// Example:
  /// ```motoko
  /// import Sort "mo:sort/Nat32Key";
  /// import Array "mo:core/Array";
  /// import VarArray "mo:core/VarArray";
  ///
  /// // Example with a custom type
  /// type User = {
  ///   id : Nat32;
  ///   name : Text;
  /// };
  ///
  /// let users : [var User] = [var
  ///   { id = 101; name = "Alice" },
  ///   { id = 22; name = "Bob" },
  ///   { id = 75; name = "Charlie" },
  ///   { id = 5; name = "David" },
  /// ];
  ///
  /// // Sort the users by their 'id' field
  /// Sort.bucketSort<User>(users, func(user) = user.id, null);
  ///
  /// // The 'users' array is now sorted in-place
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  public func bucketSort<T>(array : [var T], key : T -> Nat32, maxInclusive : ?Nat32) {
    let radixBits : Nat32 -> Nat32 = func n = 31 - Nat32.bitcountLeadingZero(n);
    BucketSortInternal.bucketSort(array, key, maxInclusive, radixBits);
  };

  /// Sorts an array in place using radix sort.
  ///
  /// Max `n` value id `2 ** 32 - 1`.
  ///
  /// Example:
  /// ```motoko
  /// import Sort "mo:sort/Nat32Key";
  /// import Array "mo:core/Array";
  /// import VarArray "mo:core/VarArray";
  ///
  /// // Example with a custom type
  /// type User = {
  ///   id : Nat32;
  ///   name : Text;
  /// };
  ///
  /// let users : [var User] = [var
  ///   { id = 101; name = "Alice" },
  ///   { id = 22; name = "Bob" },
  ///   { id = 75; name = "Charlie" },
  ///   { id = 5; name = "David" },
  /// ];
  ///
  /// // Sort the users by their 'id' field
  /// Sort.radixSort<User>(users, func(user) = user.id, null);
  ///
  /// // The 'users' array is now sorted in-place
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  public func radixSort<T>(array : [var T], key : T -> Nat32, maxInclusive : ?Nat32) {
    let n = array.size();
    if (n <= 1) return;

    let bits : Nat32 = 32 - (
      switch (maxInclusive) {
        case (null) 0;
        case (?x) {
          if (x == 0) return;
          Nat32.bitcountLeadingZero(x);
        };
      }
    );

    let NBITS = 31 - Nat32.bitcountLeadingZero(Nat32.fromNat(n));
    let STEPS = (bits + NBITS - 1) / NBITS;

    if (STEPS > 5) {
      VarArray.sortInPlace(array, func(x, y) = Nat32.compare(key(x), key(y)));
      return;
    };

    let RADIX_BITS = (bits + STEPS - 1) / STEPS;
    let RADIX = 1 << RADIX_BITS;
    let MASK = RADIX -% 1;

    let buffer = VarArray.repeat<T>(array[0], n);
    let counts = VarArray.repeat<Nat32>(0, nat(RADIX));

    for (step in Nat32.range(0, STEPS)) {
      if (step > 0) for (i in counts.keys()) counts[i] := 0;

      let SHIFT = step * RADIX_BITS;

      if (step == 0) {
        for (x in array.vals()) counts[nat(key(x) & MASK)] +%= 1;
      } else if (step < (STEPS - 1 : Nat32)) {
        for (x in array.vals()) counts[nat((key(x) >> SHIFT) & MASK)] +%= 1;
      } else {
        for (x in array.vals()) counts[nat(key(x) >> SHIFT)] +%= 1;
      };

      var sum : Nat32 = 0;
      for (i in counts.keys()) {
        let t = counts[i];
        counts[i] := sum;
        sum +%= t;
      };

      let (from, to) = if (step % 2 == 0) (array, buffer) else (buffer, array);

      if (step == 0) {
        for (x in from.vals()) {
          let digit = nat(key(x) & MASK);
          let pos = counts[digit];
          to[nat(pos)] := x;
          counts[digit] := pos +% 1;
        };
      } else if (step < (STEPS - 1 : Nat32)) {
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

    if (STEPS % 2 != 0) for (i in array.keys()) array[i] := buffer[i];
  };
};
