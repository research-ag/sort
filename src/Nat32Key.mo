/// In-place sorting of mutable arrays (`[var T]`) by a `Nat32`-valued key function.
///
/// This module provides three implementations — merge sort, bucket sort, and radix
/// sort. All three sort `self` in place and take the same key function
/// (`key : T -> Nat32`). The `bucketSort` and `radixSort` variants additionally
/// accept a `Settings` value: when the caller knows an inclusive upper bound on
/// the keys, passing it via `#max` lets these algorithms skip work on the unused
/// high bits and run faster.
///
/// All three sorts accept arrays whose length fits in a `Nat32` — i.e. up to
/// `2 ** 32 - 1` elements. They are not guaranteed to be stable: elements with
/// equal keys may be reordered relative to each other.
///
/// ```motoko name=import
/// import Sort "mo:sort/Nat32Key";
/// ```

import Nat32 "mo:core/Nat32";

import Bucket "private/bucket";
import Merge "private/merge";
import Radix "private/radix";

module {
  /// Optional bound on the keys, consumed by `bucketSort` and `radixSort`.
  ///
  /// - `#default` — no upper bound assumed; the algorithm considers the full
  ///   32-bit key range.
  /// - `#max m` — the caller asserts that every element's key satisfies
  ///   `key(elem) <= m`. A tight bound makes the sort faster because fewer
  ///   high bits need to be processed. If any key exceeds `m`, the result is
  ///   undefined and the function may trap.
  public type Settings = {
    #default;
    #max : Nat32;
  };

  /// Sorts `self` in place by `key` using merge sort.
  ///
  /// Allocates an auxiliary buffer of `self.size() / 2` elements. Cost is
  /// `O(n log n)` comparisons regardless of the key distribution; use this
  /// when you have no upper bound on the keys or when `radixSort` would
  /// require more than three passes (in which case `radixSort` itself
  /// delegates here).
  ///
  /// ```motoko include=import
  /// import Array "mo:core/Array";
  /// import VarArray "mo:core/VarArray";
  ///
  /// type User = { id : Nat32; name : Text };
  ///
  /// let users : [var User] = [var
  ///   { id = 101; name = "Alice" },
  ///   { id = 22;  name = "Bob" },
  ///   { id = 75;  name = "Charlie" },
  ///   { id = 5;   name = "David" },
  /// ];
  ///
  /// users.mergeSort<User>(func(user) = user.id);
  ///
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  ///
  /// Traps if `self.size() > 2 ** 32 - 1`.
  public func mergeSort<T>(self : [var T], key : (implicit : T -> Nat32)) {
    Merge.mergeSort(self, key);
  };

  /// Sorts `self` in place by `key` using bucket sort.
  ///
  /// `settings` is either `#default` (no upper bound on keys) or `#max m`
  /// (every key is `<= m`). Supplying a tight `#max` makes the sort faster
  /// by limiting the number of bits that have to be partitioned.
  ///
  /// Allocates an auxiliary buffer the same size as `self`. Small arrays
  /// (`self.size() <= 16`) bypass bucketing and use insertion/merge sort
  /// internally.
  ///
  /// ```motoko include=import
  /// import Array "mo:core/Array";
  /// import VarArray "mo:core/VarArray";
  ///
  /// type User = { id : Nat32; name : Text };
  ///
  /// let users : [var User] = [var
  ///   { id = 101; name = "Alice" },
  ///   { id = 22;  name = "Bob" },
  ///   { id = 75;  name = "Charlie" },
  ///   { id = 5;   name = "David" },
  /// ];
  ///
  /// users.bucketSort<User>(func(user) = user.id, #max 101);
  ///
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  ///
  /// Traps if `self.size() > 2 ** 32 - 1`. If `settings = #max m` and any
  /// element's key exceeds `m`, the result is undefined (the sort may
  /// silently produce a wrongly ordered array).
  public func bucketSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings) {
    Bucket.bucketSort(
      self,
      key,
      switch (settings) {
        case (#default) null;
        case (#max x) ?x;
      },
      func n = 30 - Nat32.min(Nat32.bitcountLeadingZero(n), 29),
    );
  };

  /// Sorts `self` in place by `key` using radix sort.
  ///
  /// `settings` is either `#default` (no upper bound on keys) or `#max m`
  /// (every key is `<= m`). A tight `#max` lets radix sort use fewer passes.
  /// If the chosen parameters would require more than three passes, this
  /// function delegates to `mergeSort` instead.
  ///
  /// Allocates an auxiliary buffer the same size as `self`. Small arrays
  /// (`self.size() <= 8`) bypass radix and use insertion sort internally.
  ///
  /// ```motoko include=import
  /// import Array "mo:core/Array";
  /// import VarArray "mo:core/VarArray";
  ///
  /// type User = { id : Nat32; name : Text };
  ///
  /// let users : [var User] = [var
  ///   { id = 101; name = "Alice" },
  ///   { id = 22;  name = "Bob" },
  ///   { id = 75;  name = "Charlie" },
  ///   { id = 5;   name = "David" },
  /// ];
  ///
  /// users.radixSort<User>(func(user) = user.id, #max 101);
  ///
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  ///
  /// Traps if `self.size() > 2 ** 32 - 1`. If `settings = #max m` and any
  /// element's key exceeds `m`, the result is undefined and the function
  /// may trap with an out-of-bounds index error.
  public func radixSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings) {
    Radix.radixSort(
      self,
      key,
      switch (settings) {
        case (#default) null;
        case (#max x) ?x;
      },
    );
  };
};
