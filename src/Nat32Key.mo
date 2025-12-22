import Nat32 "mo:core/Nat32";

import Bucket "private/bucket";
import Merge "private/merge";
import Radix "private/radix";

/// This module provides implementations of radix sort and bucket sort for sorting arrays of elements.
/// The sorts are based on a key function that maps elements to `Nat32` values.
module {
  /// Sorting algorithms options.
  ///
  /// `#default` means the no upper bound on key assumed.
  ///
  /// `#max` means maximal values inclusive of keys of the array.
  public type Settings = {
    #default;
    #max : Nat32;
  };

  /// Sorts an array in place using merge sort.
  ///
  /// Max `self.size()` value is `2 ** 32 - 1`.
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
  /// users.mergeSort<User>(func(user) = user.id);
  ///
  /// // The 'users' array is now sorted in-place
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
  public func mergeSort<T>(self : [var T], key : (implicit : T -> Nat32)) {
    Merge.mergeSort(self, key);
  };

  /// Sorts an array in place using bucket sort.
  ///
  /// Max `self.size()` value is `2 ** 32 - 1`.
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
  /// users.bucketSort<User>(func(user) = user.id, #default);
  ///
  /// // The 'users' array is now sorted in-place
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
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

  /// Sorts an array in place using radix sort.
  ///
  /// Max `self.size()` value is `2 ** 32 - 1`.
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
  /// users.radixSort<User>(func(user) = user.id, #default);
  ///
  /// // The 'users' array is now sorted in-place
  /// Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
  /// ```
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
