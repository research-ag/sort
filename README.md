# sort

An optimized merge sort, radix sort and bucket sort implementations for Motoko. Each algorithm is **stable**, i.e. for equal elements their relarive order is preserved.

## What is Radix Sort and Bucket Sort?

Radix sort is a non-comparative sorting algorithm that sorts integers by processing individual digits. It has a time complexity of `O(d * (n + b))`, where `d` is the number of digits, `n` is the number of elements, and `b` is the base of the number system. This makes it significantly faster than comparison-based sorting algorithms (like quicksort or mergesort) for sorting by `Nat32` keys (or other finite non-negative integer).

Bucket sort version presented splits data into `2 ** m` buckets where `m` is maximal possible such that `2 ** m <= array.size()`, and sorts buckets with the same algorithm recursively with loop unrolled insertion sort for buckets of size less than or equal to 8. It works in `O(n)` for uniform random distribution.

Merge sort is a divide-and-conquer sorting algorithm that repeatedly splits the input into two halves, recursively sorts each half, and then merges the two sorted halves by repeatedly taking the smaller front element from each; this yields `O(n log n)` time in best, average, and worst cases, is stable, and (for array-based implementations) requires `O(n)` extra space.

## Install

```bash
mops add sort
```

## Usage

The library provides three sorting functions: `mergeSort`, `radixSort` and `bucketSort`. For most use cases, `radixSort` is the recommended choice.

```motoko
import Sort "mo:sort/Nat32Key";
import Array "mo:core/Array";
import VarArray "mo:core/VarArray";

// Example with a custom type
type User = {
  id : Nat32;
  name : Text;
};

let users : [var User] = [var
  { id = 101; name = "Alice" },
  { id = 22; name = "Bob" },
  { id = 75; name = "Charlie" },
  { id = 5; name = "David" },
];

// Sort the users by their 'id' field
users.radixSort<User>(func(user) = user.id, null);

// The 'users' array is now sorted in-place
Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
```

## API

### `func radixSort<T>(self : [var T], key : (implicit : T -> Nat32), maxInclusive : ?Nat32)`

Sorts the given array in-place using an iterative radix sort algorithm. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.
*   `maxInclusive`: An optional `Nat32` value representing the maximum possible value of the key. Providing this value can optimize the sorting process by tailoring the number of bits to consider. If `null` is passed, the sort will consider all 32 bits of the key.

### `func bucketSort<T>(self : [var T], key : (implicit : T -> Nat32), maxInclusive : ?Nat32)`

Sorts the given array in-place using a recursive bucket sort. This implementation is highly optimized for random data but may be slightly slower than `radixSort` in the general case. The algorithm is **stable**.

*   Parameters are the same as `radixSort`.

### `func mergeSort<T>(self : [var T], key : (implicit : T -> Nat32))`

Sorts the given array in-place using a recursive merge sort. This implementation allocates buffer of type `T` of `self.size() / 2`, not `self.size()`. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.

## Performance

This library is heavily optimized for performance. The benchmarks in the `bench/` directory show that it significantly outperforms the standard library's `Array.sort` for large arrays of integers. The `bucketSort` implementation includes specific optimizations for small buckets, using insertion sort-like networks to minimize recursion overhead.

## Copyright

MR Research AG, 2025
## Authors

Main author: Andrii Stepanov (AStepanov25)
Contributor: Timo Hanke (timohanke)
## License

Apache-2.0