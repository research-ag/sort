[![mops](https://oknww-riaaa-aaaam-qaf6a-cai.raw.ic0.app/badge/mops/sort)](https://mops.one/sort)

# sort

Optimized merge sort, radix sort, and bucket sort implementations for Motoko. Each algorithm is **stable**, i.e., for equal elements, their relative order is preserved.

## What are Radix Sort, Bucket Sort, and Merge Sort?

Currently, we provide only sorting by `Nat32` key, but different key types as well as additional sorting algorithms can be added to the package in the future.

### Radix sort

Radix sort is a non-comparative sorting algorithm that sorts integers by processing individual digits.

It has a time complexity of `O(steps * (n + radix))` and memory complexity of `O(radix + n)`, where `steps` is the number of digits, `n` is the number of elements, and `radix` is the base of the number system.

* We choose `radix` as the maximal power of 2 less than or equal to `n` (with some stipulations; see the code for details).
* We choose `steps` to be minimal so that `max >= radix ** steps`, where `max` is either the value from `settings` or `2 ** 32`.

This makes it significantly faster than comparison-based sorting algorithms (like quicksort or mergesort) for sorting by `Nat32` keys (or other finite non-negative integers).

### Bucket sort

Bucket sort splits data into `2 ** m` buckets, where `m` is the maximal value such that `2 ** m <= array.size()`, and sorts buckets recursively, using an unrolled insertion sort for buckets of size less than or equal to 8. For uniformly random keys, it works in `O(n)` expected time and `O(n)` expected memory complexity. The worst-case time complexity as well as the worst-case memory complexity is `O(steps * n)`, where `steps` is calculated in the same way as in radix sort (see above). 

### Merge sort

Merge sort is a divide-and-conquer sorting algorithm that repeatedly splits the input into two halves, recursively sorts each half, and then merges the two sorted halves by repeatedly taking the smaller front element from each. This yields `O(n log n)` time in best, average, and worst cases, is stable, and (for array-based implementations) requires `O(n / 2)` extra space.

### How to choose?

* `radixSort`: Recommended choice for `Nat32` keys; equally fast on average and worst cases.
* `bucketSort`: Best for uniformly random keys; worst-case is slower.
* `mergeSort`: Has the lowest memory overhead; only a buffer of size `array.size() / 2` of type `T` is needed.

Provide the `max` parameter in `settings` if there is a known upper bound on key values for radix and bucket sorts; this will speed up the code.

See the performance section below.

## Install

```bash
mops add sort
```

## Usage

The library provides three sorting functions: `mergeSort`, `radixSort`, and `bucketSort`. For most use cases, `radixSort` is the recommended choice.

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

users.radixSort<User>(func(user) = user.id, #default);

// users.radixSort<User>(func(user) = user.id, #max 101);

// users.bucketSort<User>(func(user) = user.id, #default);
// users.bucketSort<User>(func(user) = user.id, #max 101);

// users.mergeSort<User>(func(user) = user.id);

// Or with implicit key

func key(u : User) : Nat32 = u.id;

// users.radixSort<User>(#default);
// users.bucketSort<User>(#default);

// users.radixSort<User>(#max 101);
// users.bucketSort<User>(#max 101);

// users.mergeSort<User>();

// The 'users' array is now sorted in-place
Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
```

## API

### `func radixSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings)`

Sorts the given array in-place using an iterative radix sort algorithm. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.
*   `settings`: See below.

### `func bucketSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings)`

Sorts the given array in-place using a recursive bucket sort. This implementation is highly optimized for random data but may be slightly slower than `radixSort` in the general case. The algorithm is **stable**.

*   Parameters are the same as `radixSort`.

### `func mergeSort<T>(self : [var T], key : (implicit : T -> Nat32))`

Sorts the given array in-place using a recursive merge sort. This implementation allocates a buffer of type `T` of size `self.size() / 2`, not `self.size()`. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.

### `type Settings`

Sorting algorithm options.

* `#default` means no upper bound on key is assumed.
* `#max v` means `v` is an upper bound (inclusive) for the value of all keys occurring in the input array.

**Note**: The maximum allowed input size (`self.size()`) is `2 ** 32 - 1` for all the algorithms.

## Performance

This library is heavily optimized for performance. The benchmarks in the `bench/` directory show that it significantly outperforms the standard library's `Array.sort` for large arrays of integers. The `bucketSort` implementation includes specific optimizations for small buckets, using unrolled stack-based insertion-sort code to minimize recursion overhead.

### Instructions

|                     |     100 |      1000 |      10000 |      100000 |       1000000 |
| :------------------ | ------: | --------: | ---------: | ----------: | ------------: |
| bucketSort          |  43_872 |   417_375 |  4_166_215 |  41_198_139 |   410_992_567 |
| bucketSortWorstCase | 222_150 | 1_190_243 |  9_652_639 |  94_272_975 |   564_592_363 |
| radixSort           |  66_411 | 1_036_675 |  8_819_675 |  63_920_821 |   526_519_803 |
| mergeSort           |  66_577 | 1_036_841 | 15_445_103 | 193_077_729 | 2_318_504_400 |
| VarArray            | 206_451 | 2_682_815 | 35_811_320 | 442_388_549 | 5_046_583_599 |

### Garbage Collection

|                     |      100 |      1000 |      10000 |     100000 |   1000000 |
| :------------------ | -------: | --------: | ---------: | ---------: | --------: |
| bucketSort          |    872 B |  5.24 KiB |   55.4 KiB | 518.96 KiB |  4.82 MiB |
| bucketSortWorstCase | 1.54 KiB |  8.27 KiB |  72.41 KiB | 646.99 KiB |  4.88 MiB |
| radixSort           |    536 B |  2.28 KiB |  47.44 KiB |    647 KiB |  4.07 MiB |
| mergeSort           |    536 B |  2.28 KiB |  19.86 KiB | 195.64 KiB |  1.91 MiB |
| VarArray            |    736 B |  4.23 KiB |  39.39 KiB | 390.95 KiB |  3.82 MiB |

## Contributing

Contributions, bug reports, and feature requests are welcome! Please open an issue or pull request on [GitHub](https://github.com/research-ag/sort).

## Copyright

MR Research AG, 2025

## Authors

Main author: Andrii Stepanov (AStepanov25)

Contributor: Timo Hanke (timohanke)

## License

This project is licensed under the Apache-2.0 license.