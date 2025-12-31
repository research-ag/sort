[![mops](https://oknww-riaaa-aaaam-qaf6a-cai.raw.ic0.app/badge/mops/sort)](https://mops.one/sort)
[![documentation](https://oknww-riaaa-aaaam-qaf6a-cai.raw.ic0.app/badge/documentation/sort)](https://mops.one/sort/docs)

# sort

Optimized merge sort, radix sort, and bucket sort implementations for Motoko.
All algorithms are **stable**, i.e. equal elements have their relative order preserved during sorting.

## What are Radix Sort, Bucket Sort, and Merge Sort?

Currently, we provide only sorting by `Nat32` key, but different key types can be added by request.
Additional sorting algorithms may also be added over time.

Radix sort and bucket sort are counting based (not comparison based) and have complexity `O(n * d)`
where `n` is the input size and `d` is the key length in bits.
They are faster than comparison-based sorting algorithms like quicksort or mergesort but are only possible for key types that have "digits".

Merge sort is comparison based and has complexity `O(n log n)`.
It is possible for all key types that allow comparison,
though this package only implements it for `Nat32` keys.

### Radix sort

Radix sort is a non-comparative sorting algorithm that sorts integers by processing some bits at a time (the "radix bits").
Starting at the lower bits,
it does multiple iterations over the data (called "steps") until all bits are processed.

Our implementation automatically chooses radix bits and steps based on the input size. 
The time complexity of our algorithm is `O(n * steps)`.
Memory use for scratch space and counting array is expected to be `3/2 * n` 
but, due to increase in discrete steps, can vary between `n` and `2*n` in practice.

The user can specify the maximal occurring key value in the `settings` argument.
By default the algorithm will assume that the entire `Nat32` key space can occur.
A lower maximal key value can speed up the algorithm and reduce memory because less key bits have to be processed.

Since all bits are processed equally, the time complexity does not depend on the distribution of keys.
This is why radix sort is the recommended algorithm choice in the general case.

### Bucket sort

Bucket sort is a non-comparative sorting algorithm that sorts integers by sorting them into "buckets" first, and then recursively sorting the buckets.
The sorting into buckets is based on some of the key's bits.
Unlike radix sort, bucket sort starts with the highest bits first.

Our implementation automatically chooses the number of buckets based on the input size.
The time complexity is the same as for radix sort, `O(n * steps)`,
where "steps" now refers to the number of recursion levels.
Memory use for scratch space and counting array is expected to be around `3/2 * n`.
If recursion happens, for example because of non-uniform key input,
then the memory use can increase depending on the bucket sizes.

Bucket sort can be faster than radix sort because sorting small buckets is highly optimized with inlined code.
This is most noticeable on input with uniformly distributed keys.
Hence, bucket sort is the recommended algorithm choice in the case of uniformly distributed keys.

Bucket sort can be slower than radix sort on highly non-uniform input, for example if all keys fall in the same bucket.

The user can specify the maximal occurring key value in the `settings` argument.
This is useful if the keys are uniformly distributed in their range
but the range is smaller than the entire `Nat32` key space.
By default the algorithm will assume that the entire `Nat32` key space can occur.

### Merge sort

Merge sort is a divide-and-conquer sorting algorithm that repeatedly splits the input into two halves, recursively sorts each half, and then merges the two sorted halves.

Our implementation has time complexity of `O(n log n)`.
Memory use for scratch space is `n / 2`. 

### How to choose?

* `radixSort`: Recommended choice for the general case (arbitrary key distribution).
Equally fast on average and worst cases.
* `bucketSort`: Recommended choice for uniformly distributed random keys. Worst-case is slower than radix sort.
* `mergeSort`: Recommended choice if absolute lowest memory overhead is desired. 

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

// Same with specifying the max key value
users.radixSort<User>(func(user) = user.id, #max 101);

// Same with bucket sort 
users.bucketSort<User>(func(user) = user.id, #default);
users.bucketSort<User>(func(user) = user.id, #max 101);

// Same with merge sort
users.mergeSort<User>(func(user) = user.id);

// All of the above with implicit key definition
func key(u : User) : Nat32 = u.id;
users.radixSort<User>(#default);
users.bucketSort<User>(#default);
users.radixSort<User>(#max 101);
users.bucketSort<User>(#max 101);
users.mergeSort<User>();

// The 'users' array is now sorted in-place
Array.fromVarArray(VarArray.map(users, func(user) = user.name)) == ["David", "Bob", "Charlie", "Alice"]
```

## API

### radixSort

```motoko
func radixSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings)
```

Sorts the given array in-place using an iterative radix sort algorithm. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.
*   `settings`: See below.

### bucketSort

```motoko
func bucketSort<T>(self : [var T], key : (implicit : T -> Nat32), settings : Settings)
```

Sorts the given array in-place using a recursive bucket sort. This implementation is highly optimized for random data but may be slightly slower than `radixSort` in the general case. The algorithm is **stable**.

*   Parameters are the same as `radixSort`.

### mergeSort

```motoko
func mergeSort<T>(self : [var T], key : (implicit : T -> Nat32))
```

Sorts the given array in-place using a recursive merge sort. This implementation allocates a buffer of type `T` of size `self.size() / 2`, not `self.size()`. The algorithm is **stable**.

*   `self`: The array to be sorted.
*   `key`: A function that extracts a `Nat32` key from an element of the array. The array will be sorted based on this key.

### Settings

```motoko
public type Settings = {
  #default;
  #max : Nat32;
};
```
  
Sorting algorithm options.

* `#default` means no upper bound on key is assumed.
* `#max v` means `v` is an upper bound (inclusive) for the value of all keys occurring in the input array.

**Note**: The maximum allowed input size, `self.size()`, is `2 ** 32 - 1` for all the algorithms.

## Performance

This library is heavily optimized for performance. The benchmarks in the `bench/` directory show that it significantly outperforms the core library's `Array.sort` for large arrays of integers. The `bucketSort` implementation includes specific optimizations for small buckets, using unrolled stack-based insertion-sort code to minimize recursion overhead.

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