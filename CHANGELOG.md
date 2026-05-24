# Sort changelog

## 0.0.2

- Added comprehensive doc strings to the public API in `src/Nat32Key.mo` and brief doc strings to the internal modules in `src/private/`.
- Bumped dependency `core` from `2.0.0` to `2.5.0`.
- Raised `[requirements] moc` from `1.0.0` to `1.6.0` to match the minimum required by `core@2.5.0`.
- Fixed `M0244` warnings in `src/private/insertion.mo` by changing four unreassigned `var` bindings to `let`.

## 0.0.1

- Initial version for `VarArray` and `Nat32` keys
- `bucketSort`
- `radixSort`
- `mergeSort`
