# binary-search

A generic binary search implementation that finds the transition point where a predicate switches from `false` to `true` over `core::ops` implementations.

## Overview

This library provides a binary search algorithm that finds a pair of values `(l, r)` that bracket the point where a predicate switches from `false` to `true`. Specifically, `predicate(l)` will be `false` and `predicate(r)` will be `true`.

## Usage

```rust
fn main() {
    let values = [0, 4, 5, 6, 7, 9, 456];
    
    // Find where values become >= 6
    let predicate = |&i: &usize| values[i] >= 6;
    
    let (highest_false, lowest_true) = binary_search(predicate, 0, values.len() - 1);
    
    // highest_false will be Some(2) (index of value 5)
    // lowest_true will be Some(3) (index of value 6)
    eprintln!("Highest false: {:?}", highest_false);
    eprintln!("Lowest true: {:?}", lowest_true);
}
```

## Return Values

The `binary_search` function returns a tuple of `(Option<T>, Option<T>)` with the following meanings:

- If the predicate switches from false to true within the input range, it returns `(Some(l), Some(r))` where `l` is the highest value where the predicate is false and `r` is the lowest value where the predicate is true.
- If the predicate is always true in the range, it returns `(None, Some(l))` where `l` is the bottom of the range.
- If the predicate is always false in the range, it returns `(Some(r), None)` where `r` is the top of the range.
- If the predicate is not monotonic (violates the preconditions), it may return `(None, None)` or an incorrect result.

## Example: Finding a Numeric Threshold

```rust
fn main() {
    // Find where numbers become >= 23
    let predicate = |x: &usize| *x >= 23;
    
    let (highest_false, lowest_true) = binary_search(predicate, 1, 100);
    
    // highest_false will be Some(22)
    // lowest_true will be Some(23)
    eprintln!("Highest false: {:?}", highest_false);
    eprintln!("Lowest true: {:?}", lowest_true);
}
```

## Example: Finding Cube Root

```rust
fn main() {
    // Find the cube root of 512 (which is 8)
    let predicate = |x: &u64| x.pow(3) >= 512;
    
    let (highest_false, lowest_true) = binary_search(predicate, 0, 20);
    
    // highest_false will be Some(7)
    // lowest_true will be Some(8)
    eprintln!("Highest false: {:?}", highest_false);
    eprintln!("Lowest true: {:?}", lowest_true);
}
```

## Fallible Predicates

For predicates that may fail, you can use `binary_search_fallible` which accepts a predicate that returns a `Result`:

```rust
fn main() -> Result<(), String> {
    // A predicate that could fail
    let fallible_predicate = |x: &u64| -> Result<bool, String> {
        if *x == 13 {
            return Err("Unlucky number encountered".to_string());
        }
        Ok(*x >= 10)
    };
    
    let result = binary_search_fallible(fallible_predicate, 0, 20)?;
    
    eprintln!("Result: {:?}", result);
    Ok(())
}
```

## Preconditions

For the binary search to work correctly:

1. The predicate must be "monotonic". That is, if the predicate returns true for some value `x`, it must return true for any value `y` if `y >= x`.
2. The range must be ascending (i.e. l < r). It is actually OK to reverse the order, but then the predicate must be monotonic in the opposite direction.


## Inspirations

- https://github.com/dfinity/ic/blob/master/rs/nervous_system/common/src/binary_search.rs
- https://github.com/danielwaterworth/binary-search