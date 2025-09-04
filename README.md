# binary-search

A generic binary search implementation that finds the transition point where a predicate switches from `false` to `true` over `core` traits implementations.

Correctness, soundenss and panic safety are priority over performance. 

## Overview

This library provides a binary search algorithm that returns a `Mid<T>` describing the relationship of the search range to the transition point where a predicate switches from `false` to `true`:

- `Mid::Switches { l, r }`: the predicate switches within the range, with `predicate(l) == false`, `predicate(r) == true`, and `l < r`.
- `Mid::True { l }`: the predicate is always true; `l` is the bottom of the range.
- `Mid::False { r }`: the predicate is always false; `r` is the top of the range.
- `Mid::NonMonotonic`: detected a violation of the monotonicity precondition or invalid inputs.

## Usage

```rust
fn main() {
    let values = [0, 4, 5, 6, 7, 9, 456];

    // Find where values become >= 6
    let predicate = |&i: &usize| values[i] >= 6;

    match binary_search(predicate, 0, values.len() - 1) {
        Mid::Switches { l, r } => {
            // l == 2 (index of 5), r == 3 (index of 6)
            eprintln!("highest false index: {}", l);
            eprintln!("lowest true index: {}", r);
        }
        Mid::True { l } => {
            eprintln!("always true; bottom of range: {}", l);
        }
        Mid::False { r } => {
            eprintln!("always false; top of range: {}", r);
        }
        Mid::NonMonotonic => {
            eprintln!("predicate not monotonic over range");
        }
    }
}
```

## Return Values

`binary_search` returns a `Mid<T>`:

- `Mid::Switches { l, r }`: brackets the transition (`p(l) == false`, `p(r) == true`).
- `Mid::True { l }`: predicate is always true; `l` is the bottom of the range.
- `Mid::False { r }`: predicate is always false; `r` is the top of the range.
- `Mid::NonMonotonic`: precondition (monotonicity) was violated or inputs were invalid.

## Example: Finding a Numeric Threshold

```rust
fn main() {
    // Find where numbers become >= 23
    let predicate = |x: &usize| *x >= 23;

    match binary_search(predicate, 1, 100) {
        Mid::Switches { l, r } => {
            // l == 22, r == 23
            eprintln!("highest false: {}", l);
            eprintln!("lowest true: {}", r);
        }
        _ => unreachable!("predicate switches in this range"),
    }
}
```

## Example: Finding Cube Root

```rust
fn main() {
    // Find the cube root of 512 (which is 8)
    let predicate = |x: &u64| x.pow(3) >= 512;

    match binary_search(predicate, 0, 20) {
        Mid::Switches { l, r } => {
            // l == 7, r == 8
            eprintln!("highest false: {}", l);
            eprintln!("lowest true: {}", r);
        }
        _ => unreachable!("predicate switches in this range"),
    }
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

    match binary_search_fallible(fallible_predicate, 0, 20)? {
        Mid::Switches { l, r } => {
            eprintln!("highest false: {} / lowest true: {}", l, r);
        }
        Mid::True { l } => eprintln!("always true from {}", l),
        Mid::False { r } => eprintln!("always false until {}", r),
        Mid::NonMonotonic => eprintln!("non monotonic or invalid range"),
    }

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
