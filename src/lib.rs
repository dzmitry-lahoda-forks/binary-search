use core::{
    cmp::{Ord, PartialEq},
    convert::From,
    marker::Copy,
    ops::{Add, BitAnd, BitXor, Div, Shr, Sub},
};

/// # Returns
///
/// - `Some(value)` halfway between `a` and `b`, rounded to -infinity.
///
/// - `None`` there is no value between `a` and `b`.
///
/// # Performance
///
/// Ensures orders of inputs and ensures there is middle number not equal to either of the inputs.
///
/// Other than that it is fast as https://docs.rs/num-integer/latest/src/num_integer/average.rs.html#45
///
/// # Safety
///
/// ## Panics
///
/// Does not panic, assuming correct trait implementations for `T`.
#[inline]
fn mid_copy<T>(a: T, b: T) -> Option<T>
where
    T: Copy
        + Ord
        + PartialEq
        + Add<Output = T>
        + Sub<Output = T>
        + BitAnd<Output = T>
        + BitXor<Output = T>
        + Shr<Output = T>
        + From<u8>,
{
    let (small, large) = if a <= b { (a, b) } else { (b, a) };
    let mid_value = (small & large) + ((small ^ large) >> T::from(1));
    if mid_value == small {
        None
    } else {
        Some(mid_value)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Mid<T> {
    /// - If the predicate is not monotonic, the function may return an incorrect
    ///   result, or return this.    
    NonMonotonic,
    /// - If the predicate is monotonic and always true, the function will return
    ///   this where `l` is the bottom of the range
    True { l: T },

    /// - If the predicate is monotonic and switches from false to true within the
    ///   input range, the function will return this, where `l` is the
    ///   highest value where the `predicate` is false and `r`` is the lowest value where
    ///   the predicate is true.
    Switches { l: T, r: T },

    /// - If the predicate is monotonic and always false, the function will return
    ///   this where `r` is the top of the range.
    False { r: T },
}

/// Performs a binary search to find the point where a predicate `p` switches
/// from `false` to `true`. Returns a [`Mid`] describing the outcome:
/// - [`Mid::Switches { l, r }`]: `p(l)` is `false` and `p(r)` is `true`, and `l < r`.
/// - [`Mid::True { l }`]: the predicate is always true in the given range; `l` is the bottom of the range.
/// - [`Mid::False { r }`]: the predicate is always false in the given range; `r` is the top of the range.
/// - [`Mid::NonMonotonic`]: detected violation of monotonicity or invalid inputs.
///
/// The function takes a range and a predicate.
/// Preconditions:
/// * It requires that the predicate is "monotonic". That is, if the predicate
///   returns true for some value `x`, it must return true for any value
///   `y` if `y >= x`.
/// * The range must be ascending (i.e. l < r). It is actually OK to reverse
///   the order, but then the predicate must be monotonic in the opposite
///   direction (i.e. once it returns false for `x` it must return false for any
///   value `y` if `y >= x`)
///
#[inline]
pub fn binary_search<T, G>(predicate: G, l: T, r: T) -> Mid<T>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Ord
        + Copy
        + From<u8>
        + BitAnd<Output = T>
        + BitXor<Output = T>
        + Shr<Output = T>,
    G: Fn(&T) -> bool,
{
    let predicate = move |x: &T| Ok::<bool, ()>(predicate(x));
    binary_search_fallible(predicate, l, r).unwrap() // can never fail because p is infallible
}

/// Like `binary_search`, but takes a predicate that returns a Result. If the predicate
/// returns an error while performing the binary search, this function returns
/// an error.
#[inline]
pub fn binary_search_fallible<T, G, E>(
    predicate: G,
    mut l: T,
    mut r: T,
) -> Result<Mid<T>, E>
where
    T: Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Ord
        + Copy
        + From<u8>
        + BitAnd<Output = T>
        + BitXor<Output = T>
        + Shr<Output = T>,
    G: Fn(&T) -> Result<bool, E>,
{
    match (predicate(&l)?, predicate(&r)?) {
        (false, true) => {}
        // Check if the predicate is "always true" or "always false" and return
        // early if so.
        (true, true) => return Ok(Mid::True { l }),
        (false, false) => return Ok(Mid::False { r }),
        // Sanity check that will detect some non-monotonic functions. This is a
        // precondition violation.
        (true, false) => return Ok(Mid::NonMonotonic),
    }
    loop {
        // Sanity check: f must be false for l and true for r, otherwise
        // the input function was not monotonic
        if predicate(&l)? {
            return Ok(Mid::NonMonotonic);
        }
        if !predicate(&r)? {
            return Ok(Mid::NonMonotonic);
        }

        match mid_copy(l, r) {
            None => return Ok(Mid::Switches { l, r }),
            Some(m) => {
                if predicate(&m)? {
                    r = m;
                } else {
                    l = m;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn midpoint() {
        assert_eq!(mid_copy(10, 20), Some(15));
        assert_eq!(mid_copy(20, 10), Some(15));
        assert_eq!(mid_copy(0, 20), Some(10));
        assert_eq!(mid_copy(20, 0), Some(10));
        assert_eq!(mid_copy(u64::MAX - 2, u64::MAX), Some(u64::MAX - 1));
    }

    #[test]
    fn midpoint_rounding() {
        assert_eq!(mid_copy(10, 13), Some(11));
        assert_eq!(mid_copy(13, 10), Some(11));
        assert_eq!(mid_copy(10, 12), Some(11));
        assert_eq!(mid_copy(12, 10), Some(11));
    }

    #[test]
    fn midpoint_no_mid() {
        assert_eq!(mid_copy(0, 0), None);
        assert_eq!(mid_copy(10, 11), None);
        assert_eq!(mid_copy(11, 10), None);
        assert_eq!(mid_copy(10, 10), None);
        assert_eq!(mid_copy(u64::MAX, u64::MAX), None);
    }

    #[test]
    fn midpoint_near_min_max() {
        assert_eq!(mid_copy(1, 0), None);
        assert_eq!(mid_copy(1, 1), None);
        assert_eq!(mid_copy(1, 2), None);
        assert_eq!(mid_copy(1, 3), Some(2));
        assert_eq!(
            mid_copy(usize::MAX - 3, usize::MAX - 1),
            Some(usize::MAX - 2),
        );
        assert_eq!(mid_copy(usize::MAX - 2, usize::MAX), Some(usize::MAX - 1),);
    }

    #[test]
    fn search_basic() {
        let predicate = |x: &u64| *x >= 5;

        let result = binary_search(predicate, 0, u64::MAX);
        assert_eq!(result, Mid::Switches { l: 4, r: 5 });
    }

    #[test]
    fn search_invalid_initial_conditions() {
        let predicate = |x: &u64| *x >= 5;

        let result = binary_search(predicate, 6, 10);
        assert_eq!(result, Mid::True { l: 6 });

        let result = binary_search(predicate, 0, 4);
        assert_eq!(result, Mid::False { r: 4 });
    }

    #[test]
    fn search_cube_root_of_512() {
        let predicate = |x: &u64| x.pow(3) >= 512;

        let result = binary_search(predicate, 0, 20);
        assert_eq!(result, Mid::Switches { l: 7, r: 8 });
    }

    #[test]
    fn search_usize() {
        let result = binary_search(|x: &usize| *x >= 23, 1, 100);
        assert_eq!(result, Mid::Switches { l: 22, r: 23 });
    }

    proptest! {
        #[test]
        fn search_properties(start in 0u64..25_000_000, pivot in 0u64..100_000_000, end in 25_000_001u64..100_000_000) {
            let predicate = |x: &u64| *x >= pivot;
            let result = binary_search(predicate, start, end);

            match result {
                Mid::Switches { l, r } => {
                    // Check that f is false for l and true for r
                    prop_assert!(!predicate(&l));
                    prop_assert!(predicate(&r));

                    // Ensure that l and r are in ascending order
                    prop_assert!(l < r);

                    // Validate the monotonicity of the predicate
                    prop_assert!(predicate(&(l + 1)));
                }
                Mid::True { .. } => {
                    // Always true across the range
                    prop_assert!(predicate(&start));
                }
                Mid::False { .. } => {
                    // Always false across the range
                    prop_assert!(!predicate(&end));
                }
                Mid::NonMonotonic => {
                    // For a monotonic predicate, this should not happen
                    prop_assert!(false, "NonMonotonic for monotonic predicate");
                }
            }
        }
    }
}
