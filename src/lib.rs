use core::ops::{Add, Div, Sub};

/// Returns the value halfway between `a` and `b`, rounded to -infinity.
/// If there is no value between `a` and `b`, returns `None`.
fn mid<T>(a: &T, b: &T) -> Option<T>
where
    T: Add<Output = T> + Sub<Output = T> + Div<Output = T> + Ord + Copy + From<u8>,
{
    let (small, large) = if a <= b {
        (a, b)
    } else {
        (b, a)
    };
    let difference = *large - *small;
    let two = T::from(2u8);

    let mid_value = *small + (difference / two);
    if mid_value == *small || mid_value == *large {
        None
    } else {
        Some(mid_value)
    }
}

/// Performs a binary search to find a pair of values `(l, r)` that bracket the
/// point where a predicate `p` switches from `False` to `True`. Specifically,
/// `p(l)` will be `False` and `p(r)` will be `True`.
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
/// Returns:
/// - If the predicate is not monotonic, the function may return an incorrect
///   result, or return `(None, None)`.
/// - If the predicate is monotonic and switches from false to true within the
///   input range, the function will return `Some((l, r))` where l is the
///   highest value where the predicate is false and r is the lowest value where
///   the predicate is true.
/// - If the predicate is monotonic and always true, the function will return
///   `(None, Some(l))` where `l` is the bottom of the range.
/// - If the predicate is monotonic and always false, the function will return
///   `(Some(r), None)` where `r` is the top of the range.
pub fn binary_search<T, G>(predicate: G, l: T, r: T) -> (Option<T>, Option<T>)
where
    T: Add<Output = T> + Sub<Output = T> + Div<Output = T> + Ord + Copy + From<u8>,
    G: Fn(&T) -> bool,
{
    let p = move |x: &T| Ok::<bool, ()>(predicate(x));
    binary_search_fallible(p, l, r).unwrap() // can never fail because p is infallible
}

/// Like `binary_search`, but takes a predicate that returns a Result. If the predicate
/// returns an error while performing the binary search, this function returns
/// an error.
#[inline]
pub fn binary_search_fallible<T, G, E>(
    predicate: G,
    mut l: T,
    mut r: T,
) -> Result<(Option<T>, Option<T>), E>
where
    T: Add<Output = T> + Sub<Output = T> + Div<Output = T> + Ord + Copy + From<u8>,
    G: Fn(&T) -> Result<bool, E>,
{
    match (predicate(&l)?, predicate(&r)?) {
        (false, true) => {}
        // Check if the predicate is "always true" or "always false" and return
        // early if so.
        (true, true) => return Ok((None, Some(l))),
        (false, false) => return Ok((Some(r), None)),
        // Sanity check that will detect some non-monotonic functions. This is a
        // precondition violation, so we return (None, None).
        (true, false) => return Ok((None, None)),
    }
    loop {
        // Sanity check: f must be false for l and true for r, otherwise
        // the input function was not monotonic
        if predicate(&l)? {
            return Ok((None, None));
        }
        if !predicate(&r)? {
            return Ok((None, None));
        }

        match mid(&l, &r) {
            None => return Ok((Some(l), Some(r))),
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
        assert_eq!(mid(&10, &20), Some(15));
        assert_eq!(mid(&20, &10), Some(15));
        assert_eq!(mid(&0, &20), Some(10));
        assert_eq!(mid(&20, &0), Some(10));
        assert_eq!(mid(&(u64::MAX - 2), &u64::MAX), Some(u64::MAX - 1));
    }

    #[test]
    fn midpoint_rounding() {
        assert_eq!(mid(&10, &13), Some(11));
        assert_eq!(mid(&13, &10), Some(11));
        assert_eq!(mid(&10, &12), Some(11));
        assert_eq!(mid(&12, &10), Some(11));
    }

    #[test]
    fn midpoint_no_mid() {
        assert_eq!(mid(&0, &0), None);
        assert_eq!(mid(&10, &11), None);
        assert_eq!(mid(&11, &10), None);
        assert_eq!(mid(&10, &10), None);
        assert_eq!(mid(&u64::MAX, &u64::MAX), None);
    }

    #[test]
    fn midpoint_near_min_max() {
        assert_eq!(mid(&1, &0), None);
        assert_eq!(mid(&1, &1), None);
        assert_eq!(mid(&1, &2), None);
        assert_eq!(mid(&1, &3), Some(2));
        assert_eq!(
          mid(&(usize::MAX-3), &(usize::MAX-1)),
          Some(usize::MAX-2),
        );
        assert_eq!(
          mid(&(usize::MAX-2), &usize::MAX),
          Some(usize::MAX-1),
        );
    }

    #[test]
    fn search_basic() {
        let predicate = |x: &u64| *x >= 5;

        let result = binary_search(predicate, 0, u64::MAX);
        assert_eq!(result, (Some(4), Some(5)));
    }

    #[test]
    fn search_invalid_initial_conditions() {
        let predicate = |x: &u64| *x >= 5;

        let result = binary_search(predicate, 6, 10);
        assert_eq!(result, (None, Some(6)));

        let result = binary_search(predicate, 0, 4);
        assert_eq!(result, (Some(4), None));
    }

    #[test]
    fn search_cube_root_of_512() {
        let predicate = |x: &u64| x.pow(3) >= 512;

        let result = binary_search(predicate, 0, 20);
        assert_eq!(result, (Some(7), Some(8)));
    }

    #[test]
    fn search_usize() {
        let result = binary_search(|x: &usize| *x >= 23, 1, 100);
        assert_eq!(result, (Some(22), Some(23)));
    }

    proptest! {
        #[test]
        fn search_properties(start in 0u64..25_000_000, pivot in 0u64..100_000_000, end in 25_000_001u64..100_000_000) {
            let predicate = |x: &u64| *x >= pivot;
            let (highest_false, lowest_true) = binary_search(predicate, start, end);

            prop_assert!(highest_false.is_some() || lowest_true.is_some());

            // Verify that search returned some result
            if highest_false.is_none() {
                prop_assert!(predicate(&start));
            }
            if lowest_true.is_none() {
                prop_assert!(!predicate(&end));
            }

            if let (Some(l), Some(r)) = (highest_false, lowest_true) {
                // Check that f is false for l and true for r
                prop_assert!(!predicate(&l));
                prop_assert!(predicate(&r));

                // Ensure that l and r are in ascending order
                prop_assert!(l < r);

                // Validate the monotonicity of the predicate
                prop_assert!(predicate(&(l + 1)));
            }
        }
    }
}
