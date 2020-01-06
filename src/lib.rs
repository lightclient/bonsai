//! Implements various index arithmetic functions for perfect binary trees.
#![no_std]

#[cfg(feature = "u64")]
type T = u64;

#[cfg(feature = "u128")]
type T = u128;

const BITS: T = (core::mem::size_of::<T>() * 8) as T;
const NEGATIVE_TWO: T = -2i8 as T;

/// Returns an index's family.
pub const fn expand(index: T) -> (T, T, T) {
    let left = index & NEGATIVE_TWO;
    let right = left + 1;
    let parent = left / 2;

    (left, right, parent)
}

/// Returns an index's children.
pub const fn children(index: T) -> (T, T) {
    let (left, right, _) = expand(index << 1);
    (left, right)
}

/// Returns the index's sibling.
pub const fn sibling(index: T) -> T {
    (index & NEGATIVE_TWO) + ((index & 1) ^ 1)
}

/// Returns the first leaf of a tree rooted at `root` with a `depth`.
pub const fn first_leaf(root: T, depth: T) -> T {
    root * (1 << depth)
}

/// Returns the last leaf of a tree rooted at `root` with a `depth`.
pub const fn last_leaf(root: T, depth: T) -> T {
    let pow = 1 << depth;
    root * pow + pow - 1
}

/// Returns if `index` is in the subtree rooted at `root`.
pub const fn is_in_subtree(root: T, index: T) -> bool {
    let diff = relative_depth(root, index);
    let left_most = first_leaf(root, diff);
    let right_most = last_leaf(root, diff);

    (left_most <= index) & (index <= right_most)
}

/// Returns the depth between two general indicies.
pub const fn relative_depth(a: T, b: T) -> T {
    let a = log2(last_power_of_two(a));
    let b = log2(last_power_of_two(b));

    (b - a) as T
}

/// Returns the next power of two for `n` using bit twiddling.
///
/// Source: https://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
pub const fn next_power_of_two(n: T) -> T {
    let mut ret = n - 1;

    ret = ret | ret >> 1;
    ret = ret | ret >> 2;
    ret = ret | ret >> 4;
    ret = ret | ret >> 8;
    ret = ret | ret >> 16;
    ret = ret | ret >> 32;

    #[cfg(feature = "u128")]
    {
        ret = ret | ret >> 64;
    }

    ret + 1
}

/// Returns the last power of two for `n` using bit twiddling.
pub const fn last_power_of_two(n: T) -> T {
    let mut ret = n;

    ret = ret | ret >> 1;
    ret = ret | ret >> 2;
    ret = ret | ret >> 4;
    ret = ret | ret >> 8;
    ret = ret | ret >> 16;
    ret = ret | ret >> 32;

    #[cfg(feature = "u128")]
    {
        ret = ret | ret >> 64;
    }

    let (ret, overflow) = ret.overflowing_add(1);

    // This will either be the last power of two or zero if it overflowed.
    let shifted = ret.overflowing_shr(1).0;

    // Overflows only occur at `2^BITS < n < 2^BITS-1`, so the last power of
    // two would be `2^(BITS-1)`.
    let max_pow_two = 1 << (BITS - 1);

    shifted + (max_pow_two & ((overflow as T) << (BITS - 1)))
}

/// Returns the subtree root for `index` assuming the tree is `depth` deep.
pub const fn root_from_depth(index: u64, depth: u64) -> u64 {
    index / (1 << depth)
}

/// Returns the log base 2 of `n`.
pub const fn log2(n: T) -> T {
    (BITS - 1) as T - n.leading_zeros() as T
}

/// Translate the subtree index `index` rooted at `root` into a general index.
pub const fn subtree_index_to_general(root: T, index: T) -> T {
    (root * index) - (root - 1) * (index - last_power_of_two(index))
}

/// Translate the general index `index` into a subtree index rooted at `root`.
pub const fn general_index_to_subtree(root: T, index: T) -> T {
    let depth_diff = log2(last_power_of_two(index)) - log2(last_power_of_two(root));

    (1 << depth_diff) + index - ((1 << depth_diff) * root)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TWO: T = 2;

    #[test]
    fn compute_depth_difference() {
        assert_eq!(relative_depth(1, 1), 0);
        assert_eq!(relative_depth(1, 2), 1);
        assert_eq!(relative_depth(1, 5), 2);
        assert_eq!(relative_depth(1, 13), 3);
        assert_eq!(relative_depth(1, 30), 4);

        assert_eq!(relative_depth(2, 30), 3);
        assert_eq!(relative_depth(7, 30), 2);
        assert_eq!(relative_depth(11, 30), 1);
        assert_eq!(relative_depth(28, 30), 0);

        assert_eq!(relative_depth(1, TWO.pow(63)), 63);
    }

    #[test]
    fn compute_root_from_depth() {
        assert_eq!(root_from_depth(2, 1), 1);
        assert_eq!(root_from_depth(3, 1), 1);

        assert_eq!(root_from_depth(16, 4), 1);
        assert_eq!(root_from_depth(16, 3), 2);
        assert_eq!(root_from_depth(16, 2), 4);
        assert_eq!(root_from_depth(16, 1), 8);
        assert_eq!(root_from_depth(16, 0), 16);

        assert_eq!(root_from_depth(31, 4), 1);
        assert_eq!(root_from_depth(31, 3), 3);
        assert_eq!(root_from_depth(31, 2), 7);
        assert_eq!(root_from_depth(31, 1), 15);
        assert_eq!(root_from_depth(31, 0), 31);

        assert_eq!(root_from_depth(22, 4), 1);
        assert_eq!(root_from_depth(22, 3), 2);
        assert_eq!(root_from_depth(22, 2), 5);
        assert_eq!(root_from_depth(22, 1), 11);
        assert_eq!(root_from_depth(22, 0), 22);

        assert_eq!(root_from_depth(25, 4), 1);
        assert_eq!(root_from_depth(25, 3), 3);
        assert_eq!(root_from_depth(25, 2), 6);
        assert_eq!(root_from_depth(25, 1), 12);
        assert_eq!(root_from_depth(25, 0), 25);
    }

    #[test]
    fn compute_expanded_tree_indexes() {
        assert_eq!(expand(2), (2, 3, 1));
        assert_eq!(expand(3), (2, 3, 1));
        assert_eq!(expand(14), (14, 15, 7));
        assert_eq!(expand(15), (14, 15, 7));
        assert_eq!(expand(3101), (3100, 3101, 1550));
    }

    #[test]
    fn compute_child_indexes() {
        assert_eq!(children(2), (4, 5));
        assert_eq!(children(3), (6, 7));
        assert_eq!(children(14), (28, 29));
        assert_eq!(children(15), (30, 31));
        assert_eq!(children(3101), (6202, 6203));
    }

    #[test]
    fn compute_sibling_index() {
        assert_eq!(sibling(2), 3);
        assert_eq!(sibling(3), 2);
        assert_eq!(sibling(6), 7);
        assert_eq!(sibling(7), 6);
        assert_eq!(sibling(100), 101);
        assert_eq!(sibling(101), 100);
    }

    #[test]
    fn next_and_last_power_of_two() {
        assert_eq!(last_power_of_two(1), 1);
        assert_eq!(last_power_of_two(2), 2);
        assert_eq!(last_power_of_two(9), 8);
        assert_eq!(last_power_of_two(1023), 512);
        assert_eq!(last_power_of_two(TWO.pow(63) + 1000), TWO.pow(63));

        #[cfg(feature = "u128")]
        assert_eq!(last_power_of_two(TWO.pow(127) + 1000), TWO.pow(127));

        assert_eq!(next_power_of_two(1), 1);
        assert_eq!(next_power_of_two(2), 2);
        assert_eq!(next_power_of_two(9), 16);
        assert_eq!(next_power_of_two(1023), 1024);
        assert_eq!(next_power_of_two(TWO.pow(62) + 1000), TWO.pow(63));

        #[cfg(feature = "u128")]
        assert_eq!(next_power_of_two(TWO.pow(126) + 1000), TWO.pow(127));
    }

    #[test]
    fn transform_subtree_index_to_general() {
        assert_eq!(subtree_index_to_general(1, 1), 1);
        assert_eq!(subtree_index_to_general(1, 2), 2);
        assert_eq!(subtree_index_to_general(1, 1000), 1000);
        assert_eq!(subtree_index_to_general(1, 99999), 99999);

        assert_eq!(subtree_index_to_general(2, 1), 2);
        assert_eq!(subtree_index_to_general(2, 2), 4);
        assert_eq!(subtree_index_to_general(2, 7), 11);
        assert_eq!(subtree_index_to_general(2, 11), 19);
        assert_eq!(subtree_index_to_general(2, 20), 36);

        assert_eq!(subtree_index_to_general(6, 1), 6);
        assert_eq!(subtree_index_to_general(6, 2), 12);
        assert_eq!(subtree_index_to_general(6, 6), 26);

        assert_eq!(subtree_index_to_general(26, 1), 26);
        assert_eq!(subtree_index_to_general(26, 2), 52);
        assert_eq!(subtree_index_to_general(26, 3), 53);

        assert_eq!(subtree_index_to_general(26, 7), 107);
        assert_eq!(subtree_index_to_general(26, 12), 212);

        assert_eq!(subtree_index_to_general(11, 17), 177);
    }

    #[test]
    fn transform_general_index_to_subtree() {
        assert_eq!(general_index_to_subtree(1, 1), 1);
        assert_eq!(general_index_to_subtree(1, 2), 2);
        assert_eq!(general_index_to_subtree(1, 1000), 1000);
        assert_eq!(general_index_to_subtree(1, 99999), 99999);

        assert_eq!(general_index_to_subtree(2, 2), 1);
        assert_eq!(general_index_to_subtree(2, 4), 2);
        assert_eq!(general_index_to_subtree(2, 11), 7);
        assert_eq!(general_index_to_subtree(2, 19), 11);
        assert_eq!(general_index_to_subtree(2, 35), 19);
        assert_eq!(general_index_to_subtree(2, 36), 20);

        assert_eq!(general_index_to_subtree(6, 6), 1);
        assert_eq!(general_index_to_subtree(6, 12), 2);
        assert_eq!(general_index_to_subtree(6, 26), 6);

        assert_eq!(general_index_to_subtree(26, 26), 1);
        assert_eq!(general_index_to_subtree(26, 52), 2);
        assert_eq!(general_index_to_subtree(26, 53), 3);
        assert_eq!(general_index_to_subtree(26, 107), 7);
        assert_eq!(general_index_to_subtree(26, 212), 12);
    }

    #[test]
    fn compute_log2() {
        assert_eq!(log2(TWO.pow(1)), 1);
        assert_eq!(log2(TWO.pow(10)), 10);
        assert_eq!(log2(TWO.pow(33)), 33);
        assert_eq!(log2(TWO.pow(45)), 45);
        assert_eq!(log2(TWO.pow(63)), 63);
    }

    #[test]
    fn compute_first_leaf() {
        assert_eq!(first_leaf(1, 1), TWO.pow(1));
        assert_eq!(first_leaf(1, 9), TWO.pow(9));
        assert_eq!(first_leaf(1, 50), TWO.pow(50));

        assert_eq!(first_leaf(2, 1), 2 * TWO.pow(1));
        assert_eq!(first_leaf(2, 4), 2 * TWO.pow(4));
        assert_eq!(first_leaf(2, 5), 2 * TWO.pow(5));

        assert_eq!(first_leaf(6, 1), 6 * TWO.pow(1));
        assert_eq!(first_leaf(6, 2), 6 * TWO.pow(2));
        assert_eq!(first_leaf(6, 11), 6 * TWO.pow(11));

        assert_eq!(first_leaf(25, 1), 25 * TWO.pow(1));
    }

    #[test]
    fn compute_last_leaf() {
        assert_eq!(last_leaf(1, 1), 3);
        assert_eq!(last_leaf(1, 9), TWO.pow(10) - 1);
        assert_eq!(last_leaf(1, 50), TWO.pow(51) - 1);

        assert_eq!(last_leaf(2, 1), 2 * TWO.pow(1) + 1);
        assert_eq!(last_leaf(2, 4), 2 * TWO.pow(4) + 15);
        assert_eq!(last_leaf(2, 5), 2 * TWO.pow(5) + 31);

        assert_eq!(last_leaf(6, 1), 6 * TWO.pow(1) + 1);
        assert_eq!(last_leaf(6, 2), 6 * TWO.pow(2) + 3);
        assert_eq!(last_leaf(6, 11), 6 * TWO.pow(11) + 2047);

        assert_eq!(last_leaf(25, 1), 25 * TWO.pow(1) + 1);
    }

    #[test]
    fn determine_if_index_is_in_subtree() {
        assert_eq!(is_in_subtree(1, 3), true);
        assert_eq!(is_in_subtree(1, 100), true);
        assert_eq!(is_in_subtree(2, 10), true);
        assert_eq!(is_in_subtree(2, 6), false);
        assert_eq!(is_in_subtree(2, 15), false);
    }
}
