use bellpepper_core::boolean::Boolean;
use bitvec::order::Lsb0;
use bitvec::prelude::BitVec;
use digest::{Digest, Output};

pub fn bytes_to_bitvec(bytes: &[u8]) -> Vec<Boolean> {
    let bits = BitVec::<Lsb0, u8>::from_slice(bytes);
    let bits: Vec<Boolean> = bits.iter().map(|b| Boolean::constant(*b)).collect();
    bits
}

pub fn bits_to_bytevec(bits: &[Boolean]) -> Vec<u8> {
    let result: Vec<bool> = bits.iter().map(|b| b.get_value().unwrap()).collect();
    let mut bv = BitVec::<Lsb0, u8>::new();
    for bit in result {
        bv.push(bit);
    }
    bv.as_slice().to_vec()
}

/// Constructs a fixed-depth binary Merkle tree with predefined leaf values.
///
/// This function creates a Merkle tree with a depth of 4 (including the root).
/// The leaves of the tree are the SHA3 hashes of the predefined values: "a", "b", "c", "d", "e", "f", "g", "h".
/// It computes the hash and path key for each leaf and intermediary node.
///
/// # Returns
/// A tuple containing:
/// - The root hash of the Merkle tree as the first element.
/// - A vector of tuples, each containing:
///   - The hash of a leaf or intermediary node.
///   - The path key, a `Vec<Boolean>`, representing the path from the root to the node.
///
/// # Path Key Representation
/// The path key is a vector of `Boolean` values, where each value indicates a direction at a node:
/// - `Boolean::constant(false)` for a left turn.
/// - `Boolean::constant(true)` for a right turn.
/// The path keys are 256 bits long, padded with `false` values.
///
/// # Tree Structure
/// The tree structure is as follows (indexes in the vector are shown in parentheses):
/// ```plaintext
///         root
///        /    \
///      (12)   (13)
///      /  \    /  \
///    (8) (9) (10) (11)
///    / \  / \  / \  / \
///  (0)(1)(2)(3)(4)(5)(6)(7)
///   a  b  c  d  e  f  g  h
/// ```
/// In this structure:
/// - Leaf nodes ("a" to "h") are at indexes 0 to 7.
/// - Intermediary nodes are at indexes 8 to 13.
/// - The root node is at index 14.
///
/// # Example
/// ```
/// let (root_hash, leaf_hashes_and_keys) = construct_merkle_tree();
/// for (hash, key) in leaf_hashes_and_keys.iter() {
///     // Process each leaf and intermediary node's hash and key...
/// }
/// ```
pub fn construct_merkle_tree<D: Digest>() -> (Vec<u8>, Vec<(Vec<u8>, Vec<Boolean>)>) {
    let predefined_leaves = vec![b"a", b"b", b"c", b"d", b"e", b"f", b"g", b"h"]
        .iter()
        .map(|d| hash::<D>(&d.to_vec()).to_vec())
        .collect::<Vec<Vec<u8>>>();

    let mut leaves = predefined_leaves.clone();

    for j in (0..12).step_by(2) {
        leaves.push(hash::<D>(&[leaves[j].to_owned(), leaves[j + 1].to_owned()].concat()).to_vec());
    }
    // Generate keys
    let mut leaf_key_vec = Vec::new();
    for i in 0..14 {
        let mut path = Vec::new();
        let mut node_index = i;
        let depth = if i <= 7 {
            3
        } else if i < 12 {
            2
        } else {
            1
        };

        for _ in 0..depth {
            let direction = (node_index & 1) != 0; // Right if odd, Left if even
            path.push(Boolean::constant(direction));
            node_index >>= 1;
        }

        // Reverse to get the path from root to the node
        path.reverse();

        // Pad the path to ensure it's 256 elements long
        while path.len() < 256 {
            path.push(Boolean::constant(false));
        }
        leaf_key_vec.push((leaves[i].to_owned(), path));
    }

    // Compute expected root hash
    let expected_root =
        hash::<D>(&[leaves[12].to_owned(), leaves[13].to_owned()].concat()).to_vec();

    (expected_root.to_owned(), leaf_key_vec)
}

pub fn hash<D: Digest>(data: &[u8]) -> Output<D> {
    let mut hasher = D::new();
    hasher.update(data);

    hasher.finalize()
}
