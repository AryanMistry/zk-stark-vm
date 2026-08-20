//! Merkle tree over field-element leaves, hashed with blake3.
//!
//! Leaf and internal-node hashes are domain-separated with a leading tag
//! byte, so a leaf hash can never be replayed as an internal node hash (or
//! vice versa) to forge a path.

use crate::field::Fp;

const LEAF_TAG: u8 = 0x00;
const NODE_TAG: u8 = 0x01;

pub type Digest = [u8; 32];

fn hash_leaf(values: &[Fp]) -> Digest {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[LEAF_TAG]);
    for &v in values {
        hasher.update(&v.0.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn hash_node(left: &Digest, right: &Digest) -> Digest {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[NODE_TAG]);
    hasher.update(left);
    hasher.update(right);
    *hasher.finalize().as_bytes()
}

/// A Merkle tree over a power-of-two number of leaves, each leaf being a
/// row of field elements (e.g. one column-slice of a trace at a given
/// evaluation point).
pub struct MerkleTree {
    /// layers[0] = leaf hashes, layers.last() = [root].
    layers: Vec<Vec<Digest>>,
}

impl MerkleTree {
    pub fn new(leaves: &[Vec<Fp>]) -> Self {
        assert!(!leaves.is_empty(), "cannot build a Merkle tree with no leaves");
        assert!(leaves.len().is_power_of_two(), "leaf count must be a power of two");

        let mut layers = vec![leaves.iter().map(|l| hash_leaf(l)).collect::<Vec<_>>()];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next = prev.chunks(2).map(|pair| hash_node(&pair[0], &pair[1])).collect();
            layers.push(next);
        }
        MerkleTree { layers }
    }

    pub fn root(&self) -> Digest {
        self.layers.last().unwrap()[0]
    }

    pub fn num_leaves(&self) -> usize {
        self.layers[0].len()
    }

    /// Authentication path for the leaf at `index`, from the leaf up to
    /// (but not including) the root.
    pub fn open(&self, index: usize) -> MerkleProof {
        assert!(index < self.num_leaves(), "leaf index out of range");
        let mut siblings = Vec::with_capacity(self.layers.len() - 1);
        let mut idx = index;
        for layer in &self.layers[..self.layers.len() - 1] {
            siblings.push(layer[idx ^ 1]);
            idx /= 2;
        }
        MerkleProof { index, siblings }
    }
}

/// An authentication path. Verification recomputes the leaf hash from the
/// claimed values, so a proof is only meaningful together with the leaf
/// values it's checked against — it doesn't carry them itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleProof {
    pub index: usize,
    pub siblings: Vec<Digest>,
}

impl MerkleProof {
    pub fn verify(&self, root: Digest, leaf_values: &[Fp]) -> bool {
        let mut cur = hash_leaf(leaf_values);
        let mut idx = self.index;
        for sibling in &self.siblings {
            cur = if idx.is_multiple_of(2) { hash_node(&cur, sibling) } else { hash_node(sibling, &cur) };
            idx /= 2;
        }
        cur == root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaves(n: usize) -> Vec<Vec<Fp>> {
        (0..n).map(|i| vec![Fp::new(i as u64), Fp::new((i * i) as u64)]).collect()
    }

    #[test]
    fn root_is_deterministic() {
        let tree_a = MerkleTree::new(&leaves(8));
        let tree_b = MerkleTree::new(&leaves(8));
        assert_eq!(tree_a.root(), tree_b.root());
    }

    #[test]
    fn every_leaf_opens_and_verifies() {
        let data = leaves(16);
        let tree = MerkleTree::new(&data);
        let root = tree.root();
        for (i, leaf) in data.iter().enumerate() {
            let proof = tree.open(i);
            assert!(proof.verify(root, leaf), "leaf {i} failed to verify");
        }
    }

    #[test]
    fn tampered_leaf_value_fails() {
        let data = leaves(8);
        let tree = MerkleTree::new(&data);
        let root = tree.root();
        let proof = tree.open(3);
        let tampered = vec![Fp::new(999), Fp::new(999)];
        assert!(!proof.verify(root, &tampered));
    }

    #[test]
    fn tampered_sibling_fails() {
        let data = leaves(8);
        let tree = MerkleTree::new(&data);
        let root = tree.root();
        let mut proof = tree.open(3);
        proof.siblings[0][0] ^= 0xFF;
        assert!(!proof.verify(root, &data[3]));
    }

    #[test]
    fn tampered_root_fails() {
        let data = leaves(8);
        let tree = MerkleTree::new(&data);
        let proof = tree.open(3);
        let mut bad_root = tree.root();
        bad_root[0] ^= 0xFF;
        assert!(!proof.verify(bad_root, &data[3]));
    }

    #[test]
    fn wrong_index_fails() {
        let data = leaves(8);
        let tree = MerkleTree::new(&data);
        let root = tree.root();
        let proof = tree.open(3);
        // Same path, but checked against a different leaf's values.
        assert!(!proof.verify(root, &data[4]));
    }

    #[test]
    fn single_leaf_tree() {
        let data = leaves(1);
        let tree = MerkleTree::new(&data);
        let root = tree.root();
        let proof = tree.open(0);
        assert!(proof.siblings.is_empty());
        assert!(proof.verify(root, &data[0]));
    }
}
