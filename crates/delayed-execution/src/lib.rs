//! Experimental support for [EIP-7886 Delayed execution](https://eips.ethereum.org/EIPS/eip-7886).
//!
//! This crate defines types used to store block execution outputs that are
//! validated only when executing the _next_ block (EIP-7886).

use alloy_primitives::{Bloom, B256};
use reth_primitives_traits::AlloyBlockHeader;
use serde::{Deserialize, Serialize};

/// Execution results that are validated when the child block executes.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct DelayedExecutionOutcome {
    /// Transaction root of the last executed block.
    pub last_transactions_root: B256,
    /// Receipt root of the last executed block.
    pub last_receipt_root: B256,
    /// Logs bloom of the last executed block.
    pub last_block_logs_bloom: Bloom,
    /// Requests hash of the last executed block.
    pub last_requests_hash: B256,
    /// Whether the block execution reverted.
    pub last_execution_reverted: bool,
}

impl DelayedExecutionOutcome {
    /// Derive the outcome from an executed block.
    pub fn from_executed_block<N: reth_primitives_traits::NodePrimitives>(
        block: &reth_chain_state::ExecutedBlockWithTrieUpdates<N>,
    ) -> Self {
        use alloy_eips::eip7685::EMPTY_REQUESTS_HASH;

        let header = block.recovered_block().header();
        let last_transactions_root = header.transactions_root();
        let last_receipt_root = header.receipts_root();
        let last_block_logs_bloom = header.logs_bloom();
        let last_requests_hash = header.requests_hash().unwrap_or(EMPTY_REQUESTS_HASH);

        Self {
            last_transactions_root,
            last_receipt_root,
            last_block_logs_bloom,
            last_requests_hash,
            last_execution_reverted: false,
        }
    }

    /// Derive the outcome directly from a block header.
    ///
    /// The revert flag defaults to `false` because it is not recorded in the
    /// header. Callers may update it if they know the execution outcome.
    pub fn from_header<H: AlloyBlockHeader>(header: &H) -> Self {
        use alloy_eips::eip7685::EMPTY_REQUESTS_HASH;

        Self {
            last_transactions_root: header.transactions_root(),
            last_receipt_root: header.receipts_root(),
            last_block_logs_bloom: header.logs_bloom(),
            last_requests_hash: header.requests_hash().unwrap_or(EMPTY_REQUESTS_HASH),
            last_execution_reverted: false,
        }
    }
}

use alloy_primitives::{U256};

/// Simplified block environment used for delayed execution examples.
#[derive(Clone, Debug)]
pub struct BlockEnv<S> {
    /// State database.
    pub state: S,
    /// Chain id.
    pub chain_id: u64,
    /// Base fee for the block.
    pub base_fee_per_gas: U256,
    /// Excess blob gas for the block.
    pub excess_blob_gas: U256,
    /// Block gas limit.
    pub block_gas_limit: u64,
    /// Declared block gas used.
    pub block_gas_used: u64,
}

/// Simplified block execution output.
#[derive(Default, Clone, Debug)]
pub struct BlockOutput {
    /// Actual block gas used.
    pub block_gas_used: u64,
    /// Whether execution reverted.
    pub execution_reverted: bool,
}

// Execution helpers for EIP‑7886 are implemented in the `evm` crate.
