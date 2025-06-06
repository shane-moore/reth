use crate::Database;
use alloy_eips::eip4844::{calculate_blob_gas_price, DATA_GAS_PER_BLOB};
use alloy_primitives::{Address, B256, U256};
use revm::{context_interface::journaled_state::JournalCheckpoint, database::State};
use reth_primitives_traits::transaction::signed::SignedTransaction;

/// Additional transaction fields required for delayed execution helpers.
pub trait ExtendedTransaction: SignedTransaction {
    /// Gas limit of the transaction.
    fn gas_limit(&self) -> u64;
    /// Effective gas price for the transaction.
    fn effective_gas_price(&self, base_fee: Option<u64>) -> u128;
    /// Blob hashes attached to the transaction.
    fn blob_versioned_hashes(&self) -> Option<&[B256]> { None }
}

/// Checkpoint handle used for state snapshots.
pub type Checkpoint = JournalCheckpoint;

/// Begin a state snapshot returning a checkpoint handle.
pub fn begin_transaction<DB>(state: &mut State<DB>) -> Checkpoint
where
    DB: Database,
{
    state.checkpoint()
}

/// Roll back state to the provided checkpoint.
pub fn rollback_transaction<DB>(state: &mut State<DB>, checkpoint: Checkpoint)
where
    DB: Database,
{
    state.checkpoint_revert(checkpoint);
}

/// Commit state changes made after the checkpoint.
pub fn commit_transaction<DB>(state: &mut State<DB>)
where
    DB: Database,
{
    state.checkpoint_commit();
}

/// Decode raw transactions. Currently this is a simple clone.
pub fn decode_transactions<T: Clone>(txs: &[T]) -> Vec<T> { txs.to_vec() }

/// Deduct the maximum gas fee from the sender's balance before execution.
pub fn deduct_max_tx_fee_from_sender_balance<DB, Tx>(
    state: &mut State<DB>,
    base_fee: U256,
    excess_blob_gas: U256,
    tx: &Tx,
) where
    Tx: SignedTransaction,
    DB: Database,
{
    // Recover sender address
    let sender = match tx.recover_signer_unchecked() {
        Ok(addr) => addr,
        Err(_) => return,
    };

    // Calculate gas fees according to EIP-4844
    let gas_limit = tx.gas_limit();
    let effective_gas_price = U256::from(tx.effective_gas_price(Some(base_fee.as_limbs()[0] as u64)));
    let blob_gas_used = tx
        .blob_versioned_hashes()
        .map(|hashes| U256::from(hashes.len() as u64) * U256::from(DATA_GAS_PER_BLOB))
        .unwrap_or_default();
    let blob_gas_price = U256::from(calculate_blob_gas_price(excess_blob_gas.as_limbs()[0] as u64));

    let max_fee = U256::from(gas_limit) * effective_gas_price + blob_gas_used * blob_gas_price;

    // Deduct from sender balance
    if let Ok(mut acc) = state.basic(sender) {
        if let Some(mut info) = acc.info {
            if info.balance > max_fee { info.balance -= max_fee; } else { info.balance = U256::ZERO; }
            state.set_account_info(sender, info);
        }
    }
}

/// Update gas usage and stop execution if the block gas limit would be exceeded.
pub fn process_transaction(out_gas: &mut u64, tx_gas: u64, block_gas_limit: u64) -> bool {
    if *out_gas + tx_gas > block_gas_limit { return false; }
    *out_gas += tx_gas;
    true
}

