use alloc::{format, vec::Vec};
use alloy_consensus::{proofs::calculate_receipt_root, BlockHeader, Transaction, TxReceipt, constants::KECCAK_EMPTY};
use alloy_eips::eip7685::Requests;
use alloy_primitives::{Bloom, B256, U256, Address};
use revm_interpreter::gas::calculate_initial_tx_gas;
use revm_primitives::hardfork::SpecId;
use std::collections::HashMap;
use reth_chainspec::EthereumHardforks;
use reth_consensus::ConsensusError;
use reth_delayed_execution::DelayedExecutionOutcome;
use reth_provider::StateProvider;
use reth_primitives_traits::{
    receipt::gas_spent_by_transactions, Block, BlockBody, GotExpected, Receipt,
    RecoveredBlock,
};

/// Placeholder trait exposing delayed execution header fields required for
/// EIP-7886 validation.
///
/// The default implementation for [`ConsensusHeader`] returns zero values so
/// validation becomes a no-op until the header type exposes these fields.
pub trait DelayedHeaderFields {
    /// Pre-execution state root from the parent block.
    fn pre_state_root(&self) -> B256 { B256::ZERO }
    /// Deferred transaction root from the parent block.
    fn parent_transactions_root(&self) -> B256 { B256::ZERO }
    /// Deferred receipt root from the parent block.
    fn parent_receipt_root(&self) -> B256 { B256::ZERO }
    /// Deferred logs bloom from the parent block.
    fn parent_bloom(&self) -> Bloom { Bloom::ZERO }
    /// Deferred requests hash from the parent block.
    fn parent_requests_hash(&self) -> B256 { B256::ZERO }
    /// Whether the parent block execution reverted.
    fn parent_execution_reverted(&self) -> bool { false }
}

impl<H: BlockHeader> DelayedHeaderFields for H {}

/// Validate a block with regard to execution results:
///
/// - Compares the receipts root in the block header to the block body
/// - Compares the gas used in the block header to the actual gas usage after execution
pub fn validate_block_post_execution<B, R, ChainSpec>(
    block: &RecoveredBlock<B>,
    chain_spec: &ChainSpec,
    receipts: &[R],
    requests: &Requests,
) -> Result<(), ConsensusError>
where
    B: Block,
    R: Receipt,
    ChainSpec: EthereumHardforks,
{
    // Check if gas used matches the value set in header.
    let cumulative_gas_used =
        receipts.last().map(|receipt| receipt.cumulative_gas_used()).unwrap_or(0);
    if block.header().gas_used() != cumulative_gas_used {
        return Err(ConsensusError::BlockGasUsed {
            gas: GotExpected { got: cumulative_gas_used, expected: block.header().gas_used() },
            gas_spent_by_tx: gas_spent_by_transactions(receipts),
        })
    }

    // Before Byzantium, receipts contained state root that would mean that expensive
    // operation as hashing that is required for state root got calculated in every
    // transaction This was replaced with is_success flag.
    // See more about EIP here: https://eips.ethereum.org/EIPS/eip-658
    if chain_spec.is_byzantium_active_at_block(block.header().number()) {
        if let Err(error) =
            verify_receipts(block.header().receipts_root(), block.header().logs_bloom(), receipts)
        {
            tracing::debug!(%error, ?receipts, "receipts verification failed");
            return Err(error)
        }
    }

    // Validate that the header requests hash matches the calculated requests hash
    if chain_spec.is_prague_active_at_timestamp(block.header().timestamp()) {
        let Some(header_requests_hash) = block.header().requests_hash() else {
            return Err(ConsensusError::RequestsHashMissing)
        };
        let requests_hash = requests.requests_hash();
        if requests_hash != header_requests_hash {
            return Err(ConsensusError::BodyRequestsHashDiff(
                GotExpected::new(requests_hash, header_requests_hash).into(),
            ))
        }
    }

    Ok(())
}

/// Calculate the receipts root, and compare it against the expected receipts root and logs
/// bloom.
fn verify_receipts<R: Receipt>(
    expected_receipts_root: B256,
    expected_logs_bloom: Bloom,
    receipts: &[R],
) -> Result<(), ConsensusError> {
    // Calculate receipts root.
    let receipts_with_bloom = receipts.iter().map(TxReceipt::with_bloom_ref).collect::<Vec<_>>();
    let receipts_root = calculate_receipt_root(&receipts_with_bloom);

    // Calculate header logs bloom.
    let logs_bloom = receipts_with_bloom.iter().fold(Bloom::ZERO, |bloom, r| bloom | r.bloom_ref());

    compare_receipts_root_and_logs_bloom(
        receipts_root,
        logs_bloom,
        expected_receipts_root,
        expected_logs_bloom,
    )?;

    Ok(())
}

/// Compare the calculated receipts root with the expected receipts root, also compare
/// the calculated logs bloom with the expected logs bloom.
fn compare_receipts_root_and_logs_bloom(
    calculated_receipts_root: B256,
    calculated_logs_bloom: Bloom,
    expected_receipts_root: B256,
    expected_logs_bloom: Bloom,
) -> Result<(), ConsensusError> {
    if calculated_receipts_root != expected_receipts_root {
        return Err(ConsensusError::BodyReceiptRootDiff(
            GotExpected { got: calculated_receipts_root, expected: expected_receipts_root }.into(),
        ))
    }

    if calculated_logs_bloom != expected_logs_bloom {
        return Err(ConsensusError::BodyBloomLogDiff(
            GotExpected { got: calculated_logs_bloom, expected: expected_logs_bloom }.into(),
        ))
    }

    Ok(())
}

/// Validate that the child header's delayed execution data matches the recorded parent outcome.
///
/// This is a placeholder implementation for EIP-7886 validation. The actual
/// checks will be added once the header exposes the necessary fields.
/// Timestamp when the Glamsterdam fork activates.
///
/// This is a placeholder constant used for integration testing of the delayed
/// execution logic until the fork activation is wired through the chain spec.
/// Placeholder timestamp for the Glamsterdam fork activation.
///
/// Until the fork wiring is fully implemented this constant is used by
/// multiple crates to gate the delayed execution logic.
pub const GLAMSTERDAM_TIMESTAMP: u64 = 0;

use reth_provider::StateProvider;

pub fn validate_parent_delayed_execution<B, SP>(
    block: &RecoveredBlock<B>,
    parent_state_root: B256,
    parent_outcome: &DelayedExecutionOutcome,
    state: &SP,
) -> Result<(), ConsensusError>
where
    B: Block,
    B::Header: DelayedHeaderFields,
    SP: StateProvider,
{
    let header = block.header();

    if header.timestamp() < GLAMSTERDAM_TIMESTAMP {
        return Ok(());
    }
    if header.pre_state_root() != parent_state_root {
        return Err(ConsensusError::Other(format!(
            "pre-state root mismatch: got {:#x}, expected {:#x}",
            header.pre_state_root(), parent_state_root
        )));
    }

    if header.parent_transactions_root() != parent_outcome.last_transactions_root {
        return Err(ConsensusError::Other("parent transactions root mismatch".into()));
    }
    if header.parent_receipt_root() != parent_outcome.last_receipt_root {
        return Err(ConsensusError::Other("parent receipt root mismatch".into()));
    }
    if header.parent_bloom() != parent_outcome.last_block_logs_bloom {
        return Err(ConsensusError::Other("parent bloom mismatch".into()));
    }
    if header.parent_requests_hash() != parent_outcome.last_requests_hash {
        return Err(ConsensusError::Other("parent requests hash mismatch".into()));
    }
    if header.parent_execution_reverted() != parent_outcome.last_execution_reverted {
        return Err(ConsensusError::Other("parent execution reverted flag mismatch".into()));
    }

    // Additional delayed execution validation derived from block contents
    use alloy_eips::eip4844::{calculate_blob_gas_price, DATA_GAS_PER_BLOB};
    use alloy_primitives::Address;
    use revm_interpreter::gas::calculate_initial_tx_gas;
    use revm_primitives::hardfork::SpecId;
    use std::collections::HashMap;

    let mut total_inclusion_gas = 0u64;
    let mut total_blob_gas_used = 0u64;
    let mut sender_balances: HashMap<Address, U256> = HashMap::new();
    let mut sender_nonces: HashMap<Address, u64> = HashMap::new();

    let base_fee = header.base_fee_per_gas().unwrap_or_default();
    let excess_blob_gas = header.excess_blob_gas().unwrap_or_default();
    let blob_gas_price = calculate_blob_gas_price(excess_blob_gas);

    for tx in block.body().transactions() {
        // Validate signature
        let sender = tx
            .recover_signer_unchecked()
            .map_err(|_| ConsensusError::Other("invalid tx signature".into()))?;

        // Fetch sender account info
        let acc = state
            .basic_account(&sender)?
            .unwrap_or_default();

        if acc.bytecode_hash.is_some() && acc.bytecode_hash.unwrap_or_default() != alloy_consensus::constants::KECCAK_EMPTY {
            return Err(ConsensusError::Other("sender not EOA".into()));
        }

        let bal = sender_balances.entry(sender).or_insert(acc.balance);
        let nonce = sender_nonces.entry(sender).or_insert(acc.nonce);

        let gas = calculate_initial_tx_gas(
            SpecId::CANCUN,
            tx.input(),
            tx.is_create(),
            tx.access_list().map(|l| l.len()).unwrap_or_default() as u64,
            tx.access_list().map(|l| l.iter().map(|i| i.storage_keys.len()).sum::<usize>()).unwrap_or_default() as u64,
            tx.authorization_list().map(|l| l.len()).unwrap_or_default() as u64,
        );

        total_inclusion_gas = total_inclusion_gas.saturating_add(gas.initial_gas.max(gas.floor_gas));

        let blob_gas_used = tx
            .blob_versioned_hashes()
            .map(|h| h.len() as u64 * DATA_GAS_PER_BLOB)
            .unwrap_or(0);
        total_blob_gas_used = total_blob_gas_used.saturating_add(blob_gas_used);

        let effective_gas_price = tx.effective_gas_price(Some(base_fee));
        let max_fee = U256::from(tx.gas_limit()) * U256::from(effective_gas_price)
            + U256::from(blob_gas_used) * U256::from(blob_gas_price);

        if *bal < max_fee + tx.value() {
            return Err(ConsensusError::Other("insufficient balance".into()));
        }
        if *nonce != tx.nonce() {
            return Err(ConsensusError::Other("nonce mismatch".into()));
        }

        *bal -= max_fee + tx.value();
        *nonce += 1;
    }

    if total_inclusion_gas > header.gas_used() {
        return Err(ConsensusError::Other("inclusion gas exceeds header gas used".into()));
    }

    if let Some(header_blob_gas) = header.blob_gas_used() {
        if header_blob_gas != total_blob_gas_used {
            return Err(ConsensusError::Other("blob gas used mismatch".into()));
        }
    }

    if let Some(withdrawals) = block.body().withdrawals() {
        let root = alloy_consensus::proofs::calculate_withdrawals_root(withdrawals);
        if Some(root) != header.withdrawals_root() {
            return Err(ConsensusError::Other("withdrawals root mismatch".into()));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::{b256, hex};
    use reth_ethereum_primitives::Receipt;

    #[test]
    fn test_verify_receipts_success() {
        // Create a vector of 5 default Receipt instances
        let receipts = vec![Receipt::default(); 5];

        // Compare against expected values
        assert!(verify_receipts(
            b256!("0x61353b4fb714dc1fccacbf7eafc4273e62f3d1eed716fe41b2a0cd2e12c63ebc"),
            Bloom::from(hex!("00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")),
            &receipts
        )
        .is_ok());
    }

    #[test]
    fn test_verify_receipts_incorrect_root() {
        // Generate random expected values to produce a failure
        let expected_receipts_root = B256::random();
        let expected_logs_bloom = Bloom::random();

        // Create a vector of 5 random Receipt instances
        let receipts = vec![Receipt::default(); 5];

        assert!(verify_receipts(expected_receipts_root, expected_logs_bloom, &receipts).is_err());
    }

    #[test]
    fn test_compare_receipts_root_and_logs_bloom_success() {
        let calculated_receipts_root = B256::random();
        let calculated_logs_bloom = Bloom::random();

        let expected_receipts_root = calculated_receipts_root;
        let expected_logs_bloom = calculated_logs_bloom;

        assert!(compare_receipts_root_and_logs_bloom(
            calculated_receipts_root,
            calculated_logs_bloom,
            expected_receipts_root,
            expected_logs_bloom
        )
        .is_ok());
    }

    #[test]
    fn test_compare_receipts_root_failure() {
        let calculated_receipts_root = B256::random();
        let calculated_logs_bloom = Bloom::random();

        let expected_receipts_root = B256::random();
        let expected_logs_bloom = calculated_logs_bloom;

        assert_eq!(
            compare_receipts_root_and_logs_bloom(
                calculated_receipts_root,
                calculated_logs_bloom,
                expected_receipts_root,
                expected_logs_bloom
            ),
            Err(ConsensusError::BodyReceiptRootDiff(
                GotExpected { got: calculated_receipts_root, expected: expected_receipts_root }
                    .into()
            ))
        );
    }

    #[test]
    fn test_compare_log_bloom_failure() {
        let calculated_receipts_root = B256::random();
        let calculated_logs_bloom = Bloom::random();

        let expected_receipts_root = calculated_receipts_root;
        let expected_logs_bloom = Bloom::random();

        assert_eq!(
            compare_receipts_root_and_logs_bloom(
                calculated_receipts_root,
                calculated_logs_bloom,
                expected_receipts_root,
                expected_logs_bloom
            ),
            Err(ConsensusError::BodyBloomLogDiff(
                GotExpected { got: calculated_logs_bloom, expected: expected_logs_bloom }.into()
            ))
        );
    }
}
