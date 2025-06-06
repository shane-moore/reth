use alloy_primitives::B256;
use reth_consensus::{ConsensusError, FullConsensus};
use reth_delayed_execution::DelayedExecutionOutcome;
use reth_provider::{
    BlockReader, HeaderProvider, ProviderError, StateProviderFactory, DBProvider,
    LatestStateProviderRef,
};
use reth_primitives_traits::{NodePrimitives, Block};
use reth_stages_api::{
    EntitiesCheckpoint, ExecInput, ExecOutput, Stage, StageCheckpoint, StageError, StageId,
    UnwindInput, UnwindOutput,
};
use std::{sync::Arc, task::{Poll, Context}};
use crate::stages::validate_parent_delayed_execution;

/// Stage performing static validation of blocks using delayed execution metadata.
#[derive(Debug, Clone)]
pub struct StaticValidationStage<E: reth_evm::ConfigureEvm> {
    consensus: Arc<dyn FullConsensus<E::Primitives, Error = ConsensusError>>,
}

impl<E: reth_evm::ConfigureEvm> StaticValidationStage<E> {
    pub const fn new(consensus: Arc<dyn FullConsensus<E::Primitives, Error = ConsensusError>>) -> Self {
        Self { consensus }
    }
}

impl<E, Provider> Stage<Provider> for StaticValidationStage<E>
where
    E: reth_evm::ConfigureEvm,
    Provider: DBProvider
        + BlockReader<Block=<E::Primitives as NodePrimitives>::Block,
                      Header=<E::Primitives as NodePrimitives>::BlockHeader>
        + HeaderProvider
        + StateProviderFactory,
{
    fn id(&self) -> StageId { StageId::StaticValidation }

    fn poll_execute_ready(&mut self, _cx: &mut Context<'_>, _input: ExecInput) -> Poll<Result<(), StageError>> {
        Poll::Ready(Ok(()))
    }

    fn execute(&mut self, provider: &Provider, input: ExecInput) -> Result<ExecOutput, StageError> {
        if input.target_reached() {
            return Ok(ExecOutput::done(input.checkpoint()))
        }

        let (range, is_final) = input.next_block_range_with_threshold(u64::MAX);
        let mut checkpoint = EntitiesCheckpoint::default();
        let mut last = input.checkpoint().block_number;
        for number in range {
            let block = provider
                .recovered_block(number.into(), reth_provider::TransactionVariant::NoHash)?
                .ok_or_else(|| ProviderError::HeaderNotFound(number.into()))?;
            let parent_hash = block.parent_hash();
            let parent_header = provider
                .sealed_header(parent_hash.into())?
                .ok_or_else(|| ProviderError::HeaderNotFound(parent_hash.into()))?;
            let parent_state_root = parent_header.state_root();
            let parent_outcome = DelayedExecutionOutcome::from_header(parent_header.header());
            let state = LatestStateProviderRef::new(provider);
            if let Err(err) = validate_parent_delayed_execution(&block, parent_state_root, &parent_outcome, &state) {
                return Err(StageError::Block { block: Box::new(block.block_with_parent()), error: reth_stages_api::BlockErrorKind::Validation(err) });
            }
            checkpoint.processed += 1;
            last = number;
        }

        Ok(ExecOutput { checkpoint: StageCheckpoint::new(last).with_entities_stage_checkpoint(checkpoint), done: is_final })
    }

    fn unwind(&mut self, _provider: &Provider, input: UnwindInput) -> Result<UnwindOutput, StageError> {
        Ok(UnwindOutput { checkpoint: input.checkpoint })
    }
}
