//! Implements Compact for alloy types.

/// Will make it a pub mod if test-utils is enabled
macro_rules! cond_mod {
    ($($mod_name:ident),*) => {
        $(
            #[cfg(feature = "test-utils")]
            pub mod $mod_name;
            #[cfg(not(feature = "test-utils"))]
            pub(crate) mod $mod_name;
        )*
    };
}

cond_mod!(
    access_list,
    authorization_list,
    genesis_account,
    header,
    log,
    signature,
    trie,
    txkind,
    withdrawal
);

pub mod transaction;

#[cfg(test)]
mod tests {
    use crate::{
        alloy::{
            genesis_account::{GenesisAccount, GenesisAccountRef, StorageEntries, StorageEntry},
            header::{Header, HeaderExt},
            transaction::{
                eip1559::TxEip1559, eip2930::TxEip2930, eip4844::TxEip4844, eip7702::TxEip7702,
                legacy::TxLegacy,
            },
            withdrawal::Withdrawal,
        },
        test_utils::UnusedBits,
        validate_bitflag_backwards_compat,
    };

    #[test]
    fn validate_bitflag_backwards_compat() {
        // In case of failure, refer to the documentation of the
        // [`validate_bitflag_backwards_compat`] macro for detailed instructions on handling
        // it.
        validate_bitflag_backwards_compat!(Header, UnusedBits::Zero);
        validate_bitflag_backwards_compat!(HeaderExt, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(TxEip2930, UnusedBits::Zero);
        validate_bitflag_backwards_compat!(StorageEntries, UnusedBits::Zero);
        validate_bitflag_backwards_compat!(StorageEntry, UnusedBits::Zero);

        validate_bitflag_backwards_compat!(GenesisAccountRef<'_>, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(GenesisAccount, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(TxEip1559, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(TxEip4844, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(TxEip7702, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(TxLegacy, UnusedBits::NotZero);
        validate_bitflag_backwards_compat!(Withdrawal, UnusedBits::NotZero);
    }
}
